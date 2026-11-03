#!/usr/bin/env python3
"""Archive Linda Cumines WordPress pages as static files, without third-party packages.

The output is built in a temporary directory and replaces --output only after
the homepage has been fetched. Review archive-report.json for individual failures.
"""

from __future__ import annotations

import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
from html import escape as html_escape, unescape
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import posixpath
import re
import shutil
import sys
import tempfile
import time
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qsl, unquote, urljoin, urlsplit, urlunsplit
from urllib.request import Request, urlopen
from xml.sax.saxutils import escape as xml_escape


ASSET_EXTENSIONS = {
    ".avif", ".css", ".csv", ".doc", ".docx", ".eot", ".gif", ".ico",
    ".jpeg", ".jpg", ".js", ".json", ".m4a", ".mp3", ".mp4", ".ogg",
    ".otf", ".pdf", ".png", ".svg", ".txt", ".webm", ".webp", ".woff",
    ".woff2", ".xml", ".zip",
}
SKIP_PATHS = ("/wp-admin/", "/wp-json/", "/wp-login.php", "/xmlrpc.php")
ACTION_QUERY_KEYS = {"add-to-cart", "action", "logout", "preview", "_wpnonce", "wc-ajax"}
DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.0 Safari/605.1.15"
)
ATTR_RE = re.compile(
    r"(?P<name>[\w:-]+)(?P<eq>\s*=\s*)(?:(?P<quote>['\"])(?P<value>.*?)(?P=quote)|(?P<unquoted>[^\s>]+))",
    re.S,
)
CSS_URL_RE = re.compile(r"url\(\s*(?P<quote>['\"]?)(?P<url>.*?)(?P=quote)\s*\)", re.I | re.S)
CSS_IMPORT_RE = re.compile(r"(@import\s+)(?P<quote>['\"])(?P<url>[^'\"]+)(?P=quote)", re.I)


def normalise(url: str) -> str:
    parts = urlsplit(url)
    path = parts.path or "/"
    own_host = parts.hostname in ("lindacumines.com.au", "www.lindacumines.com.au")
    host = "lindacumines.com.au" if own_host else parts.netloc.lower()
    scheme = "https" if own_host and parts.scheme.lower() == "http" else parts.scheme.lower()
    return urlunsplit((scheme, host, path, parts.query, ""))


def safe_path(url: str, page: bool) -> Path:
    parts = urlsplit(url)
    segments = [unquote(item) for item in parts.path.split("/") if item]
    if any(item in (".", "..") or "/" in item or "\\" in item or "\x00" in item for item in segments):
        raise ValueError(f"Unsafe URL path: {url}")
    if page:
        if segments and Path(segments[-1]).suffix.lower() in (".html", ".htm"):
            result = Path(*segments)
        else:
            result = Path(*segments, "index.html") if segments else Path("index.html")
        if parts.query:
            digest = hashlib.sha256(parts.query.encode()).hexdigest()[:12]
            result = result.parent / f"__query_{digest}" / result.name
        return result
    result = Path(*segments) if segments else Path("index.bin")
    if parts.query:
        digest = hashlib.sha256(parts.query.encode()).hexdigest()[:12]
        result = result.with_name(f"{result.stem}__query_{digest}{result.suffix}")
    return result


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.pages: set[str] = set()
        self.assets: set[str] = set()
        self.css: list[str] = []
        self.in_style = False

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        if tag == "style":
            self.in_style = True
        if tag == "a" and values.get("href"):
            self.pages.add(values["href"] or "")
        if tag == "link" and values.get("href"):
            rel = (values.get("rel") or "").lower()
            if any(word in rel for word in ("stylesheet", "icon", "preload", "prefetch", "apple-touch-icon")):
                self.assets.add(values["href"] or "")
        for attr in ("src", "poster", "data"):
            if tag in ("img", "script", "source", "video", "audio", "embed", "object", "input") and values.get(attr):
                self.assets.add(values[attr] or "")
        for attr in ("srcset", "data-src", "data-srcset"):
            if values.get(attr):
                for item in (values[attr] or "").split(","):
                    self.assets.add(item.strip().split()[0])
        if values.get("data-tbfullwidthvideo"):
            self.assets.add(values["data-tbfullwidthvideo"] or "")
        if values.get("style"):
            self.css.append(values["style"] or "")

    def handle_data(self, data: str) -> None:
        if self.in_style:
            self.css.append(data)

    def handle_endtag(self, tag: str) -> None:
        if tag == "style":
            self.in_style = False


def css_urls(css: str) -> set[str]:
    urls = {match.group("url").strip() for match in CSS_URL_RE.finditer(css)}
    urls.update(match.group("url").strip() for match in CSS_IMPORT_RE.finditer(css))
    return urls


class HtmlRewriter(HTMLParser):
    def __init__(self, source_url: str, paths: dict[str, Path]) -> None:
        super().__init__(convert_charrefs=False)
        self.source_url = source_url
        self.paths = paths
        self.output: list[str] = []
        self.in_style = False

    def rewrite_url(self, value: str) -> str:
        if not value or value.startswith(("#", "data:", "mailto:", "tel:", "javascript:")):
            return value
        absolute = normalise(urljoin(self.source_url, unescape(value)))
        local = self.paths.get(absolute)
        if local is None:
            return value
        fragment = urlsplit(value).fragment
        source = self.paths.get(self.source_url)
        if source is None:
            return value
        relative = posixpath.relpath(local.as_posix(), source.parent.as_posix())
        return relative + ("#" + fragment if fragment else "")

    def rewrite_css(self, css: str) -> str:
        css = CSS_URL_RE.sub(
            lambda m: f"url({m.group('quote')}{self.rewrite_url(m.group('url'))}{m.group('quote')})", css
        )
        return CSS_IMPORT_RE.sub(
            lambda m: f"{m.group(1)}{m.group('quote')}{self.rewrite_url(m.group('url'))}{m.group('quote')}", css
        )

    def rewrite_tag(self, tag: str, raw: str) -> str:
        def replace(match: re.Match[str]) -> str:
            name = match.group("name").lower()
            value = match.group("value") if match.group("quote") else match.group("unquoted")
            if name == "style":
                replacement = self.rewrite_css(value)
            elif name in ("srcset", "data-srcset"):
                replacement = ", ".join(
                    self.rewrite_url(item.strip().split()[0]) +
                    (" " + " ".join(item.strip().split()[1:]) if len(item.strip().split()) > 1 else "")
                    for item in value.split(",") if item.strip()
                )
            elif name in ("href", "src", "poster", "data-src", "data-tbfullwidthvideo") or (name == "data" and tag == "object"):
                replacement = self.rewrite_url(value)
            else:
                return match.group(0)
            quote = match.group("quote") or ""
            return f"{match.group('name')}{match.group('eq')}{quote}{replacement}{quote}"
        return ATTR_RE.sub(replace, raw)

    @staticmethod
    def discard_tag(tag: str, attrs: list[tuple[str, str | None]]) -> bool:
        values = dict(attrs)
        if tag == "meta" and (values.get("name") or "").lower() == "generator":
            return True
        if tag != "link":
            return False
        rel = (values.get("rel") or "").lower()
        href = values.get("href") or ""
        path = urlsplit(href).path.lower()
        return (rel in ("edituri", "wlwmanifest", "https://api.w.org/")
                or path.startswith(("/wp-json/", "/xmlrpc.php"))
                or path.endswith("/feed/") or path == "/feed/")

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if not self.discard_tag(tag, attrs):
            rel = (dict(attrs).get("rel") or "").lower()
            self.output.append(self.get_starttag_text() if tag == "link" and rel == "canonical"
                               else self.rewrite_tag(tag, self.get_starttag_text()))
        if tag == "style":
            self.in_style = True

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if not self.discard_tag(tag, attrs):
            rel = (dict(attrs).get("rel") or "").lower()
            self.output.append(self.get_starttag_text() if tag == "link" and rel == "canonical"
                               else self.rewrite_tag(tag, self.get_starttag_text()))

    def handle_endtag(self, tag: str) -> None:
        self.output.append(f"</{tag}>")
        if tag == "style":
            self.in_style = False

    def handle_data(self, data: str) -> None:
        self.output.append(self.rewrite_css(data) if self.in_style else data)

    def handle_entityref(self, name: str) -> None:
        self.output.append(f"&{name};")

    def handle_charref(self, name: str) -> None:
        self.output.append(f"&#{name};")

    def handle_comment(self, data: str) -> None:
        self.output.append(f"<!--{data}-->")

    def handle_decl(self, decl: str) -> None:
        self.output.append(f"<!{decl}>")

    def handle_pi(self, data: str) -> None:
        self.output.append(f"<?{data}>")


class StaticCleanup(HTMLParser):
    """Remove WordPress controls that cannot work on a static host."""

    VIDEO_STYLE = (
        '<style id="static-archive-video-style">'
        '.static-archive-video-row{position:relative;overflow:hidden}'
        '.static-archive-video{position:absolute;inset:0;width:100%;height:100%;'
        'object-fit:cover;z-index:0;pointer-events:none}'
        '.static-archive-video-row>.builder_row_cover{z-index:1}'
        '.static-archive-video-row>.row_inner{position:relative;z-index:2}'
        '</style>'
    )

    def __init__(self, video_styles_needed: bool = False) -> None:
        super().__init__(convert_charrefs=False)
        self.output: list[str] = []
        self.skip_tag: str | None = None
        self.skip_depth = 0
        self.in_style = False
        self.video_styles_needed = video_styles_needed

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if self.skip_tag:
            if tag == self.skip_tag:
                self.skip_depth += 1
            return
        values = dict(attrs)
        if tag == "div" and values.get("id") == "respond":
            self.skip_tag, self.skip_depth = "div", 1
        elif tag == "form":
            self.skip_tag, self.skip_depth = "form", 1
        elif tag == "a" and urlsplit(values.get("href") or "").path == "/wp-login.php":
            self.skip_tag, self.skip_depth = "a", 1
        elif tag == "link" and "wp-content/plugins/loading-page/" in (values.get("href") or ""):
            return
        elif tag == "script" and ("wp-content/plugins/loading-page/" in (values.get("src") or "")
                                  or (values.get("id") or "").startswith("codepeople-loading-page-")):
            self.skip_tag, self.skip_depth = "script", 1
        else:
            raw = self.get_starttag_text()
            video_url = values.get("data-tbfullwidthvideo") if tag == "div" else None
            already_static = "static-archive-video-row" in (values.get("class") or "").split()
            if video_url and not already_static:
                if values.get("class"):
                    raw = re.sub(r"(\bclass\s*=\s*)(['\"])(.*?)\2",
                                 lambda match: (f"{match.group(1)}{match.group(2)}{match.group(3)} "
                                                f"static-archive-video-row{match.group(2)}"),
                                 raw, count=1, flags=re.S)
                else:
                    raw = raw.replace("<div", '<div class="static-archive-video-row"', 1)
                self.output.append(raw)
                source = html_escape(video_url, quote=True)
                self.output.append(f'<video class="static-archive-video" autoplay muted loop playsinline '
                                   f'preload="metadata" aria-hidden="true"><source src="{source}" '
                                   'type="video/mp4"></video>')
            else:
                self.output.append(raw)
            if tag == "style":
                self.in_style = True

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        if not self.skip_tag and not (tag == "link" and
            "wp-content/plugins/loading-page/" in (dict(attrs).get("href") or "")):
            self.output.append(self.get_starttag_text())

    def handle_endtag(self, tag: str) -> None:
        if self.skip_tag:
            if tag == self.skip_tag:
                self.skip_depth -= 1
                if self.skip_depth == 0:
                    self.skip_tag = None
            return
        if tag == "head" and self.video_styles_needed:
            self.output.append(self.VIDEO_STYLE)
        self.output.append(f"</{tag}>")
        if tag == "style":
            self.in_style = False

    def handle_data(self, data: str) -> None:
        if not self.skip_tag:
            if self.in_style:
                data = re.sub(r"body\s*\{\s*visibility\s*:\s*hidden\s*;?\s*\}", "", data, flags=re.I)
            self.output.append(data)

    def handle_entityref(self, name: str) -> None:
        if not self.skip_tag:
            self.output.append(f"&{name};")

    def handle_charref(self, name: str) -> None:
        if not self.skip_tag:
            self.output.append(f"&#{name};")

    def handle_comment(self, data: str) -> None:
        if not self.skip_tag:
            self.output.append(f"<!--{data}-->")

    def handle_decl(self, decl: str) -> None:
        if not self.skip_tag:
            self.output.append(f"<!{decl}>")

    def handle_pi(self, data: str) -> None:
        if not self.skip_tag:
            self.output.append(f"<?{data}>")


class Archiver:
    def __init__(self, start: str, output: Path, timeout: int, delay: float, max_pages: int, max_assets: int,
                 cname: str | None = None, user_agent: str = DEFAULT_USER_AGENT) -> None:
        self.start = normalise(start)
        self.output = output
        self.timeout = timeout
        self.delay = delay
        self.max_pages = max_pages
        self.max_assets = max_assets
        self.cname = cname
        self.user_agent = user_agent
        host = urlsplit(self.start).hostname or ""
        self.hosts = {host}
        self.pages: dict[str, str] = {}
        self.assets: dict[str, bytes] = {}
        self.asset_charsets: dict[str, str] = {}
        self.paths: dict[str, Path] = {}
        self.failures: list[dict[str, str]] = []
        self.external: set[str] = set()
        self.skipped: set[str] = set()

    def eligible(self, url: str) -> bool:
        parts = urlsplit(url)
        keys = {key.lower() for key, _ in parse_qsl(parts.query, keep_blank_values=True)}
        return (parts.scheme in ("http", "https") and parts.hostname in self.hosts
                and not parts.path.startswith(SKIP_PATHS) and not keys.intersection(ACTION_QUERY_KEYS))

    def resolve(self, base: str, value: str) -> str | None:
        if not value or value.startswith(("#", "data:", "mailto:", "tel:", "javascript:")):
            return None
        url = normalise(urljoin(base, unescape(value)))
        if self.eligible(url):
            return url
        if urlsplit(url).hostname in self.hosts:
            self.skipped.add(url)
            return None
        if urlsplit(url).scheme in ("http", "https"):
            self.external.add(url)
        return None

    def fetch(self, url: str) -> tuple[bytes, str, str]:
        request = Request(url, headers={"User-Agent": self.user_agent, "Accept": "*/*"})
        if self.delay:
            time.sleep(self.delay)
        with urlopen(request, timeout=self.timeout) as response:
            final_url = normalise(response.geturl())
            if not self.eligible(final_url):
                raise ValueError(f"Redirected outside the site: {final_url}")
            data = response.read(128 * 1024 * 1024 + 1)
            if len(data) > 128 * 1024 * 1024:
                raise ValueError("Resource exceeds 128 MiB")
            charset = response.headers.get_content_charset() or "utf-8"
            content_type = response.headers.get_content_type()
            return data, charset, content_type

    def record_failure(self, url: str, error: Exception) -> None:
        self.failures.append({"url": url, "error": str(error)})
        print(f"FAILED {url}: {error}", file=sys.stderr)

    def crawl(self) -> None:
        page_queue = deque([self.start])
        asset_queue: deque[str] = deque()
        seen_pages: set[str] = set()
        seen_assets: set[str] = set()

        while page_queue:
            url = page_queue.popleft()
            if url in seen_pages:
                continue
            if len(seen_pages) >= self.max_pages:
                raise RuntimeError(f"Page limit reached ({self.max_pages}); increase --max-pages")
            seen_pages.add(url)
            try:
                data, charset, content_type = self.fetch(url)
                if content_type not in ("text/html", "application/xhtml+xml"):
                    asset_queue.append(url)
                    continue
                html = data.decode(charset, errors="replace")
                self.pages[url] = html
                self.paths[url] = safe_path(url, page=True)
                collector = LinkCollector()
                collector.feed(html)
                for value in sorted(collector.pages):
                    child = self.resolve(url, value)
                    if child:
                        if Path(urlsplit(child).path).suffix.lower() in ASSET_EXTENSIONS:
                            asset_queue.append(child)
                        elif child not in seen_pages:
                            page_queue.append(child)
                for value in sorted(collector.assets):
                    child = self.resolve(url, value)
                    if child:
                        asset_queue.append(child)
                for css in collector.css:
                    for value in css_urls(css):
                        child = self.resolve(url, value)
                        if child:
                            asset_queue.append(child)
                print(f"PAGE  {url}")
            except (HTTPError, URLError, UnicodeError, ValueError, OSError) as error:
                self.record_failure(url, error)

        while asset_queue:
            url = asset_queue.popleft()
            if url in seen_assets or url in self.pages:
                continue
            if len(seen_assets) >= self.max_assets:
                raise RuntimeError(f"Asset limit reached ({self.max_assets}); increase --max-assets")
            seen_assets.add(url)
            try:
                data, charset, content_type = self.fetch(url)
                self.assets[url] = data
                self.asset_charsets[url] = charset
                self.paths[url] = safe_path(url, page=False)
                if content_type == "text/css" or self.paths[url].suffix.lower() == ".css":
                    css = data.decode(charset, errors="replace")
                    for value in css_urls(css):
                        child = self.resolve(url, value)
                        if child:
                            asset_queue.append(child)
                print(f"ASSET {url}")
            except (HTTPError, URLError, UnicodeError, ValueError, OSError) as error:
                self.record_failure(url, error)

        if self.start not in self.pages:
            raise RuntimeError("Homepage could not be downloaded; existing output was left untouched")

    def write(self) -> None:
        self.output.parent.mkdir(parents=True, exist_ok=True)
        stage = Path(tempfile.mkdtemp(prefix=f".{self.output.name}-build-", dir=self.output.parent))
        stage.chmod(0o755)
        try:
            for url, html in self.pages.items():
                rewriter = HtmlRewriter(url, self.paths)
                rewriter.feed(html)
                rewritten = "".join(rewriter.output)
                cleanup = StaticCleanup(video_styles_needed="data-tbfullwidthvideo" in rewritten)
                cleanup.feed(rewritten)
                path = stage / self.paths[url]
                path.parent.mkdir(parents=True, exist_ok=True)
                rendered = "".join(cleanup.output)
                path.write_text(rendered, encoding="utf-8")
            for url, data in self.assets.items():
                path = stage / self.paths[url]
                path.parent.mkdir(parents=True, exist_ok=True)
                if path.suffix.lower() == ".css":
                    rewriter = HtmlRewriter(url, self.paths)
                    path.write_text(rewriter.rewrite_css(data.decode(self.asset_charsets[url], errors="replace")), encoding="utf-8")
                else:
                    path.write_bytes(data)
            canonical = self.start.rstrip("/")
            locations = set()
            for url in self.pages:
                parts = urlsplit(url)
                path = parts.path
                if not path.endswith("/") and not Path(path).suffix:
                    path += "/"
                locations.add(urlunsplit((urlsplit(canonical).scheme, urlsplit(canonical).netloc,
                                          path, parts.query, "")))
            locations = sorted(locations)
            sitemap = '<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
            sitemap += "".join(f"  <url><loc>{xml_escape(url)}</loc></url>\n" for url in locations)
            sitemap += "</urlset>\n"
            (stage / "sitemap.xml").write_text(sitemap, encoding="utf-8")
            (stage / "robots.txt").write_text("User-agent: *\nAllow: /\nSitemap: " + canonical + "/sitemap.xml\n", encoding="utf-8")
            (stage / ".nojekyll").touch()
            if self.cname:
                (stage / "CNAME").write_text(self.cname + "\n", encoding="utf-8")
            report = {
                "source": self.start,
                "generated_at_utc": datetime.now(timezone.utc).isoformat(),
                "pages": len(self.pages),
                "assets": len(self.assets),
                "failures": self.failures,
                "external_urls": sorted(self.external),
                "skipped_urls": sorted(self.skipped),
                "source_pages_with_forms": sorted(url for url, html in self.pages.items()
                                                  if re.search(r"<form\b", html, re.I)),
            }
            (stage / "archive-report.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
            backup = None
            if self.output.exists():
                backup = self.output.with_name(f".{self.output.name}-backup-{os.getpid()}")
                self.output.rename(backup)
            try:
                stage.rename(self.output)
            except OSError:
                if backup:
                    backup.rename(self.output)
                raise
            if backup:
                shutil.rmtree(backup)
            print(f"Saved {len(self.pages)} pages and {len(self.assets)} assets to {self.output}")
            print(f"Failures: {len(self.failures)}; see archive-report.json")
        finally:
            if stage.exists():
                shutil.rmtree(stage)


def finalize_existing(output: Path) -> None:
    """Apply static-only cleanup to an existing capture without contacting WordPress."""
    if not (output / "index.html").is_file():
        raise RuntimeError(f"No captured homepage at {output / 'index.html'}")
    changed = 0
    for path in output.rglob("*.html"):
        original = path.read_text(encoding="utf-8")
        cleanup = StaticCleanup(video_styles_needed=("data-tbfullwidthvideo" in original
                                                     and 'id="static-archive-video-style"' not in original))
        cleanup.feed(original)
        rendered = "".join(cleanup.output)
        if rendered != original:
            path.write_text(rendered, encoding="utf-8")
            changed += 1
    print(f"Finalized {changed} HTML files in {output}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", default="https://lindacumines.com.au/")
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1] / "public")
    parser.add_argument("--timeout", type=int, default=20)
    parser.add_argument("--delay", type=float, default=0.2, help="Seconds between requests")
    parser.add_argument("--max-pages", type=int, default=100)
    parser.add_argument("--max-assets", type=int, default=2000)
    parser.add_argument("--cname", help="Write CNAME for GitHub Pages custom-domain hosting")
    parser.add_argument("--user-agent", default=DEFAULT_USER_AGENT, help="HTTP User-Agent header")
    parser.add_argument("--finalize-existing", action="store_true",
                        help="Update existing output HTML without contacting WordPress")
    args = parser.parse_args()
    if args.finalize_existing:
        try:
            finalize_existing(args.output.resolve())
        except (RuntimeError, OSError) as error:
            print(f"Finalize stopped: {error}", file=sys.stderr)
            return 1
        return 0
    if urlsplit(args.start).scheme not in ("http", "https"):
        parser.error("--start must be an HTTP(S) URL")
    archiver = Archiver(args.start, args.output.resolve(), args.timeout, args.delay, args.max_pages, args.max_assets,
                        args.cname, args.user_agent)
    try:
        archiver.crawl()
        archiver.write()
    except (RuntimeError, OSError) as error:
        print(f"Archive stopped: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
