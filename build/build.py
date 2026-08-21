"""Build orchestrator: ingest → derive → render → downloads → compress → check."""

import html.parser
import pathlib
import shutil
import sys
import time
import urllib.parse

ROOT = pathlib.Path(__file__).resolve().parent.parent
DIST = ROOT / "dist"


class LinkCollector(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []

    def handle_starttag(self, tag, attrs):
        for k, v in attrs:
            if k in ("href", "src") and v:
                self.links.append(v)


def check_links():
    errors = []
    for page in (DIST / "heilbronn").rglob("*.html"):
        parser = LinkCollector()
        try:
            parser.feed(page.read_text())
        except Exception as exc:
            errors.append(f"{page}: HTML parse error: {exc}")
            continue
        for link in parser.links:
            u = urllib.parse.urlparse(link)
            if u.scheme in ("http", "https", "data") or link.startswith("#"):
                continue
            path = u.path
            if path.startswith("/"):
                target = DIST / path.lstrip("/")
            else:
                target = page.parent / path
            if path.endswith("/"):
                target = target / "index.html"
            if not target.exists():
                errors.append(f"{page.relative_to(DIST)}: broken link {link}")
    return errors


def run(stages=None):
    t0 = time.time()
    stages = stages or ["ingest", "render", "downloads", "compress", "check"]

    if "ingest" in stages:
        from .ingest import ingest
        ingest()

    docs = env = assets = None
    if "render" in stages:
        if DIST.exists():
            shutil.rmtree(DIST)
        from .render_pages import render
        docs, _, assets, env = render()

    if "downloads" in stages:
        from .downloads import write_downloads
        from .render_pages import load_docs, render_extra, make_env, hash_assets
        values_name = write_downloads(docs or load_docs())
        if env is None:
            env, assets = make_env(), hash_assets()
        render_extra(env, assets, values_name)

    if "compress" in stages:
        from .compress import compress_all
        n = compress_all()
        print(f"precompressed {n} files (.gz + .br)")

    if "check" in stages:
        errors = check_links()
        for e in errors:
            print("CHECK:", e, file=sys.stderr)
        if errors:
            sys.exit(f"{len(errors)} check failure(s)")

    print(f"build ok in {time.time() - t0:.1f}s -> {DIST}")
