"""Every internal link and anchor in site/, including the pair app.

The pair pages are one dynamic page, so a link into `pair.html?a=X&b=Y#rel-...`
resolves against JSON the browser fetches rather than against anything in the
HTML; the anchors those payloads carry are pulled out of the shards here.
"""
import json
import re
from html.parser import HTMLParser
from urllib.parse import unquote, urlparse, parse_qs

import lib


class P(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.links = []
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        d = dict(attrs)
        if d.get("id"):
            self.ids.add(d["id"])
        if d.get("name"):
            self.ids.add(d["name"])
        if tag == "a" and d.get("href"):
            self.links.append(d["href"])
        if d.get("src"):
            self.links.append(d["src"])


def run(ctx):
    if not lib.need_site(ctx):
        return False
    site = ctx.site

    pages = {}
    for f in site.rglob("*.html"):
        p = P()
        p.feed(f.read_text())
        pages[f] = p

    # ids the pair app produces at runtime: relation record anchors
    rel_ids = set()
    for shard in (site / "api" / "pair").glob("*.json"):
        doc = json.loads(shard.read_text())
        for payload in doc["cols"].values():
            for blocks in (payload.get("rels") or {}).values():
                for h in blocks:
                    rel_ids.update(re.findall(r'<section class="relation" id="([^"]+)"', h))

    bad = []
    nlinks = 0
    for f, p in pages.items():
        for href in p.links:
            if href.startswith(("http://", "https://", "mailto:", "data:")):
                continue
            nlinks += 1
            u = urlparse(href)
            if href.startswith("#"):
                target, frag = f, href[1:]
            else:
                target = (f.parent / unquote(u.path)).resolve()
                frag = u.fragment
            if not str(target).startswith(str(site)):
                bad.append((f, href, "escapes site"))
                continue
            if target.is_dir():
                target = target / "index.html"
            if not target.exists():
                bad.append((f, href, "missing file"))
                continue
            if frag and target.suffix == ".html":
                tp = pages.get(target)
                if tp is not None and frag not in tp.ids and frag not in rel_ids:
                    bad.append((f, href, "missing anchor"))
            if target.name == "pair.html" and u.query:
                a = parse_qs(u.query).get("a", [""])[0]
                if not (site / "api" / "pair" / f"{a}.json").exists():
                    bad.append((f, href, "no shard for row " + a))

    ctx.say(f"  {len(pages)} pages, {nlinks} links, {len(bad)} problem(s)")
    for f, h, why in bad[:40]:
        ctx.bad(f"{f.relative_to(site)} -> {h} : {why}")
    return not bad
