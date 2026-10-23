"""Shared plumbing for the checks in this directory.

The one thing worth knowing: `Zoo()` takes about a minute and a half to load
and close, so the runner builds it once and hands the same object to every
check that wants it. Anything that needs the zoo should take it from the
context rather than constructing its own.
"""
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SITE = Path(os.environ.get("ZOO_SITE") or (ROOT / "site"))

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


class Ctx:
    """What a check is given: the zoo (lazily), the built site, and a log."""

    def __init__(self, verbose=True):
        self.root = ROOT
        self.site = SITE
        self.verbose = verbose
        self._zoo = None
        self.problems = []

    @property
    def zoo(self):
        if self._zoo is None:
            import build

            t = time.time()
            self.say(f"  (loading the zoo)")
            z = build.Zoo()
            self._zoo = z
            self.say(f"  (loaded in {time.time() - t:.0f}s)")
        return self._zoo

    def say(self, *a):
        if self.verbose:
            print(*a)

    def bad(self, msg):
        self.problems.append(msg)
        print("  !", msg)


RATCHET = Path(__file__).resolve().parent / "ratchet.json"


def ratchet(ctx, key, value):
    """A one-way count: coverage may improve, never regress.

    The audits below (blank cells, missing separations) have no natural pass
    condition -- the zoo is allowed to have holes.  What it is not allowed to
    do is quietly grow new ones, so each count is compared with the last
    recorded figure.  Run with ZOO_RATCHET=update to record improvements.
    """
    import json

    book = json.loads(RATCHET.read_text()) if RATCHET.exists() else {}
    was = book.get(key)
    update = os.environ.get("ZOO_RATCHET") == "update"
    if was is None:
        ctx.say(f"  ratchet {key}: {value} (new)")
    elif value > was:
        ctx.bad(f"{key}: {value}, was {was} -- coverage went backwards")
    elif value < was:
        ctx.say(f"  ratchet {key}: {value}, was {was} -- better"
                + ("" if update else "; ZOO_RATCHET=update to record it"))
    if update and value != was:
        book[key] = value
        RATCHET.write_text(json.dumps(dict(sorted(book.items())), indent=1) + "\n")
    return was is None or value <= was


def node_path():
    """Where jsdom lives. Installed copies win; /tmp is the fallback we had."""
    for cand in (os.environ.get("NODE_PATH"), ROOT / "node_modules", "/tmp/node_modules"):
        if not cand:
            continue
        p = Path(cand)
        if (p / "jsdom").exists():
            return str(p)
    return None


def need_site(ctx):
    """Every DOM and link check reads site/; say so plainly if it is not there."""
    if not (ctx.site / "matrix.html").exists():
        print(f"  site/ not built at {ctx.site} -- run `python3 build.py` first")
        return False
    return True
