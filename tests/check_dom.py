"""Run the jsdom drivers in tests/dom/ against the built site.

Node and jsdom are optional: if jsdom is not installed anywhere we can find,
the drivers exit 77 and this check reports itself skipped rather than failed.
"""
import os
import subprocess

import lib

DRIVERS = ["views.js", "scope.js", "ladder.js", "gaps.js", "pair.js", "nbrs.js"]


def run(ctx):
    if not lib.need_site(ctx):
        return False
    np = lib.node_path()
    env = dict(os.environ, ZOO_SITE=str(ctx.site))
    if np:
        env["NODE_PATH"] = np
    ctx.say(f"  jsdom from {np or '(not found)'}")

    fails, skips = [], []
    for d in DRIVERS:
        ctx.say(f"  -- {d}")
        try:
            p = subprocess.run(["node", str(lib.ROOT / "tests" / "dom" / d)],
                               env=env, capture_output=True, text=True)
        except FileNotFoundError:
            ctx.say("  node is not installed; skipping the DOM drivers")
            return None
        if ctx.verbose and p.stdout:
            print(p.stdout.rstrip())
        if p.returncode == 77:
            skips.append(d)
        elif p.returncode:
            fails.append(d)
            if p.stderr:
                print(p.stderr.rstrip()[-2000:])
            ctx.bad(f"{d} failed")
    if fails:
        return False
    return None if len(skips) == len(DRIVERS) else True
