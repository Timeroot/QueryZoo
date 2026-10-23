#!/usr/bin/env python3
"""Run the zoo's checks.

    python3 tests/run.py                 # everything quick
    python3 tests/run.py --list
    python3 tests/run.py --only links dom
    python3 tests/run.py --slow          # adds the small-n oracle

Checks that need the data load share one `Zoo()`, because building it costs
about ninety seconds; checks that only read `site/` run first so a stale or
missing build is reported before that minute and a half is spent.
"""
import argparse
import importlib
import sys
import time

sys.path.insert(0, __file__.rsplit("/", 1)[0])
import lib  # noqa: E402

# name, module, one-liner. Order is cheapest-first.
CHECKS = [
    ("functions", "check_functions", "lint data/functions/*.yaml on their own"),
    ("links", "check_links", "every internal link and anchor in site/"),
    ("dom", "check_dom", "drive the built pages under jsdom"),
    ("blanks", "check_blanks", "census of what the matrix cells hold"),
    ("coverage", "check_coverage", "pairs with no separation of any kind"),
    ("values", "check_values", "recorded values against the zoo's unit bounds"),
    ("smalln", "smalln.check_smalln", "brute-force all small functions [slow]"),
]
SLOW = {"smalln"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="+", metavar="NAME")
    ap.add_argument("--slow", action="store_true", help="include the slow checks")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("-q", "--quiet", action="store_true")
    args = ap.parse_args()

    if args.list:
        for name, _, desc in CHECKS:
            print(f"  {name:10s} {desc}")
        return 0

    todo = [c for c in CHECKS if (args.only and c[0] in args.only)
            or (not args.only and (args.slow or c[0] not in SLOW))]
    if args.only:
        unknown = set(args.only) - {c[0] for c in CHECKS}
        if unknown:
            print("unknown check(s):", " ".join(sorted(unknown)))
            return 2

    ctx = lib.Ctx(verbose=not args.quiet)
    results = []
    for name, mod, desc in todo:
        print(f"\n=== {name}: {desc}")
        t = time.time()
        m = importlib.import_module(mod)
        try:
            ok = m.run(ctx)  # True pass, False fail, None skipped
        except Exception:  # a check that dies is a failed check
            import traceback

            traceback.print_exc()
            ok = False
        dt = time.time() - t
        results.append((name, ok, dt))
        print(f"--- {name}: {'skipped' if ok is None else 'ok' if ok else 'FAILED'}  [{dt:.0f}s]")

    print("\n" + "=" * 60)
    for name, ok, dt in results:
        print(f"  {'ok  ' if ok else 'SKIP' if ok is None else 'FAIL'}  {name:10s} {dt:5.0f}s")
    failed = [n for n, ok, _ in results if ok is False]
    print(f"{len(failed)} failed" if failed else "all clear")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
