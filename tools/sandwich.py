#!/usr/bin/env python3
"""For each function, which measures are pinned by the values already recorded?

A measure M is sandwiched at f when the zoo knows a linear-exponent upper bound
M = O(A) for some A whose value on f carries an upper bound, and a linear lower
bound M = Omega(B) likewise with a lower bound on val(B), and the two growth
rates agree.  Then val(M) = Theta(.) and can be written down for free.

An authoring aid, not a check: it says where new values can be had cheaply.

Usage:  python3 tools/sandwich.py [FunctionId ...]
        with ids, loose sandwiches are listed too
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import build  # noqa: E402
import growth  # noqa: E402


def linear(f):
    """Is this fact 'M = O(A)', exponent 1, no log blow-up?"""
    return (f and f["side"] == "upper" and f["kind"] in ("exact", "theta", "const")
            and abs(f["exp"] - 1) < 1e-9 and abs(f["log"]) < 1e-9)


def report(z, fn):
    s = fn["kind"]
    env, why = z._family_env(fn)
    if env is None:
        return []
    up, lo = {}, {}
    for v in fn.get("values", []):
        try:
            val = growth.parse_value(v["value"], env)
        except growth.Unparsable:
            continue
        if val.up is not None and v["measure"] not in up:
            up[v["measure"]] = (v["value"], val.up)
        if val.lo is not None and v["measure"] not in lo:
            lo[v["measure"]] = (v["value"], val.lo)
    have = {v["measure"] for v in fn.get("values", [])}
    out = []
    for mid, m in z.measure.items():
        if mid in have or m["settings"].get(s, {}).get("defined") != "yes":
            continue
        ups = [(a, g, txt) for a, (txt, g) in up.items()
               if linear(((z.best.get((mid, a)) or {}).get(s) or {}).get("up"))]
        los = [(b, g, txt) for b, (txt, g) in lo.items()
               if linear(((z.best.get((b, mid)) or {}).get(s) or {}).get("up"))]
        if not ups or not los:
            continue
        ups.sort(key=lambda t: t[1].key())                 # tightest upper first
        los.sort(key=lambda t: t[1].key(), reverse=True)   # largest lower first
        ua, ug, utxt = ups[0]
        lb, lg, ltxt = los[0]
        tight = (growth.compare(ug, lg) is None and growth.compare(lg, ug) is None)
        out.append((tight, mid, lb, ltxt, ua, utxt))
    out.sort(key=lambda r: (not r[0], r[1]))
    return out


def main(ids):
    z = build.Zoo()
    for fn in z.functions:
        if ids and fn["id"] not in ids:
            continue
        rows = [r for r in report(z, fn) if r[0] or ids]
        if not rows:
            continue
        n_t = sum(1 for r in rows if r[0])
        print(f"== {fn['id']} ({fn['kind']}) -- {n_t} pinned"
              + (f", {len(rows) - n_t} loose" if ids else ""))
        for tight, mid, lb, ltxt, ua, utxt in rows:
            mark = "TIGHT" if tight else "  ~  "
            print(f"   {mark} {mid:9} {lb} = {ltxt}   <=  {mid}  <=  {ua} = {utxt}")


if __name__ == "__main__":
    main(sys.argv[1:])
