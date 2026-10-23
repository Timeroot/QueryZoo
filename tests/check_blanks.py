"""Census of what the matrix cells actually hold, both sides.

A cell counts as shown in a setting when neither measure is `defined: no`
there -- exactly the rule app.js uses to hide rows and columns.  For each shown
cell: is there an upper bound, is there a separation, or is it wholly empty?

Empties that involve a dimensionless measure are counted apart, because those
cells can never be filled: a quantity in [0,1] is not a query count and no
exponent relates the two.  The rest are the ones the ratchet watches.
"""
import collections

import lib

SETTINGS = ["total", "partial", "relation"]


def run(ctx):
    z = ctx.zoo
    dimless = {m["id"] for m in z.measures if m.get("dimensionless")}

    def shown(mid, s):
        m = z.measure.get(mid)
        return bool(m) and m["settings"].get(s, {}).get("defined") != "no"

    def state(a, b, s):
        sl = (z.best.get((a, b)) or {}).get(s) or {}
        vs = sl.get("verdicts") or []
        return (bool(sl.get("up")) or any(v["side"] == "upper" for v in vs),
                bool(sl.get("lo")) or any(v["side"] == "lower" for v in vs))

    ok = True
    for s in SETTINGS:
        liv = [m["id"] for m in z.measures if shown(m["id"], s)]
        empty, no_up, no_lo = [], [], []
        for a in liv:
            for b in liv:
                if a == b:
                    continue
                u, l = state(a, b, s)
                if not u and not l:
                    empty.append((a, b))
                if not u:
                    no_up.append((a, b))
                if not l:
                    no_lo.append((a, b))
        rest = [p for p in empty if p[0] not in dimless and p[1] not in dimless]
        ctx.say("  %-9s %5d cells shown | %4d wholly empty (%d dimensionless, %d not) "
                "| %4d no upper side | %4d no separation"
                % (s, len(liv) * (len(liv) - 1), len(empty), len(empty) - len(rest),
                   len(rest), len(no_up), len(no_lo)))
        if rest:
            c = collections.Counter()
            for a, b in rest:
                c[a] += 1
                c[b] += 1
            ctx.say("       worst:", dict(c.most_common(8)))
            ctx.say("       e.g. ", sorted(rest)[:10])
        ok &= lib.ratchet(ctx, f"blanks.{s}", len(rest))
    return ok
