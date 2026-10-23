"""Ordered pairs with no separation of any kind on record.

Generous about what counts as covered: a polynomial gap, an exponential one,
an unbounded verdict or a merely logarithmic one all count.  (Log-shaped
separations are separations; an earlier version of this audit missed them and
overstated the hole by a wide margin.)

Dimensionless measures are split out for the reason given in check_blanks.
"""
import lib

SETTINGS = ["total", "partial", "relation"]


def run(ctx):
    z = ctx.zoo
    dimless = {m["id"] for m in z.measures if m.get("dimensionless")}
    import build

    def lo(a, b, s):
        sl = (z.best.get((a, b)) or {}).get(s)
        if not sl:
            return None
        if sl.get("lo"):
            return "poly"
        for v in (sl.get("verdicts") or []):
            if v["side"] == "lower" and v["kind"] in ("unbounded", "exp", "log"):
                return v["kind"]
        return None

    ok = True
    for s in SETTINGS:
        liv = [m["id"] for m in z.measures if z._defined(m["id"], s)]
        blanks = [(a, b) for a in liv for b in liv if a != b and not lo(a, b, s)]
        real = [p for p in blanks if p[0] not in dimless and p[1] not in dimless]
        ctx.say("  %-9s %5d of %5d ordered pairs have no lower side "
                "(%d dimensionless, %d otherwise)"
                % (s, len(blanks), len(liv) * (len(liv) - 1),
                   len(blanks) - len(real), len(real)))
        for a, b in real[:20]:
            sl = (z.best.get((a, b)) or {}).get(s) or {}
            up = sl.get("up")
            ctx.say("       %-8s vs %-8s  up=%s" % (
                a, b, (build.fmt_exp(up["exp"]) + "/" + up["origin"]) if up else "NONE"))
        if len(real) > 20:
            ctx.say(f"       ... and {len(real) - 20} more")
        ok &= lib.ratchet(ctx, f"nosep.{s}", len(real))
    return ok
