"""Test the zoo's upper bounds against every small function, in every setting.

For every ordered pair of measures the zoo records an upper bound
`a <= C * b^e (log b)^l` per setting.  When that bound is recorded as `exact`
-- the zoo's strongest form, meaning the inequality holds on the nose with no
hidden constant -- it must hold at every single function, including the tiny
ones.  The census in oracle.py has all of them for total functions on n <= 4,
partial functions on n <= 3, and relations on one bit, so this is a complete
test of those claims in that range.

Bounds recorded up to a constant cannot be tested this way: down here every
measure is between 0 and 4, so any constant factor swallows everything.  For
those the check only reports the largest constant the census demands, which is
information, not a verdict.

Run with `python3 tests/run.py --only smalln` (or --slow to get it in the full
sweep).  Rebuild the census with `python3 tests/smalln/oracle.py` after
changing a measure's definition.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import oracle  # noqa: E402

TOL = 1e-6          # the LP-derived values are floats
LOOSE = 6.0         # constants above this are worth a look, not a failure
POLY = ("exact", "theta", "const", "tilde")


def rows_of(census, setting):
    """(n, name, measures) for every class the census holds in this setting."""
    slot = census["settings"].get(setting) or {}
    out = []
    for n, cls in sorted((slot.get("classes") or {}).items(), key=lambda kv: int(kv[0])):
        for c in cls:
            out.append((int(n), c["table"], c["m"]))
    return out


def blame(up):
    """Where the bound came from -- a chain says which link to doubt."""
    chain = up.get("chain") or []
    if len(chain) > 1:
        return "closure: " + " then ".join(
            f"{f['a']} <= {f['b']}^{f['exp']:g}" for f in chain)
    return up["origin"] + (" " + ",".join(up["refs"]) if up.get("refs") else "")


def check(ctx, z, setting, rows):
    """Every recorded bound in one setting, against every function in it."""
    ids = sorted(rows[0][2])
    ctx.say(f"  {setting}: {len(rows)} objects over n = "
            f"{', '.join(str(k) for k in sorted({r[0] for r in rows}))}"
            f", {len(ids)} measures each")

    bad = False
    for mid in ids:
        m = z.measure.get(mid)
        if not m:
            ctx.bad(f"census computes {mid}, which is not a measure in the zoo")
            bad = True
        elif (m["settings"].get(setting) or {}).get("defined") is False:
            ctx.bad(f"census computes {mid} for {setting}, where it is undefined")
            bad = True
    if bad:
        return 0, 0, 0, 1, []

    def val(m, mid):
        v = m.get(mid)
        return None if v is None else float(v)

    checked = hard_n = tight_n = viol = 0
    loose = []
    for a in ids:
        for b in ids:
            if a == b:
                continue
            slot = (z.best.get((a, b)) or {}).get(setting)
            up = slot.get("up") if slot else None
            # a log factor is vacuous down here (log of 0 or 1), and a
            # non-polynomial bound is not of the form being tested
            if not up or up["log"] or up["kind"] not in POLY:
                continue
            e = up["exp"]
            worst, wit = 0.0, None
            hard = up["kind"] == "exact"
            for n, name, m in rows:
                x, y = val(m, a), val(m, b)
                if x is None or y is None or x <= TOL:
                    continue
                bound = y ** e if y > 0 else 0.0
                need = x / bound if bound > 0 else float("inf")
                if need > worst:
                    worst, wit = need, (n, name, x, y)
            if wit is None:
                continue
            checked += 1
            hard_n += hard
            tight_n += hard and worst > 1 - TOL   # some function meets it exactly
            if hard and worst > 1 + TOL:
                viol += 1
                n, name, x, y = wit
                ctx.bad(f"[{setting}] {a} <= {b}^{e:g} is recorded exact "
                        f"({blame(up)}), but n={n} {name} has {a}={x:g}, {b}={y:g} "
                        f"(needs a factor {worst:.3f})")
            elif not hard and worst > LOOSE:
                loose.append((worst, setting, a, b, e, up["kind"], wit))

    # the identities the zoo states as exact equalities, tested pointwise
    ident = 0
    for mid, m in z.measure.items():
        if mid not in ids:
            continue
        for eq in (m.get("equivalent") or []):
            other, form = eq.get("measure"), eq.get("form") or {}
            if other not in ids or form.get("kind") != "exact" or form.get("exp", 1) != 1:
                continue
            ident += 1
            for n, name, mm in rows:
                x, y = val(mm, mid), val(mm, other)
                if x is None or y is None:
                    continue
                if abs(x - y) > TOL * max(1.0, abs(x)):
                    viol += 1
                    ctx.bad(f"[{setting}] {mid} = {other} is recorded as an exact "
                            f"identity, but n={n} {name} has {mid}={x:g}, "
                            f"{other}={y:g}")
                    break

    ctx.say(f"    {checked} ordered pairs with a testable upper bound, of which "
            f"{hard_n} are exact ({tight_n} met with equality by some object "
            f"down here, so the test has teeth on those); {ident} exact "
            f"identities; {viol} violation(s)")
    return checked, hard_n, ident, viol, loose


def run(ctx):
    if not oracle.CENSUS.exists():
        ctx.say("  no census yet; building it (a few minutes)")
    census = oracle.load()
    z = ctx.zoo
    viol, loose = 0, []
    for setting in ("total", "partial", "relation"):
        rows = rows_of(census, setting)
        if not rows:
            ctx.say(f"  {setting}: nothing in the census")
            continue
        _, _, _, v, lo = check(ctx, z, setting, rows)
        viol += v
        loose += lo
    if loose:
        loose.sort(reverse=True)
        ctx.say("  largest constants the census demands (these are allowed):")
        for worst, setting, a, b, e, kind, (n, name, x, y) in loose[:12]:
            ctx.say(f"    [{setting}] {a} <= {worst:5.2f} * {b}^{e:g}  [{kind}]  "
                    f"at n={n} {name}: {a}={x:g}, {b}={y:g}")
    return not viol
