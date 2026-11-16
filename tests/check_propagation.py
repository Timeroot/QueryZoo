"""Known upper bounds must survive exact equivalences and downstream chains."""


def run(ctx):
    z = ctx.zoo
    ok = True

    def upper(a, b, setting):
        return (z.best.get((a, b), {}).get(setting) or {}).get("up")

    def require(a, b, setting, exp):
        nonlocal ok
        fact = upper(a, b, setting)
        if not fact or fact["exp"] > exp + 1e-8:
            ctx.bad(f"{a} vs {b} ({setting}): expected an upper exponent at most {exp}")
            ok = False

    # Exact equality is reversible, including its non-unit exponent.
    for setting in ("total", "partial"):
        require("s", "lambdacert", setting, 2)
        require("lambdacert", "s", setting, 0.5)
    for a, b, setting in (("FC", "fbs", "total"), ("cbs", "bs", "partial"),
                          ("bdeg", "deg", "total")):
        require(a, b, setting, 1)
        require(b, a, setting, 1)

    require("D", "UCmin", "total", 2)
    checked = 0
    for mid in z.measure:
        # Every bounded total sensitivity cell has a corresponding bounded
        # certification cell. Check the whole column, including R and Q.
        sensitivity = upper(mid, "s", "total")
        if sensitivity and mid != "lambdacert" and z._defined(mid, "total"):
            require(mid, "lambdacert", "total", 2 * sensitivity["exp"])
            checked += 1
        deterministic = upper(mid, "D", "total")
        if deterministic and mid != "UCmin" and z._defined(mid, "total"):
            require(mid, "UCmin", "total", 2 * deterministic["exp"])
            checked += 1
    ctx.say(f"  checked exact equivalences and {checked} propagated upper bounds")
    return ok
