"""Recorded function values against the zoo's own unit bounds.

For every function and every recorded pair of values (m1, m2) where the data
says m1 = O(m2) with exponent 1 and no log factor, evaluate both values
asymptotically with sympy.  If m1/m2 grows without bound then one of the three
facts -- the two values or the bound -- is wrong.  Only values that parse into
a closed form in one variable take part.
"""
import re

import sympy as sp

SUB = [
    (r"\\Theta\s*(?:\\!)?\s*\\big\((.*)\\big\)", r"(\1)"),
    (r"\\Theta\s*(?:\\!)?\s*\((.*)\)", r"(\1)"),
    (r"\\lceil|\\rceil|\\lfloor|\\rfloor|\\!|\\,|\\;|\\big|\\Big|\\left|\\right", ""),
    # 'N^{0.753\ldots}' -- truncating the exponent is harmless for a ratio test.
    (r"\\ldots|\\dots", ""),
    (r"\\sqrt\s*\{([^{}]*)\}", r"((\1)**0.5)"),
    (r"\\sqrt\s*(\w)", r"((\1)**0.5)"),
    (r"\\log_2|\\log|\\lg", "log"),
    (r"\\cdot", "*"),
    (r"\^\{([^{}]*)\}", r"**(\1)"),
    (r"\^(\w)", r"**\1"),
    (r"\\mathrm\{[^{}]*\}|\\tilde|\\widetilde|\\text\{[^{}]*\}", ""),
]


def parse(v, var):
    s = v.strip()
    for pat, rep in SUB:
        s = re.sub(pat, rep, s)
    s = s.replace("{", "(").replace("}", ")")
    if "\\" in s or not s:
        return None
    try:
        e = sp.sympify(s, locals={var.name: var, "log": sp.log})
    except Exception:
        return None
    if not isinstance(e, sp.Expr) or e.free_symbols != {var}:
        return None
    return e


def grows(a, b, var):
    try:
        return sp.limit(a / b, var, sp.oo) == sp.oo
    except Exception:
        return False


def run(ctx):
    z = ctx.zoo
    bad = checked = parsed = 0
    for f in z.functions:
        setting = f.get("kind", "total")
        if setting not in z.settings:
            continue
        raw = {v["measure"]: v["value"] for v in (f.get("values") or []) if v.get("value")}
        letters = {}
        for v in raw.values():
            for m in re.findall(r"(?<![\\a-zA-Z])([a-zA-Z])(?![a-zA-Z])", v):
                if m not in "eO":
                    letters[m] = letters.get(m, 0) + 1
        if not letters:
            continue
        var = sp.Symbol(max(letters, key=letters.get), positive=True)
        vals = {}
        for m, v in raw.items():
            e = parse(v, var)
            if e is not None:
                vals[m] = (e, v)
                parsed += 1
        for m1, (e1, v1) in vals.items():
            for m2, (e2, v2) in vals.items():
                if m1 == m2:
                    continue
                slot = z.best.get((m1, m2), {}).get(setting)
                up = slot.get("up") if slot else None
                if not up or abs(up["exp"] - 1) > 1e-9 or up["log"]:
                    continue
                if up["kind"] not in ("exact", "const", "theta"):
                    continue
                checked += 1
                if grows(e1, e2, var):
                    bad += 1
                    ctx.bad(f"{f['id']} [{setting}]: data says {m1} <= {m2} "
                            f"({up['kind']}, {up['origin']}), but {m1} = {v1} and "
                            f"{m2} = {v2}   [var {var}]")
    ctx.say(f"  {parsed} values parsed, {checked} (value, value, bound) triples "
            f"checked, {bad} suspicious")
    return not bad
