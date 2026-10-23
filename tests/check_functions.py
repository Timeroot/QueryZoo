"""Lint data/functions/*.yaml without building anything.

This one deliberately does not go through `build.Zoo`: the point is to catch
what the build silently swallows.  A repeated (function, measure) pair, for
instance, makes the build drop that measure rather than complain.

    python3 tests/check_functions.py [file ...]
"""
import glob
import sys

import yaml

import lib

sys.path.insert(0, str(lib.ROOT))
import growth  # noqa: E402


def load_measures():
    M = {}
    for p in glob.glob(str(lib.ROOT / "data/measures/*.yaml")):
        x = yaml.safe_load(open(p))
        for m in (x["measures"] if isinstance(x, dict) else x):
            M[m["id"]] = m
    return M


def load_refkeys():
    refs = yaml.safe_load(open(lib.ROOT / "data/refs.yaml"))
    keys = set(refs)
    for v in refs.values():
        if isinstance(v, dict):
            keys.update(v.get("aliases") or [])
    return keys


def family_env(f):
    """Mirror of build.Zoo._family_env."""
    sc = f.get("scale")
    if sc:
        env = {sc["var"]: growth.VAR}
        for name, expr in (sc.get("subs") or {}).items():
            env[name] = growth.parse_value(expr, {sc["var"]: growth.VAR}).lo
        return env, None
    names = set()
    for v in f.get("values", []):
        names |= growth.free_names(v.get("value") or "") or set()
    if len(names) == 1:
        return {names.pop(): growth.VAR}, None
    if not names:
        return None, "no value is a closed form"
    return None, "values use " + ", ".join(sorted(names)) + " -- needs `scale:`"


def lint(path, M, RK, ctx, detail=False):
    d = yaml.safe_load(open(path))
    fs = d["functions"] if isinstance(d, dict) else d
    bad, soft, total = 0, 0, 0
    for f in fs:
        kind = f.get("kind", "total")
        vals = f.get("values", [])
        total += len(vals)
        seen = [v["measure"] for v in vals]
        for m in sorted({m for m in seen if seen.count(m) > 1}):
            ctx.bad(f"DUPLICATE  {f['id']}.{m}  -- build will DROP this measure")
            bad += 1
        for m in sorted(set(seen)):
            if m not in M:
                ctx.bad(f"UNKNOWN MEASURE  {f['id']}.{m}")
                bad += 1
            elif ((M[m].get("settings") or {}).get(kind) or {}).get("defined") is False:
                ctx.bad(f"UNDEFINED HERE  {f['id']}.{m}  -- not defined for {kind}")
                bad += 1
        for v in vals:
            for r in v.get("refs") or []:
                if r not in RK:
                    ctx.bad(f"UNKNOWN REF  {f['id']}.{v['measure']}  [{r}]")
                    bad += 1
        env, why = family_env(f)
        if env is None:
            continue  # families with no single scale variable: nothing to parse against
        # An unparsed value is not an error -- a family with a second parameter
        # has values the growth grammar cannot hold -- so it is counted per
        # function and only itemised on request.
        stuck = []
        for v in vals:
            try:
                growth.parse_value(v["value"], env)
            except Exception as exc:
                stuck.append((v, exc))
                soft += 1
        if stuck and detail:
            for v, exc in stuck:
                ctx.say(f"    unparsed  {f['id']}.{v['measure']} = {v['value']!r}  ({exc})")
        elif stuck:
            why = sorted({str(exc) for _, exc in stuck})
            ctx.say(f"    unparsed  {f['id']}: {len(stuck)} of {len(vals)} values"
                    f"  ({'; '.join(why[:3])})")
    return len(fs), total, bad, soft


def run(ctx, paths=None):
    """With explicit paths -- one file being worked on -- itemise the unparsed."""
    M, RK = load_measures(), load_refkeys()
    detail = bool(paths)
    paths = paths or sorted(glob.glob(str(lib.ROOT / "data/functions/*.yaml")))
    nf = nv = bad = soft = 0
    for p in paths:
        a, b, c, d = lint(p, M, RK, ctx, detail)
        nf, nv, bad, soft = nf + a, nv + b, bad + c, soft + d
    ctx.say(f"  {len(paths)} files, {nf} functions, {nv} values, "
            f"{bad} hard problem(s), {soft} unparsed value(s)")
    return not bad


if __name__ == "__main__":
    sys.exit(0 if run(lib.Ctx(), sys.argv[1:] or None) else 1)
