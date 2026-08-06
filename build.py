#!/usr/bin/env python3
"""
Build the Query Complexity Zoo static site from the YAML data files.

    python3 build.py                 # build into ./site
    python3 build.py --strict        # fail on any unresolved reference
    python3 build.py --serve 8000    # build, then serve

Everything factual lives in data/*.yaml; this script only arranges it.
"""

from __future__ import annotations

import argparse
import html
import json
import os
import re
import shutil
import sys
from collections import Counter, defaultdict, OrderedDict
from pathlib import Path

import yaml

try:
    import mistune
except ImportError:  # pragma: no cover
    mistune = None

from jinja2 import Environment, FileSystemLoader, pass_context, select_autoescape

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
TEMPLATES = ROOT / "templates"
STATIC = ROOT / "static"

# The vocabulary of `form: {kind: ...}` on a relation bullet -- see the schema
# comment at the top of data/relations/01-classical-core.yaml.
#   exact/const/theta/tilde are polynomial relations M1 <= M2^exp (log^log M2),
#   differing only in how much slack the statement hides;
#   exp/log/none/unbounded are the non-polynomial verdicts, which the
#   transitive closure refuses to compose.
_POLY_KINDS = ("exact", "theta", "const", "tilde")
FORM_KINDS = set(_POLY_KINDS) | {"exp", "log", "none", "unbounded"}

# Settings, from most restricted class of problems to most general. A bound
# that holds for the general class holds for the restricted one; a separation
# for the restricted one is a separation for the general one.
SETTING_GENERALITY = ["total", "partial", "relation"]

# --------------------------------------------------------------------------
# loading
# --------------------------------------------------------------------------


def load_yaml(path: Path):
    with path.open() as fh:
        return yaml.safe_load(fh)


def load_collection(pattern: str, key: str):
    """Load and concatenate the `key` list from every file matching pattern."""
    out = []
    for path in sorted(DATA.glob(pattern)):
        doc = load_yaml(path)
        if not doc:
            continue
        items = doc.get(key)
        if items is None:
            raise SystemExit(f"{path}: expected top-level key '{key}'")
        for item in items:
            item["_source"] = str(path.relative_to(ROOT))
            out.append(item)
    return out


class Zoo:
    def __init__(self):
        self.site = load_yaml(DATA / "site.yaml")
        self.refs = load_yaml(DATA / "refs.yaml")
        self.measures = load_collection("measures/*.yaml", "measures")
        self.functions = load_collection("functions/*.yaml", "functions")
        self.relations = load_collection("relations/*.yaml", "relations")
        self.concepts = load_yaml(DATA / "concepts.yaml")["concepts"]
        self.open_problems = load_yaml(DATA / "open_problems.yaml")["open_problems"]
        self.tables = {}
        for path in sorted(DATA.glob("tables/*.yaml")):
            doc = load_yaml(path)
            self.tables[doc["id"]] = doc

        self.problems: list[str] = []

        # -------- indexes
        self.measure = OrderedDict()
        for m in self.measures:
            if m["id"] in self.measure:
                self.err(f"duplicate measure id {m['id']} ({m['_source']})")
            self.measure[m["id"]] = m
        self.function = OrderedDict()
        for f in self.functions:
            if f["id"] in self.function:
                self.err(f"duplicate function id {f['id']} ({f['_source']})")
            self.function[f["id"]] = f
        self.concept = OrderedDict((c["id"], c) for c in self.concepts)
        self.open_problem = OrderedDict((o["id"], o) for o in self.open_problems)

        # ref aliases
        self.ref_key = {}
        for key, entry in self.refs.items():
            self.ref_key[key] = key
            for alias in (entry.get("aliases") or []):
                self.ref_key.setdefault(alias, key)

        self.settings = [s["id"] for s in self.site["settings"]]
        self.setting_by_id = {s["id"]: s for s in self.site["settings"]}
        self.categories = self.site["categories"]
        self.category_by_id = {c["id"]: c for c in self.categories}

        self._normalise()
        self._build_pairs()
        self._attach()
        self._derive()

    # ---------------------------------------------------------------- utils
    def err(self, msg):
        self.problems.append(msg)

    def resolve(self, ident: str):
        """Return (kind, id) for any cross-reference id, or None."""
        if ident in self.measure:
            return ("measure", ident)
        if ident in self.function:
            return ("function", ident)
        if ident in self.concept:
            return ("concept", ident)
        if ident in self.open_problem:
            return ("open", ident)
        if ident in self.relation_by_id:
            return ("relation", ident)
        if ident in self.ref_key:
            return ("ref", self.ref_key[ident])
        return None

    # ------------------------------------------------------------ normalise
    def _normalise(self):
        # measures
        for m in self.measures:
            m.setdefault("category", "deterministic")
            m.setdefault("order", 999)
            m.setdefault("aliases", [])
            m.setdefault("facts", [])
            m.setdefault("params", [])
            m.setdefault("refs", [])
            m.setdefault("see_also", [])
            m.setdefault("confidence", "medium")
            st = m.get("settings") or {}
            norm = {}
            for s in self.settings:
                v = st.get(s)
                if v is None:
                    norm[s] = {"defined": "unknown", "note": None}
                elif isinstance(v, dict):
                    d = v.get("defined", "yes")
                    norm[s] = {"defined": _yn(d), "note": v.get("note")}
                else:
                    norm[s] = {"defined": _yn(v), "note": None}
            m["settings"] = norm
            if m["category"] not in self.category_by_id:
                self.err(f"measure {m['id']}: unknown category {m['category']}")
            for eq in (m.get("equivalent") or []):
                eq.setdefault("setting", "total")
                eq["form"] = self._form(eq.get("form"), {"id": f"{m['id']} equivalent"}, "upper")
            # normalise param dicts (some files use `name`, some `id`)
            for p in m["params"]:
                if "name" not in p and "id" in p:
                    p["name"] = p.pop("id")
                p.setdefault("symbol", p.get("name", ""))
                p.setdefault("default", "")

        # functions
        for f in self.functions:
            f.setdefault("kind", "total")
            f.setdefault("group", "other")
            f.setdefault("order", 999)
            f.setdefault("aliases", [])
            f.setdefault("values", [])
            f.setdefault("witnesses", [])
            f.setdefault("refs", [])
            f.setdefault("see_also", [])
            if f["kind"] not in ("total", "partial", "relation"):
                self.err(f"function {f['id']}: bad kind {f['kind']}")
            for v in f["values"]:
                v.setdefault("putative", False)
                v.setdefault("refs", [])
                if v.get("measure") and v["measure"] not in self.measure:
                    self.err(f"function {f['id']}: unknown measure {v['measure']}")
                # A value nobody has published needs its argument written down.
                if v["putative"] and not v.get("note"):
                    self.err(f"function {f['id']}: putative value for "
                             f"{v.get('measure')} has no `note` giving the argument")

        # relations
        self.relation_by_id = OrderedDict()
        for i, r in enumerate(self.relations):
            r.setdefault("setting", "total")
            r.setdefault("status", "gap")
            r.setdefault("upper", [])
            r.setdefault("lower", [])
            r.setdefault("see_also", [])
            r.setdefault("kind", "pair")
            if r["setting"] not in self.settings:
                self.err(f"relation {r.get('from')}->{r.get('to')}: bad setting {r['setting']}")
            if r["status"] not in self.site["statuses"]:
                self.err(f"relation {r.get('from')}->{r.get('to')}: bad status {r['status']}")
            for side in ("upper", "lower"):
                for b in r[side] or []:
                    b.setdefault("conf", "medium")
                    b.setdefault("refs", [])
                    b.setdefault("putative", False)
                    if b["putative"] and not b.get("note"):
                        self.err(f"relation {rid_hint(r)}: putative bullet has no "
                                 f"`note` giving the argument")
                    b["form"] = self._form(b.get("form"), r, side)
            for end in ("from", "to"):
                if r.get(end) not in self.measure:
                    self.err(f"relation in {r['_source']}: unknown measure '{r.get(end)}'")
            rid = r.get("id") or f"{r['from']}__{r['to']}__{r['setting']}"
            r["id"] = rid
            if rid in self.relation_by_id:
                self.err(f"duplicate relation id {rid}")
            self.relation_by_id[rid] = r

        # concepts / open problems
        for c in self.concepts:
            c.setdefault("order", 999)
            c.setdefault("refs", [])
            c.setdefault("see_also", [])
        for o in self.open_problems:
            o.setdefault("order", 999)
            o.setdefault("refs", [])
            o.setdefault("see_also", [])
            o.setdefault("best_known", [])
            o.setdefault("setting", "total")

    # ----------------------------------------------------------------- form
    def _form(self, fm, where, side):
        """Validate and fill in a `form:` block. Returns None if absent."""
        if fm is None:
            return None
        label = where.get("id") or f"{where.get('from')}->{where.get('to')}"
        if not isinstance(fm, dict):
            self.err(f"{label}: `form` must be a mapping")
            return None
        extra = set(fm) - {"exp", "log", "kind", "dir", "inherit"}
        if extra:
            self.err(f"{label}: unknown key(s) in `form`: {', '.join(sorted(extra))}")
        kind = fm.get("kind", "const")
        if kind not in FORM_KINDS:
            self.err(f"{label}: unknown form kind '{kind}'")
            kind = "const"
        if kind == "none" and side != "upper":
            self.err(f"{label}: form kind 'none' belongs on an `upper` bullet")
        if kind == "unbounded" and side != "lower":
            self.err(f"{label}: form kind 'unbounded' belongs on a `lower` bullet")
        try:
            exp = float(fm.get("exp", 1))
            log = float(fm.get("log", 0))
        except (TypeError, ValueError):
            self.err(f"{label}: `exp`/`log` in `form` must be numbers")
            return None
        if exp <= 0 and kind in _POLY_KINDS:
            self.err(f"{label}: `exp` must be positive")
        direction = fm.get("dir", "forward")
        if direction not in ("forward", "reverse"):
            self.err(f"{label}: form `dir` must be forward or reverse")
            direction = "forward"
        inherit = fm.get("inherit", True)
        if not isinstance(inherit, bool):
            self.err(f"{label}: form `inherit` must be true or false")
            inherit = True
        return {"exp": exp, "log": log, "kind": kind, "dir": direction,
                "inherit": inherit, "poly": kind in _POLY_KINDS}

    # ---------------------------------------------------------------- pairs
    def _build_pairs(self):
        self.pairs = OrderedDict()
        for r in self.relations:
            key = (r["from"], r["to"])
            p = self.pairs.setdefault(
                key,
                {
                    "a": r["from"],
                    "b": r["to"],
                    "slug": f"{r['from']}__{r['to']}",
                    "by_setting": {},
                    "relations": [],
                },
            )
            p["relations"].append(r)
            p["by_setting"].setdefault(r["setting"], []).append(r)

        # attach matrix cells
        table = self.tables.get("total-exponents")
        self.matrix = table
        if table:
            for row, cols in (table.get("cells") or {}).items():
                for col, cell in (cols or {}).items():
                    key = (row, col)
                    p = self.pairs.setdefault(
                        key,
                        {
                            "a": row,
                            "b": col,
                            "slug": f"{row}__{col}",
                            "by_setting": {},
                            "relations": [],
                        },
                    )
                    p["cell"] = cell
                    if row not in self.measure:
                        self.err(f"matrix row {row} is not a measure")
                    if col not in self.measure:
                        self.err(f"matrix column {col} is not a measure")

        for p in self.pairs.values():
            p.setdefault("cell", None)
            p["reverse"] = f"{p['b']}__{p['a']}" if (p["b"], p["a"]) in self.pairs else None

    # --------------------------------------------------------------- attach
    def _attach(self):
        for m in self.measures:
            m["out"] = []
            m["inn"] = []
            m["pairs_out"] = []
            m["pairs_in"] = []
            m["witness_of"] = []
        for f in self.functions:
            f["witness_for"] = []

        for r in self.relations:
            self.measure[r["from"]]["out"].append(r)
            self.measure[r["to"]]["inn"].append(r)
            for side in ("upper", "lower"):
                for b in r[side]:
                    w = b.get("witness")
                    if w:
                        if w not in self.function:
                            self.err(f"relation {r['id']}: unknown witness function '{w}'")
                        else:
                            self.function[w]["witness_for"].append((r, b, side))

        for (a, b), p in self.pairs.items():
            self.measure[a]["pairs_out"].append(p)
            self.measure[b]["pairs_in"].append(p)
            cell = p.get("cell")
            if cell and cell.get("w"):
                w = cell["w"]
                if w not in self.function:
                    self.err(f"matrix cell {a}/{b}: unknown witness '{w}'")

        # values recorded on function pages -> measure pages
        for f in self.functions:
            for v in f["values"]:
                mid = v.get("measure")
                if mid in self.measure:
                    self.measure[mid].setdefault("function_values", []).append((f, v))

        # open problems referenced from measures
        for o in self.open_problems:
            for sid in o["see_also"]:
                if sid in self.measure:
                    self.measure[sid].setdefault("open_problems", []).append(o)

    # ------------------------------------------------------------ derivation
    #
    # Three things are computed here and nowhere else. None of them is ever
    # written back to YAML; they are labelled "derived" wherever they surface.
    #
    #   1. setting inheritance -- an upper bound proved for the more general
    #      class holds for the less general one, and a separation exhibited in
    #      the less general one is a separation in the more general one;
    #   2. the transitive closure of the recorded upper bounds;
    #   3. separations pushed through those upper bounds:
    #      M1(f_n) >= M2(f_n)^p together with M3 = O(M2^r) gives
    #      M1(f_n) >= M3(f_n)^{p/r} on the same family.
    #
    def _derive(self):
        self.facts = []
        self.derivation_notes = []
        self._collect_facts()
        self._inherit_settings()
        self.closure = {s: self._close(s) for s in self.settings}
        self._push_separations()
        self._best_bounds()

    # -- 0. every machine-readable statement in the data, as a directed fact
    def _collect_facts(self):
        def fact(a, b, setting, side, form, src, **kw):
            f = {
                "a": a, "b": b, "setting": setting, "side": side,
                "exp": form["exp"], "log": form["log"], "kind": form["kind"],
                "poly": form["poly"], "origin": "recorded", "chain": [],
                "stmt": src.get("stmt") or src.get("statement"),
                "refs": src.get("refs") or [], "note": src.get("note"),
                "witness": src.get("witness"), "conf": src.get("conf", "medium"),
                "rel": None, "reverse": form["dir"] == "reverse",
                "inherit": form["inherit"],
            }
            f.update(kw)
            self.facts.append(f)
            return f

        for r in self.relations:
            for side in ("upper", "lower"):
                for b in r[side]:
                    if not b.get("form"):
                        continue
                    if r["kind"] != "pair":
                        self.err(f"relation {r['id']}: `form` only belongs on a pair "
                                 f"record (this one is a {r['kind']} record)")
                        continue
                    a, c = r["from"], r["to"]
                    if b["form"]["dir"] == "reverse":
                        a, c = c, a
                    f = fact(a, c, r["setting"], side, b["form"], b, rel=r, bullet=b)
                    # M1 = Theta(M2^e) is also a bound on M2 in terms of M1
                    if (side == "upper" and b["form"]["kind"] == "theta"
                            and not b["form"]["log"] and b["form"]["exp"] > 0
                            and a != c):
                        back = dict(b["form"], exp=1.0 / b["form"]["exp"])
                        g = fact(c, a, r["setting"], "upper", back, b, rel=r, bullet=b,
                                 flipped=True, chain=[f])
                        # ... and Theta is tight in the separation sense too:
                        # M1 >= const * M2^e holds for *every* f, so the best
                        # separation exponent is at least e, in both directions.
                        fact(a, c, r["setting"], "lower", b["form"], b, rel=r, bullet=b,
                             from_theta=True, chain=[f])
                        fact(c, a, r["setting"], "lower", back, b, rel=r, bullet=b,
                             from_theta=True, flipped=True, chain=[g])

        # `equivalent:` blocks on measure pages, where they carry a form.
        # kind: theta there means M1 = Theta(M2^e), i.e. an edge each way.
        for m in self.measures:
            for eq in (m.get("equivalent") or []):
                form, other = eq.get("form"), eq.get("measure")
                if not form or other not in self.measure:
                    continue
                s = eq["setting"]
                f = fact(m["id"], other, s, "upper", form, eq, equiv=True)
                if form["kind"] == "theta" and form["exp"] > 0:
                    back = dict(form, exp=1.0 / form["exp"])
                    g = fact(other, m["id"], s, "upper", back, eq, equiv=True,
                             note=(eq.get("note") or "") or None, flipped=True)
                    fact(m["id"], other, s, "lower", form, eq, equiv=True,
                         from_theta=True, chain=[f])
                    fact(other, m["id"], s, "lower", back, eq, equiv=True,
                         from_theta=True, flipped=True, chain=[g])

    # -- 1. total <-> partial <-> relation
    def _defined(self, mid, setting):
        m = self.measure.get(mid)
        return bool(m) and m["settings"].get(setting, {}).get("defined") == "yes"

    def _inherit_settings(self):
        order = [s for s in SETTING_GENERALITY if s in self.settings]
        for f in list(self.facts):
            if f["setting"] not in order or not f["inherit"]:
                continue
            i = order.index(f["setting"])
            # positive statement (a bound holds) -> restrict; negative
            # statement (a separation, or "no bound exists") -> generalise
            positive = f["side"] == "upper" and f["kind"] != "none"
            targets = order[:i] if positive else order[i + 1:]
            for t in targets:
                if not (self._defined(f["a"], t) and self._defined(f["b"], t)):
                    continue
                g = dict(f, setting=t, origin="setting", from_setting=f["setting"],
                         chain=[f])
                self.facts.append(g)

    # -- 2. transitive closure of the upper bounds, per setting
    @staticmethod
    def _rank_path(p):
        """Smaller is a stronger upper bound."""
        return (p["exp"], p["tilde"], p["log"], 0 if p["exact"] else 1, len(p["chain"]))

    @staticmethod
    def _compose(p, q):
        """p: a <= b^{pe} log^{pl} b,  q: b <= c^{qe} log^{ql} c."""
        return {
            "exp": p["exp"] * q["exp"],
            "log": q["log"] * p["exp"] + p["log"],
            "tilde": p["tilde"] or q["tilde"],
            "exact": p["exact"] and q["exact"],
            "theta": p["theta"] and q["theta"],
            "chain": p["chain"] + q["chain"],
        }

    def _close(self, setting, max_steps=4):
        dist = {}
        for f in self.facts:
            if f["setting"] != setting or f["side"] != "upper" or not f["poly"]:
                continue
            if f["a"] == f["b"]:
                continue
            p = {"exp": f["exp"], "log": f["log"], "tilde": f["kind"] == "tilde",
                 "exact": f["kind"] == "exact", "theta": f["kind"] == "theta",
                 "chain": [f]}
            cur = dist.setdefault(f["a"], {}).get(f["b"])
            if cur is None or self._rank_path(p) < self._rank_path(cur):
                dist[f["a"]][f["b"]] = p

        nodes = sorted(set(dist) | {b for row in dist.values() for b in row})
        for k in nodes:
            for i in nodes:
                pik = dist.get(i, {}).get(k)
                if pik is None or i == k:
                    continue
                for j, pkj in list(dist.get(k, {}).items()):
                    if j == i or j == k:
                        continue
                    cand = self._compose(pik, pkj)
                    if len(cand["chain"]) > max_steps:
                        continue
                    cur = dist.setdefault(i, {}).get(j)
                    if cur is None or self._rank_path(cand) < self._rank_path(cur):
                        dist[i][j] = cand

        # a cycle of exponent < 1 would say M = O(M^{<1}): a data error.
        for i in nodes:
            loop = dist.get(i, {}).get(i)
            if loop and loop["exp"] < 1 - 1e-9:
                self.err(f"inconsistent bounds ({setting}): {i} = O({i}^{loop['exp']:.3g}) "
                         f"via {' -> '.join([loop['chain'][0]['a']] + [s['b'] for s in loop['chain']])}")
            if i in dist:
                dist[i].pop(i, None)
        return dist

    # -- 3. separations pushed through upper bounds
    def _push_separations(self):
        for setting in self.settings:
            dist = self.closure[setting]
            seps = [f for f in self.facts
                    if f["setting"] == setting and f["side"] == "lower" and f["poly"]]
            for f in seps:
                b = f["b"]
                for c, row in dist.items():
                    p = row.get(b)
                    if c in (f["a"], b) or p is None or p["exp"] <= 0:
                        continue
                    if p["exp"] == 1 and len(p["chain"]) == 1 and p["chain"][0]["b"] == b \
                            and p["chain"][0]["a"] == c and p["exact"] and f["exp"] == 1:
                        pass  # still worth recording; no special case
                    self.facts.append({
                        **f,
                        "b": c,
                        "exp": f["exp"] / p["exp"],
                        "log": 0,
                        "kind": "tilde" if (p["tilde"] or f["kind"] == "tilde") else "const",
                        "origin": "closure",
                        "chain": [f] + p["chain"],
                        "via": p,
                        "stmt": None,
                    })

    # -- 4. the best fact of each kind, per (ordered pair, setting)
    def _best_bounds(self):
        origin_rank = {"recorded": 0, "setting": 1, "closure": 2}

        def up_key(f):
            # strongest first, but at equal strength prefer the statement
            # somebody actually wrote down (it carries refs and a proof note)
            return (f["exp"], f["kind"] == "tilde", f["log"],
                    origin_rank[f["origin"]],
                    0 if f["kind"] == "exact" else 1, len(f["chain"]))

        def lo_key(f):
            return (-f["exp"], f["kind"] == "tilde",
                    origin_rank[f["origin"]], len(f["chain"]))

        best = {}
        for f in self.facts:
            slot = best.setdefault((f["a"], f["b"]), {}).setdefault(f["setting"], {})
            if f["kind"] in ("none", "unbounded", "exp", "log"):
                slot.setdefault("verdicts", []).append(f)
            if not f["poly"]:
                continue
            side = "up" if f["side"] == "upper" else "lo"
            key = up_key if side == "up" else lo_key
            cur = slot.get(side)
            if cur is None or key(f) < key(cur):
                slot[side] = f

        # add the closure's upper bounds where they beat (or supply) a fact
        for setting, dist in self.closure.items():
            for a, row in dist.items():
                for b, p in row.items():
                    slot = best.setdefault((a, b), {}).setdefault(setting, {})
                    kind = ("tilde" if p["tilde"] else
                            "exact" if p["exact"] else
                            "theta" if p["theta"] else "const")
                    f = {"a": a, "b": b, "setting": setting, "side": "upper",
                         "exp": p["exp"], "log": p["log"], "kind": kind, "poly": True,
                         "origin": "recorded" if len(p["chain"]) == 1 else "closure",
                         "chain": p["chain"], "stmt": None, "refs": [], "note": None,
                         "witness": None, "conf": "high", "rel": None, "reverse": False}
                    if len(p["chain"]) == 1:
                        f = p["chain"][0]
                    cur = slot.get("up")
                    if cur is None or up_key(f) < up_key(cur):
                        slot["up"] = f

        for key, per_setting in best.items():
            for s, slot in per_setting.items():
                # "no bound exists" and an actual bound cannot both be true.
                # If the closure ever derives one against a recorded `none`,
                # one of the two is wrong and we want to hear about it.
                bad = [v for v in slot.get("verdicts", [])
                       if v["kind"] in ("none", "unbounded")]
                if bad and slot.get("up"):
                    self.err(f"{key[0]} vs {key[1]} ({s}): a bullet says no bound "
                             f"exists, but a bound of exponent "
                             f"{fmt_exp(slot['up']['exp'])} is on the table "
                             f"({slot['up']['origin']})")
                slot["verdict"] = self._verdict(slot)
                slot["derived"] = all(
                    x["origin"] != "recorded"
                    for x in (slot.get("up"), slot.get("lo")) if x
                ) and not any(v["origin"] == "recorded" for v in slot.get("verdicts", []))
        self.best = best

    @staticmethod
    def _verdict(slot):
        """How tight is what we know? Drives the matrix token."""
        up, lo = slot.get("up"), slot.get("lo")
        vs = slot.get("verdicts") or []
        if any(v["kind"] == "none" for v in vs):
            return "none"
        if any(v["kind"] == "unbounded" for v in vs) and not up:
            return "unbounded"
        if any(v["kind"] == "exp" for v in vs) and not up:
            return "exp"
        if any(v["kind"] == "log" for v in vs) and not up:
            return "log"
        if up and lo:
            if abs(up["exp"] - lo["exp"]) < 1e-9:
                return "settled"
            return "gap"
        if up:
            return "upper"
        if lo:
            return "lower"
        return "bare"

    # ------------------------------------------------------------ validation
    def validate(self):
        known_refs = set(self.ref_key)
        for path in sorted(DATA.rglob("*.yaml")):
            if path.name == "refs.yaml":
                continue
            doc = load_yaml(path)
            rel = str(path.relative_to(ROOT))
            for key, value in _walk(doc):
                if key == "refs" and isinstance(value, list):
                    for k in value:
                        if k not in known_refs:
                            self.err(f"{rel}: unknown citation key '{k}'")
                elif key == "superseded_by" and isinstance(value, str):
                    if value not in known_refs:
                        self.err(f"{rel}: unknown citation key '{value}'")
                elif key == "see_also" and isinstance(value, list):
                    for k in value:
                        if self.resolve(k) is None:
                            self.err(f"{rel}: unresolved see_also '{k}'")
                elif isinstance(value, str):
                    for wl in re.findall(r"\[\[([^\]|]+)(?:\|[^\]]*)?\]\]", value):
                        if self.resolve(wl.strip()) is None:
                            self.err(f"{rel}: unresolved [[{wl}]]")
        return self.problems


def rid_hint(r):
    """Best label for a relation in an error message, before ids are assigned."""
    return r.get("id") or f"{r.get('from')}->{r.get('to')} ({r.get('setting')})"


def _yn(v):
    if isinstance(v, bool):
        return "yes" if v else "no"
    return str(v)


def _walk(obj, key=None):
    if isinstance(obj, dict):
        for k, v in obj.items():
            yield from _walk(v, k)
        return
    if isinstance(obj, list):
        if key in ("refs", "see_also"):
            yield (key, obj)
        for v in obj:
            yield from _walk(v, key)
        return
    yield (key, obj)


# --------------------------------------------------------------------------
# rendering helpers
# --------------------------------------------------------------------------

TOKEN = "\x00Z%d\x00"
TOKEN_RE = re.compile(r"\x00Z(\d+)\x00")


class _Shelf:
    """Holds spans that must survive the markdown pass untouched.

    Two kinds:
      * math   -- restored HTML-escaped, because MathJax reads DOM *text*
                  and markdown would eat the backslashes;
      * html   -- restored verbatim (links we generated ourselves).
    """

    def __init__(self):
        self.spans = []

    def put(self, raw, kind):
        self.spans.append((kind, raw))
        return TOKEN % (len(self.spans) - 1)

    def protect_math(self, text):
        def grab(m):
            return self.put(m.group(0), "math")

        text = re.sub(r"\$\$.+?\$\$", grab, text, flags=re.S)
        text = re.sub(r"(?<!\\)\$(?:\\.|[^$\\])+?\$", grab, text, flags=re.S)
        return text

    def restore(self, text):
        def out(m):
            kind, raw = self.spans[int(m.group(1))]
            return html.escape(raw, quote=False) if kind == "math" else raw

        # Tokens can be nested inside restored html (a link label holds math),
        # so keep expanding until nothing is left.
        for _ in range(4):
            new = TOKEN_RE.sub(out, text)
            if new == text:
                break
            text = new
        return text


class Renderer:
    def __init__(self, zoo: Zoo):
        self.zoo = zoo
        if mistune is None:
            raise SystemExit("mistune is required: pip install mistune")
        self.md = mistune.create_markdown(
            plugins=["table", "strikethrough", "footnotes"],
            escape=False,
        )

    # ---- links
    def url(self, kind, ident, root=""):
        if kind == "measure":
            return f"{root}measures/{ident}.html"
        if kind == "function":
            return f"{root}functions/{ident}.html"
        if kind == "concept":
            return f"{root}concepts/{ident}.html"
        if kind == "open":
            return f"{root}open.html#{ident}"
        if kind == "ref":
            return f"{root}refs.html#{ident}"
        if kind == "relation":
            r = self.zoo.relation_by_id[ident]
            return pair_url(r["from"], r["to"], ident, root)
        if kind == "pair":
            a, _, b = ident.partition("__")
            return pair_url(a, b, None, root)
        raise ValueError(kind)

    def label(self, kind, ident):
        z = self.zoo
        if kind == "measure":
            return z.measure[ident].get("symbol") or ident
        if kind == "function":
            return z.function[ident].get("symbol") or z.function[ident].get("name") or ident
        if kind == "concept":
            return z.concept[ident]["title"]
        if kind == "open":
            return z.open_problem[ident]["title"]
        if kind == "ref":
            return ident
        if kind == "relation":
            r = z.relation_by_id[ident]
            return r.get("headline") or f"{r['from']} vs {r['to']}"
        return ident

    def link(self, ident, root="", text=None, cls=""):
        res = self.zoo.resolve(ident)
        if res is None:
            return f'<span class="broken">{html.escape(ident)}</span>'
        kind, rid = res
        href = self.url(kind, rid, root)
        if text is None:
            if kind == "measure":
                sym = html.escape(self.zoo.measure[rid]["symbol"], quote=False)
                text = f'<span class="tex">\\({sym}\\)</span>'
            elif kind == "function":
                fn = self.zoo.function[rid]
                sym = fn.get("symbol")
                text = (
                    f'<span class="tex">\\({html.escape(sym, quote=False)}\\)</span>'
                    if sym
                    else html.escape(fn.get("name", rid))
                )
            elif kind == "ref":
                text = f"[{html.escape(rid)}]"
            elif kind == "concept":
                text = html.escape(self.zoo.concept[rid]["title"])
            elif kind == "open":
                text = html.escape(re.sub(r"\$[^$]*\$", "…", self.zoo.open_problem[rid]["title"]))
            elif kind == "relation":
                text = html.escape(rid)
            else:
                text = html.escape(rid)
        else:
            text = html.escape(text)
        c = f' class="xref {kind} {cls}"'.replace("  ", " ")
        return f'<a href="{href}"{c}>{text}</a>'

    # ---- text passes
    def _wiki(self, text, root, shelf):
        def sub(m):
            body = m.group(1)
            if "|" in body:
                ident, label = body.split("|", 1)
            else:
                ident, label = body, None
            return shelf.put(
                self.link(ident.strip(), root, text=label.strip() if label else None), "html"
            )

        return re.sub(r"\[\[([^\]]+)\]\]", sub, text)

    def _cites(self, text, root, shelf):
        known = self.zoo.ref_key

        def sub(m):
            inner = m.group(1)
            parts = [p.strip() for p in inner.split(",")]
            if not parts or parts[0] not in known:
                return m.group(0)
            out = []
            for p in parts:
                out.append(self.link(p, root, text=p) if p in known else html.escape(p))
            return shelf.put("[" + ", ".join(out) + "]", "html")

        return re.sub(r"\[([^\[\]\n]+)\](?!\()", sub, text)

    def markdown(self, text, root=""):
        if not text:
            return ""
        shelf = _Shelf()
        text = shelf.protect_math(str(text))
        text = self._wiki(text, root, shelf)
        text = self._cites(text, root, shelf)
        return shelf.restore(self.md(text))

    def inline(self, text, root=""):
        """Markdown for a short snippet: no wrapping <p>."""
        out = self.markdown(text, root).strip()
        if out.startswith("<p>") and out.endswith("</p>") and out.count("<p>") == 1:
            out = out[3:-4]
        return out

    def tex(self, s):
        if s is None:
            return ""
        return f'<span class="tex">\\({html.escape(str(s), quote=False)}\\)</span>'

    def texd(self, s):
        if s is None:
            return ""
        return f'<div class="texd">\\[{html.escape(str(s), quote=False)}\\]</div>'

    def citelist(self, keys, root=""):
        if not keys:
            return ""
        return " ".join(self.link(k, root, text=k) for k in keys)


# --------------------------------------------------------------------------
# site generation
# --------------------------------------------------------------------------


_STATUS_RANK = {"settled": 0, "gap": 1, "open": 2, "fails": 3}


def _worst_status(rels):
    return max((r["status"] for r in rels), key=lambda s: _STATUS_RANK.get(s, 9))


def _pair_statuses(pair, settings):
    if not pair:
        return {}
    return {
        s: _worst_status(pair["by_setting"][s])
        for s in settings
        if pair["by_setting"].get(s)
    }


# Glyph shown in a matrix cell that has no published exponent: what kind of
# statement the zoo holds for that (pair, setting).
_GLYPH = {
    "fails": "⊘",   # no bound of this form can exist
    "upper": "≤",   # an upper bound is recorded
    "lower": "≫",   # only a separation is recorded
    "bare": "·",    # a record exists but carries neither
}


def _cell_summary(pair, settings):
    """Per-setting digest of a pair, for matrix cells and their tooltips."""
    out = {}
    if not pair:
        return out
    for s in settings:
        rs = pair["by_setting"].get(s) or []
        if not rs:
            continue
        status = _worst_status(rs)
        up = next((b for r in rs for b in (r.get("upper") or [])), None)
        lo = next((b for r in rs for b in (r.get("lower") or [])), None)
        if status == "fails":
            g = _GLYPH["fails"]
        elif up:
            g = _GLYPH["upper"]
        elif lo:
            g = _GLYPH["lower"]
        else:
            g = _GLYPH["bare"]
        out[s] = {"status": status, "glyph": g, "up": up, "lo": lo, "n": len(rs)}
    return out


# --------------------------------------------------------------------------
# Rendering the derived layer: exponents, tightness chips, derivations.
#
# The engine (Zoo._derive) knows, for every ordered pair and setting, the best
# upper bound and the best separation it can justify. What follows turns that
# into what a cell shows. Nothing here decides anything -- it only formats.
# --------------------------------------------------------------------------

# How tight is the upper bound, beyond its exponent? This is the distinction
# the matrix used to hide: `2` alone could mean any of these.
_CHIP = {
    "exact": "≤",   # M1 <= M2^b on the nose, no hidden constant
    "theta": "Θ",   # M1 = Theta(M2^b): tight in both directions
    "tilde": "Õ",   # up to polylog factors
    "const": "O",        # up to a constant factor
}
_CHIP_NAME = {
    "exact": "exact inequality, no hidden constant",
    "theta": "tight up to constants in both directions",
    "tilde": "tight up to polylogarithmic factors",
    "const": "up to a constant factor",
}
# The same question on the separation side: how tight is the witness family?
# `exact` here is the strong statement -- a family attaining M1 >= M2^a with no
# constant loss -- which, paired with an `exact` upper bound of the same
# exponent, settles a pair completely rather than up to constants.
_CHIP_LO = {
    "exact": "\u2265",  # a family with M1 >= M2^a on the nose
    "theta": "\u0398",  # M1 = Theta(M2^a) on the family
    "tilde": "\u03a9\u0303",
    "const": "\u03a9",
}
_CHIP_LO_NAME = {
    "exact": "a family attains M1 >= M2^a exactly, with no constant loss",
    "theta": "a family with M1 = Theta(M2^a)",
    "tilde": "a family with M1 = Omega-tilde(M2^a): tight up to logs",
    "const": "a family with M1 = Omega(M2^a)",
}
# What a cell shows in place of an exponent when the relationship is not
# polynomial. `unbounded`/`none` keep their glyph; `exp`/`log` name themselves,
# so a cell can read `exp, exp`: an exponential separation against an
# exponential upper bound is just as settled as `2, 2`.
_NONPOLY_LABEL = {"exp": "exp", "log": "log", "unbounded": "\u221e"}
VERDICT_WORD = {
    "settled": "settled",
    "gap": "gap",
    "upper": "upper bound only",
    "lower": "separation only",
    "none": "no bound exists",
    "unbounded": "unbounded",
    "exp": "exponential only",
    "log": "log-type only",
    "bare": "records, no exponent",
}
# Cells where no polynomial bound is on the table at all.
_VGLYPH = {
    "none": ("⊘", "no bound of this form exists"),
    "unbounded": ("∞", "unbounded: no bound at all"),
    "exp": ("2ⁿ", "only an exponential bound is known"),
    "log": ("log", "only a logarithmic-type bound is known"),
}


def fmt_exp(x):
    """1.0 -> '1', 0.5 -> '0.5', 1.6309... -> '1.6309'. Matches the table's style."""
    if x is None:
        return "?"
    s = f"{float(x):.4f}".rstrip("0").rstrip(".")
    return s or "0"


def _numeric(v):
    return float(v) if isinstance(v, (int, float)) and not isinstance(v, bool) else None


def _sym(z, mid):
    """A measure's symbol without its argument: '\\mathrm{D}(f)' -> '\\mathrm{D}'."""
    s = z.measure[mid]["symbol"]
    return re.sub(r"\((f|x)\)\s*$", "", s)


def _tex_bound(z, f):
    """LaTeX for a fact that carries no statement of its own (a derived one)."""
    sa = _sym(z, f["a"])
    sb = _sym(z, f["b"])
    pw = "" if abs(f["exp"] - 1) < 1e-9 else "^{%s}" % fmt_exp(f["exp"])
    lg = ""
    if f["log"]:
        lg = (r"\,\log %s(f)" % sb if abs(f["log"] - 1) < 1e-9
              else r"\,\log^{%s} %s(f)" % (fmt_exp(f["log"]), sb))
    if f["side"] == "lower":
        head = r"\widetilde\Omega" if f["kind"] == "tilde" else r"\Omega"
        return r"%s(f_n) = %s\big(%s(f_n)%s\big)" % (sa, head, sb, pw)
    if f["kind"] == "exact" and not lg:
        return r"%s(f) \le %s(f)%s" % (sa, sb, pw)
    head = {"theta": r"\Theta", "tilde": r"\widetilde O"}.get(f["kind"], "O")
    return r"%s(f) = %s\big(%s(f)%s%s\big)" % (sa, head, sb, pw, lg)


def _fact_tex(z, f):
    return f.get("stmt") or _tex_bound(z, f)


def _chain_ids(chain):
    ids = []
    for g in chain:
        if not ids or ids[-1] != g["a"]:
            ids.append(g["a"])
        ids.append(g["b"])
    return ids


def _derivation(z, f):
    """How a non-recorded fact was obtained, for the tooltip and pair page."""
    if f["origin"] == "recorded":
        return None
    steps = []
    for g in f.get("chain") or []:
        steps.append({
            "tex": _fact_tex(z, g), "refs": g.get("refs") or [],
            "setting": g["setting"], "a": g["a"], "b": g["b"],
            "side": g["side"], "witness": g.get("witness"),
        })
    d = {"how": f["origin"], "steps": steps, "path": [], "from_setting": f.get("from_setting")}
    if f["origin"] == "closure" and f["side"] == "upper":
        d["path"] = [_sym(z, i) for i in _chain_ids(f["chain"])]
    if f["origin"] == "closure" and f["side"] == "lower" and steps:
        d["how"] = "push"
    return d


def _side_view(z, f, src):
    """One side of a cell, ready for a template."""
    if f is None:
        return None
    lo = f["side"] == "lower"
    return {
        "exp": f["exp"], "e": fmt_exp(f["exp"]), "kind": f["kind"],
        "side": f["side"],
        "chip": (_CHIP_LO if lo else _CHIP).get(f["kind"], ""),
        "chip_name": (_CHIP_LO_NAME if lo else _CHIP_NAME).get(f["kind"], ""),
        "tex": _fact_tex(z, f), "refs": f.get("refs") or [],
        "witness": f.get("witness"), "note": f.get("note"),
        "origin": f["origin"], "src": src, "setting": f["setting"],
        "deriv": _derivation(z, f), "conf": f.get("conf"),
        "from_theta": bool(f.get("from_theta")),
    }


def _token(z, row, col, setting, cell):
    """The merged cell for (row, col) in one setting: published table + derived."""
    slot = (z.best.get((row, col)) or {}).get(setting) or {}
    up, lo = slot.get("up"), slot.get("lo")
    vs = slot.get("verdicts") or []
    pub = cell if (cell and setting == "total") else None
    pub_a = _numeric(pub.get("a")) if pub else None
    pub_b = _numeric(pub.get("b")) if pub else None

    a_exp, a_src = (lo["exp"] if lo else None), ("zoo" if lo else None)
    if pub_a is not None and (a_exp is None or pub_a > a_exp + 1e-9):
        a_exp, a_src, lo = pub_a, "table", None
    b_exp, b_src = (up["exp"] if up else None), ("zoo" if up else None)
    if pub_b is not None and (b_exp is None or pub_b < b_exp - 1e-9):
        b_exp, b_src, up = pub_b, "table", None

    # The published table rounds (1.63 for log 6 / log 3); where the zoo's own
    # exponent agrees to within that rounding, show the table's number so the
    # core grid still reads exactly like the source. The tooltip is exact.
    if pub_a is not None and a_exp is not None and abs(pub_a - a_exp) < 0.02:
        a_exp = pub_a
    if pub_b is not None and b_exp is not None and abs(pub_b - b_exp) < 0.02:
        b_exp = pub_b

    fails = next((v for v in vs if v["kind"] == "none"), None)
    # A non-polynomial statement is still a statement, and it has a side: an
    # exponential *upper bound* goes in the upper column, an exponential
    # *separation* in the separation column. Lumping them together was what
    # made a cell read "no bound" on one line and "bound" on the next.
    other_up = next((v for v in vs if v["side"] == "upper"
                     and v["kind"] in ("exp", "log")), None)
    other_lo = next((v for v in vs if v["side"] == "lower"
                     and v["kind"] in ("unbounded", "exp", "log")), None)
    unb = other_lo is not None and other_lo["kind"] == "unbounded"
    if fails is not None:
        verdict = "none"
    elif b_exp is None and unb:
        verdict = "unbounded"
    elif b_exp is None and (other_up is not None or other_lo is not None):
        verdict = (other_up or other_lo)["kind"]
    elif a_exp is not None and b_exp is not None:
        verdict = "settled" if abs(a_exp - b_exp) < 1e-9 else "gap"
    elif b_exp is not None:
        verdict = "upper"
    elif a_exp is not None:
        verdict = "lower"
    elif slot or pub:
        verdict = "bare"
    else:
        return None

    def written_down(f, src, pub_v, exp):
        """Is this side of the cell something a human put in the data?"""
        if src == "table" or (f is not None and f["origin"] == "recorded"):
            return True
        # the closure reproduced a value the published table already states
        return pub_v is not None and exp is not None and abs(pub_v - exp) < 1e-9

    if verdict == "none":
        drivers = [fails is not None and fails["origin"] == "recorded"]
    elif verdict in ("unbounded", "exp", "log"):
        drivers = [v["origin"] == "recorded"
                   for v in (other_up, other_lo) if v is not None]
    else:
        drivers = [written_down(f, src, pv, ex) for f, src, pv, ex in
                   ((up, b_src, pub_b, b_exp), (lo, a_src, pub_a, a_exp))
                   if ex is not None]
    # `none` and `unbounded` still get a glyph: there is nothing to put in the
    # two columns, and "no bound at all" deserves to be shouted. `exp`/`log`
    # do have something to say in each column, so they read like exponents.
    glyph, glyph_name = (_VGLYPH.get(verdict, ("", ""))
                         if verdict in ("none", "unbounded") else ("", ""))
    a_txt = fmt_exp(a_exp) if a_exp is not None else "?"
    b_txt = fmt_exp(b_exp) if b_exp is not None else "?"
    if verdict in ("exp", "log"):
        if other_lo is not None and a_exp is None:
            a_txt = _NONPOLY_LABEL[other_lo["kind"]]
        if other_up is not None and b_exp is None:
            b_txt = _NONPOLY_LABEL[other_up["kind"]]
    # The strongest thing a cell can say: the upper bound is an exact
    # inequality and a family meets it with no constant to spare.
    tight_exact = (verdict == "settled" and up is not None and lo is not None
                   and up["kind"] == "exact" and lo["kind"] == "exact"
                   and not up["log"] and not lo["log"])
    return {
        "verdict": verdict,
        "a": a_txt,
        "b": b_txt,
        "chip": _CHIP.get(up["kind"], "") if up else "",
        "chip_kind": up["kind"] if up else "",
        "chip_lo": _CHIP_LO.get(lo["kind"], "") if lo else "",
        "chip_lo_kind": lo["kind"] if lo else "",
        "tight_exact": tight_exact,
        "glyph": glyph, "glyph_name": glyph_name,
        "up": _side_view(z, up, b_src), "lo": _side_view(z, lo, a_src),
        "fails": _side_view(z, fails, "zoo"),
        "other_up": _side_view(z, other_up, "zoo") if b_exp is None else None,
        "other_lo": _side_view(z, other_lo, "zoo"),
        # "derived" = nothing a human wrote states this cell; the closure or
        # setting inheritance produced it. Flagged everywhere it is shown.
        "derived": bool(drivers) and not any(drivers),
        "from_table": "table" in (a_src, b_src),
    }


def _prune(obj):
    """Drop empty values from a payload. Halves the JSON; nothing reads them."""
    if isinstance(obj, dict):
        return {k: _prune(v) for k, v in obj.items()
                if v is not None and v is not False and v != "" and v != [] and v != {}}
    if isinstance(obj, list):
        return [_prune(v) for v in obj]
    return obj


def pair_url(a, b, anchor=None, root=""):
    """Every ordered pair is a view of one page, not a page of its own.

    There are 67*67 = 4489 of them and most are interesting only because the
    build can derive something about them; writing that many files to disk to
    say so would be silly. `pair.html` renders any of them from JSON.
    """
    return f"{root}pair.html?a={a}&b={b}" + (f"#{anchor}" if anchor else "")


def strip_tex(s: str) -> str:
    """Crude plain-text version of a LaTeX/markdown string, for search."""
    s = re.sub(r"\$\$?", " ", str(s))
    s = re.sub(r"\\[a-zA-Z]+", " ", s)
    s = re.sub(r"\[\[([^\]|]+)(\|[^\]]*)?\]\]", r"\1", s)
    s = re.sub(r"[{}\\^_~`*#|]", " ", s)
    return re.sub(r"\s+", " ", s).strip()


class Builder:
    def __init__(self, zoo: Zoo, out: Path):
        self.zoo = zoo
        self.out = out
        self.r = Renderer(zoo)
        self.env = Environment(
            loader=FileSystemLoader(str(TEMPLATES)),
            autoescape=select_autoescape(["html"]),
            trim_blocks=True,
            lstrip_blocks=True,
        )
        r = self.r
        env = self.env

        @pass_context
        def md(ctx, text):
            return _safe(r.markdown(text, ctx.get("root", "")))

        @pass_context
        def mdi(ctx, text):
            return _safe(r.inline(text, ctx.get("root", "")))

        @pass_context
        def xref(ctx, ident, text=None):
            return _safe(r.link(ident, ctx.get("root", ""), text=text))

        @pass_context
        def cites(ctx, keys):
            return _safe(r.citelist(keys, ctx.get("root", "")))

        @pass_context
        def link_to(ctx, kind, ident):
            return r.url(kind, ident, ctx.get("root", ""))

        env.filters["md"] = md
        env.filters["mdi"] = mdi
        env.filters["tex"] = lambda s: _safe(r.tex(s))
        env.filters["texd"] = lambda s: _safe(r.texd(s))
        env.filters["cites"] = cites
        env.globals["xref"] = xref
        env.globals["url"] = link_to
        env.globals["site"] = zoo.site
        env.globals["zoo"] = zoo
        env.globals["statuses"] = zoo.site["statuses"]
        env.globals["settings"] = zoo.site["settings"]
        env.globals["categories"] = zoo.categories
        env.globals["verdict_word"] = VERDICT_WORD
        env.globals["chip_name"] = _CHIP_NAME

        @pass_context
        def pu(ctx, a, b, anchor=None):
            return pair_url(a, b, anchor, ctx.get("root", ""))

        env.globals["pair_url"] = pu
        # one relation record, rendered exactly as the old pair pages did;
        # the pair app ships these as HTML rather than reimplementing them
        self._rel_tpl = env.from_string(
            '{% from "macros.html" import relation_block with context %}'
            '{{ relation_block(r) }}')

        self.search = []

    # ------------------------------------------------------------------ IO
    def write(self, relpath: str, template: str, **ctx):
        depth = relpath.count("/")
        ctx.setdefault("root", "../" * depth)
        ctx.setdefault("nav_active", relpath)
        ctx.setdefault("page_path", relpath)
        html_text = self.env.get_template(template).render(**ctx)
        target = self.out / relpath
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(html_text)

    def index_entry(self, url, kind, title, subtitle, text):
        self.search.append(
            {
                "u": url,
                "k": kind,
                "t": strip_tex(title),
                "s": strip_tex(subtitle or ""),
                "x": strip_tex(text or "")[:900],
            }
        )

    # --------------------------------------------------------------- build
    def build(self):
        if self.out.exists():
            shutil.rmtree(self.out)
        self.out.mkdir(parents=True)
        if STATIC.exists():
            shutil.copytree(STATIC, self.out / "static")

        self.page_index()
        self.page_matrix()
        self.page_measures()
        self.page_pairs()
        self.page_functions()
        self.page_concepts()
        self.page_open()
        self.page_refs()
        self.page_relations_index()
        self.page_editing()

        (self.out / "search-index.json").write_text(json.dumps(self.search, separators=(",", ":")))

    # ------------------------------------------------------------- pages
    def page_index(self):
        z = self.zoo
        by_cat = defaultdict(list)
        for m in z.measures:
            by_cat[m["category"]].append(m)
        for v in by_cat.values():
            v.sort(key=lambda m: (m["order"], m["id"]))
        stats = {
            "measures": len(z.measures),
            "functions": len(z.functions),
            "relations": len(z.relations),
            "pairs": len(z.pairs),
            "refs": len(z.refs),
            "concepts": len(z.concepts),
            "open": len(z.open_problems),
            "cells": sum(len(v) for v in (z.matrix or {}).get("cells", {}).values()),
        }
        self.write("index.html", "index.html", by_cat=by_cat, stats=stats)

    def page_matrix(self):
        z = self.zoo
        t = z.matrix
        if not t:
            return
        cells = t.get("cells") or {}

        # Measures that declare each other equivalent have no relation record
        # (there is nothing to bound), but the cell should not read as empty.
        equiv = {}
        for m in z.measures:
            for e in m.get("equivalent") or []:
                other = e.get("measure")
                if not other or other == m["id"] or other not in z.measure:
                    continue
                equiv.setdefault((m["id"], other), e)
                equiv.setdefault((other, m["id"]), e)

        def entry(row, col):
            pair = z.pairs.get((row, col))
            summ = _cell_summary(pair, z.settings)
            cell = (cells.get(row) or {}).get(col)
            tok = {} if row == col else {
                s: t for s in z.settings
                for t in [_token(z, row, col, s, cell)] if t
            }
            return {
                "col": col,
                "a": row,
                "b": col,
                "cell": cell,
                "tok": tok,
                "diag": row == col,
                "slug": f"{row}__{col}",
                "have_pair": pair is not None,
                "st": {s: v["status"] for s, v in summ.items()},
                "sum": summ,
                # A measure paired with itself: composition theorems and
                # parameter dependence. Marked on the diagonal.
                "rels": pair["relations"] if (pair and row == col) else [],
                "eq": equiv.get((row, col)) if not pair else None,
            }

        # -- the published table: its own row/column order, kept verbatim.
        grid = [
            {"row": row, "m": z.measure[row], "entries": [entry(row, c) for c in t["axis"]]}
            for row in t["rows"]
        ]
        cols = [z.measure[c] for c in t["axis"]]

        # -- the full grid: every measure, grouped by category.
        cat_order = {c["id"]: i for i, c in enumerate(z.categories)}
        allm = sorted(
            z.measures,
            key=lambda m: (cat_order.get(m["category"], 99), m["order"], m["id"]),
        )
        core = set(t["axis"]) | set(t["rows"])
        recorded = core | {r["from"] for r in z.relations} | {r["to"] for r in z.relations}
        scope_of = {
            m["id"]: ("core" if m["id"] in core else "recorded" if m["id"] in recorded else "all")
            for m in allm
        }
        big = [
            {"row": m["id"], "m": m, "entries": [entry(m["id"], c["id"]) for c in allm]}
            for m in allm
        ]
        meta = {
            "measures": [
                {"id": m["id"], "cat": m["category"], "scope": scope_of[m["id"]]} for m in allm
            ],
            "counts": {
                "core": len(core),
                "recorded": len(recorded),
                "all": len(allm),
            },
        }
        cat_counts = defaultdict(int)
        for m in allm:
            cat_counts[m["category"]] += 1

        self.write(
            "matrix.html",
            "matrix.html",
            t=t,
            grid=grid,
            cols=cols,
            big=big,
            allm=allm,
            meta=meta,
            meta_json=json.dumps(meta, separators=(",", ":")),
            cat_counts=cat_counts,
            glyphs=_GLYPH,
        )
        self.index_entry("matrix.html", "page", "Exponent matrix",
                         f"The {len(core)}x{len(core)} table of best-known exponents, "
                         f"expandable to all {len(allm)} measures",
                         t.get("convention", ""))

    def page_measures(self):
        z = self.zoo
        by_cat = defaultdict(list)
        for m in z.measures:
            by_cat[m["category"]].append(m)
        for v in by_cat.values():
            v.sort(key=lambda m: (m["order"], m["id"]))
        self.write("measures/index.html", "measures_index.html", by_cat=by_cat)

        cat_order = {c["id"]: i for i, c in enumerate(z.categories)}
        for m in z.measures:
            m["out"].sort(key=lambda r: (r["to"], r["setting"]))
            m["inn"].sort(key=lambda r: (r["from"], r["setting"]))
            nbrs = {}
            for p in m["pairs_out"]:
                nbrs.setdefault(p["b"], {})["out"] = p
            for p in m["pairs_in"]:
                nbrs.setdefault(p["a"], {})["in"] = p
            rows = []
            for oid, d in nbrs.items():
                o = z.measure[oid]
                rows.append(
                    {
                        "other": o,
                        "out": d.get("out"),
                        "in": d.get("in"),
                        "st_out": _pair_statuses(d.get("out"), z.settings),
                        "st_in": _pair_statuses(d.get("in"), z.settings),
                    }
                )
            rows.sort(key=lambda r: (cat_order.get(r["other"]["category"], 99),
                                     r["other"]["order"], r["other"]["id"]))
            m["nbrs"] = rows
            # parameter-dependence records that mention this measure
            prm = defaultdict(list)
            for r in m["out"] + m["inn"]:
                if r.get("param"):
                    if r not in prm[r["param"]]:
                        prm[r["param"]].append(r)
            m["param_rels"] = prm
            self.write(f"measures/{m['id']}.html", "measure.html", m=m)
            self.index_entry(
                f"measures/{m['id']}.html", "measure",
                f"{m['name']} ({m['id']})",
                m.get("short", ""),
                " ".join([m.get("definition") or ""] + [str(x) for x in m["facts"]] + m["aliases"]),
            )

    # ------------------------------------------------------------ the pairs
    #
    # One page, `pair.html`, renders any of the 67x67 ordered pairs from JSON
    # shards -- one shard per row measure, so browsing along a row costs one
    # fetch. The prose of a *recorded* relation is rendered here, by the same
    # Jinja macro the rest of the site uses, and shipped as HTML; only the
    # derived layer (exponents, chips, derivation chains) is assembled in the
    # browser, from the same structures the matrix cells use.
    #
    def page_pairs(self):
        z = self.zoo
        api = self.out / "api" / "pair"
        api.mkdir(parents=True, exist_ok=True)

        self.write("pair.html", "pair_app.html",
                   measures=sorted(z.measures, key=self._measure_sort),
                   nav_active="relations.html")

        (self.out / "api" / "meta.json").write_text(json.dumps({
            "measures": {
                m["id"]: {"sym": m["symbol"], "name": m["name"], "cat": m["category"],
                          "short": m.get("short", ""),
                          "def": {s: m["settings"][s]["defined"] for s in z.settings}}
                for m in z.measures
            },
            "functions": {f["id"]: {"sym": f.get("symbol") or f["name"], "name": f["name"]}
                          for f in z.functions},
            "settings": [{"id": s["id"], "name": s["name"], "short": s["short"],
                          "blurb": s.get("blurb", "")} for s in z.site["settings"]],
            "verdicts": VERDICT_WORD,
            "chips": _CHIP,
            "chip_names": _CHIP_NAME,
            "chips_lo": _CHIP_LO,
            "chip_lo_names": _CHIP_LO_NAME,
            "source": (z.matrix or {}).get("source"),
        }, separators=(",", ":")))

        for a in z.measure:
            cols = {}
            for b in z.measure:
                payload = self.pair_payload(a, b)
                if payload:
                    cols[b] = payload
            (api / f"{a}.json").write_text(
                json.dumps({"a": a, "cols": cols}, separators=(",", ":")))

        # the search index still lists the pairs somebody wrote about
        for (a, b), p in z.pairs.items():
            ma, mb = z.measure[a], z.measure[b]
            txt = []
            for r in p["relations"]:
                for side in ("upper", "lower"):
                    for x in r[side]:
                        txt.append(x.get("stmt", ""))
                        txt.append(x.get("note", "") or "")
            self.index_entry(
                pair_url(a, b), "pair",
                f"{ma['id']} vs {mb['id']}",
                f"{ma['name']} versus {mb['name']}",
                " ".join(txt),
            )

    def _measure_sort(self, m):
        cat_order = {c["id"]: i for i, c in enumerate(self.zoo.categories)}
        return (cat_order.get(m["category"], 99), m["order"], m["id"])

    def pair_payload(self, a, b):
        """Everything `pair.html` needs for one ordered pair, or None."""
        z = self.zoo
        p = z.pairs.get((a, b))
        cell = p.get("cell") if p else None
        tok = {} if a == b else {
            s: t for s in z.settings for t in [_token(z, a, b, s, cell)] if t
        }
        for t in tok.values():
            for k in ("up", "lo", "fails", "other"):
                v = t.get(k)
                if v and v.get("note"):
                    v["note"] = self.r.inline(v["note"], "")
        rels = {}
        for s in z.settings:
            html_blocks = [self.rel_html(r) for r in ((p or {}).get("by_setting") or {}).get(s, [])]
            if html_blocks:
                rels[s] = html_blocks
        out = {"tok": tok, "rels": rels}
        if cell:
            c = dict(cell)
            if c.get("note"):
                c["note"] = self.r.inline(c["note"], "")
            if c.get("update_note"):
                c["update_note"] = self.r.inline(c["update_note"], "")
            out["cell"] = c
        if a == b:
            out["self"] = self.diagonal_payload(a)
        if not (tok or rels or cell or out.get("self")):
            return None
        return _prune(out)

    def diagonal_payload(self, mid):
        """A measure against itself: parameters, amplification, composition."""
        z = self.zoo
        m = z.measure[mid]
        params = []
        for prm in m["params"]:
            params.append({
                "name": prm.get("name"), "symbol": prm.get("symbol"),
                "default": str(prm.get("default", "")), "range": str(prm.get("range", "")),
                "description": self.r.inline(prm.get("description") or "", ""),
                "dependence": self.r.markdown(prm.get("dependence") or "", ""),
            })
        comp = [self.rel_html(r) for r in z.relations
                if r["kind"] == "composition" and mid in (r["from"], r["to"])
                and not (r["from"] == r["to"] == mid)]
        facts = [self.r.inline(str(x), "") for x in m["facts"]]
        return {"params": params, "comp": comp, "facts": facts,
                "name": m["name"], "short": m.get("short", "")}

    def rel_html(self, r):
        return self._rel_tpl.render(r=r, root="")

    def page_functions(self):
        z = self.zoo
        by_kind = defaultdict(list)
        for f in z.functions:
            by_kind[f["kind"]].append(f)
        for v in by_kind.values():
            v.sort(key=lambda f: (f.get("group", ""), f["order"], f["id"]))
        self.write("functions/index.html", "functions_index.html", by_kind=by_kind)
        for f in z.functions:
            self.write(f"functions/{f['id']}.html", "function.html", f=f)
            self.index_entry(
                f"functions/{f['id']}.html", "function",
                f"{f['name']} ({f['id']})",
                f.get("short", ""),
                " ".join([f.get("definition") or "", f.get("formal") or ""] + f["aliases"]),
            )

    def page_concepts(self):
        z = self.zoo
        cs = sorted(z.concepts, key=lambda c: (c["order"], c["id"]))
        self.write("concepts/index.html", "concepts_index.html", cs=cs)
        for c in cs:
            self.write(f"concepts/{c['id']}.html", "concept.html", c=c)
            self.index_entry(f"concepts/{c['id']}.html", "concept",
                             c["title"], c.get("blurb", ""), c.get("body", ""))

    def page_open(self):
        ops = sorted(self.zoo.open_problems, key=lambda o: (o["order"], o["id"]))
        self.write("open.html", "open.html", ops=ops)
        for o in ops:
            self.index_entry(f"open.html#{o['id']}", "open",
                             o["title"], o.get("status", ""), o.get("statement", ""))

    def page_refs(self):
        z = self.zoo
        used = defaultdict(set)
        for path in sorted(DATA.rglob("*.yaml")):
            if path.name == "refs.yaml":
                continue
            for key, value in _walk(load_yaml(path)):
                if key == "refs" and isinstance(value, list):
                    for k in value:
                        if k in z.ref_key:
                            used[z.ref_key[k]].add(str(path.relative_to(ROOT)))
        items = sorted(
            z.refs.items(),
            key=lambda kv: (-(kv[1].get("year") or 0), kv[0].lower()),
        )
        self.write("refs.html", "refs.html", items=items, used=used)
        for key, e in items:
            self.index_entry(f"refs.html#{key}", "ref", f"[{key}] {e.get('title','')}",
                             e.get("venue", ""), e.get("note", ""))

    def page_relations_index(self):
        z = self.zoo
        cat_order = {c["id"]: i for i, c in enumerate(z.categories)}
        rows = []
        for (a, b), p in z.pairs.items():
            summary = {}
            for s in z.settings:
                rels = p["by_setting"].get(s) or []
                if not rels:
                    continue
                up = next((x for r in rels for x in r["upper"]), None)
                lo = next((x for r in rels for x in r["lower"]), None)
                summary[s] = {
                    "status": _worst_status(rels),
                    "upper": up,
                    "lower": lo,
                    "n": sum(len(r["upper"]) + len(r["lower"]) for r in rels),
                }
            p["summary"] = summary
            p["ma"] = z.measure[a]
            p["mb"] = z.measure[b]
            rows.append(p)
        rows.sort(
            key=lambda p: (
                cat_order.get(p["ma"]["category"], 99), p["ma"]["order"], p["ma"]["id"],
                cat_order.get(p["mb"]["category"], 99), p["mb"]["order"], p["mb"]["id"],
            )
        )
        named = [r for r in z.relations if not r["id"].endswith(("__total", "__partial", "__relation"))]
        named.sort(key=lambda r: r["id"])
        self.write("relations.html", "relations_index.html", rows=rows, named=named)

    def page_editing(self):
        self.write("editing.html", "editing.html")


class _safe(str):
    def __html__(self):
        return self


# --------------------------------------------------------------------------


def report_derived(zoo):
    """One honest paragraph about the derived layer, printed on every build."""
    origins = Counter(f["origin"] for f in zoo.facts)
    bullets = with_form = 0
    for r in zoo.relations:
        for side in ("upper", "lower"):
            for b in r[side]:
                bullets += 1
                with_form += bool(b.get("form"))
    slots = sum(len(v) for v in zoo.best.values())
    cov = {s: 0 for s in zoo.settings}
    for per in zoo.best.values():
        for s, slot in per.items():
            if slot.get("up") or slot.get("lo"):
                cov[s] += 1

    # every derived exponent, checked against the published table
    clash = 0
    for row, cols in ((zoo.matrix or {}).get("cells") or {}).items():
        for col, c in (cols or {}).items():
            slot = (zoo.best.get((row, col)) or {}).get("total") or {}
            up, lo = slot.get("up"), slot.get("lo")
            pa, pb = _numeric(c.get("a")), _numeric(c.get("b"))
            if up and pb is not None and up["exp"] < pb - 0.005:
                clash += 1
            if lo and pa is not None and lo["exp"] > pa + 0.005:
                clash += 1

    print(f"facts: {origins['recorded']} recorded, {origins['setting']} by setting "
          f"inheritance, {origins['closure']} by closure "
          f"({with_form}/{bullets} bullets carry a `form:`)")
    print("bounds: " + ", ".join(f"{cov[s]} {s}" for s in zoo.settings)
          + f" (pair, setting) slots of {slots}; "
          + f"{clash} conflict(s) with the published table")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true", help="fail on unresolved references")
    ap.add_argument("--out", default=None)
    ap.add_argument("--serve", type=int, default=None, metavar="PORT")
    args = ap.parse_args()

    zoo = Zoo()
    problems = zoo.validate()
    if problems:
        print(f"{len(problems)} validation problem(s):", file=sys.stderr)
        for p in problems[:200]:
            print("  -", p, file=sys.stderr)
        if args.strict:
            sys.exit(1)
    else:
        print("validation: clean")

    report_derived(zoo)

    out = Path(args.out) if args.out else ROOT / zoo.site.get("output_dir", "site")
    Builder(zoo, out).build()
    n = sum(1 for _ in out.rglob("*.html"))
    print(f"built {n} pages into {out}")

    if args.serve:
        import http.server
        import socketserver

        os.chdir(out)
        with socketserver.TCPServer(("", args.serve), http.server.SimpleHTTPRequestHandler) as httpd:
            print(f"serving http://localhost:{args.serve}/ (ctrl-c to stop)")
            httpd.serve_forever()


if __name__ == "__main__":
    main()
