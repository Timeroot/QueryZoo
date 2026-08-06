# The Query Complexity Zoo

A browsable, editable catalogue of query-complexity measures and everything known about how
they relate — upper bounds with their log factors, matching separations with named witnesses,
and the total / partial / relational distinctions kept strictly apart.

All content is YAML under `data/`. `build.py` turns it into a static site.

```bash
python3 build.py --strict        # validate every cross-reference, then build into ./site
python3 build.py --serve 8000    # build and serve at http://localhost:8000/
python3 -m http.server -d site 8000
```

Requirements: Python 3.8+, `PyYAML`, `Jinja2`, `mistune`. MathJax is loaded from a CDN;
if you need the site fully offline, drop `tex-chtml.js` into `static/` and point
`templates/base.html` at it.

## What is in here

| | count |
|---|---|
| measures | 75 |
| ordered pairs with an entry | 225 |
| relation records (bounds and separations) | 141 |
| witness functions | 41 |
| concept pages | 11 |
| open problems | 14 |
| references | 139 |

The site generates one page per measure, function and concept, plus the exponent matrix, the
relations index, the open-problem list, the bibliography, and this guide's on-site twin
(`editing.html`).

**Pairs are not pages.** There are 75×75 = 5625 ordered pairs of measures and the build has
something to say about roughly a quarter of them, mostly by derivation. Writing that many files
would be silly, so `pair.html` renders any of them in the browser:

```
pair.html?a=D&b=R            D versus R
pair.html?a=D&b=R#D__R__total   ... scrolled to a particular record
pair.html?a=R&b=R            the diagonal: composition and parameter dependence
```

It reads `api/pair/<row>.json` — one shard per matrix row, so walking along a row costs one
fetch. Recorded relations travel as HTML rendered by the same Jinja macro the rest of the site
uses (no second renderer to keep in sync); the derived layer travels as data and is assembled
by `static/pair.js`.

## Layout

```
data/
  site.yaml                 title, nav, categories, the three settings, status vocabulary
  refs.yaml                 bibliography: a flat map from citation key to entry
  measures/*.yaml           one block per measure, under `measures:`
  functions/*.yaml          witness families, under `functions:`
  relations/*.yaml          the bounds, under `relations:`   <- the heart of the site
  tables/*.yaml             the published 13x13 exponent matrix (the matrix page
                            expands to all 75 measures using relation records)
  concepts.yaml             prose pages
  open_problems.yaml        open problems
build.py                    loader + validator + renderer
templates/*.html            Jinja2
static/style.css            styling
static/app.js               client-side search, matrix views, table filters
static/pair.js              the pair browser (pair.html)
```

Files within a directory are concatenated in filename order, so a new
`data/relations/08-whatever.yaml` needs no registration.

## The data model

Three layers, deliberately separate:

1. **The exponent matrix** (`data/tables/total-exponents.yaml`) is a faithful reproduction of
   Table 1 of [IJKKKSWW23], which itself updates [ABKRT21]. Cells record only exponents,
   `a, b`, meaning *some total `g` has `M1(g) ≥ M2(g)^{a−o(1)}`* and *every total `f` has
   `M1(f) ≤ M2(f)^{b+o(1)}`*. Deviations from the published table are marked
   `updated: true` with an `update_note` saying why. The matrix page shows this 13×13 table by
   default and can widen to *all* measures (`#recorded`, `#all` on the URL); outside the published
   axis the exponents shown are computed from layers 2 and 3, not read off the table.
2. **Relation records** (`data/relations/*.yaml`) carry the fine-grained statements — the
   actual `O(R² log R)` rather than the exponent `2` — one record per (from, to, setting).
   This is where log factors, ε-dependence, and the partial/relational story live. A bullet may
   carry a `form:` — the same statement in machine-readable form — which is what the build
   reasons with (see below).
3. **Measures, functions, concepts, open problems** are the nodes those records point at.

A relation is directional: `from` is the quantity being bounded, so an `upper` bullet on the
pair `(M1, M2)` is a statement `M1 = O(g(M2))` and a `lower` bullet is a separation
`M1 = Ω(g(M2))` on some family. The reverse direction lives in the reverse pair, and the two
pages link to each other.

## Adding a bound

```yaml
relations:
  - from: R              # LHS measure id (the matrix ROW)
    to: Q                # RHS measure id (the matrix COLUMN)
    setting: total       # total | partial | relation
    status: gap          # settled | gap | open | fails
    upper:
      - stmt: '\mathrm{R}(f) = O\big(\mathrm{Q}(f)^4\big)'
        form: {exp: 4, kind: const}    # machine-readable shadow of stmt
        refs: [BBCMdW01]
        note: 'Theorem 4. Via the polynomial method.'
        conf: high       # high | medium | low
        tight: 'up to the exponent'
    lower:
      - stmt: '\mathrm{R}(f_n) = \tilde\Omega\big(\mathrm{Q}(f_n)^3\big)'
        form: {exp: 3, kind: tilde}
        witness: kForrelation
        refs: [BansalSinha21, SSW21]
    notes: |
      Free markdown, $\LaTeX$, and [[wiki-links]] to any id.
    see_also: [D, adeg, composition]
```

Optional: `id` (gives the record a stable anchor and a row on the relations index),
`headline`, `kind: composition`, `param: eps`, `superseded_by: <refkey>`.

## `form:` and the derived layer

`stmt` is LaTeX for a human; `form` is the same statement for the build, and the only field the
engine reasons with. A bullet without one still renders — it just does not feed the matrix
cells, the tightness chips or the closure.

```yaml
form: {exp: 2, log: 1, kind: const}    # = O(M2^2 log M2)
```

| key | meaning |
| --- | --- |
| `exp` | the exponent (default `1`) |
| `log` | how many log factors (default `0`) |
| `kind` | `exact` (no hidden constant) · `const` (`O`) · `theta` (tight both ways) · `tilde` (up to polylogs) · `exp` · `log` · `none` (no such bound exists) · `unbounded` |
| `dir` | `reverse`: this bullet really bounds `to` in terms of `from`, so file the edge under the reverse pair |
| `inherit` | `false`: do **not** propagate to other settings — for bounds with side conditions |

`kind` is what the matrix chip shows: `≤` exact, `Θ` theta, `Õ` tilde, `O` constant, nothing when
only the exponent is on record. An exponent alone cannot tell you whether `1,1` means a one-line
inequality or a theorem with polylog slack; the chip can.

From these the build derives three things, all labelled as derived wherever they appear, all
losing to a recorded statement of the same strength, and none ever written back to the YAML:

- **transitive closure** — `M1 ≤ M2^p log^a M2` and `M2 ≤ M3^q log^b M3` give
  `M1 = O(M3^{pq} log^{bp+a} M3)`, up to four steps; `exact ∘ exact` stays exact, `tilde` is
  contagious, and a cycle of exponent `< 1` is reported as a data error;
- **separations pushed forward** — a family with `M1 ≥ M2^p`, plus a universal `M3 = O(M2^r)`,
  separates `M1` from `M3` at exponent `p/r` on that same family;
- **setting inheritance** — upper bounds travel relation → partial → total, separations and
  `none` verdicts travel total → partial → relation, both gated on the measure being defined in
  the target setting. This is why a bound with a side condition needs `inherit: false`: without
  it, "R₀ = O(R) for search problems with verifiable outputs" quietly becomes a false theorem
  about total functions.

Every build prints how much of this there is, and checks every derived total-function exponent
against the published table:

```
facts: 253 recorded, 148 by setting inheritance, 2549 by closure (174/239 bullets carry a `form:`)
bounds: 1001 total, 160 partial, 30 relation (pair, setting) slots of 1197; 0 conflict(s) with the published table
```

The ~65 bullets with no `form:` are chains, parameterised statements and prose that do not reduce
to a single exponent; adding one where it belongs is a good contribution.

## Conventions

- **Keep the logs.** The point of the fine-grained layer is that `O(R² log R)` and `Õ(R²)` are
  different statements. Write `Õ` only where the source does.
- **Say which setting.** A statement with no setting is a bug. If a bound is known only for
  total functions, that is a fact about the bound: record it under `total`, and add a `fails`
  record under `partial` if there is a counterexample.
- **Confidence is visible.** `conf: low` renders a `?` badge on the page. Use it instead of
  deleting something you are unsure of, and pair it with `todo:` saying what to check.
- **Witnesses are ids**, not prose. If the function is not catalogued yet, add a stub with
  `id/name/short/refs`; its page shows a "definition not yet transcribed" banner until someone
  fills in `formal:`.
- **`stmt:`, `headline:` and `value:` are bare LaTeX** (no `$`; the templates wrap them). Every other prose field is markdown, where you *do* need
  `$…$`. YAML eats backslashes in double-quoted scalars, so use single quotes or a `|` block.

## Cross-references

In any markdown field, `[[D]]`, `[[pointer]]`, `[[minimax]]`, `[[open-D-vs-bs]]` and
`[[Nisan91]]` all resolve to links with sensible labels; `[[D|the deterministic measure]]`
overrides the label. A bare `[Nisan91]` or `[BdW02, Cor. 1]` in prose is auto-linked when the
first token is a known citation key. Ids are global and must be unique across measures,
functions, concepts, open problems, and named relations.

`python3 build.py --strict` resolves every citation key, `see_also`, `witness` and
`[[wiki-link]]` and exits non-zero on the first unresolved one. Run it before committing.

## Health warning

This is a secondary source assembled quickly. Entries carry confidence markers, but even the
unmarked ones are transcriptions. Check the cited paper before you rely on anything here, and
please fix the YAML when you find an error.
