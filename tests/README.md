# Checks

    python3 tests/run.py                  # everything quick (~3 minutes)
    python3 tests/run.py --list
    python3 tests/run.py --only links dom
    python3 tests/run.py --slow           # adds the small-n oracle

Most of these read `site/`, so build first: `python3 build.py`. Point them at a
build somewhere else with `ZOO_SITE=/path/to/site`.

Building `Zoo()` costs about ninety seconds and closing the relations another
twenty, so the runner constructs one and hands the same object to every check
that asks for it (`ctx.zoo`). The checks that only read `site/` are ordered
first, so a stale or missing build is reported before that time is spent.

| check | what it is for |
| --- | --- |
| `functions` | lints `data/functions/*.yaml` on their own: duplicate ids, values for measures that do not exist or are undefined in that setting, unparsable growth expressions, refs with no bibliography entry. Duplicates matter because the build silently keeps the last one. |
| `links` | every internal link and anchor in the built site, including the relation anchors that only exist at runtime inside `site/api/pair/*.json`, and the `pair.html?a=…` shards those pages fetch. |
| `dom` | loads the built pages in jsdom and drives them: the scope and view buttons, the ladder ordering and crosshair, the gap-report filters, six rendered pair pages, and the neighbour fold on a measure page (the hand-picked `related:` rows plus every other measure behind "Show all"). Skipped, not failed, when node or jsdom is missing. |
| `blanks` | a census of what the matrix cells actually hold, per setting, ratcheted. |
| `coverage` | ordered pairs with no separation of any kind, per setting, ratcheted. |
| `propagation` | exact equivalences work in both directions, and known total-function bounds propagate through sensitivity certification and minimum unambiguous certificates. |
| `values` | recorded function values against the zoo's own unit-exponent bounds -- a value that violates a bound the zoo asserts is either the value or the bound being wrong. |
| `smalln` | brute-forces every function on n <= 4 variables and tests the total-setting bounds against them. Slow, and only needed after a definition changes. |

## The ratchet

`blanks` and `coverage` have no natural pass condition: the zoo is allowed to
have holes. What it is not allowed to do is grow new ones. Each count is
compared against `tests/ratchet.json` and only an increase fails. When a count
improves, record it:

    ZOO_RATCHET=update python3 tests/run.py --only blanks coverage

## jsdom

`dom` needs node and jsdom. It looks in `$NODE_PATH`, then `node_modules/`,
then `/tmp/node_modules`. To install:

    npm install --prefix . jsdom

Each driver in `tests/dom/` is also runnable on its own, which is much faster
than the whole suite while working on one page:

    NODE_PATH=$(pwd)/node_modules ZOO_SITE=$(pwd)/site node tests/dom/ladder.js

Exit code 77 means the driver skipped itself (a page that does not exist in
this build).

## The small-n oracle

`tests/smalln/oracle.py` computes each measure from its definition, by brute
force, for every small object in each of the zoo's three settings -- one
representative per class under permuting and negating the *inputs* (the output
is deliberately not negated: a few measures are not symmetric under it, and a
relation's output symbols are not permuted either).

| setting | range | classes | measures |
| --- | --- | --- | --- |
| total | n <= 4 | 3, 6, 22, 402 | 38 |
| partial | n <= 3 | 6, 21, 267 | 28 (everything but the Fourier family and mod-2 degree) |
| relation | n = 1, 3 outputs | 28 | 7 (D, DTsize, rank, D-na, D-parity, C, C-min) |

The measures computed in a setting are exactly the ones the zoo declares
defined there. A relation is the general object -- each input carries a
non-empty set of acceptable outputs -- and a partial function is the case where
off-promise inputs accept everything, so the three share one implementation.

    python3 tests/smalln/oracle.py                    # build/refresh census.json
    python3 tests/smalln/oracle.py --show 3 0xE8      # every measure of MAJ3
    python3 tests/smalln/oracle.py --show 3 '011*1***'  # a partial function
    python3 tests/smalln/oracle.py --show 1 '0|12'    # a relation
    python3 tests/smalln/oracle.py --counts           # how many classes there are

Nothing in the oracle consults the zoo's recorded relations -- the point is to
have an independent witness -- so a measure defined in terms of another is
computed twice, separately, and the two are compared. The census is cached in
`census.json` and only rebuilt on demand; rebuild it after changing what a
measure means.

The promise conventions follow the measure pages: trees, certificates, blocks
and the exact degrees constrain Dom(f) alone, while `adeg` and `cjdeg` also
demand a bound of 1+eps on the whole cube. One thing the pages left open is
settled in the code and flagged there -- subcube partitions and unambiguous
covers partition Dom(f) rather than the cube.

The ranges are where the counts stop being free. A partial function on 4 bits
is 132102 classes, about a day; relations with 3 outputs are 406 at n = 2 and
135877 at n = 3, so n = 2 is a minute if it is ever wanted and n = 3 is not.
Widening a setting is one flag: `--partial-n 4`, `--relation-n 2`, `--outputs 4`.

`check_smalln.py` then tests the zoo against it, setting by setting. Only
bounds recorded as `exact` are hard-failed, since those are the ones asserted
to hold with no hidden constant; down here every measure lands between 0 and 4,
so a bound with a constant in it cannot be falsified. For those it reports the
largest constant the census demands, which is information rather than a
verdict.
