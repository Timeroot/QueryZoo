#!/usr/bin/env python3
"""Small functions, partial functions and relations, with their measures computed exactly.

Three censuses, one per setting the zoo distinguishes:

    total     every f : {0,1}^n -> {0,1},      n <= 4     (3, 6, 22, 402 classes)
    partial   every f : {0,1}^n -> {0,1,*},    n <= 3     (6, 21, 267)
    relation  every R with 3 possible outputs, n = 1      (28)

Everything is enumerated up to permuting and negating **input** coordinates --
the group of order n!*2^n that every measure here is invariant under.  The
output is deliberately *not* negated: several measures in the zoo are one-sided
(C^1, s^1, bs^1, UC_min, one-sided approximate degree, nondeterministic degree)
and would be scrambled by it.  Output *symbols* of a relation are not permuted
either, so the relation classes are a little finer than they need to be.

Everything below is computed from the definitions on the measure pages, by
brute force or by a small LP -- nothing is read off a relation the zoo claims,
because the point of the census is to test those relations.  The one exception
is rational degree, which is computed through the characterisation
rdeg = max(ndeg(f), ndeg(not f)) recorded on its page; there is no direct
search for a rational representation here.

Only measures the zoo declares defined in a setting are computed there: 38 for
total functions, the 28 non-Fourier ones for partial, and the seven that survive
having no Boolean output for relations (D, DTsize, rank, D^na, D^parity, C,
C_min).  The promise conventions follow the measure pages: the tree, the
certificate, the blocks, and every degree except the approximate one constrain
Dom(f) alone, while adeg additionally demands |p| <= 1+eps on the whole cube.
One reading the pages left open is settled here and documented on the relevant
method: subcube partitions and unambiguous covers have to partition Dom(f),
not the cube.

    python3 tests/smalln/oracle.py               # build/refresh census.json
    python3 tests/smalln/oracle.py --n 3         # smaller, for a quick look
    python3 tests/smalln/oracle.py --show 4 0x6996
    python3 tests/smalln/oracle.py --show 3 '01**0*11'      # a partial function
    python3 tests/smalln/oracle.py --show 1 '0|12'          # a relation

Cost: about four minutes for the lot, so the result is cached in census.json
next to this file and only rebuilt on demand.
"""
import argparse
import itertools
import json
import sys
import time
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

HERE = Path(__file__).resolve().parent
CENSUS = HERE / "census.json"

EPS = 1e-9          # LP slack: values are small rationals, so this is generous
ADEG_EPS = 1.0 / 3  # the zoo's default epsilon for adeg / odeg / cjdeg

TOTAL_NS = (1, 2, 3, 4)
PARTIAL_NS = (1, 2, 3)
RELATION_NS = (1,)
RELATION_K = 3      # output symbols; with two, a relation is a partial function


# ----------------------------------------------------------------- enumeration

def orbit_reps(n):
    """Truth tables, one per class under permuting and negating the inputs.

    A function is a 2^n-bit integer: bit x is f(x).  A group element sends the
    point x to y, so it sends bit x to bit y; the class representative is the
    smallest integer in the orbit.  Done with numpy because n = 4 means 65536
    tables times 384 group elements.
    """
    N = 1 << n
    tables = np.arange(1 << N, dtype=np.int64)
    bits = ((tables[:, None] >> np.arange(N)) & 1).astype(np.int64)
    best = tables.copy()
    for tgt in group_maps(n):
        np.minimum(best, bits.dot((np.int64(1) << np.array(tgt))), out=best)
    return [int(t) for t in tables[best == tables]]


def group_maps(n):
    """The group, as permutations of the 2^n points: tgt[x] is where x goes."""
    N = 1 << n
    out = []
    for perm in itertools.permutations(range(n)):
        for neg in range(1 << n):
            tgt = []
            for x in range(N):
                y = 0
                for i in range(n):
                    if (x >> i) & 1:
                        y |= 1 << perm[i]
                tgt.append(y ^ neg)
            out.append(tgt)
    return out


def label_reps(n, symbols):
    """One representative per class of labellings of the cube by `symbols`.

    Used for the settings whose objects are not single integers: a partial
    function labels each point 0, 1 or * and a relation labels it with a
    non-empty set of outputs.
    """
    N = 1 << n
    maps = group_maps(n)
    seen, reps = set(), []
    for lab in itertools.product(symbols, repeat=N):
        if lab in seen:
            continue
        orbit = set()
        for tgt in maps:
            l2 = [None] * N
            for x in range(N):
                l2[tgt[x]] = lab[x]
            orbit.add(tuple(l2))
        seen |= orbit
        reps.append(min(orbit))
    return reps


def partial_reps(n):
    """Partial functions as tuples over {0, 1, 2}, 2 meaning off the promise."""
    return label_reps(n, (0, 1, 2))


def relation_reps(n, k=RELATION_K):
    """Relations as tuples of non-empty output sets, each a bitmask over [k]."""
    return label_reps(n, tuple(range(1, 1 << k)))


def burnside(n, alphabet):
    """Class count without enumerating: (1/|G|) sum_g alphabet^{cycles(g)}.

    With alphabet = 2 this counts total functions, 3 counts partial ones (the
    third symbol being "off the promise"), and 2^k - 1 counts relations with k
    output symbols (every input needs at least one valid answer).
    """
    N = 1 << n
    total = 0
    for tgt in group_maps(n):
        seen, cycles = [False] * N, 0
        for x in range(N):
            if seen[x]:
                continue
            cycles += 1
            y = x
            while not seen[y]:
                seen[y] = True
                y = tgt[y]
        total += alphabet ** cycles
    g = 1
    for k in range(1, n + 1):
        g *= k
    return total // (g * (1 << n))


# ------------------------------------------------------------------- utilities

def popcount(x):
    return bin(x).count("1")


def submasks(m):
    """Every subset of the bitmask m, including 0 and m itself."""
    s = m
    while True:
        yield s
        if s == 0:
            return
        s = (s - 1) & m


def exact_rank(rows):
    """Rank over the rationals of a list of integer rows."""
    rows = [[Fraction(v) for v in r] for r in rows]
    if not rows:
        return 0
    ncols, piv = len(rows[0]), 0
    for c in range(ncols):
        p = next((r for r in range(piv, len(rows)) if rows[r][c] != 0), None)
        if p is None:
            continue
        rows[piv], rows[p] = rows[p], rows[piv]
        pr = rows[piv]
        for r in range(piv + 1, len(rows)):
            if rows[r][c]:
                k = rows[r][c] / pr[c]
                rows[r] = [a - k * b for a, b in zip(rows[r], pr)]
        piv += 1
    return piv


def wht(a):
    """Walsh-Hadamard transform: out[S] = sum_x a[x] (-1)^{|S and x|}."""
    a = list(a)
    h = 1
    while h < len(a):
        for i in range(0, len(a), h * 2):
            for j in range(i, i + h):
                u, v = a[j], a[j + h]
                a[j], a[j + h] = u + v, u - v
        h *= 2
    return a


def lp_feasible(A_ub, b_ub, nvars, bounds=(None, None), A_eq=None, b_eq=None):
    r = linprog([0.0] * nvars, A_ub=A_ub or None, b_ub=b_ub or None,
                A_eq=A_eq, b_eq=b_eq, bounds=[bounds] * nvars, method="highs")
    return r.status == 0


# --------------------------------------------------------------- the relation

class Rel:
    """A relation: every input carries a non-empty set of acceptable outputs.

    This is the weakest structure any of these measures needs, so the partial
    and total settings are special cases of it -- a partial function is the
    relation whose off-promise inputs accept everything.  Only the measures
    that survive not having a Boolean output live here; the rest are in Part.
    """

    ids = ("D", "D_size", "rank", "Dna", "PDT", "C", "Cmin")

    def __init__(self, n, sets, k):
        self.n = n
        self.k = k
        self.N = 1 << n
        self.S = list(sets)             # bitmask of good outputs, per input
        self.ALL = (1 << k) - 1

    def _agree(self, pts):
        """Is there one output that is acceptable for every point in pts?"""
        m = self.ALL
        for x in pts:
            m &= self.S[x]
            if not m:
                return False
        return True

    # -- decision trees -----------------------------------------------------

    @lru_cache(maxsize=None)
    def _tree(self, fix, val):
        """(depth, leaves, rank) of the best tree for the subcube, each optimal."""
        pts = [x for x in range(self.N) if x & fix == val]
        if self._agree(pts):
            return (0, 1, 0)
        d = s = r = None
        for i in range(self.n):
            b = 1 << i
            if fix & b:
                continue
            d0, s0, r0 = self._tree(fix | b, val)
            d1, s1, r1 = self._tree(fix | b, val | b)
            cd = 1 + max(d0, d1)
            cs = s0 + s1
            cr = max(r0, r1) + (1 if r0 == r1 else 0)
            d = cd if d is None else min(d, cd)
            s = cs if s is None else min(s, cs)
            r = cr if r is None else min(r, cr)
        return (d, s, r)

    def D(self):
        return self._tree(0, 0)[0]

    def D_size(self):
        return self._tree(0, 0)[1]

    def rank(self):
        return self._tree(0, 0)[2]

    def Dna(self):
        """Fewest coordinates that, read in advance, always determine an answer."""
        for k in range(self.n + 1):
            for S in itertools.combinations(range(self.n), k):
                m = 0
                for i in S:
                    m |= 1 << i
                if all(self._agree([x for x in range(self.N) if x & m == val])
                       for val in submasks(m)):
                    return k
        return self.n

    def PDT(self):
        """Parity decision tree depth: each query is the parity of a subset."""
        memo = {}

        def go(pts):
            if self._agree(pts):
                return 0
            key = pts
            if key in memo:
                return memo[key]
            best = None
            for a in range(1, self.N):
                p0 = tuple(x for x in pts if popcount(x & a) % 2 == 0)
                p1 = tuple(x for x in pts if popcount(x & a) % 2 == 1)
                if not p0 or not p1:
                    continue
                c = 1 + max(go(p0), go(p1))
                best = c if best is None else min(best, c)
            memo[key] = best
            return best

        return go(tuple(range(self.N)))

    # -- certificates --------------------------------------------------------

    def C_x(self, x):
        """Fewest coordinates of x whose values already fix an acceptable output."""
        for k in range(self.n + 1):
            for S in itertools.combinations(range(self.n), k):
                m = 0
                for i in S:
                    m |= 1 << i
                if self._agree([y for y in range(self.N) if y & m == x & m]):
                    return k
        return self.n

    def _cert_points(self):
        """Which inputs C and C_min range over -- everything, for a relation."""
        return list(range(self.N))

    def all_measures(self):
        cx = [self.C_x(x) for x in self._cert_points()]
        return {"D": self.D(), "D_size": self.D_size(), "rank": self.rank(),
                "Dna": self.Dna(), "PDT": self.PDT(),
                "C": max(cx, default=0), "Cmin": min(cx, default=0)}


# ------------------------------------------- the partial (and total) function

class Part(Rel):
    """A Boolean function, possibly with a promise: f[x] is 0, 1 or None."""

    ids = ("D", "D_size", "rank", "Dna", "PDT", "s0", "s1", "s",
           "bs0", "bs1", "bs", "fbs", "FC", "C0", "C1", "C", "Cmin",
           "UC", "UCmin", "SP", "lambda", "deg", "adeg", "odeg", "sdeg",
           "cjdeg", "ndeg", "rdeg")

    def __init__(self, n, vals):
        super().__init__(n, [3 if v is None else 1 << v for v in vals], 2)
        self.f = list(vals)
        self.dom = [x for x in range(self.N) if self.f[x] is not None]
        self.ones = [x for x in self.dom if self.f[x]]
        self.zeros = [x for x in self.dom if not self.f[x]]

    def _cert_points(self):
        """C is a worst case over the promise, so off-promise inputs sit out."""
        return self.dom

    # -- sensitivity and blocks ---------------------------------------------

    def _flip(self, x, B):
        """Does flipping the block B at x land in the domain and change f?"""
        y = x ^ B
        return self.f[y] is not None and self.f[y] != self.f[x]

    def sens(self, x):
        return sum(1 for i in range(self.n) if self._flip(x, 1 << i))

    def blocks(self, x):
        """Minimal sensitive blocks at x, as coordinate bitmasks."""
        sens = [B for B in range(1, self.N) if self._flip(x, B)]
        out = []
        for B in sens:
            if not any(C != B and C & B == C and self._flip(x, C)
                       for C in submasks(B)):
                out.append(B)
        return out

    def bs_x(self, x):
        """Largest family of pairwise disjoint sensitive blocks at x."""
        bl = self.blocks(x)

        @lru_cache(maxsize=None)
        def pack(avail):
            best = 0
            for B in bl:
                if B & avail == B:
                    best = max(best, 1 + pack(avail & ~B))
            return best

        return pack(self.N - 1)

    def fbs_x(self, x):
        """LP relaxation of bs_x: max sum of block weights, each coordinate <= 1."""
        bl = self.blocks(x)
        if not bl:
            return 0.0
        A = [[1.0 if B & (1 << i) else 0.0 for B in bl] for i in range(self.n)]
        r = linprog([-1.0] * len(bl), A_ub=A, b_ub=[1.0] * self.n,
                    bounds=[(0, None)] * len(bl), method="highs")
        return -r.fun

    def FC_x(self, x):
        """The dual LP: fractional certificate weights covering every disagreement."""
        cons = []
        for y in self.dom:
            if self.f[y] != self.f[x]:
                d = x ^ y
                cons.append([-1.0 if d & (1 << i) else 0.0 for i in range(self.n)])
        if not cons:
            return 0.0
        r = linprog([1.0] * self.n, A_ub=cons, b_ub=[-1.0] * len(cons),
                    bounds=[(0, 1)] * self.n, method="highs")
        return r.fun

    # -- unambiguous covers --------------------------------------------------

    def _cubes(self, codim, colour=None):
        """Monochromatic subcubes of codimension <= codim, as domain-point masks.

        A subcube counts as monochromatic when the domain points inside it
        agree; a cube is represented by the domain points it holds, so two
        cubes differing only off the promise are the same object here.  That
        is the reading of SP and UC taken for partial functions: what has to
        be partitioned is Dom(f), and cubes may overlap off it.
        """
        out = set()
        for fix in range(self.N):
            if popcount(fix) > codim:
                continue
            for val in submasks(fix):
                pts = [x for x in self.dom if x & fix == val]
                vs = {self.f[x] for x in pts}
                if len(vs) == 1 and (colour is None or vs == {colour}):
                    m = 0
                    for x in pts:
                        m |= 1 << x
                    out.add(m)
        return list(out)

    @staticmethod
    def _partitionable(target, cubes):
        """Can `target` be split into disjoint cubes drawn from `cubes`?"""
        memo = {}

        def go(rem):
            if not rem:
                return True
            if rem in memo:
                return memo[rem]
            low = rem & -rem
            res = any(go(rem & ~c) for c in cubes if c & low and c & rem == c)
            memo[rem] = res
            return res

        return go(target)

    def UC_b(self, b):
        pts = self.ones if b else self.zeros
        if not pts:
            return 0
        target = 0
        for x in pts:
            target |= 1 << x
        for k in range(self.n + 1):
            if self._partitionable(target, self._cubes(k, colour=b)):
                return k
        return self.n

    def SP(self):
        target = 0
        for x in self.dom:
            target |= 1 << x
        if not target:
            return 0
        for k in range(self.n + 1):
            if self._partitionable(target, self._cubes(k)):
                return k
        return self.n

    # -- spectral ------------------------------------------------------------

    def lam(self):
        """Spectral norm of the adjacency matrix of the sensitivity graph."""
        A = np.zeros((self.N, self.N))
        for x in self.dom:
            for i in range(self.n):
                if self._flip(x, 1 << i):
                    A[x, x ^ (1 << i)] = 1.0
        if not A.any():
            return 0.0
        return float(np.max(np.abs(np.linalg.eigvalsh(A))))

    # -- degree --------------------------------------------------------------

    def _monomials(self, d):
        """Multilinear monomials of degree <= d, as (mask, evaluation vector)."""
        out = []
        for S in range(self.N):
            if popcount(S) <= d:
                out.append([1.0 if x & S == S else 0.0 for x in range(self.N)])
        return out

    def deg(self):
        """Least degree of a polynomial agreeing with f on the domain.

        Off the promise it is unconstrained, so this is a solvability question:
        the system is consistent iff adding the values as a column does not
        raise the rank.
        """
        for d in range(self.n + 1):
            mons = self._monomials(d)
            rows = [[m[x] for m in mons] for x in self.dom]
            aug = [r + [float(self.f[x])] for r, x in zip(rows, self.dom)]
            if exact_rank(rows) == exact_rank(aug):
                return d
        return self.n

    def adeg(self, eps=ADEG_EPS):
        """|p - f| <= eps on the domain, and |p| <= 1 + eps on the whole cube.

        The boundedness off the promise is the part that makes this the
        measure quantum algorithms produce; for a total function it is implied.
        """
        for d in range(self.n + 1):
            mons = self._monomials(d)
            k = len(mons)
            A, b = [], []
            for x in self.dom:
                row = [m[x] for m in mons]
                A.append(row)
                b.append(self.f[x] + eps)
                A.append([-v for v in row])
                b.append(-(self.f[x] - eps))
            for x in range(self.N):
                row = [m[x] for m in mons]
                A.append(row)
                b.append(1.0 + eps)
                A.append([-v for v in row])
                b.append(1.0 + eps)
            if lp_feasible(A, b, k):
                return d
        return self.n

    def odeg(self, eps=ADEG_EPS):
        """One-sided: |p| <= eps on 0-inputs, p >= 1 - eps on 1-inputs."""
        for d in range(self.n + 1):
            mons = self._monomials(d)
            k = len(mons)
            A, b = [], []
            for x in self.dom:
                row = [m[x] for m in mons]
                if self.f[x]:
                    A.append([-v for v in row])
                    b.append(-(1.0 - eps))
                else:
                    A.append(row)
                    b.append(eps)
                    A.append([-v for v in row])
                    b.append(eps)
            if lp_feasible(A, b, k):
                return d
        return self.n

    def sdeg(self):
        """Least degree with sign(p(x)) = (-1)^{f(x)} on the domain."""
        for d in range(self.n + 1):
            mons = self._monomials(d)
            k = len(mons)
            # maximise the margin gamma with coefficients bounded, feasible iff > 0
            A, b = [], []
            for x in self.dom:
                s = -1.0 if self.f[x] else 1.0
                A.append([-s * m[x] for m in mons] + [1.0])
                b.append(0.0)
            r = linprog([0.0] * k + [-1.0], A_ub=A or None, b_ub=b or None,
                        bounds=[(-1, 1)] * k + [(0, 1)], method="highs")
            if r.status == 0 and -r.fun > EPS:
                return d
        return self.n

    def cjdeg(self, eps=ADEG_EPS):
        """Least width of a conical junta (non-negative combination) approximation.

        The junta approximates f on the promise and, like adeg and unlike the
        exact degrees, stays below 1 + eps on the whole cube.  That bound is
        what a randomized algorithm hands over -- Pr[output 1] is defined off
        the promise as well -- and without it cjdeg drops below adeg, which
        the zoo records as impossible; see the note on the measure's page.
        """
        for d in range(self.n + 1):
            cubes = []
            for fix in range(self.N):
                if popcount(fix) > d:
                    continue
                for val in submasks(fix):
                    cubes.append([1.0 if x & fix == val else 0.0
                                  for x in range(self.N)])
            k = len(cubes)
            A, b = [], []
            for x in self.dom:
                row = [c[x] for c in cubes]
                A.append(row)
                b.append(self.f[x] + eps)
                A.append([-v for v in row])
                b.append(-(self.f[x] - eps))
            for x in range(self.N):
                A.append([c[x] for c in cubes])
                b.append(1.0 + eps)
            if lp_feasible(A, b, k, bounds=(0, None)):
                return d
        return self.n

    def ndeg_of(self, ones, zeros):
        """Least degree of p vanishing exactly off `ones`.

        p must vanish on every point of `zeros` and be nonzero at every point
        of `ones`.  Over the reals a generic member of the vanishing subspace
        works, so the condition at a point x is just that the evaluation row of
        x is not already in the row space of the vanishing constraints.
        """
        for d in range(self.n + 1):
            mons = self._monomials(d)
            rows = [[m[x] for m in mons] for x in zeros]
            base = exact_rank(rows)
            if all(exact_rank(rows + [[m[x] for m in mons]]) > base for x in ones):
                return d
        return self.n

    # -- the census row ------------------------------------------------------

    def all_measures(self):
        m = super().all_measures()
        m["s0"] = max((self.sens(x) for x in self.zeros), default=0)
        m["s1"] = max((self.sens(x) for x in self.ones), default=0)
        m["s"] = max(m["s0"], m["s1"])
        m["bs0"] = max((self.bs_x(x) for x in self.zeros), default=0)
        m["bs1"] = max((self.bs_x(x) for x in self.ones), default=0)
        m["bs"] = max(m["bs0"], m["bs1"])
        m["fbs"] = max((self.fbs_x(x) for x in self.dom), default=0.0)
        m["FC"] = max((self.FC_x(x) for x in self.dom), default=0.0)
        m["C0"] = max((self.C_x(x) for x in self.zeros), default=0)
        m["C1"] = max((self.C_x(x) for x in self.ones), default=0)
        uc0, uc1 = self.UC_b(0), self.UC_b(1)
        m["UC"] = max(uc0, uc1)
        m["UCmin"] = min(uc0, uc1)
        m["SP"] = self.SP()
        m["lambda"] = self.lam()
        m["deg"] = self.deg()
        m["adeg"] = self.adeg()
        m["odeg"] = self.odeg()
        m["sdeg"] = self.sdeg()
        m["cjdeg"] = self.cjdeg()
        m["ndeg"] = self.ndeg_of(self.ones, self.zeros)
        m["rdeg"] = max(m["ndeg"], self.ndeg_of(self.zeros, self.ones))
        return m


# ------------------------------------------------------- the total function

class Small(Part):
    """A total function: everything above, plus the measures Fourier analysis needs."""

    ids = Part.ids + ("deg2", "spar", "Fdim", "L1", "Var", "Inf", "Inf1",
                      "MaxInf", "osss", "nsr")

    def __init__(self, n, table):
        super().__init__(n, [(table >> x) & 1 for x in range(1 << n)])
        self.table = table
        self.constant = not self.ones or not self.zeros

    # -- Fourier (pm 1 convention: f = 0 -> +1, f = 1 -> -1) -----------------

    def fourier(self):
        F = [1 - 2 * v for v in self.f]
        g = wht(F)                      # g[S] = 2^n * fhat(S), an integer
        return g

    def deg2(self):
        """F_2 degree: Mobius transform of the 0/1 table over GF(2)."""
        a = list(self.f)
        h = 1
        while h < self.N:
            for i in range(0, self.N, h * 2):
                for j in range(i, i + h):
                    a[j + h] ^= a[j]
            h *= 2
        return max((popcount(S) for S in range(self.N) if a[S]), default=0)

    def all_measures(self):
        m = super().all_measures()
        g = self.fourier()
        scale = Fraction(1, 1 << self.n)
        sq = [Fraction(v * v, 1 << (2 * self.n)) for v in g]
        var = float(1 - sq[0])
        inf_i = [float(sum(sq[S] for S in range(self.N) if S & (1 << i)))
                 for i in range(self.n)]
        support = [S for S in range(self.N) if g[S]]

        def ns(delta):
            rho = 1 - 2 * delta
            return 0.5 * (1 - sum(float(sq[S]) * rho ** popcount(S)
                                  for S in range(self.N)))

        m["deg2"] = self.deg2()
        m["spar"] = len(support)
        m["Fdim"] = exact_rank_gf2(support, self.n)
        m["L1"] = float(sum(abs(v) for v in g) * scale)
        m["Var"] = var
        m["Inf"] = float(sum(inf_i))
        m["Inf1"] = float(sum(inf_i))   # equal to Inf for Boolean-valued f
        m["MaxInf"] = float(max(inf_i)) if inf_i else 0.0
        m["osss"] = var / m["MaxInf"] if m["MaxInf"] > 0 else None
        m["nsr"] = None
        if not self.constant:
            # NS is non-decreasing on [0, 1/2] and reaches Var/2 there, so the
            # threshold Var/4 is always crossed: bisect for it.
            lo, hi = 0.0, 0.5
            for _ in range(60):
                mid = (lo + hi) / 2
                if ns(mid) >= var / 4:
                    hi = mid
                else:
                    lo = mid
            m["nsr"] = 1.0 / hi if hi > 0 else None
        return m


def exact_rank_gf2(support, n):
    """Dimension of the F_2 span of the Fourier support, viewed as vectors."""
    basis = []
    for S in support:
        v = S
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
            basis.sort(reverse=True)
    return len(basis)


# --------------------------------------------------------------- naming things

def partial_str(vals):
    """A partial function as a string over 0, 1, * -- index is the input."""
    return "".join("*" if v is None else str(v) for v in vals)


def partial_parse(s):
    return [None if c == "*" else int(c) for c in s]


def relation_str(sets, k):
    """A relation as output sets per input: '0|12' allows 0 at x=0, 1 or 2 at x=1."""
    return "|".join("".join(str(o) for o in range(k) if S >> o & 1) for S in sets)


def relation_parse(s):
    sets = []
    for part in s.split("|"):
        m = 0
        for c in part:
            m |= 1 << int(c)
        sets.append(m)
    k = max(1, max(x.bit_length() for x in sets))
    return sets, k


# ------------------------------------------------------------------- the census

def _sweep(name, ns, reps, make, label, verbose):
    out = {"ns": list(ns), "classes": {}}
    for n in ns:
        t = time.time()
        items = reps(n)
        rows = []
        for i, item in enumerate(items):
            rows.append({"table": label(n, item), "m": make(n, item).all_measures()})
            if verbose and (i + 1) % 50 == 0:
                print(f"    {name} n={n}: {i + 1}/{len(items)} classes "
                      f"({time.time() - t:.0f}s)", flush=True)
        out["classes"][str(n)] = rows
        if verbose:
            print(f"  {name} n={n}: {len(items)} classes in {time.time() - t:.0f}s",
                  flush=True)
    return out


def build(ns=TOTAL_NS, partial_ns=PARTIAL_NS, relation_ns=RELATION_NS,
          k=RELATION_K, verbose=True):
    settings = {}
    settings["total"] = _sweep(
        "total", ns, orbit_reps, Small, lambda n, t: f"0x{t:x}", verbose)
    settings["partial"] = _sweep(
        "partial", partial_ns, partial_reps,
        lambda n, lab: Part(n, [None if v == 2 else v for v in lab]),
        lambda n, lab: partial_str([None if v == 2 else v for v in lab]), verbose)
    settings["relation"] = _sweep(
        "relation", relation_ns, lambda n: relation_reps(n, k),
        lambda n, lab: Rel(n, lab, k),
        lambda n, lab: relation_str(lab, k), verbose)
    settings["relation"]["outputs"] = k
    counts = {}
    for n in sorted({*ns, *partial_ns, *relation_ns}):
        counts[str(n)] = {
            "total_raw": 1 << (1 << n),
            "total_classes": burnside(n, 2),
            "partial_classes": burnside(n, 3),
            f"relation_classes_{k}": burnside(n, (1 << k) - 1),
        }
    return {"settings": settings, "counts": counts}


def load(rebuild=False, **kw):
    if CENSUS.exists() and not rebuild:
        return json.loads(CENSUS.read_text())
    data = build(**kw)
    CENSUS.write_text(json.dumps(data))
    return data


def show(n, spec):
    """Print one object's measures; the spec says which setting it belongs to."""
    if "|" in spec:
        sets, k = relation_parse(spec)
        obj, what = Rel(n, sets, max(k, 2)), f"relation {spec}"
    elif "*" in spec:
        obj, what = Part(n, partial_parse(spec)), f"partial function {spec}"
    else:
        t = int(spec, 0)
        obj, what = Small(n, t), f"table 0x{t:x} f={''.join(str(b) for b in [(t >> x) & 1 for x in range(1 << n)])}"
    print(f"n={n} {what}")
    for key, v in sorted(obj.all_measures().items()):
        print(f"  {key:8s} {v}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=max(TOTAL_NS),
                    help="largest arity of total function to enumerate")
    ap.add_argument("--partial-n", type=int, default=max(PARTIAL_NS))
    ap.add_argument("--relation-n", type=int, default=max(RELATION_NS))
    ap.add_argument("--outputs", type=int, default=RELATION_K,
                    help="output symbols a relation may use")
    ap.add_argument("--show", nargs=2, metavar=("N", "OBJECT"),
                    help="print one object's measures and exit: a truth table, "
                         "a 0/1/* string, or output sets like '0|12'")
    ap.add_argument("--counts", action="store_true",
                    help="just print how many classes there are")
    args = ap.parse_args()

    if args.show:
        show(int(args.show[0]), args.show[1])
        return 0

    if args.counts:
        k = args.outputs
        print(f"{'n':>2} {'raw total':>12} {'total':>8} {'partial raw':>14} "
              f"{'partial':>10} {'relations (' + str(k) + ' outputs)':>22}")
        for n in range(1, args.n + 1):
            print(f"{n:>2} {1 << (1 << n):>12} {burnside(n, 2):>8} "
                  f"{3 ** (1 << n):>14} {burnside(n, 3):>10} "
                  f"{burnside(n, (1 << k) - 1):>22}")
        return 0

    data = build(tuple(range(1, args.n + 1)),
                 tuple(range(1, args.partial_n + 1)),
                 tuple(range(1, args.relation_n + 1)), args.outputs)
    CENSUS.write_text(json.dumps(data))
    tot = sum(len(rows) for s in data["settings"].values()
              for rows in s["classes"].values())
    print(f"wrote {CENSUS} -- {tot} classes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
