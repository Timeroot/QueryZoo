#!/usr/bin/env python3
r"""
Asymptotics for the LaTeX values recorded on function pages.

The zoo records values like `\Theta(n)`, `\sqrt{n}`, `2^{n/2}\sqrt n`,
`\Theta(m^{3/2}) = \Theta(\sqrt N)`, `3 - 2^{2-n}`. Comparing two of them --
"is UC(OR) unbounded in terms of C_min(OR)?" -- is the whole content of a
separation, so it is worth doing exactly rather than by eyeball.

Everything here is a means to one end: `compare(A, B)`, which says how much
bigger the family makes A than B. What it needs from a value is only its
growth rate, and the growth rates that actually appear in the data all fit one
shape:

    s * c * 2^(e n^r) * n^p * (log n)^q * (log log n)^t * (log log log n)^u

with a single asymptotic variable `n`. That is a Hardy field small enough to
compute in with tuples of floats and big enough for every value the zoo
records: polynomials, roots, logs, exponentials of a power, and products and
quotients of those. The last two slots exist only because `log` of a value has
to land back in the family (log of n^p is p log n; log of that is log log n).

Anything outside the shape -- a second free variable, a value that depends on
a parameter such as $\varepsilon$, a conditional value ("$1$ if $p=2$;
$n$ if $p>2$"), a value phrased in terms of another *measure* -- raises
Unparsable and is skipped by the caller. Skipping is always safe; guessing is
not.

Run this file directly to execute its self-test.
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass, replace

EPS = 1e-9


class Unparsable(Exception):
    """This value is not a single closed form in the family's variable."""


# --------------------------------------------------------------------------
# the growth algebra
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class G:
    """One growth rate. See the module docstring for the shape."""

    c: float = 1.0     # positive coefficient
    e: float = 0.0     # 2^(e n^r): the exponential factor, 0 if there is none
    r: float = 0.0
    p: float = 0.0     # n^p
    q: float = 0.0     # (log n)^q
    t: float = 0.0     # (log log n)^t
    u: float = 0.0     # (log log log n)^u
    s: int = 1         # sign

    # -- ordering by magnitude
    def key(self):
        """Lexicographic key: bigger tuple = bigger |value|, for large n."""
        if self.e > EPS:
            lvl = (2, self.r, self.e)
        elif self.e < -EPS:
            # a decaying exponential: the faster it decays the smaller it is
            lvl = (0, -self.r, self.e)
        else:
            lvl = (1, 0.0, 0.0)
        return (lvl, self.p, self.q, self.t, self.u)

    def limit(self):
        """+-inf, 0.0, or the finite limit."""
        k, base = self.key(), G().key()
        if k > base:
            return math.inf * self.s
        if k < base:
            return 0.0
        return self.c * self.s

    def grows(self):
        return self.limit() in (math.inf, -math.inf)

    def bounded(self):
        return not self.grows()

    def is_zero(self):
        """Exactly 0, as opposed to merely tending to 0 (like 1/n)."""
        return self.c == 0 and self.key() == G().key()

    def __str__(self):
        bits = []
        if abs(self.c - 1) > EPS or not (self.e or self.p or self.q):
            bits.append(f"{self.c:g}")
        if self.e:
            bits.append(f"2^({self.e:g} n^{self.r:g})")
        if self.p:
            bits.append(f"n^{self.p:g}")
        if self.q:
            bits.append(f"log^{self.q:g} n")
        if self.t:
            bits.append(f"loglog^{self.t:g} n")
        if self.u:
            bits.append(f"logloglog^{self.u:g} n")
        return ("-" if self.s < 0 else "") + " ".join(bits)


ONE = G()
VAR = G(p=1.0)


def _clean(g: G) -> G:
    if abs(g.e) < EPS:
        g = replace(g, e=0.0, r=0.0)
    return replace(g, **{k: (0.0 if abs(getattr(g, k)) < EPS else getattr(g, k))
                         for k in "pqtu"})


def _exp_sum(e1, r1, e2, r2):
    """e1 n^r1 + e2 n^r2, kept in the family: the dominant term wins."""
    if abs(e1) < EPS:
        return (e2, r2)
    if abs(e2) < EPS:
        return (e1, r1)
    if abs(r1 - r2) < EPS:
        return (e1 + e2, r1)
    return (e1, r1) if r1 > r2 else (e2, r2)


def mul(a: G, b: G) -> G:
    e, r = _exp_sum(a.e, a.r, b.e, b.r)
    return _clean(G(c=a.c * b.c, e=e, r=r, p=a.p + b.p, q=a.q + b.q,
                    t=a.t + b.t, u=a.u + b.u, s=a.s * b.s))


def inv(a: G) -> G:
    if a.c == 0:
        raise Unparsable("division by zero")
    return _clean(G(c=1.0 / a.c, e=-a.e, r=a.r, p=-a.p, q=-a.q, t=-a.t,
                    u=-a.u, s=a.s))


def div(a: G, b: G) -> G:
    return mul(a, inv(b))


def add(a: G, b: G) -> G:
    """a + b, where b may be negative. The dominant term wins."""
    ka, kb = a.key(), b.key()
    if ka > kb:
        return a
    if kb > ka:
        return b
    c = a.c * a.s + b.c * b.s
    if abs(c) < EPS * max(a.c, b.c, 1.0):
        # exact cancellation of the leading term: what is left is invisible
        # at this resolution, so refuse rather than guess ($n - n$, $1 - 1$).
        raise Unparsable("leading terms cancel")
    return replace(a, c=abs(c), s=1 if c > 0 else -1)


def power(a: G, k: float) -> G:
    """a^k for a numeric exponent k."""
    if a.s < 0 and abs(k - round(k)) > EPS:
        raise Unparsable("fractional power of a negative quantity")
    s = -1 if (a.s < 0 and round(k) % 2) else 1
    return _clean(G(c=a.c ** k, e=a.e * k, r=a.r, p=a.p * k, q=a.q * k,
                    t=a.t * k, u=a.u * k, s=s))


def powg(a: G, b: G) -> G:
    """a^b where the exponent may itself grow: this is where 2^n comes from."""
    if b.key() == ONE.key():        # constant exponent
        return power(a, b.c * b.s)
    if a.key() != ONE.key() or a.s < 0:
        raise Unparsable("non-constant base raised to a growing power")
    base = a.c
    if base <= 0:
        raise Unparsable("non-positive base")
    lg = math.log2(base)            # a^b = 2^(lg * b)
    coef = lg * b.c * b.s
    if b.p:                         # 2^(coef n^p): a genuine exponential
        if b.q or b.t or b.u:
            raise Unparsable("exponent mixes powers and logs")
        return _clean(G(e=coef, r=b.p))
    if b.q == 1 and not (b.t or b.u):   # 2^(coef log n) = n^coef
        return _clean(G(p=coef))
    raise Unparsable("exponent is not a power of n or a single log")


def log(a: G) -> G:
    """log2 of a growing quantity, back inside the family."""
    if a.s < 0:
        raise Unparsable("log of a negative quantity")
    if a.e:
        return _clean(G(c=abs(a.e), p=a.r, s=1 if a.e > 0 else -1))
    for src, dst in (("p", "q"), ("q", "t"), ("t", "u")):
        v = getattr(a, src)
        if v:
            return _clean(G(**{dst: 1.0}, c=abs(v), s=1 if v > 0 else -1))
    if a.u:
        raise Unparsable("log of a quadruply-logarithmic quantity")
    if a.c <= 0:
        raise Unparsable("log of a non-positive constant")
    lg = math.log2(a.c)
    if abs(lg) < EPS:
        raise Unparsable("log of 1 is 0, which has no growth rate")
    return G(c=abs(lg), s=1 if lg > 0 else -1)


def bigger(a: G, b: G) -> bool:
    return (a.key(), a.c * a.s) > (b.key(), b.c * b.s)


# --------------------------------------------------------------------------
# the parser
# --------------------------------------------------------------------------

# Decoration that carries no mathematics.
_DROP = {r"\,", r"\!", r"\;", r"\:", r"\ ", r"\quad", r"\qquad", r"\left",
         r"\right", r"\big", r"\Big", r"\bigg", r"\bigl", r"\bigr", r"\Bigl",
         r"\Bigr", r"\ldots", r"\dots", r"\cdots", r"\displaystyle", r"\,"}
_MUL = {r"\cdot", r"\times"}
_OPEN = {"(", "{", "[", r"\lceil", r"\lfloor", r"\{"}
_CLOSE = {")", "}", "]", r"\rceil", r"\rfloor", r"\}"}
_QUAL = {r"\Theta": "both", "O": "up", "o": "up", r"\Omega": "lo",
         r"\omega": "lo", r"\Lambda": "both"}
_TILDE = {r"\widetilde", r"\tilde", r"\overline"}
_REL = {r"\le": "up", r"\leq": "up", r"\ge": "lo", r"\geq": "lo"}
_CONST = {r"\pi": math.pi, "e": math.e}
# A value that mentions any of these is not a closed form in the family's
# variable: it is conditional prose, or it is phrased in another measure.
_REJECT = (r"\text", r"\mathrm", r"\mathbb", r"\operatorname", r"\deg",
           r"\mathcal", r"\mathbf", "|", r"\sim", r"\approx", r"\pm", "%")
# a bare `;` separates two regimes ("1 if p = 2; n if p > 2"); `\;` is a space
_REJECT_RE = re.compile(r"(?<!\\);")

_TOKEN = re.compile(r"\\[a-zA-Z]+|\\[{}]|\\[,!;: ]|\d+\.\d+|\d+|[a-zA-Z]|\S")


def tokenize(text: str):
    out = []
    for tok in _TOKEN.findall(text):
        if tok in _DROP:
            continue
        if tok == "_":                     # \log_2 -> \log
            continue
        out.append(tok)
    return out


def _split_top(toks, seps):
    """Split a token list on separators at bracket depth zero."""
    parts, cur, depth = [], [], 0
    for tok in toks:
        if tok in _OPEN:
            depth += 1
        elif tok in _CLOSE:
            depth -= 1
        if depth == 0 and tok in seps:
            parts.append(cur)
            cur = []
        else:
            cur.append(tok)
    parts.append(cur)
    return [p for p in parts if p]


class _Parser:
    """Recursive descent straight into the growth algebra."""

    def __init__(self, toks, env):
        self.toks = toks
        self.i = 0
        self.env = env            # variable name -> G

    # -- token helpers
    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else None

    def take(self):
        tok = self.peek()
        if tok is None:
            raise Unparsable("unexpected end of value")
        self.i += 1
        return tok

    def expect(self, kinds):
        tok = self.take()
        if tok not in kinds:
            raise Unparsable(f"expected one of {sorted(kinds)}, got {tok!r}")
        return tok

    def done(self):
        return self.i >= len(self.toks)

    # -- grammar
    def expr(self) -> G:
        val = self.term()
        while self.peek() in ("+", "-"):
            op = self.take()
            rhs = self.term()
            val = add(val, rhs if op == "+" else mul(G(s=-1), rhs))
        return val

    def term(self) -> G:
        val = self.factor()
        while True:
            tok = self.peek()
            if tok in _MUL or tok == "*":
                self.take()
                val = mul(val, self.factor())
            elif tok == "/":
                self.take()
                val = div(val, self.factor())
            elif self.starts_factor(tok):
                val = mul(val, self.factor())        # implicit multiplication
            else:
                return val

    def starts_factor(self, tok):
        if tok is None:
            return False
        if tok in ("+", "-", "*", "/", ",", "=", "^") or tok in _CLOSE:
            return False
        if tok in _REL:
            return False
        return True

    def factor(self) -> G:
        val = self.atom()
        if self.peek() == "^":
            self.take()
            val = powg(val, self.factor())
        return val

    def atom(self) -> G:
        tok = self.take()
        # Unary sign binds *looser* than `^`, as in ordinary mathematical
        # notation: `2^{-n^2}` is 2^(-(n^2)), not 2^((-n)^2). Recursing into
        # factor() rather than atom() is what gets the decaying exponentials
        # (`\Theta(n^2 2^{-n})` for the total influence of an unbalanced
        # function) on the correct side of 1.
        if tok == "-":
            return mul(G(s=-1), self.factor())
        if tok == "+":
            return self.factor()
        if tok in _OPEN:
            val = self.expr()
            self.expect(_CLOSE)
            return val
        if re.fullmatch(r"\d+(\.\d+)?", tok):
            return G(c=float(tok))
        if tok in _CONST and not (tok == "e" and "e" in self.env):
            return G(c=_CONST[tok])
        if tok in (r"\frac", r"\tfrac", r"\dfrac"):
            return div(self.atom(), self.atom())
        if tok == r"\sqrt":
            root = 2.0
            if self.peek() == "[":
                self.take()
                root = self.expr().c
                self.expect("]")
            return power(self.atom(), 1.0 / root)
        if tok in (r"\log", r"\lg", r"\ln"):
            k = 1.0
            if self.peek() == "^":                   # \log^2 n
                self.take()
                k = self.atom().c
            if self.peek() in ("2", "3"):            # the subscript of \log_2
                self.take()
            return power(log(self.atom()), k)
        if tok == r"\binom":
            top, bot = self.atom(), self.atom()
            if bot.key() != ONE.key():
                raise Unparsable("binomial with a growing lower index")
            k = bot.c * bot.s
            if abs(k - round(k)) > EPS or k < 0:
                raise Unparsable("binomial with a non-integer lower index")
            return mul(G(c=1.0 / math.factorial(int(round(k)))),
                       power(top, round(k)))
        if tok in (r"\min", r"\max"):
            args = self.arglist()
            best = args[0]
            for a in args[1:]:
                if (tok == r"\max") == bigger(a, best):
                    best = a
            return best
        if tok in _TILDE:
            return self.atom()
        if tok in _QUAL or (tok in ("O", "o") and self.peek() in _OPEN):
            return self.atom()                       # a wrapper is identity
        if tok in self.env:
            return self.env[tok]
        raise Unparsable(f"unknown symbol {tok!r}")

    def arglist(self):
        """The arguments of \\min / \\max: one bracketed, comma-separated group."""
        self.expect(_OPEN)
        depth, inner = 1, []
        while True:
            tok = self.take()
            if tok in _OPEN:
                depth += 1
            elif tok in _CLOSE:
                depth -= 1
                if depth == 0:
                    break
            inner.append(tok)
        return [_Parser(part, self.env).run() for part in _split_top(inner, {","})]

    def run(self) -> G:
        val = self.expr()
        if not self.done():
            raise Unparsable(f"trailing tokens from {self.peek()!r}")
        return val


_NAME = re.compile(r"[a-zA-Z]")


def free_names(text: str):
    """The symbols a value needs in its environment, or None if it is not a
    closed form at all. Used to work out a family's asymptotic variable."""
    try:
        for bad in _REJECT:
            if bad in text:
                return None
        if _REJECT_RE.search(text):
            return None
        toks = tokenize(text)
    except Exception:
        return None
    out = set()
    for i, tok in enumerate(toks):
        if tok == r"\ell":
            out.add(tok)
        elif _NAME.fullmatch(tok):
            nxt = toks[i + 1] if i + 1 < len(toks) else None
            if tok in ("O", "o") and nxt in _OPEN:
                continue          # a Landau symbol, not a variable
            if tok == "e":
                continue          # Euler's constant
            out.add(tok)
    return out


@dataclass
class Value:
    """What a recorded value licenses: a lower bound, an upper bound, or both."""

    lo: G | None = None      # the measure is Omega(lo) on this family
    up: G | None = None      # the measure is O(up) on this family
    tilde: bool = False      # stated only up to polylog factors
    approx: bool = False     # written with a truncated decimal ("N^{0.753...}")

    def both(self):
        return self.lo if (self.lo is not None and self.up is not None) else None


def _direction(toks):
    """(direction, tilde, inner tokens) for one claim."""
    tilde = False
    if toks and toks[0] in _REL:
        return _REL[toks[0]], False, toks[1:]
    i = 0
    while i < len(toks) and toks[i] in _TILDE:
        tilde, i = True, i + 1
    if i < len(toks) and toks[i] in _QUAL:
        head, rest = toks[i], toks[i + 1:]
        # the wrapper must span the whole claim for its direction to apply
        if rest and rest[0] in _OPEN and len(_split_top(rest, set())) == 1:
            depth = 0
            for j, tok in enumerate(rest):
                depth += (tok in _OPEN) - (tok in _CLOSE)
                if depth == 0:
                    if j == len(rest) - 1:
                        return _QUAL[head], tilde, rest[1:-1]
                    break
    return "both", tilde, toks


def parse_value(text: str, env: dict[str, G]) -> Value:
    """Parse one recorded `value:` string. Raises Unparsable if it is not one.

    `env` maps every symbol the family may use to its growth: the asymptotic
    variable itself, plus any second name the function's `scale:` defines
    (`N = m^3` and the like).
    """
    if not text or not text.strip():
        raise Unparsable("empty value")
    for bad in _REJECT:
        if bad in text:
            raise Unparsable(f"contains {bad!r}")
    if _REJECT_RE.search(text):
        raise Unparsable("two regimes in one value")
    toks = tokenize(text)
    if not toks:
        raise Unparsable("no tokens")
    # `\Theta(m) = \Theta(\sqrt N)`: the same claim twice, in two variables.
    # Take the first phrasing that lands inside the family.
    last = Unparsable("no alternative parsed")
    approx = r"\ldots" in text or r"\dots" in text
    for alt in _split_top(toks, {"="}):
        out, ok = Value(approx=approx), True
        for claim in _split_top(alt, {","}):
            direction, tilde, inner = _direction(claim)
            try:
                g = _Parser(inner, env).run()
            except Unparsable as exc:
                last, ok = exc, False
                break
            except RecursionError:
                last, ok = Unparsable("too deeply nested"), False
                break
            if g.s < 0:
                last, ok = Unparsable("negative value"), False
                break
            out.tilde = out.tilde or tilde
            if direction in ("lo", "both"):
                out.lo = g if out.lo is None or bigger(g, out.lo) else out.lo
            if direction in ("up", "both"):
                out.up = g if out.up is None or bigger(out.up, g) else out.up
        if ok and (out.lo is not None or out.up is not None):
            return out
    raise last


# --------------------------------------------------------------------------
# what a pair of values proves
# --------------------------------------------------------------------------


def compare(a: G, b: G):
    """How much bigger is `a` than `b`, as a claim about this one family?

    `a` must be a *lower* bound on the first measure and `b` an *upper* bound
    on the second, so that every verdict below is sound.

        ('unbounded',)  -- the second measure is O(1) while the first grows:
                           no function of it can bound the first
        ('exp', k)      -- the first is at least 2^(k * second)
        ('poly', alpha) -- the first is Omega(second^alpha), alpha > 0
        None            -- nothing worth recording
    """
    if not a.grows():
        return None                       # nothing to separate with
    if not b.grows():
        # "no function of the second bounds the first" needs the second to
        # settle on a positive constant. If it tends to *zero* -- as fractional
        # measures like MaxInf do -- then g(x) = log(1/x) may well bound the
        # first measure on this family, and there is no separation to claim.
        #
        # Identically zero is the exception, and the strongest case there is.
        # A bound M1 <= g(M2) evaluated along a family with M2 == 0 says
        # M1 <= g(0), one fixed number, so a growing M1 refutes every g at
        # once. This is what the promise functions with s = 0, lambda = 0 or
        # D^prod = 0 are for: no g(x) = log(1/x) dodge is available at an
        # exact zero.
        if b.is_zero():
            return ("unbounded",)
        if b.limit() <= 0:
            return None
        return ("unbounded",)
    la, lb = log(a), log(b)
    ratio = div(la, lb).limit()
    if ratio == math.inf:
        rate = div(la, b).limit()         # is it really exponential?
        if rate > 0:
            return ("exp", rate)
        return None                       # superpolynomial but subexponential
    if ratio <= EPS:
        return None
    return ("poly", ratio)


# --------------------------------------------------------------------------
# self-test
# --------------------------------------------------------------------------


def _selftest():
    n = {"n": VAR}
    m = {"m": VAR, "N": G(p=3.0)}          # MinskyPapert: N = m^3
    d = {"d": VAR, "N": powg(G(c=2.0), VAR)}   # NANDtree: N = 2^d

    def val(s, env=None):
        return parse_value(s, env or n)

    # -- shapes
    assert str(val("n").lo) == "n^1"
    assert str(val(r"\Theta(\sqrt n)").lo) == "n^0.5"
    assert str(val(r"\Theta(n^{2/3})").lo) == "n^0.666667"
    assert str(val(r"\Theta(n\log n)").lo) == "n^1 log^1 n"
    assert str(val(r"\Theta(n/\log n)").lo) == "n^1 log^-1 n"
    assert str(val(r"\lceil n/2 \rceil").lo) == "0.5 n^1"
    assert str(val("(n+1)/2").lo) == "0.5 n^1"
    assert str(val(r"\Theta(2^{n/2}\sqrt n)").lo) == "2^(0.5 n^1) n^0.5"
    assert str(val(r"\Theta(2^n/\sqrt n)").lo) == "2^(1 n^1) n^-0.5"
    assert str(val(r"\lceil \log_2(n+1) \rceil").lo) == "log^1 n"
    assert str(val(r"\log_2 n - \Theta(1)").lo) == "log^1 n"
    assert str(val(r"\tfrac1\pi\ln n + O(1)").lo) == "0.31831 log^1 n"
    assert str(val("3 - 2^{2-n}").lo) == "3"          # tends to 3, not to 0
    # the +1 in the exponent is below the resolution of the algebra, so the
    # constant factor 2 is dropped -- harmless, and never changes a verdict
    assert str(val("n\\,2^{1-n}").lo) == "2^(-1 n^1) n^1"
    # unary minus binds looser than `^`: 2^{-n^2} decays, it is not 2^{n^2}
    assert str(val(r"\Theta(n^3 2^{-n^2})").lo) == "2^(-1 n^2) n^3"
    assert str(val(r"2^{-\Theta(\sqrt n)}").lo) == "2^(-1 n^0.5)"
    assert str(val(r"\binom m2 = n", m).lo) == "0.5 n^2"   # m = the variable
    assert str(val(r"\big(\tfrac{1+\sqrt{33}}{4}\big)^{d} = N^{0.753\ldots}",
                   d).lo).startswith("2^(0.753")
    assert str(val(r"\Theta(m^2) = \Theta(N^{2/3})", m).lo) == "n^2"
    assert str(val(r"\Theta(\sqrt N)", m).lo) == "n^1.5"
    assert str(val(r"\Theta(\max\{k,\;n-k+1\})", {"n": VAR, "k": G(c=1.0)}).lo) == "n^1"

    # -- directions
    assert val("O(n)").lo is None and str(val("O(n)").up) == "n^1"
    assert val(r"\Omega(n)").up is None
    assert val(r"\widetilde\Theta(\sqrt n)").tilde
    two = val(r"\Omega(2.59^{\,d}),\ O(2.64944^{\,d})", d)
    assert two.lo and two.up and two.lo.e < two.up.e

    # -- rejections
    for bad in [r"\rho^{\,n}", r"1 \text{ if } p = 2;\ n \text{ if } p > 2",
                r"O(\mathrm{D}^{0.8675})", r"\Theta(\min(n, 1/\delta^2))",
                r"\Theta\!\big(\sqrt{n(n-\Gamma(f))}\big)", "n - k + 1",
                r"\binom{n-1}{(n-1)/2}"]:
        try:
            val(bad)
        except Unparsable:
            pass
        else:
            raise AssertionError(f"should not have parsed: {bad}")

    # -- comparisons: the claims this module exists to make
    def cmp2(x, y, env=None):
        a, b = val(x, env), val(y, env)
        return compare(a.lo, b.up)

    assert cmp2("n", "1") == ("unbounded",)                     # UC vs C_min
    assert cmp2("n", r"3 - 2^{2-n}") == ("unbounded",)          # vs L_1(OR)
    # a decaying Inf is *not* an unbounded separation, for the same reason
    # MaxInf is not: log(1/x) is a function, and it bounds n here
    assert cmp2("n", r"\Theta(n^3 2^{-n^2})") is None
    # but an *exact* zero is: g(0) is one number, and n outgrows it
    assert cmp2("n", "0") == ("unbounded",)                     # deg vs s, GapMaj
    assert cmp2(r"\Theta(n)", "0") == ("unbounded",)
    assert cmp2("1", "0") is None            # a constant is bounded by g(0)
    assert cmp2("0", "0") is None
    assert val("0").lo.is_zero() and not val("1/n").lo.is_zero()
    # MaxInf(OR) -> 0, and g(x) = log(1/x) does bound n on this family, so
    # there is nothing to claim -- see the note in compare()
    assert cmp2("n", r"n\,2^{1-n}") is None
    assert cmp2("n", r"\Theta(\sqrt n)")[1] == 2.0              # D vs Q on OR
    assert cmp2(r"\Theta(\sqrt n)", "n")[1] == 0.5
    assert cmp2("n", r"\Theta(n/\log n)")[1] == 1.0             # a log gap
    assert cmp2(r"\Theta(2^{n/2})", r"\Theta(n)")[0] == "exp"   # Simon
    assert cmp2("n", r"\Theta(\log n)")[0] == "exp"             # OrderedSearch
    assert cmp2(r"\Theta(n)", r"\Theta(n)")[1] == 1.0
    assert cmp2("1", "n") is None
    assert cmp2(r"\Theta(\log n)", "n") is None                 # alpha = 0
    assert round(cmp2("N", r"\Theta(N^{0.753})", d)[1], 4) == 1.3280   # NANDtree
    assert cmp2(r"\Theta(m^2) = \Theta(N^{2/3})", r"\Theta(m)", m)[1] == 2.0
    print("growth.py: self-test passed")


if __name__ == "__main__":
    _selftest()
