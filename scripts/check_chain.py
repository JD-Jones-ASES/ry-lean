#!/usr/bin/env python3
"""Standalone arithmetic checker for a Younis-style nonlinear-Roth chain.

WHAT THIS SCRIPT CHECKS
=======================

Younis, "Lower bounds in the polynomial Szemerédi theorem"
(arXiv:1908.06058, 2019) gives, for the configuration

        x,  x + y,  x + y^2      (y != 0)

a construction of a large subset of {1, ..., N} containing no such
configuration (the digit sets below live in [0, m^Y) and are translated by +1).  The construction is driven by a modulus m together with two
residue sets R1, R2 subset of Z_m satisfying the hypotheses below (this is the
k = 2 case of the paper's construction).

  H0 (modulus)  m is square-free, and R1, R2 are sets of distinct residues
                inside [0, m).  Square-freeness is what makes
                    d not= 0 (mod m)  =>  d^2 not= 0 (mod m),
                i.e. a nonzero base-m digit has a nonzero square digit; without
                it the "leading digit doubles its position" step below breaks.

  H1 (R1 is square-difference-free mod m)
                for a, b in R1:  a - b = d^2 (mod m) for some d in Z_m
                forces a = b.   Equivalently
                    (R1 - R1) cap {d^2 : d in Z_m}  subset of  {0}.

  H2 (R2 versus squares of R1-differences)
                for a, b in R2 and c, d in R1:  a - b = (c - d)^2 (mod m)
                forces a = b.   Equivalently
                    (R2 - R2) cap (R1 - R1)^2  subset of  {0}.

  Derived edge conditions used by the digit argument:
                R2 -> R1:   (R1 - R1) cap (R2 - R2)^2  subset of  {0}
                R1 -> R1:   (R1 - R1) cap (R1 - R1)^2  subset of  {0}
                Both follow from H1, because every (c - d)^2 is a square mod m;
                they are checked here independently anyway.

  EXPONENT      With a = |R1| and b = |R2|,

                    gamma(m, a, b) = 1/2 + log a / (3 log m) + log b / (6 log m).

                This is the limiting value, as the number s of truncation
                levels grows, of

                    (#type0 * log m + #type1 * log a + #type2 * log b)
                        / (P * log m),      P = 2^(2s+1),

                for the position typing described next, since
                    #type0 = 4^s,  #type1 = (2*4^s + 1)/3,  #type2 = (4^s - 1)/3,
                i.e. the three frequencies are exactly
                    1/2,   1/3 + 1/(3P),   1/6 - 1/(3P),
                so the level-s exponent falls short of gamma by exactly
                    (log b - log a) / (3 P log m).
                Note gamma = 1/2 + log(a^2 * b) / (6 log m), which is why the
                exact integer bounds below are stated in terms of a^2 * b.

  POSITION TYPING (truncated rule at level s; P = 2^(2s+1) positions)
                For a digit position i:
                    i odd                     -> type 0   (digit unrestricted)
                    i = 0                     -> type 1   (digit in R1)
                    otherwise v = v_2(i):
                        v odd                 -> type 1   (digit in R1)
                        v even, 2 <= v <= 2s  -> type 2   (digit in R2)
                        v >= 2s + 1           -> type 1   (digit in R1)
                Squaring y sends the lowest nonzero digit position l of y to
                position 2l of y^2, so the admissible position edges are
                    (type(l), type(2l)) in {(1,1), (0,1), (1,2), (2,1)},
                each of which is covered by H1, H2 or a derived edge above.

DATA CHECKED
============

  chain     m = 145,  |R1| = 10,  |R2| = 32
  Younis    m =  65,  |R1| =  7,  |R2| = 17   (the sets published in
                                               arXiv:1908.06058)

EXACT INTEGER BOUNDS (no floating point anywhere in the proofs)
==============================================================

  With A = a^2 * b, gamma = 1/2 + log(A) / (6 log m), so a rational bound
  p/q on log(A)/log(m) is exactly the integer comparison A^q vs m^p.

      833^13  <  65^21     =>  gamma(65, 7, 17)  < 1/2 + 21/78
      3200^13 > 145^21     =>  gamma(145, 10, 32) > 1/2 + 21/78 > gamma(65,7,17)
      3200^37 > 145^60     =>  gamma(145, 10, 32) > 1/2 + 10/37 > 0.7702
      3200^230 < 145^373   =>  gamma(145, 10, 32) < 1/2 + 373/1380 < 0.77029

  (833 = 7^2 * 17, 3200 = 10^2 * 32.)

CONTROLS (each must FAIL; the script fails if a control unexpectedly passes)
===========================================================================

  * m = 145 with 1 adjoined to R2 must violate H2.
  * m = 125 must be rejected as not square-free, whatever the sets are.
  * m = 4 (not square-free) with R1 = R2 = {0}: the same digit construction
    does contain a configuration x, x + y, x + y^2.

DIRECT CONSTRUCTION TEST
========================

  For m = 145 the set A_Y of all integers in [0, m^Y) whose base-m digits obey
  the typing above is enumerated for Y = 3 (digit types 1, 0, 1; all m digits
  allowed at the type-0 position), and every configuration x, x + y, x + y^2
  with y a nonzero integer of either sign is ruled out by exhaustive search.
  Only |y| <= isqrt(m^Y - 1) can matter, since otherwise y^2 already exceeds
  every element of [0, m^Y); the search enumerates exactly the pairs
  {x, x + y} subset of A_Y with |y| within that bound, in both sign roles.

  The same enumeration with m = 4 (not square-free), R1 = R2 = {0} and Y = 4
  produces a configuration, exhibiting square-freeness as load-bearing: the
  digit 2 has 2^2 = 0 (mod 4) with a carry, so the lowest nonzero position of
  y^2 is 2l + 1 rather than 2l and the typing argument no longer applies.
  (Y = 4 rather than 3 only because position 2l + 1 = 3 must exist.)

Usage:  python check_chain.py            Exit status 0 iff every check passes.
Requires: CPython >= 3.9, standard library only.
"""

from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import product
import math
import sys

getcontext().prec = 80

DIGITS = 30  # decimal places printed for gamma

# ---------------------------------------------------------------- data ------

M_CHAIN = 145
R1_CHAIN = [0, 48, 55, 62, 69, 76, 117, 124, 131, 138]
R2_CHAIN = [3, 12, 13, 16, 21, 24, 25, 34, 35, 38, 43, 46, 47, 56, 57, 60,
            68, 69, 78, 79, 82, 91, 100, 104, 113, 122, 123, 125, 126, 135,
            136, 144]

M_YOUNIS = 65
R1_YOUNIS = [31, 39, 8, 62, 19, 42, 50]
R2_YOUNIS = [31, 47, 62, 34, 42, 39, 27, 8, 54, 23, 0, 58, 19, 50, 15, 12, 4]

ALLOWED_EDGES = {(1, 1), (0, 1), (1, 2), (2, 1)}

# ------------------------------------------------------------- reporting ----

RESULTS = []


def record(name, ok, detail=""):
    RESULTS.append((name, bool(ok), detail))
    print("  [%s] %s%s" % ("PASS" if ok else "FAIL", name,
                           ("  --  " + detail) if detail else ""))
    return bool(ok)


# ------------------------------------------------------- arithmetic core ----

def is_square_free(n):
    """True iff no prime square divides n (n >= 1)."""
    if n < 1:
        return False
    d = 2
    while d * d <= n:
        if n % (d * d) == 0:
            return False
        while n % d == 0:
            n //= d
        d += 1 if d == 2 else 2
    return True


def squares_mod(m):
    """{ d^2 mod m : d in Z_m }."""
    return {(d * d) % m for d in range(m)}


def difference_set(s, m):
    """{ (a - b) mod m : a, b in s }."""
    return {(a - b) % m for a in s for b in s}


def nonzero_differences(s, m):
    """{ (a - b) mod m : a, b in s, a != b }."""
    return {(a - b) % m for a in s for b in s if a != b}


def squared_differences(s, m):
    """{ ((a - b) mod m)^2 mod m : a, b in s }."""
    return {(d * d) % m for d in difference_set(s, m)}


def check_h1(m, r1):
    """H1: (R1 - R1) cap squares(Z_m) subset of {0}.  Returns (ok, witness)."""
    sq = squares_mod(m)
    for a in r1:
        for b in r1:
            if a != b and ((a - b) % m) in sq:
                d = next(d for d in range(m) if (d * d) % m == (a - b) % m)
                return False, (a, b, d)
    return True, None


def check_h2(m, r1, r2):
    """H2: (R2 - R2) cap (R1 - R1)^2 subset of {0}.  Returns (ok, witness)."""
    sq = squared_differences(r1, m)
    for a in r2:
        for b in r2:
            if a != b and ((a - b) % m) in sq:
                return False, (a, b)
    return True, None


def check_edge(m, target, source):
    """(target - target) cap (source - source)^2 subset of {0}."""
    sq = squared_differences(source, m)
    bad = sorted(nonzero_differences(target, m) & sq)
    return (not bad), bad[:4]


def gamma(m, a, b):
    """1/2 + log a / (3 log m) + log b / (6 log m), as a Decimal."""
    lm = Decimal(m).ln()
    return (Decimal(1) / Decimal(2)
            + Decimal(a).ln() / (Decimal(3) * lm)
            + Decimal(b).ln() / (Decimal(6) * lm))


def fmt(x, places=DIGITS):
    return format(x.quantize(Decimal(1).scaleb(-places)), "f")


# ---------------------------------------------------- position typing -------

def position_type(i, s):
    """Truncated typing rule at level s (see module docstring)."""
    if i == 0:
        return 1
    if i % 2 == 1:
        return 0
    v = 0
    j = i
    while j % 2 == 0:
        v += 1
        j //= 2
    if v % 2 == 1:
        return 1
    if 2 <= v <= 2 * s:
        return 2
    return 1


# ------------------------------------------------ explicit construction -----

def build_set(m, years, s, r1, r2):
    """All integers in [0, m^Y) whose base-m digits respect the typing."""
    digit_sets = []
    for i in range(years):
        t = position_type(i, s)
        digit_sets.append(sorted(r1) if t == 1
                          else sorted(r2) if t == 2
                          else list(range(m)))
    powers = [m ** i for i in range(years)]
    out = []
    for combo in product(*reversed(digit_sets)):
        digits = combo[::-1]
        out.append(sum(d * p for d, p in zip(digits, powers)))
    out.sort()
    return out


def find_configuration(elements, m, years):
    """Search for x, x+y, x+y^2 all in `elements`, y a nonzero integer.

    `elements` must be sorted and contained in [0, m^Y).  Any y with
    |y| > isqrt(m^Y - 1) has y^2 > m^Y - 1, so x + y^2 lies outside the
    ambient interval; only smaller |y| is enumerated, via the pairs
    {x, x + |y|} of elements, each pair taken in both sign roles.
    """
    n_total = m ** years
    bound = math.isqrt(n_total - 1)
    present = set(elements)
    n = len(elements)
    for i in range(n):
        x = elements[i]
        j = i + 1
        while j < n and elements[j] - x <= bound:
            gap = elements[j] - x
            if x + gap * gap in present:              # y = +gap, base x
                return (x, gap)
            if elements[j] + gap * gap in present:    # y = -gap, base elements[j]
                return (elements[j], -gap)
            j += 1
    return None


# --------------------------------------------------------------- checks -----

def check_dataset(label, m, r1, r2):
    print("\n%s: m = %d, |R1| = %d, |R2| = %d" % (label, m, len(r1), len(r2)))
    ok = True
    ok &= record("%s: m square-free" % label, is_square_free(m), "m = %d" % m)
    ok &= record("%s: R1 elements distinct" % label,
                 len(set(r1)) == len(r1), "%d listed" % len(r1))
    ok &= record("%s: R2 elements distinct" % label,
                 len(set(r2)) == len(r2), "%d listed" % len(r2))
    ok &= record("%s: R1 subset of [0, m)" % label,
                 all(0 <= x < m for x in r1))
    ok &= record("%s: R2 subset of [0, m)" % label,
                 all(0 <= x < m for x in r2))

    h1_ok, h1_w = check_h1(m, r1)
    ok &= record("%s: H1 (R1 square-difference-free mod m)" % label, h1_ok,
                 "" if h1_ok else "a=%d b=%d d=%d" % h1_w)
    h2_ok, h2_w = check_h2(m, r1, r2)
    ok &= record("%s: H2 ((R2-R2) cap (R1-R1)^2 subset {0})" % label, h2_ok,
                 "" if h2_ok else "a=%d b=%d" % h2_w)

    e1_ok, e1_bad = check_edge(m, r1, r2)
    ok &= record("%s: edge R2->R1 ((R1-R1) cap (R2-R2)^2 subset {0})" % label,
                 e1_ok, "" if e1_ok else "hits %s" % e1_bad)
    e2_ok, e2_bad = check_edge(m, r1, r1)
    ok &= record("%s: edge R1->R1 ((R1-R1) cap (R1-R1)^2 subset {0})" % label,
                 e2_ok, "" if e2_ok else "hits %s" % e2_bad)
    return ok


def check_exponents():
    print("\nExponents (Decimal, %d places):" % DIGITS)
    g0 = gamma(M_YOUNIS, len(R1_YOUNIS), len(R2_YOUNIS))
    g = gamma(M_CHAIN, len(R1_CHAIN), len(R2_CHAIN))
    print("  gamma0(65, 7, 17)    = %s" % fmt(g0))
    print("  gamma (145, 10, 32)  = %s" % fmt(g))
    ok = record("gamma0 < gamma (Decimal)", g0 < g,
                "difference = %s" % fmt(g - g0))

    half = Decimal(1) / Decimal(2)
    # Exact integer facts; each is an inequality between two integers.
    f1 = 833 ** 13 < 65 ** 21
    f2 = 3200 ** 13 > 145 ** 21
    f3 = 3200 ** 37 > 145 ** 60
    f4 = 3200 ** 230 < 145 ** 373
    ok &= record("integer: 833^13 < 65^21  (=> gamma0 < 1/2 + 21/78)", f1)
    ok &= record("integer: 3200^13 > 145^21  (=> gamma > 1/2 + 21/78)", f2)
    ok &= record("integer: both of the above (=> gamma0 < gamma, exactly)",
                 f1 and f2)
    ok &= record("integer: 3200^37 > 145^60  (=> gamma > 1/2 + 10/37 > 0.7702)",
                 f3)
    ok &= record("integer: 3200^230 < 145^373  "
                 "(=> gamma < 1/2 + 373/1380 < 0.77029)", f4)

    # The sets used in gamma must be the sets whose sizes enter a^2 * b.
    ok &= record("a^2*b matches the sets: 7^2*17 = 833, 10^2*32 = 3200",
                 len(R1_YOUNIS) ** 2 * len(R2_YOUNIS) == 833
                 and len(R1_CHAIN) ** 2 * len(R2_CHAIN) == 3200)

    # Cross-check: the Decimal values must obey the exact rational bounds.
    lo0, hi0 = half, half + Decimal(21) / Decimal(78)
    lo, hi = half + Decimal(10) / Decimal(37), half + Decimal(373) / Decimal(1380)
    ok &= record("Decimal gamma0 inside its integer-proved bound",
                 lo0 < g0 < hi0)
    ok &= record("Decimal gamma inside its integer-proved bounds",
                 lo < g < hi,
                 "%s < gamma < %s" % (fmt(lo, 10), fmt(hi, 10)))
    ok &= record("gamma > 0.7702 and gamma < 0.77029 (printed value)",
                 Decimal("0.7702") < g < Decimal("0.77029"))
    return ok


def check_controls():
    print("\nControls (each must fail):")
    ok = True
    r2_plus = sorted(set(R2_CHAIN) | {1})
    h2_ok, h2_w = check_h2(M_CHAIN, R1_CHAIN, r2_plus)
    ok &= record("control: R2 + {1} violates H2 at m = 145", not h2_ok,
                 "witness a=%d b=%d" % h2_w if h2_w else "NO WITNESS FOUND")
    ok &= record("control: m = 125 rejected as not square-free",
                 not is_square_free(125), "125 = 5^3")
    # A non-square-free modulus is rejected before any set is even looked at.
    ok &= record("control: m = 125 rejected whatever the sets are",
                 not is_square_free(125) and not is_square_free(4)
                 and not is_square_free(1445))
    return ok


def check_block_counts():
    print("\nTruncated-rule block counts and position edges:")
    ok = True
    for s in range(4):
        p = 2 ** (2 * s + 1)
        counts = {0: 0, 1: 0, 2: 0}
        for i in range(p):
            counts[position_type(i, s)] += 1
        want = {0: 4 ** s,
                1: (2 * 4 ** s + 1) // 3,
                2: (4 ** s - 1) // 3}
        exact = ((2 * 4 ** s + 1) % 3 == 0) and ((4 ** s - 1) % 3 == 0)
        ok &= record("s=%d: P=%d, counts %s = predicted %s" % (s, p, counts, want),
                     counts == want and sum(counts.values()) == p and exact)
        edges = {(position_type(l, s), position_type(2 * l, s))
                 for l in range(4 * p)}
        bad = sorted(edges - ALLOWED_EDGES)
        ok &= record("s=%d: (type(l), type(2l)) admissible for all l < 4P" % s,
                     not bad,
                     "observed %s" % sorted(edges) if not bad else "bad %s" % bad)
        # Exact frequencies: type0 is exactly half, and the other two approach
        # 1/3 and 1/6 with the same error 1/(3P) -- this is what makes the
        # level-s exponent tend to gamma.
        ok &= record("s=%d: exact frequencies 1/2, 1/3 + 1/(3P), 1/6 - 1/(3P)" % s,
                     Fraction(counts[0], p) == Fraction(1, 2)
                     and Fraction(counts[1], p) == Fraction(1, 3) + Fraction(1, 3 * p)
                     and Fraction(counts[2], p) == Fraction(1, 6) - Fraction(1, 3 * p))
        # Level-s exponent for the m = 145 data, and its exact gap to gamma.
        lm = Decimal(M_CHAIN).ln()
        la = Decimal(len(R1_CHAIN)).ln()
        lb = Decimal(len(R2_CHAIN)).ln()
        g_s = (counts[0] * lm + counts[1] * la + counts[2] * lb) / (p * lm)
        gap = (lb - la) / (Decimal(3 * p) * lm)
        ok &= record("s=%d: level exponent %s, gamma - it = (log b - log a)/(3P log m)"
                     % (s, fmt(g_s, 12)),
                     abs((gamma(M_CHAIN, len(R1_CHAIN), len(R2_CHAIN)) - g_s) - gap)
                     < Decimal(10) ** -50)
    return ok


def check_construction():
    print("\nDirect construction test:")
    ok = True
    years = 3
    s = 1
    types = [position_type(i, s) for i in range(years)]
    a_set = build_set(M_CHAIN, years, s, R1_CHAIN, R2_CHAIN)
    expected = 1
    for i in range(years):
        expected *= (len(R1_CHAIN) if types[i] == 1
                     else len(R2_CHAIN) if types[i] == 2 else M_CHAIN)
    ok &= record("m=145, Y=3: |A_Y| = %d as predicted by the typing %s"
                 % (len(a_set), types),
                 len(a_set) == expected and len(set(a_set)) == len(a_set))
    hit = find_configuration(a_set, M_CHAIN, years)
    ok &= record("m=145, Y=3: no x, x+y, x+y^2 in A_Y with y != 0 (both signs)",
                 hit is None,
                 "searched |y| <= %d over %d elements of [0, %d)"
                 % (math.isqrt(M_CHAIN ** years - 1), len(a_set),
                    M_CHAIN ** years)
                 if hit is None else "witness x=%d y=%d" % hit)

    # Control: a non-square-free modulus breaks the digit argument.
    years4 = 4
    ctrl = build_set(4, years4, 1, [0], [0])
    hit4 = find_configuration(ctrl, 4, years4)
    ok &= record("control: m=4 (not square-free), R1=R2={0}, Y=4 DOES contain "
                 "a configuration", hit4 is not None,
                 "x=%d, y=%d: %d, %d, %d all in A_Y"
                 % (hit4[0], hit4[1], hit4[0], hit4[0] + hit4[1],
                    hit4[0] + hit4[1] ** 2) if hit4 else "none found")
    if hit4 is not None:
        x, y = hit4
        ok &= record("control witness really is a configuration",
                     y != 0 and x in set(ctrl) and (x + y) in set(ctrl)
                     and (x + y * y) in set(ctrl))
    return ok


def main():
    print("Nonlinear-Roth chain checker "
          "(Younis, arXiv:1908.06058, k = 2 construction)")
    ok = True
    ok &= check_dataset("Younis m=65", M_YOUNIS, R1_YOUNIS, R2_YOUNIS)
    ok &= check_dataset("chain m=145", M_CHAIN, R1_CHAIN, R2_CHAIN)
    ok &= check_exponents()
    ok &= check_controls()
    ok &= check_block_counts()
    ok &= check_construction()

    failed = [name for name, good, _ in RESULTS if not good]
    print("\n%d checks, %d failed." % (len(RESULTS), len(failed)))
    for name in failed:
        print("  FAILED: %s" % name)
    return 0 if (ok and not failed) else 1


if __name__ == "__main__":
    sys.exit(main())
