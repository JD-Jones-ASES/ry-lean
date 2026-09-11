# The mathematics

This document states the theorems proved in this repository and gives the proofs in
ordinary mathematical language. Every numbered Theorem, Lemma and Proposition below is proved in
Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. The comparisons with
[Y] (end of §1, the closing paragraphs of §3, and §7), the description of the untruncated rule in
§2–§3, and the per-period counts of §4 are exposition: true, but not what the Lean proves. Where
the Lean reaches a statement by a different route than the prose, §8 says so.

## 1. Statements

Throughout, `[N] = {1, …, N}`. A set `A ⊆ ℤ` is **configuration-free** if there are no
integers `x` and `y ≠ 0` with `x, x + y, x + y² ∈ A`. Following Younis [Y], "non-trivial"
is a condition on `y` alone: `y` may be negative, and the three integers need not be
distinct. In particular `y = 1` shows that a configuration-free set contains no two
consecutive integers. Write `D(N)` for the largest size of a configuration-free subset of
`[N]`.

For a modulus `m ≥ 2` and integers `a, b ≥ 1` put

    γ(m, a, b) = 1/2 + log a / (3 log m) + log b / (6 log m) = 1/2 + log(a²b) / (6 log m).

**Theorem A (Younis's two-set construction).** Let `m ≥ 2` be square-free and let
`R₁, R₂ ⊆ ℤ/m` be nonempty sets of residues such that

* (H1) if `r, r' ∈ R₁` and `r − r'` is a square modulo `m`, then `r = r'`;
* (H2) if `r, r' ∈ R₂` and `r − r' ≡ (c − c')²` for some `c, c' ∈ R₁`, then `r = r'`.

Then for every real `ρ < γ(m, |R₁|, |R₂|)` there is a constant `C > 0` such that for every
`N ≥ 1` the interval `[N]` contains a configuration-free set of size at least `C · N^ρ`.

**Theorem B (the exponent at `m = 145`).** The residue sets

    R₁ = {0, 48, 55, 62, 69, 76, 117, 124, 131, 138}                                 (10 residues)
    R₂ = {3, 12, 13, 16, 21, 24, 25, 34, 35, 38, 43, 46, 47, 56, 57, 60, 68, 69, 78, 79,
          82, 91, 100, 104, 113, 122, 123, 125, 126, 135, 136, 144}                   (32 residues)

satisfy (H1) and (H2) modulo `145 = 5 · 29`. Consequently, with

    γ = γ(145, 10, 32) = 1/2 + log 3200 / (6 log 145) = 0.770287920636…,

for every `ρ < γ` there is `C > 0` with `D(N) ≥ C · N^ρ` for all `N ≥ 1`, and

    liminf_{N→∞} log D(N) / log N ≥ γ.

**Theorem C (the exponent, located).** Younis's exponent is `γ₀ = γ(65, 7, 17) =
1/2 + log 833 / (6 log 65) = 0.768503822930…`. Then `γ₀ < γ`, and `0.7702 < γ < 0.77029`.

Context. Configuration-free subsets of `[N]` have size `o(N)` [BL], in fact at most
`N (log N)^(−c)` for some `c > 0` [PP1] (an earlier bound `N (log log N)^(−c)` is [PP2]). The
two-point analogue — sets with no two elements differing by a nonzero square — is the
Furstenberg–Sárközy problem [F, S]; its best published lower-bound exponent is `0.7527964558…`
[K], and the digit method used below is Ruzsa's [R]. Every square-difference-free set is
configuration-free (if `x, x + y, x + y²` all lie in `A` then `(x + y²) − x = y²`), so such
exponents transfer to this problem; they are below both `γ₀` and `γ`.

In Lean, sets are `Finset ℤ`; every subset of `[N]` is finite, so this is the same statement. In
Theorem C, `γ₀` is the number `γ(65, 7, 17)` and nothing more: that Younis's residue sets at
`m = 65` are admissible is taken from [Y] and re-checked in `scripts/check_chain.py`, not in Lean, so
Theorem C is a comparison of two explicitly defined real numbers.

Theorem A is Theorem 1.5 of [Y] with `k = 2`, `R₀ = ℤ/m`, and the periodic chain
`R₀, R₁, R₂, R₁, R₂, …`; its exponent formula (1.2) evaluates to `γ(m, |R₁|, |R₂|)`. Theorem
1.1 of [Y] is Theorem A at Younis's data `m = 65`, `|R₁| = 7`, `|R₂| = 17`. Theorem B is the
same theorem at new data, and Theorem C says that the new exponent is larger.

## 2. The construction

Fix `m`, `R₁`, `R₂` as in Theorem A and write `R₀ = ℤ/m` (every residue). Positions of
base-`m` digits are indexed by `i = 0, 1, 2, …`. Assign to each position a *type* in
`{0, 1, 2}`, meaning that the digit at that position must lie in `R₀`, `R₁`, or `R₂`:

    type(0) = 1;                                 (position 0 carries R₁)
    type(i) = 0            for odd i;            (odd positions are unrestricted)
    type(i) = 1            for even i ≥ 2 with v₂(i) odd;
    type(i) = 2            for even i ≥ 2 with v₂(i) even,

where `v₂(i)` is the exponent of `2` in `i`. This is Younis's rule (2.1) at `k = 2`: position
`i` carries `R_n` when `2ⁿ` exactly divides `i` (and `R₁` at `i = 0`), and the chain
`R₀, R₁, R₂, R₁, R₂, …` reads `R_n = R₁` for `n` odd and `R_n = R₂` for even `n ≥ 2`.

For `Y ≥ 0` let `A_Y` be the set of integers `Σ_{i<Y} d_i mⁱ` with `d_i ∈ R_{type(i)}` for
each `i < Y`, where residues are identified with their representatives in `{0, …, m − 1}`.
Then `A_Y ⊆ [0, mʸ)` and, since base-`m` expansion is injective,

    |A_Y| = ∏_{i<Y} |R_{type(i)}|.

The set is translated by `+1` to sit inside `[N]`; translation preserves the
configuration-free property because the pattern `x, x + y, x + y²` is translation-invariant.

## 3. Why `A_Y` is configuration-free

Two lemmas, then the argument.

**Lemma 1 (digit congruence).** For integers `u, v` and `ℓ ≥ 0` with `mˡ | (v − u)`,

    (v − u) / mˡ ≡ digit_ℓ(v) − digit_ℓ(u)   (mod m),

where `digit_ℓ(x) = ⌊x / mˡ⌋ mod m` is the base-`m` digit of `x` at position `ℓ`. (For a
positive divisor Lean's Euclidean division is the floor, so this is `(x / mˡ) % m` as written in
`RY/Defs.lean`, with the remainder in `{0, …, m − 1}`.)

*Proof.* Write `v = u + mˡ t`. Then `⌊v / mˡ⌋ = ⌊u / mˡ⌋ + t`, and reducing modulo `m`
gives `t ≡ digit_ℓ(v) − digit_ℓ(u)`. ∎

**Lemma 2 (square-free moduli).** If `m` is square-free and `m | z²`, then `m | z`.

*Proof.* Each prime `p | m` divides `z²`, hence `z`; the primes dividing `m` are distinct,
so their product `m` divides `z`. ∎

**Proposition 3 (avoidance).** Let `m ≥ 2` be square-free and let `(S_i)_{i<Y}` be sets of
digits — subsets of `{0, …, m − 1}`, residues identified with their representatives as in §2; this
is the hypothesis `hS` of the Lean statement — such that for every `ℓ` with `2ℓ < Y`:

    (E_ℓ)  if r, r' ∈ S_{2ℓ} and c, c' ∈ S_ℓ with r − r' ≡ (c − c')² (mod m), then r = r'.

Then the digit set `{Σ_{i<Y} d_i mⁱ : d_i ∈ S_i}` is configuration-free.

*Proof.* Suppose `u`, `v = u + y`, `w = u + y²` all lie in the set, with `y ≠ 0`. Let `ℓ`
be the largest integer with `mˡ | y` (it exists because `y ≠ 0`), and write `y = mˡ y'`
with `m ∤ y'`. Since `|y| < mʸ`, we have `ℓ < Y`. Also `m^{2ℓ} | y² = w − u` and
`(w − u) / m^{2ℓ} = y'²`.

If `2ℓ ≥ Y`, then `|w − u| < mʸ ≤ m^{2ℓ}` together with `m^{2ℓ} | (w − u)` forces `w = u`,
so `y = 0`, a contradiction.

If `2ℓ < Y`, apply Lemma 1 to `(u, v, ℓ)` and to `(u, w, 2ℓ)`:

    y'  ≡ digit_ℓ(v) − digit_ℓ(u),        y'² ≡ digit_{2ℓ}(w) − digit_{2ℓ}(u)   (mod m).

Hence `digit_{2ℓ}(w) − digit_{2ℓ}(u) ≡ (digit_ℓ(v) − digit_ℓ(u))²`, where the two digits
at position `2ℓ` lie in `S_{2ℓ}` and the two at position `ℓ` lie in `S_ℓ`. By `(E_ℓ)`,
`digit_{2ℓ}(w) = digit_{2ℓ}(u)`, so `m | y'²`, so `m | y'` by Lemma 2 — contradicting
`m ∤ y'`. ∎

Square-freeness enters exactly once, in the last step. It cannot be dropped: modulo `m = 4`
the sets `R₁ = R₂ = {0}` satisfy (H1) and (H2) (every nonzero difference is `0`), yet the
digit set for `Y = 4` contains `0, 8, 64` — a configuration with `y = 8`. The reason is that
`8 = 2 · 4` has `y' = 2` with `y'² = 4 ≡ 0 (mod 4)`, which Lemma 2 excludes for square-free
`m`.

**Which edges the rule needs.** For the type assignment of Section 2, the pairs
`(type(ℓ), type(2ℓ))` that occur are `(1, 1)` at `ℓ = 0`, `(0, 1)` for odd `ℓ`, `(1, 2)`
when `v₂(ℓ)` is odd, and `(2, 1)` when `v₂(ℓ)` is even and positive. The pair `(2, 2)`
never occurs. Condition `(E_ℓ)` for each pair reads:

* `(0, 1)`: a nonzero difference in `R₁` is not the square of any residue — this is (H1);
* `(1, 1)` and `(2, 1)`: a nonzero difference in `R₁` is not the square of a difference of
  `R₁`, resp. `R₂` — both follow from (H1), since these squares are squares;
* `(1, 2)`: a nonzero difference in `R₂` is not the square of a difference of `R₁` — (H2).

So (H1) and (H2) are exactly what Proposition 3 needs, and `A_Y` is configuration-free for
every `Y`. (The Lean development does not define this untruncated rule: `typ s` in `RY/Defs.lean` is
the depth-`s` rule of §4 for every `s`, and `blockSet_ruleSet_configFree` in `RY/Rule.lean` proves
configuration-freeness for that rule at every depth and every `Y`. The untruncated rule is used
here only to describe the construction; the argument applies to it verbatim, and §4 checks that
truncation introduces no new edge beyond `(1, 1)`.)

**Relation to the chain condition of [Y].** Younis requires, for every `n ≥ 0`,
`(R_{n+1} − R_{n+1}) ∩ (R_n − R_n)² ⊆ {0}` modulo `m`. For the chain `ℤ/m, R₁, R₂, R₁, R₂, …`
the condition at `n = 0` is (H1) (because `R₀ − R₀` is all of `ℤ/m`, its squares are all
squares), at `n = 1` it is (H2), and at `n = 2` it is the pair `(2, 1)` above, implied by
(H1); from `n = 3` on the conditions repeat. Thus (H1) and (H2) together are equivalent to
the full chain condition for this chain. One remark on the printed statement of Theorem 1.5:
rule (2.1) places `R₁` at position `0`, which is paired with itself (`2 · 0 = 0`), so the
proof also uses the edge `R₁ → R₁`; it is not among the printed conditions `R_n → R_{n+1}`,
but it follows from the `n = 0` condition when `R₀ = ℤ/m`, as above.

## 4. Counting: a periodic truncation

The exponent `γ` is the limiting density of `log |A_Y| / (Y log m)`. Rather than estimate
`|A_Y|` for arbitrary `Y` (which involves floor sums), the proof uses, for each depth
`s ≥ 0`, a *truncated* rule whose digit sets are periodic in the position, so that the count
over any whole number of periods is an exact power.

Define `type_s` like `type`, except that positions with `v₂(i) ≥ 2s + 1` receive type `1`
(that is, `R₁` instead of what the untruncated rule would give). Two facts:

* The truncated rule still satisfies the edge conditions of Proposition 3: the only new
  pairs `(type_s(ℓ), type_s(2ℓ))` are `(1, 1)`, already covered by (H1). Since `R₁` is
  placed only where the untruncated rule allowed `R₁` or `R₂`, nothing else changes.
* `type_s(i + P) = type_s(i)` with `P = 2^{2s+1}`: adding `P` does not change `v₂(i)` when
  `v₂(i) ≤ 2s`, and positions with `v₂ ≥ 2s + 1` all have type `1` (including `i = 0`).

Neither the periodicity nor the position counts below are formalized as such. The Lean proves the
product identity directly, by the phase recursion `∏_{i<2Q} |S_i| = |S_odd|^Q · ∏_{i<Q} |S'_i|`
(`prod_sizeAt_split`, `prod_sizeAt_pow`, `prod_sizeAt_odd_phase` in `RY/Rule.lean`), whose value over
one period is `prod_sizeAt_period`; `α_s` and `β_s` are the recursively defined `alpha`/`beta`, with
the closed forms below as `alpha_spec`/`beta_spec`.

Over one period `0 ≤ i < P`: `P/2` positions are odd (type `0`); for `1 ≤ v ≤ 2s` exactly
`P / 2^{v+1}` positions have `v₂(i) = v`; and position `0` has type `1`. Hence

    #type₀ = 4ˢ,     #type₁ = 1 + Σ_{v odd ≤ 2s−1} P/2^{v+1} = (2 · 4ˢ + 1) / 3,
    #type₂ = Σ_{v even, 2 ≤ v ≤ 2s} P/2^{v+1} = (4ˢ − 1) / 3,

and for `Y = qP` the truncated digit set `A^{(s)}_{qP}` has exactly `K_s^q` elements, where

    K_s = m^{4ˢ} · a^{(2·4ˢ+1)/3} · b^{(4ˢ−1)/3},     a = |R₁|,  b = |R₂|,

and `A^{(s)}_{qP} ⊆ [0, M_s^q)` with `M_s = m^P`. The block exponent is

    γ_s := log K_s / log M_s = 1/2 + (1/3 + 1/(6·4ˢ)) log_m a + (1/6 − 1/(6·4ˢ)) log_m b
         = γ(m, a, b) − (log b − log a) / (6 · 4ˢ · log m),

which tends to `γ(m, a, b)` as `s → ∞` (`blockCard_log_ratio` and `exists_depth_gt` in
`RY/Numeric.lean`).

## 5. From blocks to the theorems

**Lemma 4 (blocks to all `N`).** Let `M ≥ 2` and `K ≥ 1` be integers and `ρ ≤ log K / log M`
a real number. If for every `q ≥ 0` the interval `[M^q]` contains a configuration-free set
of size `K^q`, then there is `C > 0` such that for every `N ≥ 1` the interval `[N]` contains a
configuration-free set of size at least `C · N^ρ`; one may take `C = M^{−ρ}` when `ρ > 0` and
`C = 1` when `ρ ≤ 0`.

*Proof.* If `ρ ≤ 0` then `N^ρ ≤ 1` for `N ≥ 1`, and `{1}` is a configuration-free subset of `[N]`,
so `C = 1` works. Let `ρ > 0` and `q = ⌊log_M N⌋`, so `M^q ≤ N < M^{q+1}`. The set for `[M^q]`
lies in `[N]` and has size `K^q = M^{q · log K / log M} ≥ M^{qρ} = (M^{q+1})^ρ / M^ρ > N^ρ / M^ρ`.
(The step `(M^{q+1})^ρ > N^ρ` is where `ρ > 0` is used.) ∎

In Lean the bound is first proved for the counting function, `C · N^ρ ≤ D(N)` (`younis_D`); the
set required by Theorem A is then recovered from the fact that the supremum defining `D(N)` is
attained (`exists_configFree_card_eq_D`, from `Nat.sSup_mem`: the competitor set contains `0` and
is bounded by `N`). Monotonicity of `D` (`D_mono`) is what places the set built for `[M^q]` inside
`[N]`.

*Proof of Theorem A.* Given `ρ < γ(m, a, b)`, choose `s` so large that `γ_s > ρ` (possible
because `4ˢ` is unbounded). Apply Lemma 4 with `M = M_s`, `K = K_s`, using the translated
truncated digit sets `A^{(s)}_{qP} + 1 ⊆ [M_s^q]`, which are configuration-free by
Proposition 3 and Section 4. The constant is `C = M_s^{−ρ}` for `ρ > 0` and `C = 1` for `ρ ≤ 0`. ∎

*Proof of Theorem B.* Verify (H1) and (H2) for the two residue sets modulo `145` — finite
checks — and that `145 = 5 · 29` is square-free. In Lean the hypotheses are not decided in their
quantified form (the direct check of (H2) is `32 · 32 · 10 · 10 = 102,400` cases and does not
terminate); each is reduced to a disjointness of two explicit finsets — the nonzero differences of
one set against the squares available to the other — which `decide` settles under raised
`maxRecDepth`/`maxHeartbeats`, and a bridging lemma (`sqDiffFree_of_disjoint`,
`avoidSqDiffs_of_disjoint` in `RY/Instance.lean`) returns the quantified form. The pointwise
statement is Theorem A. For the liminf: given `ρ < γ`, the pointwise bound gives
`log D(N) / log N ≥ ρ + log C / log N` for `N ≥ 2`, whose right side tends to `ρ`; hence
`liminf ≥ ρ` for every `ρ < γ`, so `liminf ≥ γ`. (The sequence is bounded: `1 ≤ D(N) ≤ N`
for `N ≥ 1`, so `0 ≤ log D(N)/log N ≤ 1` for `N ≥ 2`, and the liminf is the genuine one.) ∎

## 6. Locating the exponent

Since `γ(m, a, b) − 1/2 = log(a²b) / (6 log m)`, each comparison reduces to a comparison of
two logarithm ratios, each of which is bracketed by a rational number `p/q` through a
comparison of integer powers: `log_m t > p/q` if and only if `t^q > m^p`.

* `γ₀ < γ`: `833^13 < 65^21` gives `log_65 833 < 21/13`, and `3200^13 > 145^21` gives
  `log_145 3200 > 21/13`.
* `0.7702 < γ`: `3200^37 > 145^60` gives `log_145 3200 > 60/37`, so
  `γ > 1/2 + 10/37 = 0.77027…`.
* `γ < 0.77029`: `3200^230 < 145^373` gives `log_145 3200 < 373/230`, so
  `γ < 1/2 + 373/1380 = 0.770289…`.

The integer inequalities are checked exactly; the largest numbers, `3200^230` and `145^373`, have
807 decimal digits each. No floating-point or transcendental evaluation is involved. In Lean three
of the four comparisons are `norm_num` evaluations; the last, `3200^230 < 145^373`, stalls
`norm_num` and is discharged by `decide +kernel`, that is, by direct kernel evaluation of the two
integers (`log3200_lt` in `RY/Numeric.lean`); this introduces no axiom.

## 7. How the data was found, and what is not claimed

The residue sets at `m = 145` were found by computer search over square-free moduli: for
each candidate `m`, a maximum square-difference-free set `R₁` (a maximum clique in the graph
on `ℤ/m` whose non-edges are square differences, the same graph searched by Lewko [L] and by
Beigel and Gasarch [BG] for the Furstenberg–Sárközy problem), then a largest `R₂`
compatible with it under (H2). At `m = 145` the largest square-difference-free set has `10`
elements and the largest compatible `R₂` found has `32`. Younis's data at `m = 65` is
optimal at its own modulus in the same sense. These optimality statements are search
results, not theorems of this repository, and the theorems do not depend on them: Theorem B
asserts a lower bound, and any admissible pair gives one.

Nothing is claimed about upper bounds, about the optimality of the exponent `γ`, or about
other polynomial configurations.

## 8. The Lean development

* `Challenge.lean` states Theorems A, B and C using only Mathlib: `younis_period_two`
  (Theorem A), `record_pointwise` and `record_liminf` (Theorem B), `younis_lt_record` and
  `record_exponent_bounds` (Theorem C). Its five declarations are intentional `sorry`
  placeholders: it is the statement surface to audit, with no proofs.
* `Solution.lean` does not import `Challenge.lean`; it proves the same five statements from the
  library `RY`.
* `RY/Defs.lean` — the five Challenge definitions verbatim, plus `digit`, `blockSet`,
  `digitsOf`/`allDigits`, the rule (`phase`, `typ`, `ruleSet`) and its sizes (`sizeAt`, `period`,
  `alpha`, `beta`, `blockCard`).
* `RY/Digits.lean` — Lemma 1 (`cast_ediv_eq_digit_sub`), the shape of `blockSet`
  (`blockSet_nonneg`, `blockSet_lt`, `digit_mem`, `blockSet_card`), the maximal power of `m`
  dividing a nonzero integer (`exists_maximal_pow_dvd`), and translation invariance of
  configuration-freeness.
* `RY/Avoid.lean` — Proposition 3 (`blockSet_configFree`).
* `RY/Rule.lean` — the truncated rule, its edge validity (`typ_edge`, `ruleSet_edge`),
  configuration-freeness of the construction (`blockSet_ruleSet_configFree`), and the block count
  over one and over `q` periods (`prod_sizeAt_period`, `prod_sizeAt_pow`).
* `RY/Asymptotics.lean` — `D` and its basic properties (`D_mono`, `D_le`, `one_le_D`,
  `exists_configFree_card_eq_D`), the `+1` translation into `{1, …, N}`, the block bound
  `D(M_s^q) ≥ K_s^q` (`blockCard_le_D`), Lemma 4 (`D_ge_of_blocks`) and the liminf passage
  (`liminf_ge_of_pointwise`).
* `RY/Numeric.lean` — the four integer power comparisons and Theorem C, the identity for
  `log K_s / log M_s` (`blockCard_log_ratio`) and the choice of depth (`exists_depth_gt`).
* `RY/Instance.lean` — the two finsets at `m = 145`, `Squarefree 145`, and (H1), (H2) by
  `decide` on the finset reformulations with the bridging lemmas.
* `RY/Main.lean` — the assembly of the five statements from the above.
* `Test/Axioms.lean` audits every constant in the `NonlinearRoth` namespace and every private
  declaration of an `RY.*` module for axioms; only `propext`, `Classical.choice` and `Quot.sound`
  occur.
* `scripts/check_chain.py` re-checks, in Python (standard library only), the finite data at both
  `m = 145` and Younis's `m = 65`, the four integer power comparisons, the per-period type counts
  and admissible position edges of the truncated rule for depths `0`–`3`, a direct enumeration of
  `A_Y` at `m = 145`, `Y = 3` with an exhaustive configuration search (this depth reaches no
  type-`2` position, so `R₂` enters only through the (H2) check), and three controls that must
  fail, including the `m = 4` example of §3.

## References

[Y] K. Younis, *Lower bounds in the polynomial Szemerédi theorem*, arXiv:1908.06058 (2019).
[R] I. Z. Ruzsa, *Difference sets without squares*, Period. Math. Hungar. 15 (1984), 205–209.
[BG] R. Beigel and W. Gasarch, *Square-difference-free sets of size Ω(n^0.7334…)*, arXiv:0804.4892 (2008).
[L] M. Lewko, *An improved lower bound related to the Furstenberg–Sárközy theorem*, Electron. J. Combin. 22 (2015), #P1.32.
[L2] M. Lewko, *An improved non-linear Roth-type theorem in finite fields*, arXiv:2604.27501 (2026).
[BL] V. Bergelson and A. Leibman, *Polynomial extensions of van der Waerden's and Szemerédi's theorems*, J. Amer. Math. Soc. 9 (1996), 725–753.
[PP1] S. Peluse and S. Prendiville, *A polylogarithmic bound in the nonlinear Roth theorem*, Int. Math. Res. Not. IMRN 2022, no. 8, 5658–5684.
[PP2] S. Peluse and S. Prendiville, *Quantitative bounds in the nonlinear Roth theorem*, Invent. Math. 238 (2024), 865–903.
[K] D. Krachun, *Square-difference-free sets beyond the three-quarter barrier*, arXiv:2608.01325 (2026).
[S] A. Sárközy, *On difference sets of sequences of integers. I*, Acta Math. Acad. Sci. Hungar. 31 (1978), 125–149.
[F] H. Furstenberg, *Ergodic behavior of diagonal measures and a theorem of Szemerédi on arithmetic progressions*, J. Analyse Math. 31 (1977), 204–256.
