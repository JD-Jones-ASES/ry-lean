import Mathlib

/-!
# Large sets of integers with no configuration `{x, x + y, x + y²}`

A set `A` of integers is *configuration-free* if it contains no three integers of the
form `x, x + y, x + y²` with `y ≠ 0`. (For `y = 1` the three integers are `x, x + 1, x + 1`,
so a configuration-free set contains no two consecutive integers; for `y = -1` they are
`x, x - 1, x + 1`.) This is the model case, with polynomials `y` and `y²`, of the polynomial
Szemerédi theorem: Bergelson and Leibman proved that a configuration-free subset of
`{1, …, N}` has size `o(N)`, and Peluse and Prendiville proved the quantitative bound
`O(N (log N)^(-c))`. The question here is the other direction: how large can a
configuration-free subset of `{1, …, N}` be?

## The construction

Fix a square-free modulus `m ≥ 2` and two nonempty sets of residues `R₁, R₂ ⊆ ℤ/m` such that

* no two distinct elements of `R₁` differ by a square modulo `m`
  (`R₁` is square-difference-free), and
* no two distinct elements of `R₂` differ by the square of a difference of two
  elements of `R₁`.

Younis (2019) showed that from such data one obtains, for every `ε > 0`, configuration-free
subsets of `{1, …, N}` of size at least `c(ε) N^(γ - ε)`, where

  `γ = 1/2 + log |R₁| / (3 log m) + log |R₂| / (6 log m)`.

The elements of the set are the integers whose base-`m` digits are constrained position by
position: an arbitrary digit at each odd position, a digit from `R₁` at position `0` and at
the even positions whose `2`-adic valuation is odd, and a digit from `R₂` at the even
positions whose `2`-adic valuation is even. Younis exhibited such data at `m = 65` with
`|R₁| = 7` and `|R₂| = 17`, giving the exponent `0.7685…`.

## What is proved here

* `younis_period_two` is Younis's theorem for this two-set construction, for every
  square-free modulus `m ≥ 2` and every admissible pair `R₁, R₂`, with the exponent above.
* `record_pointwise` and `record_liminf` instantiate it at `m = 145 = 5 · 29`, with
  `|R₁| = 10` and `|R₂| = 32`; the exponent is `γ = 0.77028…`.
* `younis_lt_record` and `record_exponent_bounds` locate that exponent: it exceeds Younis's
  exponent `0.76850…`, and `0.7702 < γ < 0.77029`.

The two residue sets at `m = 145` are

  `R₁ = {0, 48, 55, 62, 69, 76, 117, 124, 131, 138}`,

  `R₂ = {3, 12, 13, 16, 21, 24, 25, 34, 35, 38, 43, 46, 47, 56, 57, 60, 68, 69, 78, 79,
         82, 91, 100, 104, 113, 122, 123, 125, 126, 135, 136, 144}`.

They appear only in the Solution: the statements below fix the exponent numerically and
assert existence, so that the Challenge is independent of the particular witnesses.

## Conventions

Sets are `Finset ℤ`; the ambient interval is `Finset.Icc 1 N` for a natural number `N`.
Logarithms are natural logarithms (`Real.log`); the counting function `D N` is the largest
size of a configuration-free subset of `{1, …, N}`. The base-`m` digit at position `i` of an
integer `x` is `(x / m ^ i) % m` with Lean's Euclidean division; the digit sets are
`Finset (ZMod m)`.

This Mathlib-only file intentionally contains `sorry` placeholders. The corresponding
declarations are proved in `Solution.lean`, which does not import this file.
-/

namespace NonlinearRoth

/-- `A` contains no configuration `{x, x + y, x + y²}` with `y ≠ 0`. -/
def ConfigFree (A : Finset ℤ) : Prop :=
  ∀ x y : ℤ, y ≠ 0 → x ∈ A → x + y ∈ A → x + y ^ 2 ∈ A → False

/-- The exponent attached to a modulus `m` and digit sets of sizes `a` and `b`:
`1/2 + log a / (3 log m) + log b / (6 log m)`. -/
noncomputable def exponent (m a b : ℕ) : ℝ :=
  1 / 2 + Real.log a / (3 * Real.log m) + Real.log b / (6 * Real.log m)

/-- Younis's exponent, from the data `m = 65`, `|R₁| = 7`, `|R₂| = 17`: `0.76850…`. -/
noncomputable def younisExponent : ℝ := exponent 65 7 17

/-- The exponent of the construction at `m = 145`, `|R₁| = 10`, `|R₂| = 32`: `0.77028…`. -/
noncomputable def recordExponent : ℝ := exponent 145 10 32

/-- The largest size of a configuration-free subset of `{1, …, N}`. -/
noncomputable def D (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 N ∧ ConfigFree A ∧ A.card = k}

/-- **Younis's theorem for the two-set construction.** Let `m ≥ 2` be square-free and let
`R₁, R₂ ⊆ ℤ/m` be nonempty, with `R₁` square-difference-free and with no two distinct
elements of `R₂` differing by the square of a difference of two elements of `R₁`. Then for
every `ρ` below the exponent `1/2 + log |R₁| / (3 log m) + log |R₂| / (6 log m)` there is a
constant `C > 0` such that every interval `{1, …, N}` contains a configuration-free set of
size at least `C N^ρ`. -/
theorem younis_period_two (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (R₁ R₂ : Finset (ZMod m)) (h₁ : R₁.Nonempty) (h₂ : R₂.Nonempty)
    (hR₁ : ∀ a ∈ R₁, ∀ b ∈ R₁, ∀ d : ZMod m, a - b = d ^ 2 → a = b)
    (hR₂ : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b)
    (ρ : ℝ) (hρ : ρ < exponent m R₁.card R₂.card) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ A : Finset ℤ,
      A ⊆ Finset.Icc 1 N ∧ ConfigFree A ∧ C * (N : ℝ) ^ ρ ≤ A.card := by
  sorry

/-- **The lower bound at `m = 145`.** For every `ρ < 0.77028…` there is `C > 0` such that
every `{1, …, N}` contains a configuration-free set of size at least `C N^ρ`. -/
theorem record_pointwise (ρ : ℝ) (hρ : ρ < recordExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ A : Finset ℤ,
      A ⊆ Finset.Icc 1 N ∧ ConfigFree A ∧ C * (N : ℝ) ^ ρ ≤ A.card := by
  sorry

/-- **The same bound in liminf form:** `liminf log D(N) / log N ≥ 0.77028…`. -/
theorem record_liminf :
    recordExponent ≤ Filter.liminf (fun N : ℕ => Real.log (D N) / Real.log N) Filter.atTop := by
  sorry

/-- The exponent at `m = 145` exceeds Younis's exponent at `m = 65`. -/
theorem younis_lt_record : younisExponent < recordExponent := by
  sorry

/-- Decimal bounds for the exponent at `m = 145`. -/
theorem record_exponent_bounds : (0.7702 : ℝ) < recordExponent ∧ recordExponent < 0.77029 := by
  sorry

end NonlinearRoth
