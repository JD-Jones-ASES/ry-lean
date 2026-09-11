import RY.Main

/-!
# Large sets of integers with no configuration `{x, x + y, x + y²}`

The five statements of `Challenge.lean`, restated verbatim and discharged from `RY.Main`.
The definitions they mention — `ConfigFree`, `exponent`, `younisExponent`,
`recordExponent`, `D` — are the ones of `RY.Defs`, again verbatim.

The two residue sets at `m = 145` are `NonlinearRoth.R145₁` and `NonlinearRoth.R145₂` of
`RY.Instance`:

  `R₁ = {0, 48, 55, 62, 69, 76, 117, 124, 131, 138}`,

  `R₂ = {3, 12, 13, 16, 21, 24, 25, 34, 35, 38, 43, 46, 47, 56, 57, 60, 68, 69, 78, 79,
         82, 91, 100, 104, 113, 122, 123, 125, 126, 135, 136, 144}`.
-/

namespace NonlinearRoth

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
  exact younis_period_two_internal m hm hsf R₁ R₂ h₁ h₂ hR₁ hR₂ ρ hρ

/-- **The lower bound at `m = 145`.** For every `ρ < 0.77028…` there is `C > 0` such that
every `{1, …, N}` contains a configuration-free set of size at least `C N^ρ`. -/
theorem record_pointwise (ρ : ℝ) (hρ : ρ < recordExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ A : Finset ℤ,
      A ⊆ Finset.Icc 1 N ∧ ConfigFree A ∧ C * (N : ℝ) ^ ρ ≤ A.card := by
  exact record_pointwise_internal ρ hρ

/-- **The same bound in liminf form:** `liminf log D(N) / log N ≥ 0.77028…`. -/
theorem record_liminf :
    recordExponent ≤ Filter.liminf (fun N : ℕ => Real.log (D N) / Real.log N) Filter.atTop := by
  exact record_liminf_internal

/-- The exponent at `m = 145` exceeds Younis's exponent at `m = 65`. -/
theorem younis_lt_record : younisExponent < recordExponent := by
  exact younis_lt_record_internal

/-- Decimal bounds for the exponent at `m = 145`. -/
theorem record_exponent_bounds : (0.7702 : ℝ) < recordExponent ∧ recordExponent < 0.77029 := by
  exact record_exponent_bounds_internal

end NonlinearRoth
