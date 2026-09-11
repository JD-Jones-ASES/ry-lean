import RY.Asymptotics
import RY.Numeric
import RY.Instance

/-!
# The five targets

Everything is glue at this point.

* `younis_D` picks a depth `s` with `log K_s / log M_s > ρ` (`RY.Numeric`) and feeds the
  block bound `D (M_s ^ q) ≥ K_s ^ q` (`RY.Asymptotics`) to the block lemma.
* `younis_period_two_internal` replaces `D N` by a set realising it.
* `record_pointwise_internal` and `record_liminf_internal` instantiate at `m = 145` with
  the finsets of `RY.Instance`.
* the two numerical targets are `RY.Numeric` verbatim.

The Challenge's names are left free: `Solution.lean` declares them, with these as proofs.
-/

namespace NonlinearRoth

/-- **Younis's theorem, in terms of `D`.** -/
theorem younis_D (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (R₁ R₂ : Finset (ZMod m)) (h₁ : R₁.Nonempty) (h₂ : R₂.Nonempty)
    (hR₁ : ∀ a ∈ R₁, ∀ b ∈ R₁, ∀ d : ZMod m, a - b = d ^ 2 → a = b)
    (hR₂ : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b)
    (ρ : ℝ) (hρ : ρ < exponent m R₁.card R₂.card) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → C * (N : ℝ) ^ ρ ≤ (D N : ℝ) := by
  have ha : 1 ≤ R₁.card := Finset.card_pos.mpr h₁
  have hb : 1 ≤ R₂.card := Finset.card_pos.mpr h₂
  obtain ⟨s, hs⟩ := exists_depth_gt m R₁.card R₂.card hm ha hb ρ hρ
  exact D_ge_of_blocks (m ^ period s) (blockCard m R₁.card R₂.card s)
    (two_le_pow_period m s hm)
    (one_le_blockCard m R₁.card R₂.card s (by omega) ha hb)
    (fun q => blockCard_le_D hm hsf R₁ R₂ hR₁ hR₂ s q) ρ hs

/-- **Younis's theorem for the two-set construction.** -/
theorem younis_period_two_internal (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m)
    (R₁ R₂ : Finset (ZMod m)) (h₁ : R₁.Nonempty) (h₂ : R₂.Nonempty)
    (hR₁ : ∀ a ∈ R₁, ∀ b ∈ R₁, ∀ d : ZMod m, a - b = d ^ 2 → a = b)
    (hR₂ : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b)
    (ρ : ℝ) (hρ : ρ < exponent m R₁.card R₂.card) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ A : Finset ℤ,
      A ⊆ Finset.Icc 1 N ∧ ConfigFree A ∧ C * (N : ℝ) ^ ρ ≤ A.card := by
  obtain ⟨C, hC, hD⟩ := younis_D m hm hsf R₁ R₂ h₁ h₂ hR₁ hR₂ ρ hρ
  refine ⟨C, hC, fun N hN => ?_⟩
  obtain ⟨A, hAsub, hAcf, hAcard⟩ := exists_configFree_card_eq_D N
  exact ⟨A, hAsub, hAcf, by rw [hAcard]; exact hD N hN⟩

/-- `recordExponent` is the exponent of the data at `m = 145`. -/
theorem exponent_R145 : exponent 145 R145₁.card R145₂.card = recordExponent := by
  rw [R145₁_card, R145₂_card, recordExponent]

/-- **The lower bound at `m = 145`.** -/
theorem record_pointwise_internal (ρ : ℝ) (hρ : ρ < recordExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ A : Finset ℤ,
      A ⊆ Finset.Icc 1 N ∧ ConfigFree A ∧ C * (N : ℝ) ^ ρ ≤ A.card :=
  younis_period_two_internal 145 (by norm_num) squarefree_145 R145₁ R145₂
    R145₁_nonempty R145₂_nonempty hR145₁ hR145₂ ρ (by rw [exponent_R145]; exact hρ)

/-- **The same bound in liminf form.** -/
theorem record_liminf_internal :
    recordExponent ≤ Filter.liminf (fun N : ℕ => Real.log (D N) / Real.log N) Filter.atTop := by
  refine liminf_ge_of_pointwise recordExponent fun ρ hρ => ?_
  exact younis_D 145 (by norm_num) squarefree_145 R145₁ R145₂ R145₁_nonempty R145₂_nonempty
    hR145₁ hR145₂ ρ (by rw [exponent_R145]; exact hρ)

/-- The exponent at `m = 145` exceeds Younis's exponent at `m = 65`. -/
theorem younis_lt_record_internal : younisExponent < recordExponent :=
  younisExponent_lt_recordExponent

/-- Decimal bounds for the exponent at `m = 145`. -/
theorem record_exponent_bounds_internal :
    (0.7702 : ℝ) < recordExponent ∧ recordExponent < 0.77029 :=
  ⟨recordExponent_lower, recordExponent_upper⟩

end NonlinearRoth
