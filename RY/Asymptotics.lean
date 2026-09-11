import RY.Rule

/-!
# From blocks to all `N`

`D N` is a supremum over a set of naturals bounded by `N`, so it is attained, monotone and
at most `N`. The construction gives `D (M ^ q) ≥ K ^ q` for `M = m ^ (2^(2s+1))` and
`K = K_s`; the block lemma turns that into `D N ≥ M ^ (-ρ) · N ^ ρ` for every `N ≥ 1` and
every `ρ ≤ log K / log M`, by taking `q = Nat.log M N`, so that `M ^ q ≤ N < M ^ (q+1)`.
The liminf statement then follows by letting `ρ` increase to the exponent, with
`Filter.le_liminf_of_le`; its `IsCoboundedUnder (· ≥ ·)` side condition is paid by
`D N ≤ N`, which gives `log (D N) / log N ≤ 1` eventually.
-/

namespace NonlinearRoth

/-! ## The counting function -/

/-- The competitor set of `D N` is bounded above by `N`. -/
theorem D_bddAbove (N : ℕ) :
    BddAbove {k : ℕ | ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree A ∧ A.card = k} := by
  sorry

/-- The competitor set of `D N` is nonempty: `∅` is configuration-free. -/
theorem D_set_nonempty (N : ℕ) :
    {k : ℕ | ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree A ∧ A.card = k}.Nonempty := by
  sorry

/-- Every configuration-free subset of `{1, …, N}` is counted by `D N`. -/
theorem le_D {N : ℕ} {A : Finset ℤ} (hA : A ⊆ Finset.Icc 1 (N : ℤ)) (hcf : ConfigFree A) :
    A.card ≤ D N := by
  sorry

/-- The supremum is attained. -/
theorem exists_configFree_card_eq_D (N : ℕ) :
    ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree A ∧ A.card = D N := by
  sorry

/-- `D` is monotone. -/
theorem D_mono : Monotone D := by
  sorry

/-- `D N ≤ N`. Load-bearing: this is the coboundedness witness of the liminf passage. -/
theorem D_le (N : ℕ) : D N ≤ N := by
  sorry

/-- `D N ≥ 1` for `N ≥ 1`: the singleton `{1}` is configuration-free. -/
theorem one_le_D (N : ℕ) (hN : 1 ≤ N) : 1 ≤ D N := by
  sorry

/-! ## The construction, placed inside `{1, …, N}` -/

/-- The block set, shifted by `1`, sits inside `{1, …, m ^ Y}`. -/
theorem blockSet_shift_subset (m : ℕ) (hm : 0 < m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) :
    (blockSet m S Y).image (fun x => x + 1) ⊆ Finset.Icc 1 ((m ^ Y : ℕ) : ℤ) := by
  sorry

/-- **The block bound.** `D (M_s ^ q) ≥ K_s ^ q`. -/
theorem blockCard_le_D {m : ℕ} (hm : 2 ≤ m) (hsf : Squarefree m) (R₁ R₂ : Finset (ZMod m))
    (hR₁ : ∀ a ∈ R₁, ∀ b ∈ R₁, ∀ d : ZMod m, a - b = d ^ 2 → a = b)
    (hR₂ : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b)
    (s q : ℕ) :
    blockCard m R₁.card R₂.card s ^ q ≤ D ((m ^ period s) ^ q) := by
  have hm0 : 0 < m := by omega
  have hsub : (blockSet m (ruleSet R₁ R₂ s) (q * period s)).image (fun x => x + 1)
      ⊆ Finset.Icc 1 ((m ^ (q * period s) : ℕ) : ℤ) :=
    blockSet_shift_subset m hm0 _ (fun i => ruleSet_bounds hm0 R₁ R₂ s i) _
  have hcf : ConfigFree
      ((blockSet m (ruleSet R₁ R₂ s) (q * period s)).image (fun x => x + 1)) :=
    configFree_image_add _ 1 (blockSet_ruleSet_configFree hm hsf R₁ R₂ hR₁ hR₂ s _)
  have hle := le_D hsub hcf
  rw [card_image_add, blockSet_ruleSet_card hm0 R₁ R₂ s _, prod_sizeAt_mul_period] at hle
  have hpow : (m ^ period s) ^ q = m ^ (q * period s) := by rw [← pow_mul, mul_comm]
  rw [hpow]
  exact hle

/-! ## The block lemma and the liminf -/

/-- **The block lemma.** If `D (M ^ q) ≥ K ^ q` for every `q` and `ρ ≤ log K / log M`, then
`D N ≥ C N ^ ρ` for every `N ≥ 1`, with `C = M ^ (-ρ)` (any positive `C` will do for
`ρ < 0`, where the bound is trivial). -/
theorem D_ge_of_blocks (M K : ℕ) (hM : 2 ≤ M) (hK : 1 ≤ K)
    (hDq : ∀ q : ℕ, K ^ q ≤ D (M ^ q)) (ρ : ℝ)
    (hρ : ρ ≤ Real.log (K : ℝ) / Real.log (M : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → C * (N : ℝ) ^ ρ ≤ (D N : ℝ) := by
  sorry

/-- **The liminf from the pointwise bounds.** -/
theorem liminf_ge_of_pointwise (γ : ℝ)
    (h : ∀ ρ : ℝ, ρ < γ → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → C * (N : ℝ) ^ ρ ≤ (D N : ℝ)) :
    γ ≤ Filter.liminf (fun N : ℕ => Real.log (D N) / Real.log N) Filter.atTop := by
  sorry

end NonlinearRoth
