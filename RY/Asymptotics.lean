import RY.Rule

/-!
# From blocks to all `N`

`D N` is a supremum over a set of naturals bounded by `N`, so it is attained, monotone and
at most `N`. The construction gives `D (M ^ q) ≥ K ^ q` for `M = m ^ (2^(2s+1))` and
`K = K_s`; the block lemma turns that into `D N ≥ C · N ^ ρ` (with `C = M ^ (-ρ)` for `ρ > 0` and
`C = 1` for `ρ ≤ 0`) for every `N ≥ 1` and
every `ρ ≤ log K / log M`, by taking `q = Nat.log M N`, so that `M ^ q ≤ N < M ^ (q+1)`.
The liminf statement then follows by letting `ρ` increase to the exponent, with
`Filter.le_liminf_of_le`; its `IsCoboundedUnder (· ≥ ·)` side condition is paid by
`D N ≤ N`, which gives `log (D N) / log N ≤ 1` eventually.
-/

namespace NonlinearRoth

/-! ## The counting function -/

/-- The interval `{1, …, N}` has `N` elements. -/
private theorem card_Icc_one_natCast (N : ℕ) : (Finset.Icc (1 : ℤ) (N : ℤ)).card = N := by
  rw [Int.card_Icc]
  omega

/-- The competitor set of `D N` is bounded above by `N`. -/
theorem D_bddAbove (N : ℕ) :
    BddAbove {k : ℕ | ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree A ∧ A.card = k} := by
  refine ⟨N, ?_⟩
  rintro k ⟨A, hA, -, rfl⟩
  exact le_trans (Finset.card_le_card hA) (le_of_eq (card_Icc_one_natCast N))

/-- The competitor set of `D N` is nonempty: `∅` is configuration-free. -/
theorem D_set_nonempty (N : ℕ) :
    {k : ℕ | ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree A ∧ A.card = k}.Nonempty := by
  refine ⟨0, ?_⟩
  show ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree A ∧ A.card = 0
  refine ⟨∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
  intro x y _ hx _ _
  simp at hx

/-- Every configuration-free subset of `{1, …, N}` is counted by `D N`. -/
theorem le_D {N : ℕ} {A : Finset ℤ} (hA : A ⊆ Finset.Icc 1 (N : ℤ)) (hcf : ConfigFree A) :
    A.card ≤ D N := by
  show A.card ≤ sSup {k : ℕ | ∃ B : Finset ℤ, B ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree B ∧ B.card = k}
  exact le_csSup (D_bddAbove N) ⟨A, hA, hcf, rfl⟩

/-- The supremum is attained. -/
theorem exists_configFree_card_eq_D (N : ℕ) :
    ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 (N : ℤ) ∧ ConfigFree A ∧ A.card = D N :=
  Nat.sSup_mem (D_set_nonempty N) (D_bddAbove N)

/-- `D` is monotone. -/
theorem D_mono : Monotone D := by
  intro a b hab
  obtain ⟨A, hA, hcf, hcard⟩ := exists_configFree_card_eq_D a
  rw [← hcard]
  refine le_D (hA.trans (Finset.Icc_subset_Icc_right ?_)) hcf
  exact_mod_cast hab

/-- `D N ≤ N`. Load-bearing: this is the coboundedness witness of the liminf passage. -/
theorem D_le (N : ℕ) : D N ≤ N := by
  obtain ⟨A, hA, -, hcard⟩ := exists_configFree_card_eq_D N
  rw [← hcard]
  exact le_trans (Finset.card_le_card hA) (le_of_eq (card_Icc_one_natCast N))

/-- `D N ≥ 1` for `N ≥ 1`: the singleton `{1}` is configuration-free. -/
theorem one_le_D (N : ℕ) (hN : 1 ≤ N) : 1 ≤ D N := by
  have hsub : ({1} : Finset ℤ) ⊆ Finset.Icc 1 (N : ℤ) := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [Finset.mem_Icc]
    refine ⟨le_rfl, ?_⟩
    exact_mod_cast hN
  have hcf : ConfigFree ({1} : Finset ℤ) := by
    intro x y hy hx hxy _
    rw [Finset.mem_singleton] at hx hxy
    omega
  have h := le_D hsub hcf
  simpa using h

/-! ## The construction, placed inside `{1, …, N}` -/

/-- The block set, shifted by `1`, sits inside `{1, …, m ^ Y}`. -/
theorem blockSet_shift_subset (m : ℕ) (_hm : 0 < m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) :
    (blockSet m S Y).image (fun x => x + 1) ⊆ Finset.Icc 1 ((m ^ Y : ℕ) : ℤ) := by
  intro z hz
  rw [Finset.mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  have h0 : 0 ≤ x := blockSet_nonneg m S (fun i d hd => (hS i d hd).1) Y x hx
  have h1 : x < (m : ℤ) ^ Y := blockSet_lt m S hS Y x hx
  have hcast : ((m ^ Y : ℕ) : ℤ) = (m : ℤ) ^ Y := by push_cast; ring
  rw [Finset.mem_Icc, hcast]
  exact ⟨by linarith, Int.add_one_le_iff.mpr h1⟩

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

/-- `x ^ (n · ρ) = (x ^ ρ) ^ n` for a natural exponent `n`. -/
private theorem rpow_natCast_mul (x : ℝ) (hx : 0 ≤ x) (ρ : ℝ) (n : ℕ) :
    x ^ ((n : ℝ) * ρ) = (x ^ ρ) ^ n := by
  rw [mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

/-- **The block lemma.** If `D (M ^ q) ≥ K ^ q` for every `q` and `ρ ≤ log K / log M`, then
`D N ≥ C N ^ ρ` for every `N ≥ 1`, with `C = M ^ (-ρ)` (when `ρ ≤ 0` the proof takes `C = 1`, since then
`N ^ ρ ≤ 1 ≤ D N` for `N ≥ 1`). -/
theorem D_ge_of_blocks (M K : ℕ) (hM : 2 ≤ M) (hK : 1 ≤ K)
    (hDq : ∀ q : ℕ, K ^ q ≤ D (M ^ q)) (ρ : ℝ)
    (hρ : ρ ≤ Real.log (K : ℝ) / Real.log (M : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → C * (N : ℝ) ^ ρ ≤ (D N : ℝ) := by
  have hM1 : 1 < M := by omega
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM1R : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  by_cases hρ0 : ρ ≤ 0
  · -- `N ^ ρ ≤ 1 ≤ D N`
    refine ⟨1, one_pos, fun N hN => ?_⟩
    have h1 : ((N : ℝ)) ^ ρ ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ hρ0
      exact_mod_cast hN
    have h2 : (1 : ℝ) ≤ (D N : ℝ) := by exact_mod_cast one_le_D N hN
    calc (1 : ℝ) * (N : ℝ) ^ ρ = (N : ℝ) ^ ρ := one_mul _
      _ ≤ 1 := h1
      _ ≤ (D N : ℝ) := h2
  · replace hρ0 : 0 < ρ := not_le.mp hρ0
    have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos hM1R
    have hlogMne : Real.log (M : ℝ) ≠ 0 := ne_of_gt hlogM
    have hmul : ρ * Real.log (M : ℝ) ≤ Real.log (K : ℝ) := by
      have h1 : ρ * Real.log (M : ℝ)
          ≤ Real.log (K : ℝ) / Real.log (M : ℝ) * Real.log (M : ℝ) :=
        mul_le_mul_of_nonneg_right hρ hlogM.le
      have h2 : Real.log (K : ℝ) / Real.log (M : ℝ) * Real.log (M : ℝ) = Real.log (K : ℝ) := by
        field_simp
      linarith
    have hMrhoK : (M : ℝ) ^ ρ ≤ (K : ℝ) := by
      rw [Real.rpow_def_of_pos hMposR]
      calc Real.exp (Real.log (M : ℝ) * ρ) ≤ Real.exp (Real.log (K : ℝ)) :=
            Real.exp_le_exp.mpr (by rw [mul_comm]; exact hmul)
        _ = (K : ℝ) := Real.exp_log hKposR
    refine ⟨(M : ℝ) ^ (-ρ), Real.rpow_pos_of_pos hMposR _, fun N hN => ?_⟩
    obtain ⟨q, hqle, hqlt⟩ : ∃ q : ℕ, M ^ q ≤ N ∧ N < M ^ (q + 1) :=
      ⟨Nat.log M N, Nat.pow_log_le_self M (by omega), Nat.lt_pow_succ_log_self hM1 N⟩
    have hDN : ((K : ℝ)) ^ q ≤ (D N : ℝ) := by
      have h1 : K ^ q ≤ D N := le_trans (hDq q) (D_mono hqle)
      have h2 : ((K : ℝ)) ^ q = ((K ^ q : ℕ) : ℝ) := by push_cast; ring
      rw [h2]
      exact_mod_cast h1
    have hNle : (N : ℝ) ≤ (M : ℝ) ^ (q + 1) := by exact_mod_cast hqlt.le
    have step1 : (N : ℝ) ^ ρ ≤ ((M : ℝ) ^ (q + 1)) ^ ρ :=
      Real.rpow_le_rpow (by positivity) hNle hρ0.le
    have e1 : ((M : ℝ) ^ (q + 1)) ^ ρ = (M : ℝ) ^ (((q : ℝ) + 1) * ρ) := by
      rw [← Real.rpow_natCast (M : ℝ) (q + 1), ← Real.rpow_mul hMposR.le]
      congr 1
      push_cast
      ring
    have e2 : (M : ℝ) ^ (-ρ) * (M : ℝ) ^ (((q : ℝ) + 1) * ρ) = (M : ℝ) ^ ((q : ℝ) * ρ) := by
      rw [← Real.rpow_add hMposR]
      congr 1
      ring
    have key : (M : ℝ) ^ (-ρ) * (N : ℝ) ^ ρ ≤ ((K : ℝ)) ^ q := by
      calc (M : ℝ) ^ (-ρ) * (N : ℝ) ^ ρ
          ≤ (M : ℝ) ^ (-ρ) * ((M : ℝ) ^ (q + 1)) ^ ρ :=
            mul_le_mul_of_nonneg_left step1 (Real.rpow_pos_of_pos hMposR _).le
        _ = (M : ℝ) ^ (-ρ) * (M : ℝ) ^ (((q : ℝ) + 1) * ρ) := by rw [e1]
        _ = (M : ℝ) ^ ((q : ℝ) * ρ) := e2
        _ = ((M : ℝ) ^ ρ) ^ q := rpow_natCast_mul (M : ℝ) hMposR.le ρ q
        _ ≤ ((K : ℝ)) ^ q := pow_le_pow_left₀ (Real.rpow_nonneg hMposR.le ρ) hMrhoK q
    exact key.trans hDN

/-- **The liminf from the pointwise bounds.** -/
theorem liminf_ge_of_pointwise (γ : ℝ)
    (h : ∀ ρ : ℝ, ρ < γ → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → C * (N : ℝ) ^ ρ ≤ (D N : ℝ)) :
    γ ≤ Filter.liminf (fun N : ℕ => Real.log (D N) / Real.log N) Filter.atTop := by
  -- `log (D N) / log N ≤ 1` eventually, which is the coboundedness side condition.
  have hcb : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun N : ℕ => Real.log (D N) / Real.log N) := by
    refine Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop (x := (1 : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    have hN1 : 1 ≤ N := by omega
    have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
    have hDpos : (0 : ℝ) < (D N : ℝ) := by exact_mod_cast one_le_D N hN1
    have hDle : ((D N : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast D_le N
    exact (div_le_one hlogN).mpr (Real.log_le_log hDpos hDle)
  by_contra hcon
  obtain ⟨ρ, hLρ, hργ⟩ := exists_between (not_le.mp hcon)
  obtain ⟨ρ', hLρ', hρ'ρ⟩ := exists_between hLρ
  obtain ⟨C, hC, hCN⟩ := h ρ hργ
  have hd : 0 < ρ - ρ' := by linarith
  have hlim : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim2 : Filter.Tendsto (fun N : ℕ => (ρ - ρ') * Real.log (N : ℝ))
      Filter.atTop Filter.atTop := hlim.const_mul_atTop hd
  have hev : ∀ᶠ N : ℕ in Filter.atTop, ρ' ≤ Real.log (D N) / Real.log N := by
    filter_upwards [Filter.eventually_ge_atTop 2,
      hlim2.eventually_ge_atTop (-Real.log C)] with N hN hbig
    have hN1 : 1 ≤ N := by omega
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
    have hlogNne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogN
    have hrp : (0 : ℝ) < (N : ℝ) ^ ρ := Real.rpow_pos_of_pos hNposR ρ
    have hlog : Real.log (C * (N : ℝ) ^ ρ) ≤ Real.log (D N : ℝ) :=
      Real.log_le_log (mul_pos hC hrp) (hCN N hN1)
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt hrp), Real.log_rpow hNposR] at hlog
    -- `ρ' log N ≤ ρ log N + log C ≤ log (D N)`
    have hnum : 0 ≤ Real.log (D N : ℝ) - ρ' * Real.log (N : ℝ) := by linarith
    have hfin : 0 ≤ (Real.log (D N : ℝ) - ρ' * Real.log (N : ℝ)) / Real.log (N : ℝ) :=
      div_nonneg hnum hlogN.le
    have heq : (Real.log (D N : ℝ) - ρ' * Real.log (N : ℝ)) / Real.log (N : ℝ)
        = Real.log (D N : ℝ) / Real.log (N : ℝ) - ρ' := by
      rw [sub_div, mul_div_assoc, div_self hlogNne, mul_one]
    rw [heq] at hfin
    linarith
  have hle := Filter.le_liminf_of_le hcb hev
  linarith

end NonlinearRoth
