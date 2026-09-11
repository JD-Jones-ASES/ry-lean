import RY.Avoid

/-!
# The digit rule

The rule `typ s 0` assigns to each position a digit type in `{0, 1, 2}` — `ℤ/m`, `R₁`,
`R₂` — and `ruleSet R₁ R₂ s` is the corresponding family of digit sets. Three things are
proved about it.

* **Edge validity.** For every `ℓ`, either the digit set at `2 ℓ` is `R₁` (and then the
  hypothesis `hR₁` applies, whatever the digit set at `ℓ` is, because a difference of
  residues is an arbitrary residue), or it is `R₂` and the digit set at `ℓ` is `R₁` (and
  then `hR₂` applies). The pair `(R₂, R₂)` never occurs. Combined with `RY.Avoid` this
  makes `blockSet m (ruleSet R₁ R₂ s) Y` configuration-free for every `Y`.
* **Cardinality.** `(ruleSet R₁ R₂ s i).card = sizeAt m |R₁| |R₂| s 0 i`.
* **The product over `q` periods.** `∏_{i < q · 2^(2s+1)} sizeAt … = K_s ^ q` with
  `K_s = m ^ (4^s) · a ^ α_s · b ^ β_s`. The proof is the phase recursion
  `∏_{i < 2Q} sizeAt t i = (sizeAt t 1) ^ Q · ∏_{i < Q} sizeAt (t+1) i`, which holds
  because odd positions have type `phase s t` and `typ s t (2i) = typ s (t+1) i`.
-/

namespace NonlinearRoth

/-! ## Arithmetic of `alpha`, `beta`, `period` -/

/-- `3 β_s + 1 = 4 ^ s`. -/
theorem beta_spec : ∀ s : ℕ, 3 * beta s + 1 = 4 ^ s
  | 0 => by simp [beta]
  | s + 1 => by
      have ih := beta_spec s
      simp only [beta, pow_succ]
      omega

/-- `3 α_s = 2 · 4 ^ s + 1`. -/
theorem alpha_spec (s : ℕ) : 3 * alpha s = 2 * 4 ^ s + 1 := by
  have h := beta_spec s
  simp only [alpha]
  omega

/-- `2 ^ (2s+1) = 2 · 4 ^ s`. -/
theorem period_eq (s : ℕ) : period s = 2 * 4 ^ s := by
  simp only [period, pow_succ, pow_mul]
  norm_num [mul_comm]

/-- The period is positive. -/
theorem period_ne_zero (s : ℕ) : period s ≠ 0 := by
  simp only [period]
  positivity

/-- `K_s ≥ 1`. -/
theorem one_le_blockCard (m a b s : ℕ) (hm : 1 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ blockCard m a b s := by
  have h1 : 1 ≤ m ^ 4 ^ s := Nat.one_le_pow _ _ hm
  have h2 : 1 ≤ a ^ alpha s := Nat.one_le_pow _ _ ha
  have h3 : 1 ≤ b ^ beta s := Nat.one_le_pow _ _ hb
  simp only [blockCard]
  calc (1 : ℕ) = 1 * 1 * 1 := by norm_num
    _ ≤ m ^ 4 ^ s * a ^ alpha s * b ^ beta s :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

/-- `M_s = m ^ (2 ^ (2s+1)) ≥ 2`. -/
theorem two_le_pow_period (m s : ℕ) (hm : 2 ≤ m) : 2 ≤ m ^ period s :=
  le_trans hm (Nat.le_self_pow (period_ne_zero s) m)

/-! ## The rule itself -/

/-- Position `0` always has type `1`. -/
theorem typ_zero (s t : ℕ) : typ s t 0 = 1 := by
  sorry

/-- An odd position has the type of its phase. -/
theorem typ_odd (s t i : ℕ) (hi : i % 2 = 1) : typ s t i = phase s t := by
  sorry

/-- Doubling the position is the same as advancing the phase. -/
theorem typ_two_mul (s t i : ℕ) : typ s t (2 * i) = typ s (t + 1) i := by
  sorry

/-- Beyond depth `s` every position has type `1`. -/
theorem typ_of_ge (s t i : ℕ) (ht : 2 * s + 1 ≤ t) : typ s t i = 1 := by
  sorry

/-- Types are `0`, `1` or `2`. -/
theorem typ_lt_three (s t i : ℕ) : typ s t i < 3 := by
  sorry

/-- **Edge validity.** The digit set at `2 ℓ` is `R₁`, or it is `R₂` and the digit set at
`ℓ` is `R₁`. -/
theorem typ_edge (s ℓ : ℕ) : typ s 0 (2 * ℓ) = 1 ∨ (typ s 0 (2 * ℓ) = 2 ∧ typ s 0 ℓ = 1) := by
  sorry

/-! ## Digit sets -/

/-- Residue digits lie in `[0, m)`. -/
theorem digitsOf_bounds {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) :
    ∀ d ∈ digitsOf R, 0 ≤ d ∧ d < (m : ℤ) := by
  sorry

/-- `ZMod.val` is injective, so `digitsOf` preserves cardinality. -/
theorem digitsOf_card {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) :
    (digitsOf R).card = R.card := by
  sorry

/-- An integer digit of `digitsOf R` reduces into `R`. -/
theorem cast_mem_of_mem_digitsOf {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) {x : ℤ}
    (hx : x ∈ digitsOf R) : ((x : ZMod m)) ∈ R := by
  sorry

/-- All digits lie in `[0, m)`. -/
theorem allDigits_bounds (m : ℕ) : ∀ d ∈ allDigits m, 0 ≤ d ∧ d < (m : ℤ) := by
  sorry

/-- There are `m` digits. -/
theorem allDigits_card (m : ℕ) : (allDigits m).card = m := by
  sorry

/-- Every residue is the reduction of a digit: this is what makes the `R₀ = ℤ/m` edge an
instance of `hR₁` with an arbitrary `d`. -/
theorem exists_mem_allDigits {m : ℕ} (hm : 0 < m) (r : ZMod m) :
    ∃ x ∈ allDigits m, ((x : ZMod m)) = r := by
  sorry

/-! ## `ruleSet` -/

/-- The digits of the rule lie in `[0, m)`. -/
theorem ruleSet_bounds {m : ℕ} (hm : 0 < m) (R₁ R₂ : Finset (ZMod m)) (s i : ℕ) :
    ∀ d ∈ ruleSet R₁ R₂ s i, 0 ≤ d ∧ d < (m : ℤ) := by
  sorry

/-- The size of the digit set at position `i`. -/
theorem ruleSet_card {m : ℕ} (hm : 0 < m) (R₁ R₂ : Finset (ZMod m)) (s i : ℕ) :
    (ruleSet R₁ R₂ s i).card = sizeAt m R₁.card R₂.card s 0 i := by
  sorry

/-- **The edge condition for `ruleSet`,** the hypothesis `RY.Avoid` asks for. -/
theorem ruleSet_edge {m : ℕ} (hm : 2 ≤ m) (R₁ R₂ : Finset (ZMod m))
    (hR₁ : ∀ a ∈ R₁, ∀ b ∈ R₁, ∀ d : ZMod m, a - b = d ^ 2 → a = b)
    (hR₂ : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b)
    (s ℓ : ℕ) :
    ∀ p ∈ ruleSet R₁ R₂ s (2 * ℓ), ∀ q ∈ ruleSet R₁ R₂ s (2 * ℓ),
      ∀ c ∈ ruleSet R₁ R₂ s ℓ, ∀ d ∈ ruleSet R₁ R₂ s ℓ,
        ((p : ZMod m) - (q : ZMod m) = ((c : ZMod m) - (d : ZMod m)) ^ 2) →
          ((p : ZMod m) = (q : ZMod m)) := by
  sorry

/-- **The construction is configuration-free.** -/
theorem blockSet_ruleSet_configFree {m : ℕ} (hm : 2 ≤ m) (hsf : Squarefree m)
    (R₁ R₂ : Finset (ZMod m))
    (hR₁ : ∀ a ∈ R₁, ∀ b ∈ R₁, ∀ d : ZMod m, a - b = d ^ 2 → a = b)
    (hR₂ : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b)
    (s Y : ℕ) : ConfigFree (blockSet m (ruleSet R₁ R₂ s) Y) :=
  blockSet_configFree m hm hsf _ (fun i => ruleSet_bounds (by omega) R₁ R₂ s i) Y
    (fun ℓ _ => ruleSet_edge hm R₁ R₂ hR₁ hR₂ s ℓ)

/-- **The construction's size.** -/
theorem blockSet_ruleSet_card {m : ℕ} (hm : 0 < m) (R₁ R₂ : Finset (ZMod m)) (s Y : ℕ) :
    (blockSet m (ruleSet R₁ R₂ s) Y).card
      = ∏ i ∈ Finset.range Y, sizeAt m R₁.card R₂.card s 0 i := by
  rw [blockSet_card m hm _ (fun i => ruleSet_bounds hm R₁ R₂ s i) Y]
  exact Finset.prod_congr rfl fun i _ => ruleSet_card hm R₁ R₂ s i

/-! ## The product over a period -/

/-- Odd positions all carry the phase's type. -/
theorem sizeAt_odd (m a b s t i : ℕ) (hi : i % 2 = 1) :
    sizeAt m a b s t i = sizeAt m a b s t 1 := by
  sorry

/-- **The phase recursion.** `N_t(2Q) = c_{h t} ^ Q · N_{t+1}(Q)`. -/
theorem prod_sizeAt_split (m a b s t Q : ℕ) :
    ∏ i ∈ Finset.range (2 * Q), sizeAt m a b s t i
      = sizeAt m a b s t 1 ^ Q * ∏ i ∈ Finset.range Q, sizeAt m a b s (t + 1) i := by
  sorry

/-- The product over `q` periods of the phase-`t` rule is the `q`-th power of the product
over one period. Here `2 ^ n` is the period of phase `t`, i.e. `t + n = 2s + 1`. -/
theorem prod_sizeAt_pow (m a b s t n q : ℕ) (h : t + n = 2 * s + 1) :
    ∏ i ∈ Finset.range (q * 2 ^ n), sizeAt m a b s t i
      = (∏ i ∈ Finset.range (2 ^ n), sizeAt m a b s t i) ^ q := by
  sorry

/-- The product over one period of an odd phase `2j+1`, where `j + r = s`: the `m` factor
has already been consumed, and what is left is `a ^ α_r · b ^ β_r`. -/
theorem prod_sizeAt_odd_phase (m a b s j r : ℕ) (h : j + r = s) :
    ∏ i ∈ Finset.range (2 ^ (2 * r)), sizeAt m a b s (2 * j + 1) i
      = a ^ alpha r * b ^ beta r := by
  sorry

/-- **The product over one period.** -/
theorem prod_sizeAt_period (m a b s : ℕ) :
    ∏ i ∈ Finset.range (period s), sizeAt m a b s 0 i = blockCard m a b s := by
  sorry

/-- **The product over `q` periods.** -/
theorem prod_sizeAt_mul_period (m a b s q : ℕ) :
    ∏ i ∈ Finset.range (q * period s), sizeAt m a b s 0 i = blockCard m a b s ^ q := by
  rw [period, prod_sizeAt_pow m a b s 0 (2 * s + 1) q (by omega), ← period,
    prod_sizeAt_period]

end NonlinearRoth
