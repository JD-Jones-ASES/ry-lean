import RY.Avoid

/-!
# The digit rule

The rule `typ s 0` assigns to each position a digit type in `{0, 1, 2}` — `ℤ/m`, `R₁`,
`R₂` — and `ruleSet R₁ R₂ s` is the corresponding family of digit sets. Three things are
proved about it.

* **Edge validity.** For every `ℓ`, either the digit set at `2 ℓ` is `R₁` (and then the
  hypothesis `hR₁` applies, whatever the digit set at `ℓ` is, because `hR₁` is stated for an
  arbitrary square `d ^ 2`), or it is `R₂` and the digit set at `ℓ` is `R₁` (and
  then `hR₂` applies). The pair `(R₂, R₂)` never occurs. Combined with `RY.Avoid` this
  makes `blockSet m (ruleSet R₁ R₂ s) Y` configuration-free for every `Y`.
* **Cardinality.** `(ruleSet R₁ R₂ s i).card = sizeAt m |R₁| |R₂| s 0 i`.
* **The product over `q` periods.** `∏_{i < q · 2^(2s+1)} sizeAt … = K_s ^ q` with
  `K_s = m ^ (4^s) · a ^ α_s · b ^ β_s`. The proof is the phase recursion
  `∏_{i < 2Q} sizeAt t i = (sizeAt t 1) ^ Q * ∏_{i < Q} sizeAt (t+1) i`, which holds
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
  simp [typ]

/-- An odd position has the type of its phase. -/
theorem typ_odd (s t i : ℕ) (hi : i % 2 = 1) : typ s t i = phase s t := by
  have hi0 : i ≠ 0 := by omega
  have hnd : ¬ (2 ∣ i) := by omega
  have hv : padicValNat 2 i = 0 := padicValNat.eq_zero_of_not_dvd hnd
  simp [typ, hi0, hv]

/-- Doubling the position is the same as advancing the phase. -/
theorem typ_two_mul (s t i : ℕ) : typ s t (2 * i) = typ s (t + 1) i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [typ]
  · have hi0 : i ≠ 0 := hi.ne'
    have h2i : 2 * i ≠ 0 := by omega
    have hv : padicValNat 2 (2 * i) = 1 + padicValNat 2 i := by
      rw [padicValNat.mul (p := 2) (two_ne_zero) hi0, padicValNat_self]
    simp only [typ, if_neg h2i, if_neg hi0, hv]
    congr 1
    omega

/-- Beyond depth `s` every position has type `1`. -/
theorem typ_of_ge (s t i : ℕ) (ht : 2 * s + 1 ≤ t) : typ s t i = 1 := by
  simp only [typ]
  split_ifs with h
  · rfl
  · have hle : 2 * s + 1 ≤ t + padicValNat 2 i := by omega
    simp only [phase, if_pos hle]

/-- **Edge validity.** The digit set at `2 ℓ` is `R₁`, or it is `R₂` and the digit set at
`ℓ` is `R₁`. -/
theorem typ_edge (s ℓ : ℕ) : typ s 0 (2 * ℓ) = 1 ∨ (typ s 0 (2 * ℓ) = 2 ∧ typ s 0 ℓ = 1) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · left
    simpa using typ_zero s 0
  · have hℓ0 : ℓ ≠ 0 := hℓ.ne'
    rw [typ_two_mul s 0 ℓ]
    simp only [typ, if_neg hℓ0, phase]
    split_ifs <;> omega

/-! ## Digit sets -/

/-- Residue digits lie in `[0, m)`. -/
theorem digitsOf_bounds {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) :
    ∀ d ∈ digitsOf R, 0 ≤ d ∧ d < (m : ℤ) := by
  have : NeZero m := ⟨hm.ne'⟩
  intro d hd
  simp only [digitsOf, Finset.mem_image] at hd
  obtain ⟨r, _, rfl⟩ := hd
  refine ⟨by positivity, ?_⟩
  exact_mod_cast ZMod.val_lt r

/-- `ZMod.val` is injective, so `digitsOf` preserves cardinality. -/
theorem digitsOf_card {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) :
    (digitsOf R).card = R.card := by
  have : NeZero m := ⟨hm.ne'⟩
  have hinj : Function.Injective (fun r : ZMod m => (r.val : ℤ)) := by
    intro x y hxy
    have h : (x.val : ℤ) = (y.val : ℤ) := hxy
    exact ZMod.val_injective m (by exact_mod_cast h)
  show (R.image fun r : ZMod m => (r.val : ℤ)).card = R.card
  exact Finset.card_image_of_injective R hinj

/-- An integer digit of `digitsOf R` reduces into `R`. -/
theorem cast_mem_of_mem_digitsOf {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) {x : ℤ}
    (hx : x ∈ digitsOf R) : ((x : ZMod m)) ∈ R := by
  have : NeZero m := ⟨hm.ne'⟩
  simp only [digitsOf, Finset.mem_image] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  simpa [ZMod.natCast_val, ZMod.cast_id] using hr

/-- All digits lie in `[0, m)`. -/
theorem allDigits_bounds (m : ℕ) : ∀ d ∈ allDigits m, 0 ≤ d ∧ d < (m : ℤ) := by
  intro d hd
  simp only [allDigits, Finset.mem_image, Finset.mem_range] at hd
  obtain ⟨k, hk, rfl⟩ := hd
  exact ⟨by positivity, by exact_mod_cast hk⟩

/-- There are `m` digits. -/
theorem allDigits_card (m : ℕ) : (allDigits m).card = m := by
  have hinj : Function.Injective (fun d : ℕ => (d : ℤ)) := by
    intro x y hxy
    have h : (x : ℤ) = (y : ℤ) := hxy
    exact_mod_cast h
  show ((Finset.range m).image fun d : ℕ => (d : ℤ)).card = m
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

/-! ## `ruleSet` -/

/-- The digits of the rule lie in `[0, m)`. -/
theorem ruleSet_bounds {m : ℕ} (hm : 0 < m) (R₁ R₂ : Finset (ZMod m)) (s i : ℕ) :
    ∀ d ∈ ruleSet R₁ R₂ s i, 0 ≤ d ∧ d < (m : ℤ) := by
  intro d hd
  simp only [ruleSet] at hd
  split_ifs at hd
  · exact allDigits_bounds m d hd
  · exact digitsOf_bounds hm R₁ d hd
  · exact digitsOf_bounds hm R₂ d hd

/-- The size of the digit set at position `i`. -/
theorem ruleSet_card {m : ℕ} (hm : 0 < m) (R₁ R₂ : Finset (ZMod m)) (s i : ℕ) :
    (ruleSet R₁ R₂ s i).card = sizeAt m R₁.card R₂.card s 0 i := by
  simp only [ruleSet, sizeAt]
  split_ifs
  · exact allDigits_card m
  · exact digitsOf_card hm R₁
  · exact digitsOf_card hm R₂

/-- **The edge condition for `ruleSet`,** the hypothesis `RY.Avoid` asks for. -/
theorem ruleSet_edge {m : ℕ} (hm : 2 ≤ m) (R₁ R₂ : Finset (ZMod m))
    (hR₁ : ∀ a ∈ R₁, ∀ b ∈ R₁, ∀ d : ZMod m, a - b = d ^ 2 → a = b)
    (hR₂ : ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b)
    (s ℓ : ℕ) :
    ∀ p ∈ ruleSet R₁ R₂ s (2 * ℓ), ∀ q ∈ ruleSet R₁ R₂ s (2 * ℓ),
      ∀ c ∈ ruleSet R₁ R₂ s ℓ, ∀ d ∈ ruleSet R₁ R₂ s ℓ,
        ((p : ZMod m) - (q : ZMod m) = ((c : ZMod m) - (d : ZMod m)) ^ 2) →
          ((p : ZMod m) = (q : ZMod m)) := by
  have hm0 : 0 < m := by omega
  intro p hp q hq c hc d hd hpq
  rcases typ_edge s ℓ with h1 | ⟨h2, h1ℓ⟩
  · have hset : ruleSet R₁ R₂ s (2 * ℓ) = digitsOf R₁ := by
      simp [ruleSet, h1]
    rw [hset] at hp hq
    exact hR₁ _ (cast_mem_of_mem_digitsOf hm0 R₁ hp) _ (cast_mem_of_mem_digitsOf hm0 R₁ hq)
      ((c : ZMod m) - (d : ZMod m)) hpq
  · have hsetp : ruleSet R₁ R₂ s (2 * ℓ) = digitsOf R₂ := by
      simp [ruleSet, h2]
    have hsetc : ruleSet R₁ R₂ s ℓ = digitsOf R₁ := by
      simp [ruleSet, h1ℓ]
    rw [hsetp] at hp hq
    rw [hsetc] at hc hd
    exact hR₂ _ (cast_mem_of_mem_digitsOf hm0 R₂ hp) _ (cast_mem_of_mem_digitsOf hm0 R₂ hq)
      _ (cast_mem_of_mem_digitsOf hm0 R₁ hc) _ (cast_mem_of_mem_digitsOf hm0 R₁ hd) hpq

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
  simp only [sizeAt, typ_odd s t i hi, typ_odd s t 1 (by norm_num)]

/-- **The phase recursion.** `N_t(2Q) = c_{h t} ^ Q · N_{t+1}(Q)`. -/
theorem prod_sizeAt_split (m a b s t Q : ℕ) :
    ∏ i ∈ Finset.range (2 * Q), sizeAt m a b s t i
      = sizeAt m a b s t 1 ^ Q * ∏ i ∈ Finset.range Q, sizeAt m a b s (t + 1) i := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      have h2 : 2 * (Q + 1) = 2 * Q + 1 + 1 := by ring
      have hodd : sizeAt m a b s t (2 * Q + 1) = sizeAt m a b s t 1 :=
        sizeAt_odd m a b s t (2 * Q + 1) (by omega)
      have heven : sizeAt m a b s t (2 * Q) = sizeAt m a b s (t + 1) Q := by
        simp only [sizeAt, typ_two_mul]
      rw [h2, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ,
        hodd, heven]
      ring

/-- Auxiliary form of `prod_sizeAt_pow`, with the phase universally quantified so that the
induction on the remaining depth `n` can move the phase. -/
private theorem prod_sizeAt_pow_aux (m a b s q : ℕ) :
    ∀ n t : ℕ, t + n = 2 * s + 1 →
      ∏ i ∈ Finset.range (q * 2 ^ n), sizeAt m a b s t i
        = (∏ i ∈ Finset.range (2 ^ n), sizeAt m a b s t i) ^ q := by
  intro n
  induction n with
  | zero =>
      intro t h
      have ht : 2 * s + 1 ≤ t := by omega
      have hall : ∀ i, sizeAt m a b s t i = a := by
        intro i
        simp [sizeAt, typ_of_ge s t i ht]
      simp [hall, Finset.prod_const, Finset.card_range]
  | succ n ih =>
      intro t h
      have h' : t + 1 + n = 2 * s + 1 := by omega
      have e1 : q * 2 ^ (n + 1) = 2 * (q * 2 ^ n) := by ring
      have e2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
      rw [e1, prod_sizeAt_split, ih (t + 1) h', e2, prod_sizeAt_split]
      ring

/-- The product over `q` periods of the phase-`t` rule is the `q`-th power of the product
over one period. Here `2 ^ n` is the period of phase `t`, i.e. `t + n = 2s + 1`. -/
theorem prod_sizeAt_pow (m a b s t n q : ℕ) (h : t + n = 2 * s + 1) :
    ∏ i ∈ Finset.range (q * 2 ^ n), sizeAt m a b s t i
      = (∏ i ∈ Finset.range (2 ^ n), sizeAt m a b s t i) ^ q :=
  prod_sizeAt_pow_aux m a b s q n t h

/-- Auxiliary form of `prod_sizeAt_odd_phase`: the induction runs on the remaining depth
`r`, which forces the starting phase `2j+1` to move, so both are quantified. -/
private theorem prod_sizeAt_odd_phase_aux (m a b s : ℕ) :
    ∀ r j : ℕ, j + r = s →
      ∏ i ∈ Finset.range (2 ^ (2 * r)), sizeAt m a b s (2 * j + 1) i
        = a ^ alpha r * b ^ beta r := by
  intro r
  induction r with
  | zero =>
      intro j _
      simp [alpha, beta, sizeAt, typ_zero]
  | succ r ih =>
      intro j h
      have hj : j + 1 + r = s := by omega
      have hlt1 : 2 * j + 1 < 2 * s + 1 := by omega
      have hlt2 : 2 * j + 1 + 1 < 2 * s + 1 := by omega
      have ha1 : sizeAt m a b s (2 * j + 1) 1 = a := by
        have htyp : typ s (2 * j + 1) 1 = 1 := by
          rw [typ_odd s (2 * j + 1) 1 (by norm_num)]
          simp only [phase]
          split_ifs <;> omega
        simp [sizeAt, htyp]
      have hb1 : sizeAt m a b s (2 * j + 1 + 1) 1 = b := by
        have htyp : typ s (2 * j + 1 + 1) 1 = 2 := by
          rw [typ_odd s (2 * j + 1 + 1) 1 (by norm_num)]
          simp only [phase]
          split_ifs <;> omega
        simp [sizeAt, htyp]
      have ih' : ∏ i ∈ Finset.range (2 ^ (2 * r)), sizeAt m a b s (2 * j + 1 + 1 + 1) i
          = a ^ alpha r * b ^ beta r := by
        have e3 : 2 * j + 1 + 1 + 1 = 2 * (j + 1) + 1 := by ring
        rw [e3]
        exact ih (j + 1) hj
      have e1 : (2 : ℕ) ^ (2 * (r + 1)) = 2 * 2 ^ (2 * r + 1) := by
        rw [show 2 * (r + 1) = 2 * r + 1 + 1 by ring, pow_succ]
        ring
      have e2 : (2 : ℕ) ^ (2 * r + 1) = 2 * 2 ^ (2 * r) := by
        rw [pow_succ]
        ring
      have e4 : (2 : ℕ) ^ (2 * r) = 4 ^ r := by
        rw [pow_mul]
        norm_num
      have hbr := beta_spec r
      have hA : 2 * 2 ^ (2 * r) + alpha r = alpha (r + 1) := by
        rw [e4]
        simp only [alpha, beta]
        omega
      have hB : 2 ^ (2 * r) + beta r = beta (r + 1) := by
        rw [e4]
        simp only [beta]
        omega
      rw [e1, prod_sizeAt_split, ha1, e2, prod_sizeAt_split, hb1, ih', ← hA, ← hB]
      ring

/-- The product over one period of an odd phase `2j+1`, where `j + r = s`: the `m` factor
has already been consumed, and what is left is `a ^ α_r · b ^ β_r`. -/
theorem prod_sizeAt_odd_phase (m a b s j r : ℕ) (h : j + r = s) :
    ∏ i ∈ Finset.range (2 ^ (2 * r)), sizeAt m a b s (2 * j + 1) i
      = a ^ alpha r * b ^ beta r :=
  prod_sizeAt_odd_phase_aux m a b s r j h

/-- **The product over one period.** -/
theorem prod_sizeAt_period (m a b s : ℕ) :
    ∏ i ∈ Finset.range (period s), sizeAt m a b s 0 i = blockCard m a b s := by
  have e1 : period s = 2 * 2 ^ (2 * s) := by
    simp only [period]
    rw [pow_succ]
    ring
  have e4 : (2 : ℕ) ^ (2 * s) = 4 ^ s := by
    rw [pow_mul]
    norm_num
  have hm1 : sizeAt m a b s 0 1 = m := by
    have htyp : typ s 0 1 = 0 := by
      rw [typ_odd s 0 1 (by norm_num)]
      simp only [phase]
      split_ifs <;> omega
    simp [sizeAt, htyp]
  have h0 : ∏ i ∈ Finset.range (2 ^ (2 * s)), sizeAt m a b s (0 + 1) i
      = a ^ alpha s * b ^ beta s := by
    have e3 : (0 : ℕ) + 1 = 2 * 0 + 1 := by ring
    rw [e3]
    exact prod_sizeAt_odd_phase m a b s 0 s (by omega)
  rw [e1, prod_sizeAt_split, hm1, h0, e4, blockCard]
  ring

/-- **The product over `q` periods.** -/
theorem prod_sizeAt_mul_period (m a b s q : ℕ) :
    ∏ i ∈ Finset.range (q * period s), sizeAt m a b s 0 i = blockCard m a b s ^ q := by
  rw [period, prod_sizeAt_pow m a b s 0 (2 * s + 1) q (by omega), ← period,
    prod_sizeAt_period]

end NonlinearRoth
