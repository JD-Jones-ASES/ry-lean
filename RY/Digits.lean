import RY.Defs

/-!
# Digits of the block set

Three groups of facts.

* The **digit congruence** `cast_ediv_eq_digit_sub`: if `m ^ ℓ` divides `v - u`, then
  `(v - u) / m ^ ℓ ≡ digit ℓ v - digit ℓ u (mod m)`. This is the only arithmetic input of
  the avoidance argument, and its proof is `Int.add_mul_ediv_left` followed by a reduction
  mod `m`.
* The **shape of `blockSet`**: its elements lie in `[0, m ^ Y)`, their digits below `Y` are
  the prescribed ones, and its cardinality is the product of the digit-set sizes.
* Two utilities: the maximal power of `m` dividing a nonzero integer, and the fact that
  translating a set preserves `ConfigFree`.
-/

namespace NonlinearRoth

/-! ## The digit congruence -/

/-- **Lemma D.** If `m ^ ℓ ∣ v - u` then `(v - u) / m ^ ℓ` and `digit ℓ v - digit ℓ u`
agree modulo `m`. -/
theorem cast_ediv_eq_digit_sub (m : ℕ) (hm : 0 < m) (ℓ : ℕ) (u v : ℤ)
    (h : (m : ℤ) ^ ℓ ∣ v - u) :
    (((v - u) / (m : ℤ) ^ ℓ : ℤ) : ZMod m)
      = ((digit m ℓ v : ℤ) : ZMod m) - ((digit m ℓ u : ℤ) : ZMod m) := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpow : (m : ℤ) ^ ℓ ≠ 0 := pow_ne_zero _ hm0
  obtain ⟨t, ht⟩ := h
  have hv : v = u + (m : ℤ) ^ ℓ * t := by rw [← ht]; ring
  have hdiv : (v - u) / (m : ℤ) ^ ℓ = t := by
    rw [ht, Int.mul_ediv_cancel_left _ hpow]
  have hvdiv : v / (m : ℤ) ^ ℓ = u / (m : ℤ) ^ ℓ + t := by
    rw [hv]; exact Int.add_mul_ediv_left _ _ hpow
  simp only [digit, ZMod.intCast_mod]
  rw [hdiv, hvdiv]
  push_cast
  ring

/-- `digit m i x` reduces mod `m` to `x / m ^ i`. -/
theorem cast_digit (m i : ℕ) (x : ℤ) :
    ((digit m i x : ℤ) : ZMod m) = ((x / (m : ℤ) ^ i : ℤ) : ZMod m) := by
  simp only [digit, ZMod.intCast_mod]

/-- Monotonicity of `i ↦ (m : ℤ) ^ i`, read off the `ℕ`-valued statement. -/
theorem natCast_pow_le_pow_of_le {m : ℕ} (hm : 1 ≤ m) {i j : ℕ} (h : i ≤ j) :
    (m : ℤ) ^ i ≤ (m : ℤ) ^ j := by
  have h' : m ^ i ≤ m ^ j := Nat.pow_le_pow_right hm h
  exact_mod_cast h'

/-! ## The shape of `blockSet` -/

/-- Every element of `blockSet m S Y` is nonnegative. -/
theorem blockSet_nonneg (m : ℕ) (S : ℕ → Finset ℤ) (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d) (Y : ℕ) :
    ∀ x ∈ blockSet m S Y, 0 ≤ x := by
  induction Y with
  | zero =>
      intro x hx
      simp only [blockSet, Finset.mem_singleton] at hx
      simp [hx]
  | succ Y ih =>
      intro x hx
      simp only [blockSet, Finset.mem_image, Finset.mem_product] at hx
      obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hx
      have h1 : 0 ≤ p.1 := hS Y p.1 hp1
      have h2 : 0 ≤ p.2 := ih p.2 hp2
      have h3 : (0 : ℤ) ≤ (m : ℤ) ^ Y := pow_nonneg (Int.natCast_nonneg m) Y
      exact add_nonneg (mul_nonneg h1 h3) h2

/-- Every element of `blockSet m S Y` is less than `m ^ Y`. -/
theorem blockSet_lt (m : ℕ) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) :
    ∀ x ∈ blockSet m S Y, x < (m : ℤ) ^ Y := by
  induction Y with
  | zero =>
      intro x hx
      simp only [blockSet, Finset.mem_singleton] at hx
      simp [hx]
  | succ Y ih =>
      intro x hx
      simp only [blockSet, Finset.mem_image, Finset.mem_product] at hx
      obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hx
      obtain ⟨hd0, hdm⟩ := hS Y p.1 hp1
      have hr : p.2 < (m : ℤ) ^ Y := ih p.2 hp2
      have hmZ : (0 : ℤ) < (m : ℤ) := lt_of_le_of_lt hd0 hdm
      have hpow : (0 : ℤ) < (m : ℤ) ^ Y := pow_pos hmZ Y
      have hd1 : p.1 + 1 ≤ (m : ℤ) := Int.lt_iff_add_one_le.mp hdm
      calc p.1 * (m : ℤ) ^ Y + p.2
          < p.1 * (m : ℤ) ^ Y + (m : ℤ) ^ Y := by linarith
        _ = (p.1 + 1) * (m : ℤ) ^ Y := by ring
        _ ≤ (m : ℤ) * (m : ℤ) ^ Y := mul_le_mul_of_nonneg_right hd1 hpow.le
        _ = (m : ℤ) ^ (Y + 1) := by ring

/-- Auxiliary form of `digit_mem`: every variable is quantified inside the statement, so
that the induction on `Y` has a strong enough hypothesis. -/
private theorem digit_mem_aux (m : ℕ) (hm : 0 < m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) :
    ∀ Y : ℕ, ∀ x ∈ blockSet m S Y, ∀ i : ℕ, i < Y → digit m i x ∈ S i := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  intro Y
  induction Y with
  | zero => intro x _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ Y ih =>
      intro x hx i hi
      simp only [blockSet, Finset.mem_image, Finset.mem_product] at hx
      obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hx
      obtain ⟨hd0, hdm⟩ := hS Y p.1 hp1
      have hr0 : 0 ≤ p.2 := blockSet_nonneg m S (fun i d hd => (hS i d hd).1) Y p.2 hp2
      have hrlt : p.2 < (m : ℤ) ^ Y := blockSet_lt m S hS Y p.2 hp2
      have hpow : ((m : ℤ)) ^ Y ≠ 0 := (pow_pos hmZ Y).ne'
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
      · obtain ⟨k, hk⟩ : ∃ k, Y = i + (k + 1) := ⟨Y - i - 1, by omega⟩
        have hpowi : ((m : ℤ)) ^ i ≠ 0 := (pow_pos hmZ i).ne'
        have key : digit m i (p.1 * (m : ℤ) ^ Y + p.2) = digit m i p.2 := by
          simp only [digit]
          rw [show p.1 * (m : ℤ) ^ Y + p.2
                = p.2 + (m : ℤ) ^ i * ((m : ℤ) * (p.1 * (m : ℤ) ^ k)) by
              subst hk; ring,
            Int.add_mul_ediv_left _ _ hpowi, Int.add_mul_emod_self_left]
        rw [key]
        exact ih p.2 hp2 i hlt
      · subst heq
        have key : digit m i (p.1 * (m : ℤ) ^ i + p.2) = p.1 := by
          simp only [digit]
          rw [show p.1 * (m : ℤ) ^ i + p.2 = p.2 + (m : ℤ) ^ i * p.1 by ring,
            Int.add_mul_ediv_left _ _ hpow, Int.ediv_eq_zero_of_lt hr0 hrlt, zero_add,
            Int.emod_eq_of_lt hd0 hdm]
        rw [key]
        exact hp1

/-- The digit of an element of `blockSet m S Y` at a position below `Y` lies in the
prescribed digit set. -/
theorem digit_mem (m : ℕ) (hm : 0 < m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) (x : ℤ) (hx : x ∈ blockSet m S Y)
    (i : ℕ) (hi : i < Y) : digit m i x ∈ S i :=
  digit_mem_aux m hm S hS Y x hx i hi

/-- The base-`m` expansion is injective on digit strings, so `blockSet` has the expected
cardinality. -/
theorem blockSet_card (m : ℕ) (hm : 0 < m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) :
    (blockSet m S Y).card = ∏ i ∈ Finset.range Y, (S i).card := by
  have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  induction Y with
  | zero => simp [blockSet]
  | succ Y ih =>
      have hpow : ((m : ℤ)) ^ Y ≠ 0 := (pow_pos hmZ Y).ne'
      have hinj : Set.InjOn (fun p : ℤ × ℤ => p.1 * (m : ℤ) ^ Y + p.2)
          ↑(S Y ×ˢ blockSet m S Y) := by
        rintro ⟨a, r⟩ ha ⟨b, t⟩ hb hab
        have ha' := Finset.mem_product.mp (Finset.mem_coe.mp ha)
        have hb' := Finset.mem_product.mp (Finset.mem_coe.mp hb)
        have har : r ∈ blockSet m S Y := ha'.2
        have hbt : t ∈ blockSet m S Y := hb'.2
        have hr0 : 0 ≤ r := blockSet_nonneg m S (fun i d hd => (hS i d hd).1) Y r har
        have hrlt : r < (m : ℤ) ^ Y := blockSet_lt m S hS Y r har
        have ht0 : 0 ≤ t := blockSet_nonneg m S (fun i d hd => (hS i d hd).1) Y t hbt
        have htlt : t < (m : ℤ) ^ Y := blockSet_lt m S hS Y t hbt
        have hab' : a * (m : ℤ) ^ Y + r = b * (m : ℤ) ^ Y + t := hab
        have e1 : (a * (m : ℤ) ^ Y + r) / (m : ℤ) ^ Y = a := by
          rw [show a * (m : ℤ) ^ Y + r = r + (m : ℤ) ^ Y * a by ring,
            Int.add_mul_ediv_left _ _ hpow, Int.ediv_eq_zero_of_lt hr0 hrlt, zero_add]
        have e2 : (b * (m : ℤ) ^ Y + t) / (m : ℤ) ^ Y = b := by
          rw [show b * (m : ℤ) ^ Y + t = t + (m : ℤ) ^ Y * b by ring,
            Int.add_mul_ediv_left _ _ hpow, Int.ediv_eq_zero_of_lt ht0 htlt, zero_add]
        have hEq : a = b := by rw [← e1, ← e2, hab']
        have hEq2 : r = t := by rw [hEq] at hab'; linarith
        rw [hEq, hEq2]
      simp only [blockSet]
      rw [Finset.card_image_of_injOn hinj, Finset.card_product, ih, Finset.prod_range_succ]
      ring

/-! ## Utilities -/

/-- The maximal power of `m` dividing a nonzero integer, together with the bound
`m ^ ℓ ≤ |y|` that turns `|y| < m ^ Y` into `ℓ < Y`. -/
theorem exists_maximal_pow_dvd (m : ℕ) (hm : 2 ≤ m) (y : ℤ) (hy : y ≠ 0) :
    ∃ ℓ : ℕ, (m : ℤ) ^ ℓ ∣ y ∧ ¬ (m : ℤ) ^ (ℓ + 1) ∣ y ∧ (m : ℤ) ^ ℓ ≤ |y| := by
  classical
  have habs : 0 < |y| := abs_pos.mpr hy
  have hex : ∃ n : ℕ, ¬ (m : ℤ) ^ n ∣ y := by
    refine ⟨y.natAbs, fun hdvd => ?_⟩
    have h1 : (m : ℤ) ^ y.natAbs ≤ |y| := Int.le_of_dvd habs ((dvd_abs _ _).mpr hdvd)
    have hnat : y.natAbs < m ^ y.natAbs :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hm _)
    have h2 : |y| < (m : ℤ) ^ y.natAbs := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hnat
    linarith
  have hfind := Nat.find_spec hex
  have hfind0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hfind
    exact hfind (by simp)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, Nat.find hex = ℓ + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hdvd : (m : ℤ) ^ ℓ ∣ y :=
    not_not.mp (Nat.find_min hex (show ℓ < Nat.find hex by omega))
  refine ⟨ℓ, hdvd, ?_, Int.le_of_dvd habs ((dvd_abs _ _).mpr hdvd)⟩
  rw [← hℓ]
  exact hfind

/-- Translation preserves `ConfigFree`. -/
theorem configFree_image_add (A : Finset ℤ) (t : ℤ) (h : ConfigFree A) :
    ConfigFree (A.image fun x => x + t) := by
  intro x y hy hx hxy hxy2
  simp only [Finset.mem_image] at hx hxy hxy2
  obtain ⟨a, ha, hae⟩ := hx
  obtain ⟨b, hb, hbe⟩ := hxy
  obtain ⟨c, hc, hce⟩ := hxy2
  have hb' : b = a + y := by linarith
  have hc' : c = a + y ^ 2 := by linarith
  exact h a y hy ha (hb' ▸ hb) (hc' ▸ hc)

/-- Translation preserves cardinality. -/
theorem card_image_add (A : Finset ℤ) (t : ℤ) : (A.image fun x => x + t).card = A.card :=
  Finset.card_image_of_injective _ (add_left_injective t)

end NonlinearRoth
