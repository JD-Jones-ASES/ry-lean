import RY.Digits

/-!
# Avoidance

The heart of the construction. Let `u`, `u + y`, `u + y²` all lie in `blockSet m S Y` with
`y ≠ 0`, and let `ℓ` be maximal with `m ^ ℓ ∣ y`, say `y = m ^ ℓ y'`. Since
`|y| < m ^ Y` we have `ℓ < Y`; and if `2 ℓ ≥ Y` then `m ^ Y ≤ m ^ (2ℓ) ≤ |y²| < m ^ Y`,
which is absurd. So `2 ℓ < Y`, and the digit congruence of `RY.Digits` at `(u, u+y, ℓ)`
and at `(u, u+y², 2ℓ)` gives, in `ℤ/m`,

`digit (2ℓ) (u + y²) - digit (2ℓ) u = (digit ℓ (u + y) - digit ℓ u) ²`,

with the two left-hand digits in `S (2ℓ)` and the two right-hand digits in `S ℓ`. The edge
hypothesis forces the left-hand side to vanish, hence `m ∣ y' ^ 2`, hence — and this is the
only place square-freeness is used — `m ∣ y'`, contradicting the maximality of `ℓ`.
-/

namespace NonlinearRoth

/-- **The avoidance theorem.** If `m` is square-free and, for every `ℓ` with `2 ℓ < Y`, no
two elements of `S (2ℓ)` differ by the square of a difference of two elements of `S ℓ` in
`ℤ/m`, then `blockSet m S Y` is configuration-free. -/
theorem blockSet_configFree (m : ℕ) (hm : 2 ≤ m) (hsf : Squarefree m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ)
    (hedge : ∀ ℓ : ℕ, 2 * ℓ < Y →
      ∀ p ∈ S (2 * ℓ), ∀ q ∈ S (2 * ℓ), ∀ c ∈ S ℓ, ∀ d ∈ S ℓ,
        ((p : ZMod m) - (q : ZMod m) = ((c : ZMod m) - (d : ZMod m)) ^ 2) →
          ((p : ZMod m) = (q : ZMod m))) :
    ConfigFree (blockSet m S Y) := by
  intro u y hy hu huy huy2
  have hm0 : 0 < m := by omega
  have hm1 : 1 ≤ m := by omega
  have hm0Z : (m : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
  -- the three points lie in `[0, m ^ Y)`
  have hnn := blockSet_nonneg m S (fun i d hd => (hS i d hd).1) Y
  have hlt := blockSet_lt m S hS Y
  have hu0 : 0 ≤ u := hnn u hu
  have huY : u < (m : ℤ) ^ Y := hlt u hu
  have hv0 : 0 ≤ u + y := hnn _ huy
  have hvY : u + y < (m : ℤ) ^ Y := hlt _ huy
  have hw0 : 0 ≤ u + y ^ 2 := hnn _ huy2
  have hwY : u + y ^ 2 < (m : ℤ) ^ Y := hlt _ huy2
  -- the maximal power of `m` dividing `y`
  obtain ⟨ℓ, hdvd, hndvd, hle⟩ := exists_maximal_pow_dvd m hm y hy
  obtain ⟨y', hy'⟩ := hdvd
  have habs : |y| < (m : ℤ) ^ Y := by
    rw [abs_lt]
    constructor <;> linarith
  have hℓY : ℓ < Y := by
    by_contra hc
    have hc' : Y ≤ ℓ := by omega
    have hmono : (m : ℤ) ^ Y ≤ (m : ℤ) ^ ℓ := natCast_pow_le_pow_of_le hm1 hc'
    linarith
  have hpow2 : (m : ℤ) ^ (2 * ℓ) = ((m : ℤ) ^ ℓ) ^ 2 := pow_mul' (m : ℤ) 2 ℓ
  have hysq : y ^ 2 = (m : ℤ) ^ (2 * ℓ) * y' ^ 2 := by rw [hy', mul_pow, hpow2]
  have hy2pos : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  by_cases h2 : 2 * ℓ < Y
  · -- the digit comparison at positions `ℓ` and `2ℓ`
    have hnm : ¬ (m : ℤ) ∣ y' := by
      rintro ⟨z, hz⟩
      exact hndvd ⟨z, by rw [hy', hz]; ring⟩
    have hD1 := cast_ediv_eq_digit_sub m hm0 ℓ u (u + y)
      ⟨y', by rw [show u + y - u = y by ring]; exact hy'⟩
    have hD2 := cast_ediv_eq_digit_sub m hm0 (2 * ℓ) u (u + y ^ 2)
      ⟨y' ^ 2, by rw [show u + y ^ 2 - u = y ^ 2 by ring]; exact hysq⟩
    have e1 : (u + y - u) / (m : ℤ) ^ ℓ = y' := by
      rw [show u + y - u = y by ring, hy', Int.mul_ediv_cancel_left _ (pow_ne_zero ℓ hm0Z)]
    have e2 : (u + y ^ 2 - u) / (m : ℤ) ^ (2 * ℓ) = y' ^ 2 := by
      rw [show u + y ^ 2 - u = y ^ 2 by ring, hysq,
        Int.mul_ediv_cancel_left _ (pow_ne_zero (2 * ℓ) hm0Z)]
    rw [e1] at hD1
    rw [e2] at hD2
    have hmw : digit m (2 * ℓ) (u + y ^ 2) ∈ S (2 * ℓ) :=
      digit_mem m hm0 S hS Y _ huy2 (2 * ℓ) h2
    have hmu2 : digit m (2 * ℓ) u ∈ S (2 * ℓ) := digit_mem m hm0 S hS Y _ hu (2 * ℓ) h2
    have hmv : digit m ℓ (u + y) ∈ S ℓ := digit_mem m hm0 S hS Y _ huy ℓ hℓY
    have hmu : digit m ℓ u ∈ S ℓ := digit_mem m hm0 S hS Y _ hu ℓ hℓY
    have key : ((digit m (2 * ℓ) (u + y ^ 2) : ℤ) : ZMod m)
          - ((digit m (2 * ℓ) u : ℤ) : ZMod m)
        = (((digit m ℓ (u + y) : ℤ) : ZMod m) - ((digit m ℓ u : ℤ) : ZMod m)) ^ 2 := by
      rw [← hD2, ← hD1]
      push_cast
      ring
    have hzero := hedge ℓ h2 _ hmw _ hmu2 _ hmv _ hmu key
    have hz0 : ((y' ^ 2 : ℤ) : ZMod m) = 0 := by rw [hD2, hzero, sub_self]
    have hdvdsq : (m : ℤ) ∣ y' ^ 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz0
    have hsfZ : Squarefree (m : ℤ) := Int.squarefree_natCast.mpr hsf
    exact hnm ((hsfZ.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp hdvdsq)
  · -- `m ^ (2ℓ)` divides `y²` and already exceeds it
    have h2' : Y ≤ 2 * ℓ := by omega
    have hdvd2 : (m : ℤ) ^ (2 * ℓ) ∣ y ^ 2 := ⟨y' ^ 2, hysq⟩
    have h1 : (m : ℤ) ^ (2 * ℓ) ≤ y ^ 2 := Int.le_of_dvd hy2pos hdvd2
    have h3 : (m : ℤ) ^ Y ≤ (m : ℤ) ^ (2 * ℓ) := natCast_pow_le_pow_of_le hm1 h2'
    linarith

end NonlinearRoth
