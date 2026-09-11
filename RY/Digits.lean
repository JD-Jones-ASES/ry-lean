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
  sorry

/-- `digit m i x` reduces mod `m` to `x / m ^ i`. -/
theorem cast_digit (m i : ℕ) (x : ℤ) :
    ((digit m i x : ℤ) : ZMod m) = ((x / (m : ℤ) ^ i : ℤ) : ZMod m) := by
  sorry

/-! ## The shape of `blockSet` -/

/-- Every element of `blockSet m S Y` is nonnegative. -/
theorem blockSet_nonneg (m : ℕ) (S : ℕ → Finset ℤ) (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d) (Y : ℕ) :
    ∀ x ∈ blockSet m S Y, 0 ≤ x := by
  sorry

/-- Every element of `blockSet m S Y` is less than `m ^ Y`. -/
theorem blockSet_lt (m : ℕ) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) :
    ∀ x ∈ blockSet m S Y, x < (m : ℤ) ^ Y := by
  sorry

/-- The digit of an element of `blockSet m S Y` at a position below `Y` lies in the
prescribed digit set. -/
theorem digit_mem (m : ℕ) (hm : 0 < m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) (x : ℤ) (hx : x ∈ blockSet m S Y)
    (i : ℕ) (hi : i < Y) : digit m i x ∈ S i := by
  sorry

/-- The base-`m` expansion is injective on digit strings, so `blockSet` has the expected
cardinality. -/
theorem blockSet_card (m : ℕ) (hm : 0 < m) (S : ℕ → Finset ℤ)
    (hS : ∀ i, ∀ d ∈ S i, 0 ≤ d ∧ d < (m : ℤ)) (Y : ℕ) :
    (blockSet m S Y).card = ∏ i ∈ Finset.range Y, (S i).card := by
  sorry

/-! ## Utilities -/

/-- The maximal power of `m` dividing a nonzero integer, together with the bound
`m ^ ℓ ≤ |y|` that turns `|y| < m ^ Y` into `ℓ < Y`. -/
theorem exists_maximal_pow_dvd (m : ℕ) (hm : 2 ≤ m) (y : ℤ) (hy : y ≠ 0) :
    ∃ ℓ : ℕ, (m : ℤ) ^ ℓ ∣ y ∧ ¬ (m : ℤ) ^ (ℓ + 1) ∣ y ∧ (m : ℤ) ^ ℓ ≤ |y| := by
  sorry

/-- Translation preserves `ConfigFree`. -/
theorem configFree_image_add (A : Finset ℤ) (t : ℤ) (h : ConfigFree A) :
    ConfigFree (A.image fun x => x + t) := by
  sorry

/-- Translation preserves cardinality. -/
theorem card_image_add (A : Finset ℤ) (t : ℤ) : (A.image fun x => x + t).card = A.card :=
  Finset.card_image_of_injective _ (add_left_injective t)

end NonlinearRoth
