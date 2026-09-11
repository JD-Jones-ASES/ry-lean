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
  sorry

end NonlinearRoth
