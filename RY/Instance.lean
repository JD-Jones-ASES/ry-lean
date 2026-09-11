import RY.Defs

/-!
# The instance at `m = 145`

`145 = 5 · 29` is square-free, and

`R₁ = {0, 48, 55, 62, 69, 76, 117, 124, 131, 138}` (ten residues),
`R₂ = {3, 12, 13, 16, 21, 24, 25, 34, 35, 38, 43, 46, 47, 56, 57, 60, 68, 69, 78, 79,
       82, 91, 100, 104, 113, 122, 123, 125, 126, 135, 136, 144}` (thirty-two residues)

satisfy the two hypotheses. Both are checked by `decide`, but not in the quantified form:
the direct check of the second hypothesis is `32 · 32 · 10 · 10 = 102 400` cases and does
not finish. Instead each hypothesis is reduced to a **disjointness of two explicit
finsets** — the nonzero differences of one set against the squares available to the other —
which is a few thousand kernel steps, and a bridging lemma turns that back into the
quantified form. The first hypothesis would survive a direct `decide` (`14 500` cases,
about 12 s); it is done the same way for uniformity and speed.
-/

-- The two `decide` checks below are deep folds over explicit finsets.
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace NonlinearRoth

/-! ## The two finset reformulations -/

/-- The nonzero differences of `R`. -/
def nzDiffs {m : ℕ} (R : Finset (ZMod m)) : Finset (ZMod m) :=
  ((R ×ˢ R).image fun p => p.1 - p.2).erase 0

/-- The squares of differences of `R`. -/
def sqDiffs {m : ℕ} (R : Finset (ZMod m)) : Finset (ZMod m) :=
  (R ×ˢ R).image fun p => (p.1 - p.2) ^ 2

/-- All squares in `ℤ/m`. -/
def allSquares (m : ℕ) [NeZero m] : Finset (ZMod m) :=
  Finset.univ.image fun d : ZMod m => d ^ 2

/-- **Bridge for the first hypothesis.** If no nonzero difference of `R` is a square, then
`R` is square-difference-free in the quantified sense. -/
theorem sqDiffFree_of_disjoint {m : ℕ} [NeZero m] (R : Finset (ZMod m))
    (h : ∀ x ∈ nzDiffs R, x ∉ allSquares m) :
    ∀ a ∈ R, ∀ b ∈ R, ∀ d : ZMod m, a - b = d ^ 2 → a = b := by
  intro a ha b hb d hd
  by_contra hab
  refine h (a - b) ?_ ?_
  · refine Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hab, ?_⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, hd.symm⟩

/-- **Bridge for the second hypothesis.** If no nonzero difference of `R₂` is the square of
a difference of two elements of `R₁`, then the quantified form holds. -/
theorem avoidSqDiffs_of_disjoint {m : ℕ} [NeZero m] (R₁ R₂ : Finset (ZMod m))
    (h : ∀ x ∈ nzDiffs R₂, x ∉ sqDiffs R₁) :
    ∀ a ∈ R₂, ∀ b ∈ R₂, ∀ c ∈ R₁, ∀ d ∈ R₁, a - b = (c - d) ^ 2 → a = b := by
  intro a ha b hb c hc d hd hab
  by_contra hne
  refine h (a - b) ?_ ?_
  · refine Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hne, ?_⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨(c, d), Finset.mem_product.mpr ⟨hc, hd⟩, hab.symm⟩

/-! ## The data -/

/-- `R₁ ⊆ ℤ/145`, ten residues. -/
def R145₁ : Finset (ZMod 145) := {0, 48, 55, 62, 69, 76, 117, 124, 131, 138}

/-- `R₂ ⊆ ℤ/145`, thirty-two residues. -/
def R145₂ : Finset (ZMod 145) :=
  {3, 12, 13, 16, 21, 24, 25, 34, 35, 38, 43, 46, 47, 56, 57, 60, 68, 69, 78, 79,
   82, 91, 100, 104, 113, 122, 123, 125, 126, 135, 136, 144}

theorem R145₁_card : R145₁.card = 10 := by decide

theorem R145₂_card : R145₂.card = 32 := by decide

theorem R145₁_nonempty : R145₁.Nonempty := by decide

theorem R145₂_nonempty : R145₂.Nonempty := by decide

/-- `145 = 5 · 29` is square-free. -/
theorem squarefree_145 : Squarefree 145 := by
  have h : (145 : ℕ) = 5 * 29 := by norm_num
  rw [h, Nat.squarefree_mul_iff]
  exact ⟨by norm_num, (Nat.prime_five).squarefree, (by norm_num : Nat.Prime 29).squarefree⟩

/-! ## The two hypotheses -/

/-- No nonzero difference of `R₁` is a square mod `145`. -/
theorem R145₁_disjoint : ∀ x ∈ nzDiffs R145₁, x ∉ allSquares 145 := by decide

/-- No nonzero difference of `R₂` is the square of a difference of two elements of `R₁`. -/
theorem R145₂_disjoint : ∀ x ∈ nzDiffs R145₂, x ∉ sqDiffs R145₁ := by decide

/-- **(H1)** `R₁` is square-difference-free. -/
theorem hR145₁ : ∀ a ∈ R145₁, ∀ b ∈ R145₁, ∀ d : ZMod 145, a - b = d ^ 2 → a = b :=
  sqDiffFree_of_disjoint R145₁ R145₁_disjoint

/-- **(H2)** No two distinct elements of `R₂` differ by the square of a difference of two
elements of `R₁`. -/
theorem hR145₂ : ∀ a ∈ R145₂, ∀ b ∈ R145₂, ∀ c ∈ R145₁, ∀ d ∈ R145₁,
    a - b = (c - d) ^ 2 → a = b :=
  avoidSqDiffs_of_disjoint R145₁ R145₂ R145₂_disjoint

end NonlinearRoth
