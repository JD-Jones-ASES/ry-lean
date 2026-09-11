import Mathlib

/-!
# Definitions

The five definitions the Challenge fixes (`ConfigFree`, `exponent`, `younisExponent`,
`recordExponent`, `D`), followed by the definitions the construction needs: base-`m`
digits, the digit-set construction `blockSet`, and the digit rule (`phase`, `typ`,
`ruleSet`) together with its sizes (`sizeAt`, `period`, `alpha`, `beta`, `blockCard`).
-/

namespace NonlinearRoth

/-! ## The Challenge's definitions -/

/-- `A` contains no configuration `{x, x + y, x + y²}` with `y ≠ 0`. -/
def ConfigFree (A : Finset ℤ) : Prop :=
  ∀ x y : ℤ, y ≠ 0 → x ∈ A → x + y ∈ A → x + y ^ 2 ∈ A → False

/-- The exponent attached to a modulus `m` and digit sets of sizes `a` and `b`:
`1/2 + log a / (3 log m) + log b / (6 log m)`. -/
noncomputable def exponent (m a b : ℕ) : ℝ :=
  1 / 2 + Real.log a / (3 * Real.log m) + Real.log b / (6 * Real.log m)

/-- Younis's exponent, from the data `m = 65`, `|R₁| = 7`, `|R₂| = 17`: `0.76850…`. -/
noncomputable def younisExponent : ℝ := exponent 65 7 17

/-- The exponent of the construction at `m = 145`, `|R₁| = 10`, `|R₂| = 32`: `0.77028…`. -/
noncomputable def recordExponent : ℝ := exponent 145 10 32

/-- The largest size of a configuration-free subset of `{1, …, N}`. -/
noncomputable def D (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℤ, A ⊆ Finset.Icc 1 N ∧ ConfigFree A ∧ A.card = k}

/-! ## Digits -/

/-- The base-`m` digit of `x` at position `i`, with Lean's Euclidean division. -/
def digit (m i : ℕ) (x : ℤ) : ℤ := (x / (m : ℤ) ^ i) % (m : ℤ)

/-- `blockSet m S Y` is the set of integers `∑_{i < Y} dᵢ mⁱ` with `dᵢ ∈ S i`. The top digit
is peeled off first, so the recursion adds position `Y` to `blockSet m S Y ⊆ [0, m^Y)`. -/
def blockSet (m : ℕ) (S : ℕ → Finset ℤ) : ℕ → Finset ℤ
  | 0 => {0}
  | Y + 1 => (S Y ×ˢ blockSet m S Y).image fun p => p.1 * (m : ℤ) ^ Y + p.2

/-- The residues of `R` as integer digits in `[0, m)`. -/
def digitsOf {m : ℕ} (R : Finset (ZMod m)) : Finset ℤ := R.image fun r => (r.val : ℤ)

/-- Every residue as an integer digit in `[0, m)`; the type-`0` digit set `R₀ = ℤ/m`. -/
def allDigits (m : ℕ) : Finset ℤ := (Finset.range m).image fun d : ℕ => (d : ℤ)

/-! ## The digit rule

`phase s t` is Younis's `h` truncated at depth `s`: the type of an *odd* position seen at
phase `t`, with every phase `≥ 2s+1` collapsed to type `1`. `typ s t i` is `f_s t i`; the
rule the construction uses is `typ s 0`. Writing `v` for the `2`-adic valuation,
`typ s t i = phase s (t + v i)` away from `i = 0`, which agrees with Younis's rule (2.1) at
`k = 2` on positions with `v i ≤ 2s` — odd positions have type `0`, position `0` has type `1`,
and an even `i ≥ 2` has type `1` or `2` according to the parity of `v i` — while positions with
`v i ≥ 2s + 1` are collapsed to type `1`. -/

/-- `h_s t`: the digit type of an odd position at phase `t`, truncated at depth `s`. -/
def phase (s t : ℕ) : ℕ :=
  if 2 * s + 1 ≤ t then 1 else if t = 0 then 0 else if t % 2 = 1 then 1 else 2

/-- `f_s t i`: the digit type of position `i` at phase `t`, truncated at depth `s`. -/
def typ (s t i : ℕ) : ℕ := if i = 0 then 1 else phase s (t + padicValNat 2 i)

/-- The digit set at position `i` of the phase-`0` rule: `ℤ/m`, `R₁` or `R₂`. -/
def ruleSet {m : ℕ} (R₁ R₂ : Finset (ZMod m)) (s i : ℕ) : Finset ℤ :=
  if typ s 0 i = 0 then allDigits m else if typ s 0 i = 1 then digitsOf R₁ else digitsOf R₂

/-- The size of the digit set at position `i` in phase `t`, for digit sets of sizes
`m`, `a`, `b`. -/
def sizeAt (m a b s t i : ℕ) : ℕ :=
  if typ s t i = 0 then m else if typ s t i = 1 then a else b

/-- The period of the depth-`s` rule: `2 ^ (2s+1) = 2 · 4 ^ s`. -/
def period (s : ℕ) : ℕ := 2 ^ (2 * s + 1)

/-- `β_s = (4 ^ s − 1) / 3`, the exponent of `b` in one period. -/
def beta : ℕ → ℕ
  | 0 => 0
  | s + 1 => 4 * beta s + 1

/-- `α_s = (2 · 4 ^ s + 1) / 3`, the exponent of `a` in one period. -/
def alpha (s : ℕ) : ℕ := 2 * beta s + 1

/-- `K_s = m ^ (4 ^ s) · a ^ α_s · b ^ β_s`: the number of digit strings in one period. -/
def blockCard (m a b s : ℕ) : ℕ := m ^ 4 ^ s * a ^ alpha s * b ^ beta s

end NonlinearRoth
