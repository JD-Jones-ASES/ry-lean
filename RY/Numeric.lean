import RY.Rule

/-!
# Numerics

Every comparison between exponents is a comparison of two logarithms, and each of those is
settled by one integer power comparison. Writing `γ(m, a, b) = 1/2 + log (a²b) / (6 log m)`,
the three numerical statements come from

* `833 ^ 13 < 65 ^ 21` and `145 ^ 21 < 3200 ^ 13` (Younis's exponent `< γ(145,10,32)`),
* `145 ^ 60 < 3200 ^ 37` (`0.7702 < γ`, since `1/2 + 10/37 = 0.77027…`),
* `3200 ^ 230 < 145 ^ 373` (`γ < 0.77029`, since `1/2 + 373/1380 = 0.770289…`).

The file also contains the limit `log K_s / log M_s = γ − (log b − log a) / (6 · 4^s log m)`
and the Archimedean choice of a depth `s` at which that exceeds a given `ρ < γ`.
-/

namespace NonlinearRoth

/-! ## Two translation lemmas -/

/-- `p / q < log a / log b`, from the power comparison `b ^ p < a ^ q`. (`_ha` is unused; it is
kept so that the two translation lemmas have the same signature.) -/
theorem lt_log_div_log (a b : ℝ) (p q : ℕ) (_ha : 2 ≤ a) (hb : 2 ≤ b) (hq : 0 < q)
    (h : b ^ p < a ^ q) : (p : ℝ) / q < Real.log a / Real.log b := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbp : (0 : ℝ) < b ^ p := by positivity
  have h1 : Real.log (b ^ p) < Real.log (a ^ q) := Real.log_lt_log hbp h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_lt_div_iff₀ hqR hlb]
  linarith

/-- `log a / log b < p / q`, from the power comparison `a ^ q < b ^ p`. -/
theorem log_div_log_lt (a b : ℝ) (p q : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hq : 0 < q)
    (h : a ^ q < b ^ p) : Real.log a / Real.log b < (p : ℝ) / q := by
  have hb1 : (1 : ℝ) < b := by linarith
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haq : (0 : ℝ) < a ^ q := by positivity
  have h1 : Real.log (a ^ q) < Real.log (b ^ p) := Real.log_lt_log haq h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_lt_div_iff₀ hlb hqR]
  linarith

/-! ## The four power comparisons -/

/-- `log₆₅ 833 < 21/13`, from `833 ^ 13 < 65 ^ 21`. -/
theorem log833_lt : Real.log 833 / Real.log 65 < (21 : ℝ) / 13 := by
  simpa using log_div_log_lt 833 65 21 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- `21/13 < log₁₄₅ 3200`, from `145 ^ 21 < 3200 ^ 13`. -/
theorem lt_log3200 : (21 : ℝ) / 13 < Real.log 3200 / Real.log 145 := by
  simpa using lt_log_div_log 3200 145 21 13 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- `60/37 < log₁₄₅ 3200`, from `145 ^ 60 < 3200 ^ 37`. -/
theorem lt_log3200' : (60 : ℝ) / 37 < Real.log 3200 / Real.log 145 := by
  simpa using lt_log_div_log 3200 145 60 37 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- `log₁₄₅ 3200 < 373/230`, from `3200 ^ 230 < 145 ^ 373`. (`norm_num` evaluates the left
side and then stalls on `145 ^ 373`; the kernel settles the comparison directly.) -/
theorem log3200_lt : Real.log 3200 / Real.log 145 < (373 : ℝ) / 230 := by
  have h : (3200 : ℕ) ^ 230 < 145 ^ 373 := by decide +kernel
  have h' : (3200 : ℝ) ^ 230 < 145 ^ 373 := by exact_mod_cast h
  simpa using log_div_log_lt 3200 145 373 230 (by norm_num) (by norm_num) (by norm_num) h'

/-! ## The exponent in closed form -/

/-- `exponent m a b = 1/2 + (2 log a + log b) / (6 log m)`. -/
theorem exponent_eq (m a b : ℕ) :
    exponent m a b = 1 / 2 + (2 * Real.log a + Real.log b) / (6 * Real.log m) := by
  unfold exponent
  rcases eq_or_ne (Real.log m) 0 with h | h
  · rw [h]; norm_num
  · field_simp
    ring

/-- `recordExponent = 1/2 + log 3200 / (6 log 145)`, since `10² · 32 = 3200`. -/
theorem recordExponent_eq : recordExponent = 1 / 2 + Real.log 3200 / (6 * Real.log 145) := by
  have h : Real.log 3200 = 2 * Real.log 10 + Real.log 32 := by
    rw [show (3200 : ℝ) = 10 ^ 2 * 32 by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  rw [recordExponent, exponent_eq, h]
  norm_num

/-- `younisExponent = 1/2 + log 833 / (6 log 65)`, since `7² · 17 = 833`. -/
theorem younisExponent_eq : younisExponent = 1 / 2 + Real.log 833 / (6 * Real.log 65) := by
  have h : Real.log 833 = 2 * Real.log 7 + Real.log 17 := by
    rw [show (833 : ℝ) = 7 ^ 2 * 17 by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  rw [younisExponent, exponent_eq, h]
  norm_num

/-! ## The three numerical statements -/

/-- The exponent at `m = 145` exceeds Younis's exponent at `m = 65`. -/
theorem younisExponent_lt_recordExponent : younisExponent < recordExponent := by
  have e1 : Real.log 833 / (6 * Real.log 65) = Real.log 833 / Real.log 65 / 6 := by
    rw [div_div, mul_comm]
  have e2 : Real.log 3200 / (6 * Real.log 145) = Real.log 3200 / Real.log 145 / 6 := by
    rw [div_div, mul_comm]
  rw [younisExponent_eq, recordExponent_eq, e1, e2]
  have h1 := log833_lt
  have h2 := lt_log3200
  linarith

/-- `0.7702 < recordExponent`. -/
theorem recordExponent_lower : (0.7702 : ℝ) < recordExponent := by
  have hlog : (0 : ℝ) < Real.log 145 := Real.log_pos (by norm_num)
  have h1 : (60 : ℝ) / 37 * Real.log 145 < Real.log 3200 := (lt_div_iff₀ hlog).mp lt_log3200'
  have h2 : (10 : ℝ) / 37 < Real.log 3200 / (6 * Real.log 145) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  rw [recordExponent_eq]
  linarith

/-- `recordExponent < 0.77029`. -/
theorem recordExponent_upper : recordExponent < 0.77029 := by
  have hlog : (0 : ℝ) < Real.log 145 := Real.log_pos (by norm_num)
  have h1 : Real.log 3200 < (373 : ℝ) / 230 * Real.log 145 := (div_lt_iff₀ hlog).mp log3200_lt
  have h2 : Real.log 3200 / (6 * Real.log 145) < (373 : ℝ) / 1380 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  rw [recordExponent_eq]
  linarith

/-! ## The exponent of one block, and the choice of depth -/

/-- `α_s` as a real number: `(2 · 4 ^ s + 1) / 3`. -/
theorem alpha_cast (s : ℕ) : ((alpha s : ℕ) : ℝ) = (2 * (4 : ℝ) ^ s + 1) / 3 := by
  have h : (3 : ℝ) * ((alpha s : ℕ) : ℝ) = 2 * (4 : ℝ) ^ s + 1 := by
    exact_mod_cast alpha_spec s
  linarith

/-- `β_s` as a real number: `(4 ^ s − 1) / 3`. -/
theorem beta_cast (s : ℕ) : ((beta s : ℕ) : ℝ) = ((4 : ℝ) ^ s - 1) / 3 := by
  have h : (3 : ℝ) * ((beta s : ℕ) : ℝ) + 1 = (4 : ℝ) ^ s := by
    exact_mod_cast beta_spec s
  linarith

/-- `log K_s = 4 ^ s log m + α_s log a + β_s log b`. -/
theorem log_blockCard (m a b s : ℕ) (hm : 1 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.log ((blockCard m a b s : ℕ) : ℝ)
      = (4 : ℝ) ^ s * Real.log (m : ℝ) + ((alpha s : ℕ) : ℝ) * Real.log (a : ℝ)
        + ((beta s : ℕ) : ℝ) * Real.log (b : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    exact ne_of_gt this
  have ha0 : (a : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    exact ne_of_gt this
  have hb0 : (b : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    exact ne_of_gt this
  simp only [blockCard]
  push_cast
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hm0) (pow_ne_zero _ ha0)) (pow_ne_zero _ hb0),
    Real.log_mul (pow_ne_zero _ hm0) (pow_ne_zero _ ha0), Real.log_pow, Real.log_pow,
    Real.log_pow]
  push_cast
  ring

/-- `log M_s = 2 · 4 ^ s · log m`. -/
theorem log_pow_period (m s : ℕ) :
    Real.log ((m ^ period s : ℕ) : ℝ) = 2 * (4 : ℝ) ^ s * Real.log (m : ℝ) := by
  rw [period_eq]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- `log K_s / log M_s = γ − (log b − log a) / (6 · 4 ^ s · log m)`. -/
theorem blockCard_log_ratio (m a b s : ℕ) (hm : 2 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.log ((blockCard m a b s : ℕ) : ℝ) / Real.log ((m ^ period s : ℕ) : ℝ)
      = exponent m a b
        - (Real.log (b : ℝ) - Real.log (a : ℝ)) / (6 * 4 ^ s * Real.log (m : ℝ)) := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hL : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hL0 : Real.log (m : ℝ) ≠ 0 := ne_of_gt hL
  have h40 : ((4 : ℝ) ^ s) ≠ 0 := by positivity
  rw [log_blockCard m a b s (by omega) ha hb, log_pow_period m s, exponent_eq, alpha_cast,
    beta_cast]
  field_simp
  ring

/-- `n < 4 ^ n`: the Archimedean witness, with no search. -/
theorem lt_four_pow (n : ℕ) : n < 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 4 ^ (k + 1) = 4 ^ k * 4 := pow_succ 4 k
      omega

/-- **The Archimedean step.** Below the exponent there is a depth whose block exponent
already exceeds `ρ`. -/
theorem exists_depth_gt (m a b : ℕ) (hm : 2 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) (ρ : ℝ)
    (hρ : ρ < exponent m a b) :
    ∃ s : ℕ, ρ ≤ Real.log ((blockCard m a b s : ℕ) : ℝ) / Real.log ((m ^ period s : ℕ) : ℝ) := by
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hL : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hE : 0 < exponent m a b - ρ := sub_pos.mpr hρ
  rcases le_or_gt (Real.log (b : ℝ) - Real.log (a : ℝ)) 0 with hd | hd
  · -- The correction term is already `≤ 0` at depth `0`.
    refine ⟨0, ?_⟩
    have hpos : (0 : ℝ) < 6 * (4 : ℝ) ^ (0 : ℕ) * Real.log (m : ℝ) :=
      mul_pos (by positivity) hL
    have hkey : (Real.log (b : ℝ) - Real.log (a : ℝ)) /
        (6 * (4 : ℝ) ^ (0 : ℕ) * Real.log (m : ℝ)) ≤ exponent m a b - ρ := by
      rw [div_le_iff₀ hpos]
      have := mul_pos hE hpos
      linarith
    rw [blockCard_log_ratio m a b 0 hm ha hb]
    linarith
  · -- Choose a depth with `4 ^ s` beyond `(log b − log a) / (6 log m (γ − ρ))`.
    have hden : (0 : ℝ) < 6 * Real.log (m : ℝ) * (exponent m a b - ρ) :=
      mul_pos (by linarith) hE
    obtain ⟨n, hn⟩ :=
      exists_nat_gt ((Real.log (b : ℝ) - Real.log (a : ℝ)) /
        (6 * Real.log (m : ℝ) * (exponent m a b - ρ)))
    have hn4 : (n : ℝ) < (4 : ℝ) ^ n := by exact_mod_cast lt_four_pow n
    have hlt : (Real.log (b : ℝ) - Real.log (a : ℝ)) /
        (6 * Real.log (m : ℝ) * (exponent m a b - ρ)) < (4 : ℝ) ^ n := lt_trans hn hn4
    have h2 := (div_lt_iff₀ hden).mp hlt
    refine ⟨n, ?_⟩
    have hpos : (0 : ℝ) < 6 * (4 : ℝ) ^ n * Real.log (m : ℝ) := mul_pos (by positivity) hL
    have hkey : (Real.log (b : ℝ) - Real.log (a : ℝ)) /
        (6 * (4 : ℝ) ^ n * Real.log (m : ℝ)) ≤ exponent m a b - ρ := by
      rw [div_le_iff₀ hpos]
      nlinarith [h2]
    rw [blockCard_log_ratio m a b n hm ha hb]
    linarith

end NonlinearRoth
