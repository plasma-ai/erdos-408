import Erdos408.Extraction.Defs

/-!
# Scale comparisons

The comparisons between `L = log x`, `T = log L` and `s = log T` used in
E6–E8: `s = o(T)`, every fixed power of `T` is at most every fixed positive
power of `L`, and `exp(-L^a)` is below every fixed negative power of `L`.
-/

namespace Erdos408

open Filter Real

/-- `T = log log x → ∞`. -/
lemma tendsto_logLog_atTop : Tendsto logLog atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_atTop

/-- Eventually `T ≥ C`. -/
lemma eventually_le_logLog (C : ℝ) : ∀ᶠ x : ℝ in atTop, C ≤ logLog x :=
  tendsto_logLog_atTop.eventually_ge_atTop C

/-- Eventually `L ≥ C`. -/
lemma eventually_le_log (C : ℝ) : ∀ᶠ x : ℝ in atTop, C ≤ Real.log x :=
  tendsto_log_atTop.eventually_ge_atTop C

/-- `s = o(T)`: eventually `D s ≤ ε T`. -/
lemma eventually_mul_logLogLog_le (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, D * logLogLog x ≤ ε * logLog x := by
  have h := (isLittleO_log_id_atTop.bound (c := ε / (|D| + 1)) (by positivity))
  filter_upwards [tendsto_logLog_atTop.eventually h, eventually_le_logLog 1] with x hx hT
  simp only [norm_eq_abs, id] at hx
  rw [abs_of_pos (show 0 < logLog x by linarith)] at hx
  have hs : |logLogLog x| ≤ ε / (|D| + 1) * logLog x := by
    rw [logLogLog]
    exact hx
  calc D * logLogLog x ≤ |D| * |logLogLog x| := by
        rw [← abs_mul]
        exact le_abs_self _
    _ ≤ (|D| + 1) * (ε / (|D| + 1) * logLog x) := by
        gcongr
        linarith
    _ = ε * logLog x := by field_simp

/-- Every fixed power of `T` is eventually at most every fixed positive power
of `L`. -/
lemma eventually_logLog_rpow_le (D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, logLog x ^ D ≤ Real.log x ^ δ := by
  filter_upwards [eventually_mul_logLogLog_le D hδ, eventually_le_logLog 1,
    eventually_le_log 1] with x hx hT hL
  rw [rpow_def_of_pos (by linarith), rpow_def_of_pos (by linarith)]
  refine exp_le_exp.2 ?_
  rw [mul_comm, mul_comm (Real.log (Real.log x))]
  exact hx

/-- `exp(-L^a)` is eventually below every fixed negative power of `L`. -/
lemma eventually_exp_neg_rpow_le {a : ℝ} (ha : 0 < a) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-(Real.log x ^ a)) ≤ Real.log x ^ (-D) := by
  filter_upwards [eventually_le_logLog (2 * |D| / a ^ 2 + 1), eventually_le_log 1] with x hT hL
  have hT0 : 0 < logLog x := by
    have : 0 ≤ 2 * |D| / a ^ 2 := by positivity
    linarith
  rw [rpow_def_of_pos (by linarith), rpow_def_of_pos (by linarith), mul_comm _ a,
    mul_comm _ (-D)]
  refine exp_le_exp.2 ?_
  -- `L^a = exp(a T) ≥ (a T)² / 2 ≥ |D| T`
  have hq := quadratic_le_exp_of_nonneg (show 0 ≤ a * logLog x by positivity)
  have h1 : |D| * logLog x ≤ (a * logLog x) ^ 2 / 2 := by
    have h2 : 2 * |D| / a ^ 2 ≤ logLog x := by linarith
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith [abs_nonneg D]
  have h3 : -D * logLog x ≥ -(|D| * logLog x) := by
    nlinarith [le_abs_self D]
  have h4 : 0 ≤ a * logLog x := by positivity
  rw [logLog] at *
  nlinarith

/-- `s³ = o(T)`: eventually `D (s + 1)³ ≤ T`. -/
lemma eventually_mul_logLogLog_cube_le (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, D * (logLogLog x + 1) ^ 3 ≤ logLog x := by
  filter_upwards [eventually_le_logLog ((125 * |D| + 1) ^ 4)] with x hT
  set T := logLog x
  have hD1 : 1 ≤ 125 * |D| + 1 := by linarith [abs_nonneg D]
  have hT1 : 1 ≤ T := le_trans (one_le_pow₀ hD1) hT
  have hT0 : 0 < T := by linarith
  set q := T ^ (1 / 4 : ℝ) with hqdef
  have hq1 : 1 ≤ q := one_le_rpow hT1 (by norm_num)
  have hq4 : q ^ 4 = T := by
    rw [hqdef, ← rpow_natCast, ← rpow_mul hT0.le]
    norm_num
  have hs : logLogLog x ≤ 4 * q := by
    have := Real.log_le_rpow_div hT0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [logLogLog]
    rw [hqdef]
    linarith
  have hs0 : 0 ≤ logLogLog x := Real.log_nonneg hT1
  have hqD : 125 * |D| + 1 ≤ q := by
    by_contra h
    push Not at h
    have : q ^ 4 < (125 * |D| + 1) ^ 4 := pow_lt_pow_left₀ h (by linarith) (by norm_num)
    linarith
  calc D * (logLogLog x + 1) ^ 3 ≤ |D| * (5 * q) ^ 3 := by
        have h1 : (logLogLog x + 1) ^ 3 ≤ (5 * q) ^ 3 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 3
        have h2 : D * (logLogLog x + 1) ^ 3 ≤ |D| * (logLogLog x + 1) ^ 3 :=
          mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity)
        exact h2.trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg D))
    _ = 125 * |D| * q ^ 3 := by ring
    _ ≤ q * q ^ 3 := by gcongr; linarith
    _ = T := by rw [← hq4]; ring

end Erdos408
