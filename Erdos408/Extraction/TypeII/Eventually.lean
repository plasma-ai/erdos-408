module

public import Erdos408.Extraction.TypeII.Assembly

/-!
# The facts at large `x`

Each field of `LargeX` holds for all large `x`: they are comparisons between fixed powers of
`L`, `T` and `s`, all following from `s^k = o(T)` and `T^A = o(L^ε)`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real Filter

/-- `C ≤ L^a` eventually, for `a > 0`. -/
theorem eventually_le_log_rpow (a C : ℝ) (ha : 0 < a) :
    ∀ᶠ x : ℝ in atTop, C ≤ Real.log x ^ a :=
  tendsto_log_atTop.eventually ((tendsto_rpow_atTop ha).eventually_ge_atTop C)

/-- The cluster layout: `2 (|C_N| s + 2) K ≤ 0.04 T`. -/
theorem eventually_lay (K : ℕ) (CN : ℝ) :
    ∀ᶠ x : ℝ in atTop, 2 * (|CN| * logLogLog x + 2) * K ≤ 4 / 100 * logLog x := by
  filter_upwards [eventually_sq_le_logLog (50 * K * (|CN| + 2)) 1 one_pos,
    eventually_le_logLogLog 0] with x hx hs
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : |CN| * logLogLog x + 2 ≤ (|CN| + 2) * (logLogLog x ^ 2 + 1) := by
    nlinarith [abs_nonneg CN, sq_nonneg (logLogLog x - 1)]
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 50 * (K : ℝ) by positivity)
  nlinarith

/-- Band primes are below the slots: `exp(2 L^{0.19}) ≤ x^{c/T²⁰}`. -/
theorem eventually_small (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.exp (2 * Real.log x ^ (19 / 100 : ℝ)) ≤ x ^ (c / logLog x ^ 20) := by
  filter_upwards [eventually_logLog_rpow_le 20 (1 / 100) (by norm_num),
    eventually_log_rpow_le_mul (20 / 100) 1 (c / 2) (by norm_num) (by positivity),
    eventually_le_log 1, eventually_le_logLog 1, eventually_gt_atTop 0]
    with x h1 h2 hL hT hx
  rw [Real.rpow_def_of_pos hx, Real.exp_le_exp]
  have hL0 : 0 < Real.log x := by linarith
  have hT20 : 0 < logLog x ^ (20 : ℕ) := by positivity
  rw [Real.rpow_one] at h2
  rw [show logLog x ^ (20 : ℝ) = logLog x ^ (20 : ℕ) by norm_cast] at h1
  rw [mul_div_assoc', le_div_iff₀ hT20]
  have h3 : Real.log x ^ (19 / 100 : ℝ) * Real.log x ^ (1 / 100 : ℝ) =
      Real.log x ^ (20 / 100 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * Real.log x ^ (19 / 100 : ℝ) by
    positivity)
  nlinarith

/-- `1/c₃ ≤ T⁴`. -/
theorem eventually_Tc (c₃ : ℝ) (hc₃ : 0 < c₃) :
    ∀ᶠ x : ℝ in atTop, 1 / c₃ ≤ logLog x ^ (4 : ℕ) := by
  filter_upwards [eventually_le_logLog ((1 / c₃) ^ (1 / 4 : ℝ) + 1)] with x hx
  have h1 : (1 / c₃) ^ (1 / 4 : ℝ) ≤ logLog x := by linarith
  calc 1 / c₃ = ((1 / c₃) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    _ ≤ logLog x ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) h1 _

/-- `2 b (s + 1) + 4 ≤ L^{1/2}`. -/
theorem eventually_jY (b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ x : ℝ in atTop, 2 * (b * (logLogLog x + 1)) + 4 ≤ Real.log x ^ (1 / 2 : ℝ) := by
  filter_upwards [eventually_sq_le_logLog (4 * b + 4) 1 one_pos,
    eventually_logLog_rpow_le 1 (1 / 2) (by norm_num), eventually_le_logLogLog 0,
    eventually_le_log 1] with x h1 h2 hs hL
  have hT : logLog x ^ (1 : ℝ) = logLog x := Real.rpow_one _
  rw [hT] at h2
  have h3 : 2 * (b * (logLogLog x + 1)) + 4 ≤ (4 * b + 4) * (logLogLog x ^ 2 + 1) := by
    nlinarith [sq_nonneg (logLogLog x - 1)]
  linarith

/-- `C ≤ L / T^{25}`. -/
theorem eventually_le_div (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C ≤ Real.log x / logLog x ^ 25 := by
  filter_upwards [eventually_logLog_rpow_le 25 (1 / 2) (by norm_num),
    eventually_le_log_rpow (1 / 2) C (by norm_num), eventually_le_log 1,
    eventually_le_logLog 1] with x h1 h2 hL hT
  have hL0 : 0 < Real.log x := by linarith
  rw [show logLog x ^ (25 : ℝ) = logLog x ^ (25 : ℕ) by norm_cast] at h1
  rw [le_div_iff₀ (by positivity)]
  have h3 : Real.log x ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hL0]; norm_num
  rcases le_or_gt C 0 with hC | hC
  · have : 0 ≤ Real.log x := hL0.le
    nlinarith [pow_pos (show (0 : ℝ) < logLog x by linarith) 25]
  · have := mul_le_mul h2 h1 (by positivity) (by positivity)
    linarith

/-- `C ≤ T^{-21} L`. -/
theorem eventually_le_gammaL (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C ≤ logLog x ^ (-21 : ℝ) * Real.log x := by
  filter_upwards [eventually_logLog_rpow_le 21 (1 / 2) (by norm_num),
    eventually_le_log_rpow (1 / 2) C (by norm_num), eventually_le_log 1,
    eventually_le_logLog 1] with x h1 h2 hL hT
  have hL0 : 0 < Real.log x := by linarith
  have hT0 : 0 < logLog x := by linarith
  rw [Real.rpow_neg hT0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  have h3 : Real.log x ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hL0]; norm_num
  rcases le_or_gt C 0 with hC | hC
  · have : 0 < logLog x ^ (21 : ℝ) := by positivity
    nlinarith
  · have := mul_le_mul h2 h1 (by positivity) (by positivity)
    linarith

/-- `L³ ≤ κ x`. -/
theorem eventually_L3 (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 3 ≤ κ * x := by
  filter_upwards [eventually_mul_log_rpow_le (1 / κ) 3 1 one_pos, eventually_ge_atTop 1]
    with x hx hx1
  rw [Real.rpow_one, show Real.log x ^ (3 : ℝ) = Real.log x ^ (3 : ℕ) by norm_cast] at hx
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hκ] at hx
  linarith

/-- `⌊κ x + 1⌋ + 1 ≤ x²`. -/
theorem eventually_N2 (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, (⌊κ * x + 1⌋₊ : ℝ) + 1 ≤ x ^ 2 := by
  filter_upwards [eventually_ge_atTop (κ + 2)] with x hx
  have h1 := Nat.floor_le (show 0 ≤ κ * x + 1 by nlinarith)
  nlinarith

/-- The Rankin comparison
`2e (log(L^{0.45}/log 2) + E/log 2 + 1/2) + log(L/T²⁵/c₃) ≤ T^{-21} L^{0.55}`. -/
theorem eventually_rank (E c₃ : ℝ) (hc₃ : 0 < c₃) :
    ∀ᶠ x : ℝ in atTop, 2 * Real.exp 1 * (Real.log (Real.log x ^ (45 / 100 : ℝ) / Real.log 2) +
        E / Real.log 2 + 1 / 2) + Real.log (Real.log x / logLog x ^ 25 / c₃) ≤
      logLog x ^ (-21 : ℝ) * Real.log x ^ (55 / 100 : ℝ) := by
  set D := 2 * Real.exp 1 * (3 + |E| / Real.log 2) + 2 + |Real.log c₃| with hD
  filter_upwards [eventually_logLog_rpow_le 22 (1 / 2) (by norm_num),
    eventually_le_log_rpow (5 / 100) D (by norm_num), eventually_le_log 2,
    eventually_le_logLog 1] with x h1 h2 hL hT
  set L := Real.log x
  set T := logLog x
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hll2 : -1 ≤ Real.log (Real.log 2) := by
    have h12 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h := Real.log_le_log (by norm_num) h12
    rw [one_div, Real.log_inv] at h
    linarith
  -- the left side is at most `D T`
  have hA : Real.log (L ^ (45 / 100 : ℝ) / Real.log 2) ≤ T + 1 := by
    rw [Real.log_div (by positivity) hl2.ne', Real.log_rpow hL0]
    have hTL : Real.log L = T := rfl
    rw [hTL]
    have : (45 / 100 : ℝ) * T ≤ T := by nlinarith
    linarith
  have hB : Real.log (L / T ^ 25 / c₃) ≤ T + |Real.log c₃| := by
    have hT25 : 1 ≤ T ^ 25 := one_le_pow₀ hT
    have hpos : 0 < L / T ^ 25 / c₃ := by positivity
    have hle : L / T ^ 25 / c₃ ≤ L / c₃ :=
      div_le_div_of_nonneg_right (div_le_self hL0.le hT25) hc₃.le
    calc Real.log (L / T ^ 25 / c₃) ≤ Real.log (L / c₃) := Real.log_le_log hpos hle
      _ = T - Real.log c₃ := Real.log_div hL0.ne' hc₃.ne'
      _ ≤ T + |Real.log c₃| := by linarith [neg_abs_le (Real.log c₃)]
  have hE : E / Real.log 2 ≤ |E| / Real.log 2 :=
    div_le_div_of_nonneg_right (le_abs_self E) hl2.le
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hLHS : 2 * Real.exp 1 * (Real.log (L ^ (45 / 100 : ℝ) / Real.log 2) + E / Real.log 2 +
      1 / 2) + Real.log (L / T ^ 25 / c₃) ≤ D * T := by
    have h1' : Real.log (L ^ (45 / 100 : ℝ) / Real.log 2) + E / Real.log 2 + 1 / 2 ≤
        (3 + |E| / Real.log 2) * T := by
      have : 0 ≤ |E| / Real.log 2 := by positivity
      nlinarith
    have h2' := mul_le_mul_of_nonneg_left h1' (show 0 ≤ 2 * Real.exp 1 by positivity)
    have : |Real.log c₃| ≤ |Real.log c₃| * T := le_mul_of_one_le_right (abs_nonneg _) hT
    rw [hD]
    nlinarith
  -- the right side is at least `D T`
  have hRHS : D * T ≤ T ^ (-21 : ℝ) * L ^ (55 / 100 : ℝ) := by
    rw [Real.rpow_neg hT0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    have e : T * T ^ (21 : ℝ) = T ^ (22 : ℝ) := by
      rw [← Real.rpow_one_add' hT0.le (by norm_num)]; norm_num
    have e2 : L ^ (5 / 100 : ℝ) * L ^ (1 / 2 : ℝ) ≤ L ^ (55 / 100 : ℝ) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    calc D * T * T ^ (21 : ℝ) = D * T ^ (22 : ℝ) := by rw [mul_assoc, e]
      _ ≤ L ^ (5 / 100 : ℝ) * L ^ (1 / 2 : ℝ) := mul_le_mul h2 h1 (by positivity) (by positivity)
      _ ≤ L ^ (55 / 100 : ℝ) := e2
  linarith

/-- `b (s + 1) + 1 ≤ L^{1/200}`. -/
theorem eventually_F3 (b : ℝ) (hb : 0 ≤ b) :
    ∀ᶠ x : ℝ in atTop, b * (logLogLog x + 1) + 1 ≤ Real.log x ^ (1 / 200 : ℝ) := by
  filter_upwards [eventually_exp_le_log_rpow (2 * b + 2) (1 / 200) (by norm_num),
    eventually_le_logLogLog 0] with x hx hs
  refine le_trans ?_ hx
  have h1 : b * (logLogLog x + 1) + 1 ≤ (2 * b + 2) * (logLogLog x ^ 2 + 1) := by
    nlinarith [sq_nonneg (logLogLog x - 1)]
  linarith [Real.add_one_le_exp ((2 * b + 2) * (logLogLog x ^ 2 + 1))]

/-- Every field of `LargeX` holds for large `x`. -/
theorem eventually_largeX {q : ℝ} {K : ℕ} {CN c Ch Cj κ CΦ C₂ c₃ C₁r E₂ L₀ EM1 EM2 : ℝ}
    (hc : 0 < c) (hκ : 1 < κ) (hc₃ : 0 < c₃)
    (hbox : ∀ᶠ x : ℝ in atTop, BoxBound q K c Ch Cj κ C₂ x) :
    ∀ᶠ x : ℝ in atTop, LargeX q K CN c Ch Cj κ CΦ C₂ c₃ C₁r E₂ L₀ EM1 EM2 x := by
  have hκ0 : 0 < κ := by linarith
  have hb : (0 : ℝ) ≤ |Cj| + 1 := by positivity
  filter_upwards [hbox, eventually_ge_atTop (4 * κ + 4), eventually_le_log 16,
    eventually_le_log L₀, eventually_le_logLog 50, eventually_le_logLogLog 1,
    eventually_presieveExponent_bounds c Ch hc, eventually_lay K CN, eventually_small c hc,
    eventually_logLog_rpow_le 21 (72 / 100) (by norm_num),
    eventually_logLog_rpow_le 25 (1 / 2) (by norm_num), eventually_Tc c₃ hc₃,
    eventually_jY (|Cj| + 1) hb, eventually_N2 κ hκ0, eventually_L3 κ hκ0,
    eventually_le_div C₁r, eventually_le_gammaL EM2, eventually_le_div EM2,
    eventually_le_log_rpow (45 / 100) EM1 (by norm_num), eventually_rank EM2 c₃ hc₃,
    eventually_le_log_rpow (28 / 100) 2 (by norm_num),
    eventually_exp_pow_le_log_rpow 3 (2 * (|Cj| + 1) + 216 * (|Cj| + 1) ^ 2) (1 / 200)
      (by norm_num),
    eventually_exp_le_log_rpow (endExp q K CN c E₂) (1 / 200) (by norm_num),
    eventually_F3 (|Cj| + 1) hb,
    eventually_logLog_rpow_le (CΦ * 1) (1 / 200) (by norm_num),
    eventually_logLog_rpow_le 42 (1 / 200) (by norm_num)]
    with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
      h24 h25 h26
  exact ⟨h1, h2, h3, h4, h5, h6, h7.1, h7.2, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, h25, h26⟩

end Erdos408.TypeII
