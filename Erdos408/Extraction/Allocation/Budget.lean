import Erdos408.Extraction.Allocation.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The budgets of E6–E8

For large `x`:

* the endpoint bound `|M₀| ((2 T^{20}/c + 1)^3 + T^3)` is at most `L^δ`;
* the number of terms of the signed expansion, at most
  `4^{2T} · 2^K 2^{K + C_N⁺ s}`, is at most `L^4`;
* the candidate-square multiples up to `κ x + 1`, at most
  `(κ x + 1) exp(-L^{0.28}) · 6 T`, number at most `x L^{-D}`.
-/

namespace Erdos408

open Filter Real

/-- The endpoint bound is eventually at most `L^δ`. -/
lemma eventually_endpoint_budget (a : ℝ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop,
      a * ((2 * logLog x ^ 20 / c + 1) ^ 3 + logLog x ^ 3) ≤ Real.log x ^ δ := by
  set β := (2 / c + 1) ^ 3 + 1
  filter_upwards [eventually_logLog_rpow_le 61 hδ, eventually_le_logLog (max 1 (|a| * β))]
    with x hL hT
  set T := logLog x
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  rw [show (61 : ℝ) = ((61 : ℕ) : ℝ) by norm_num, rpow_natCast] at hL
  have h20 : 1 ≤ T ^ 20 := one_le_pow₀ hT1
  have h1 : 2 * T ^ 20 / c + 1 ≤ (2 / c + 1) * T ^ 20 := by
    rw [add_mul, one_mul, mul_comm (2 / c), ← mul_div_assoc, mul_comm (T ^ 20)]
    linarith
  have h2 : (2 * T ^ 20 / c + 1) ^ 3 ≤ (2 / c + 1) ^ 3 * T ^ 60 := by
    calc (2 * T ^ 20 / c + 1) ^ 3 ≤ ((2 / c + 1) * T ^ 20) ^ 3 := by
          gcongr
      _ = (2 / c + 1) ^ 3 * T ^ 60 := by ring
  have h3 : T ^ 3 ≤ T ^ 60 := pow_le_pow_right₀ hT1 (by norm_num)
  have h4 : (2 * T ^ 20 / c + 1) ^ 3 + T ^ 3 ≤ β * T ^ 60 := by
    simp only [β]
    nlinarith
  have h5 : 0 ≤ (2 * T ^ 20 / c + 1) ^ 3 + T ^ 3 := by positivity
  have hβ : |a| * β ≤ T := (le_max_right _ _).trans hT
  calc a * ((2 * T ^ 20 / c + 1) ^ 3 + T ^ 3) ≤ |a| * ((2 * T ^ 20 / c + 1) ^ 3 + T ^ 3) :=
        mul_le_mul_of_nonneg_right (le_abs_self a) h5
    _ ≤ |a| * (β * T ^ 60) := mul_le_mul_of_nonneg_left h4 (abs_nonneg a)
    _ = |a| * β * T ^ 60 := by ring
    _ ≤ T * T ^ 60 := mul_le_mul_of_nonneg_right hβ (by positivity)
    _ = T ^ 61 := by ring
    _ ≤ _ := hL

/-- The number of terms of the signed expansion is eventually at most `L^4`. -/
lemma eventually_terms_budget (K : ℕ) (CN : ℝ) : ∀ᶠ x : ℝ in atTop,
    (4 : ℝ) ^ (2 * logLog x) * (2 ^ K * (2 : ℝ) ^ ((K : ℝ) + max CN 0 * logLogLog x)) ≤
      Real.log x ^ (4 : ℝ) := by
  have hl2 := log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  filter_upwards [eventually_le_logLog (4 * K * Real.log 2 * 2 + 1), eventually_le_log 1,
    eventually_mul_logLogLog_le (max CN 0 * Real.log 2) (show (0 : ℝ) < 1 / 2 by norm_num)]
    with x hT hL hs
  set T := logLog x
  have hL0 : 0 < Real.log x := by linarith
  have hLT : Real.log x = Real.exp T := (exp_log hL0).symm
  rw [hLT, ← exp_mul, rpow_def_of_pos (by norm_num : (0 : ℝ) < 4), ← rpow_natCast (2 : ℝ) K,
    rpow_def_of_pos two_pos, rpow_def_of_pos two_pos, ← exp_add, ← exp_add]
  refine exp_le_exp.2 ?_
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [hl4]
  -- `2 log 4 · T + 2K log 2 + log 2 (K + C s) ≤ 4 T`
  have h1 : Real.log 2 * (2 * T) * 2 ≤ 3 * T := by
    have : 0 ≤ T := by linarith [show (0 : ℝ) ≤ 4 * K * Real.log 2 * 2 by positivity]
    nlinarith
  have h2 : 4 * K * Real.log 2 * 2 ≤ T := by linarith
  nlinarith

/-- The candidate-square multiples are eventually at most `x L^{-D}`. -/
lemma eventually_squares_budget (κ D : ℝ) : ∀ᶠ x : ℝ in atTop,
    (κ * x + 1) * Real.exp (-(Real.log x ^ (28 / 100 : ℝ))) * (6 * logLog x) ≤
      x * Real.log x ^ (-D) := by
  filter_upwards [eventually_exp_neg_rpow_le (show (0 : ℝ) < 28 / 100 by norm_num) (D + 1),
    eventually_logLog_rpow_le 1 (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_le_log ((6 * (|κ| + 1)) ^ 2), eventually_ge_atTop 1, eventually_le_logLog 0]
    with x he hT hL hx hT0
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (by positivity) hL
  rw [rpow_one] at hT
  have hsq : 6 * (|κ| + 1) ≤ Real.log x ^ (1 / 2 : ℝ) := by
    rw [← sqrt_eq_rpow, le_sqrt (by positivity) hL0.le]
    exact hL
  have hhalf : Real.log x ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ) = Real.log x := by
    rw [← rpow_add hL0]
    norm_num
  have hDsplit : Real.log x ^ (-(D + 1)) * Real.log x = Real.log x ^ (-D) := by
    rw [← rpow_add_one hL0.ne']
    ring_nf
  have hκx : κ * x + 1 ≤ (|κ| + 1) * x := by
    nlinarith [le_abs_self κ]
  have hep := exp_pos (-(Real.log x ^ (28 / 100 : ℝ)))
  have hLD := rpow_pos_of_pos hL0 (-(D + 1))
  calc (κ * x + 1) * Real.exp (-(Real.log x ^ (28 / 100 : ℝ))) * (6 * logLog x)
      ≤ ((|κ| + 1) * x) * Real.log x ^ (-(D + 1)) * (6 * Real.log x ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = x * Real.log x ^ (-(D + 1)) * (6 * (|κ| + 1) * Real.log x ^ (1 / 2 : ℝ)) := by ring
    _ ≤ x * Real.log x ^ (-(D + 1)) * (Real.log x ^ (1 / 2 : ℝ) * Real.log x ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = x * Real.log x ^ (-D) := by rw [hhalf, mul_assoc, hDsplit]

end Erdos408
