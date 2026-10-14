import Erdos821.P5.LongGrowth

noncomputable section

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem log_two_W_le (x : ℝ) (hL : 1 ≤ L x) : Real.log (2 * W x) ≤ 2 * L x := by
  have hW : 0 < W x := Real.exp_pos _
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hW.ne', W, Real.log_exp]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hs : Real.sqrt (L x) ≤ L x := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  linarith

/-- A logarithmic frequency remains large after a bounded logarithmic shift. -/
theorem shifted_frequency_bound (l B C t σ : ℝ) (hl : 2 ≤ l)
    (hBC : C + 2 ≤ B) (hB2 : 2 ≤ B) (hσ : |σ| ≤ l ^ C) (ht : l ^ B ≤ |t|) :
    1 ≤ |t + σ| ∧ |t + σ|⁻¹ ≤ 2 * l ^ (-B) := by
  have hl1 : 1 ≤ l := by linarith
  have hlpos : 0 < l := by linarith
  have hLCpos : 0 < l ^ C := Real.rpow_pos_of_pos hlpos C
  have hBCpow := Real.rpow_le_rpow_of_exponent_le hl1 hBC
  rw [Real.rpow_add hlpos C 2, Real.rpow_two] at hBCpow
  have hsquare : 2 ≤ l ^ 2 := by nlinarith
  have hshift : 2 * l ^ C ≤ l ^ B := by
    have h := mul_le_mul_of_nonneg_left hsquare hLCpos.le
    linarith
  have hBpow := Real.rpow_le_rpow_of_exponent_le hl1 hB2
  rw [Real.rpow_two] at hBpow
  have htri : |t| ≤ |t + σ| + |σ| := by simpa using abs_add_le (t + σ) (-σ)
  have hu : l ^ B / 2 ≤ |t + σ| := by linarith
  have hu1 : 1 ≤ |t + σ| := by nlinarith
  refine ⟨hu1, ?_⟩
  calc
    _ ≤ (l ^ B / 2)⁻¹ := inv_anti₀ (by positivity) hu
    _ = _ := by rw [Real.rpow_neg hlpos.le]; simp [div_eq_mul_inv]

end Erdos821.P5Core
