import Mathlib

set_option autoImplicit false

namespace Erdos821.S34Core

noncomputable section

def bilinearDecay (U V r : ℝ) : ℝ :=
  1 / V + 1 / r + Real.log (2 * r) / U + r * Real.log (2 * r) / (U * V)

theorem bilinear_scale_sqrt_bound (U V r H : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hr : 1 ≤ r) (hH : 0 ≤ H) :
    Real.sqrt (2 * H / U) * Real.sqrt (2 * H / V) *
        Real.sqrt (U + (1 + V / r) * (U + r * Real.log (2 * r))) ≤
      4 * H * Real.sqrt (bilinearDecay U V r) := by
  let F := U + (1 + V / r) * (U + r * Real.log (2 * r))
  have hrpos : 0 < r := by linarith
  have hlog : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hUV : 0 < U * V := mul_pos hU hV
  have he : F / (U * V) = 2 / V + 1 / r + Real.log (2 * r) / U + r * Real.log (2 * r) / (U * V) := by
    dsimp [F]
    field_simp
    ring
  have hB : F / (U * V) ≤ 4 * bilinearDecay U V r := by
    rw [he]
    rw [show 2 / V = 2 * (1 / V) by ring]
    unfold bilinearDecay
    have h1 : 0 ≤ 1 / r := by positivity
    have h2 : 0 ≤ Real.log (2 * r) / U := div_nonneg hlog hU.le
    have h3 : 0 ≤ r * Real.log (2 * r) / (U * V) := by positivity
    have h4 : 0 ≤ 1 / V := by positivity
    linarith
  have heq : Real.sqrt (2 * H / U) * Real.sqrt (2 * H / V) * Real.sqrt F =
      2 * H * Real.sqrt (F / (U * V)) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * H / U),
      ← Real.sqrt_mul (by positivity : 0 ≤ (2 * H / U) * (2 * H / V))]
    have ha : (2 * H / U) * (2 * H / V) * F = (2 * H) ^ 2 * (F / (U * V)) := by ring
    rw [ha, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * H)]
  change Real.sqrt (2 * H / U) * Real.sqrt (2 * H / V) * Real.sqrt F ≤ _
  rw [heq]
  calc
    _ ≤ 2 * H * Real.sqrt (4 * bilinearDecay U V r) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) (by positivity)
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num; ring

theorem bilinear_decay_minor_bound (U V r Q S Y : ℝ)
    (hU : 0 < U) (hV : 0 < V) (hr : 1 ≤ r) (hQ : 0 < Q) (hS : 0 < S)
    (hY : 0 ≤ Y) (hrQ : Q < r) (hrS : r ≤ U * V / S)
    (hlog : Real.log (2 * r) ≤ Y) :
    bilinearDecay U V r ≤ 1 / V + 1 / Q + Y / U + Y / S := by
  have hrpos : 0 < r := by linarith
  have hlog0 : 0 ≤ Real.log (2 * r) := Real.log_nonneg (by linarith)
  unfold bilinearDecay
  apply add_le_add
  · exact add_le_add (add_le_add (le_refl _) (one_div_le_one_div_of_le hQ hrQ.le))
      (div_le_div_of_nonneg_right hlog hU.le)
  · have hnum := mul_le_mul hrS hlog hlog0 (by positivity : 0 ≤ U * V / S)
    calc
      _ ≤ (U * V / S) * Y / (U * V) := div_le_div_of_nonneg_right hnum (mul_pos hU hV).le
      _ = _ := by field_simp

end
end Erdos821.S34Core
