import Erdos821.S34.ProductSupport

set_option autoImplicit false
open Filter

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem eventually_power_le_label_scale (A c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, L x ^ A ≤ ε * Real.exp (L x ^ c) := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have ht : Tendsto (fun x => L x ^ c) atTop atTop := (tendsto_rpow_atTop hc).comp hL
  have ho := (isLittleO_rpow_exp_atTop (A / c)).comp_tendsto ht
  have hb := ho.bound hε
  filter_upwards [hb, hL.eventually_gt_atTop 0] with x hx hLx
  have he : (L x ^ c) ^ (A / c) = L x ^ A := by
    rw [← Real.rpow_mul hLx.le]
    congr 1
    field_simp
  change ‖(L x ^ c) ^ (A / c)‖ ≤ ε * ‖Real.exp (L x ^ c)‖ at hx
  rw [he] at hx
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLx A),
    abs_of_pos (Real.exp_pos _)] using hx

theorem eventually_log_count_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, C * T x + 1 ≤ L x := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto hL
  have hε : 0 < 1 / (2 * (C + 1)) := by positivity
  filter_upwards [hsmall.bound hε, hL.eventually_ge_atTop 2] with x hx hLx
  have ht : 0 ≤ T x := Real.log_nonneg (by linarith : 1 ≤ L x)
  have hLpos : 0 < L x := by linarith
  have hb : T x ≤ (1 / (2 * (C + 1))) * L x := by
    change ‖T x‖ ≤ (1 / (2 * (C + 1))) * ‖L x ^ (1 : ℝ)‖ at hx
    simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_pos hLpos] using hx
  have hm := (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp (by
    simpa only [one_div_mul_eq_div] using hb)
  nlinarith

end
end Erdos821.S34Core
