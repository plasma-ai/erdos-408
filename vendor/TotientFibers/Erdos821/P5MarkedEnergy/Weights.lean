import Erdos821.P5MarkedEnergy.WeightedMean

/-! The local-energy weight `(1+|h t|)^(-j)` and the split of its weighted
integral into a medium time range and a weighted tail. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- The weight of `LocalMellinEnergyTask`. -/
def wj (j : ℕ) (h t : ℝ) : ℝ := (1 + |h * t|) ^ (-(j : ℤ))

theorem wj_eq (j : ℕ) (h t : ℝ) : wj j h t = ((1 + |h * t|) ^ j)⁻¹ := by
  unfold wj; rw [zpow_neg, zpow_natCast]

theorem wj_nonneg (j : ℕ) (h t : ℝ) : 0 ≤ wj j h t := by rw [wj_eq]; positivity

theorem wj_le_one (j : ℕ) (h t : ℝ) : wj j h t ≤ 1 := by
  rw [wj_eq]
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [abs_nonneg (h * t)])

theorem wj_le_wt {j : ℕ} (hj : 2 ≤ j) (h t : ℝ) : wj j h t ≤ wt h t := by
  rw [wj_eq]; unfold wt
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by linarith [abs_nonneg (h * t)]) hj

theorem continuous_wj (j : ℕ) (h : ℝ) : Continuous (wj j h) := by
  have : wj j h = fun t => ((1 + |h * t|) ^ j)⁻¹ := funext (wj_eq j h)
  rw [this]
  apply Continuous.inv₀ (by fun_prop)
  intro t; positivity

theorem integrable_wt {h : ℝ} (hh : h ≠ 0) : Integrable (wt h) := by
  refine (integrable_inv_one_add_sq_mul hh).mono' (continuous_wt h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (wt_nonneg h t)]
  exact wt_le_inv_one_add_sq h t

theorem integrable_wj {j : ℕ} (hj : 2 ≤ j) {h : ℝ} (hh : h ≠ 0) : Integrable (wj j h) := by
  refine (integrable_wt hh).mono' (continuous_wj j h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (wj_nonneg j h t)]
  exact wj_le_wt hj h t

/-- Pointwise: beyond `L/h` the weight gains `(1+L)^(4-j)` against the shifted `wt`. -/
theorem wj_le_shift {j : ℕ} (hj : 4 ≤ j) {h L c t : ℝ} (hh : 0 < h) (hL : 1 ≤ L)
    (hc : |c| ≤ L / h) (ht : L / h < |t|) :
    wj j h t ≤ ((1 + L) ^ (j - 4))⁻¹ * wt h (t + c) := by
  rw [wj_eq]; unfold wt
  have hht : L < |h * t| := by
    rw [abs_mul, abs_of_pos hh]
    rwa [div_lt_iff₀ hh, mul_comm] at ht
  have hhc : |h * c| ≤ L := by
    rw [abs_mul, abs_of_pos hh]
    rwa [le_div_iff₀ hh, mul_comm] at hc
  set u := 1 + |h * t| with hu
  have hu2 : 2 ≤ u := by linarith
  have hshift : 1 + |h * (t + c)| ≤ 2 * u := by
    have : |h * (t + c)| ≤ |h * t| + |h * c| := by rw [mul_add]; exact abs_add_le _ _
    linarith
  have hsplit : u ^ j = u ^ (j - 4) * u ^ 4 := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_inv]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply inv_anti₀ (by positivity)
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  · apply inv_anti₀ (by positivity)
    calc (1 + |h * (t + c)|) ^ 2 ≤ (2 * u) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hshift 2
      _ = 4 * u ^ 2 := by ring
      _ ≤ u ^ 4 := by
          have h4 : 4 ≤ u ^ 2 := by nlinarith
          nlinarith [sq_nonneg u]

/-- Split of the weighted integral of a shifted continuous function. -/
theorem wj_integral_split {j : ℕ} (hj : 4 ≤ j) {h L c : ℝ} (hh : 0 < h) (hL : 1 ≤ L)
    (hc : |c| ≤ L / h) (F : ℝ → ℂ) (hF : Continuous F)
    (hFi : Integrable (fun s => wt h s * ‖F s‖ ^ 2)) :
    ∫ t, wj j h t * ‖F (t + c)‖ ^ 2 ≤
      (∫ s in (-(2 * L / h))..(2 * L / h), ‖F s‖ ^ 2) +
        ((1 + L) ^ (j - 4))⁻¹ * ∫ s, wt h s * ‖F s‖ ^ 2 := by
  have hLh : 0 ≤ L / h := by positivity
  set I := Set.Icc (-(L / h)) (L / h) with hI
  let g1 : ℝ → ℝ := I.indicator (fun t => ‖F (t + c)‖ ^ 2)
  let g2 : ℝ → ℝ := fun t => ((1 + L) ^ (j - 4))⁻¹ * (wt h (t + c) * ‖F (t + c)‖ ^ 2)
  have hFc : Continuous (fun t => ‖F (t + c)‖ ^ 2) := by fun_prop
  have hg1 : Integrable g1 := (hFc.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hg2 : Integrable g2 := (hFi.comp_add_right c).const_mul _
  have hpt : ∀ t, wj j h t * ‖F (t + c)‖ ^ 2 ≤ g1 t + g2 t := by
    intro t
    have hg1n : 0 ≤ g1 t := by
      simp only [g1, Set.indicator]; split_ifs <;> positivity
    have hg2n : 0 ≤ g2 t := by
      simp only [g2]; have := wt_nonneg h (t + c); positivity
    by_cases ht : |t| ≤ L / h
    · have hmem : t ∈ I := abs_le.mp ht
      have : g1 t = ‖F (t + c)‖ ^ 2 := Set.indicator_of_mem hmem _
      have hw := wj_le_one j h t
      have : wj j h t * ‖F (t + c)‖ ^ 2 ≤ ‖F (t + c)‖ ^ 2 := by
        have := sq_nonneg ‖F (t + c)‖
        nlinarith [wj_nonneg j h t]
      linarith
    · rw [not_le] at ht
      have hw := wj_le_shift hj hh hL hc ht
      have : wj j h t * ‖F (t + c)‖ ^ 2 ≤ g2 t := by
        simp only [g2]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hw (by positivity)
      linarith
  have hmono : ∫ t, wj j h t * ‖F (t + c)‖ ^ 2 ≤ ∫ t, (g1 t + g2 t) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun t =>
      mul_nonneg (wj_nonneg j h t) (by positivity)) (hg1.add hg2)
      (Filter.Eventually.of_forall hpt)
  rw [integral_add hg1 hg2] at hmono
  refine hmono.trans (add_le_add ?_ ?_)
  · simp only [g1]
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_add_right (fun s => ‖F s‖ ^ 2) c]
    have hcabs := abs_le.mp hc
    have h2L : 2 * L / h = L / h + L / h := by ring
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall fun s => by positivity
    · exact (hF.norm.pow 2).intervalIntegrable _ _
  · simp only [g2]
    rw [integral_const_mul]
    apply le_of_eq
    congr 1
    exact integral_add_right_eq_self (fun s => wt h s * ‖F s‖ ^ 2) c

end Erdos821.P5Marked
