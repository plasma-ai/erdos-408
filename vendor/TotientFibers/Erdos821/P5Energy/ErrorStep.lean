import Erdos821.P5Energy.Schur

/-! Replacing the additive kernel `K((n-v)/H)` by the dilation kernel `K(v log(n/v)/H)`
on the range `Y/2 ≤ v ≤ 5Y/2`: support, Lipschitz error, counting and integration. -/

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory

namespace Erdos821.P5Energy
open Blueprint.Analytic

theorem kernelRadius_lt : 1 / (8 * Real.pi) < 1 / 4 := by
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [Real.pi_gt_three]

theorem localKernel_eq_zero_of_far (x : ℝ) (hx : 1 / 4 ≤ |x|) : localKernel x = 0 :=
  localKernel_eq_zero_of_radius x (kernelRadius_lt.le.trans hx)

theorem localKernel_continuous : Continuous localKernel := localKernel_contDiff.continuous

theorem localKernel_lipschitz : ∃ L : NNReal, LipschitzWith L localKernel :=
  ContDiff.lipschitzWith_of_hasCompactSupport localKernel_hasCompactSupport localKernel_contDiff
    (by simp)

/-- Both kernels vanish when `|n - v| > H` on the working range. -/
theorem kernels_vanish_far {Y H n v : ℝ} (hY : 0 < Y) (hH : 0 < H) (hHY : H ≤ Y / 10)
    (hv1 : Y / 2 ≤ v) (hn1 : Y ≤ n) (hn2 : n ≤ 2 * Y) (hfar : H < |n - v|) :
    localKernel ((n - v) / H) = 0 ∧ localKernel (v * Real.log (n / v) / H) = 0 := by
  have hv : 0 < v := by linarith
  have hn : 0 < n := by linarith
  constructor
  · apply localKernel_eq_zero_of_far
    rw [abs_div, abs_of_pos hH, le_div_iff₀ hH]
    linarith
  · apply localKernel_eq_zero_of_far
    rw [abs_div, abs_of_pos hH, le_div_iff₀ hH]
    rcases lt_abs.mp hfar with h | h
    · have hlog : 1 - (n / v)⁻¹ ≤ Real.log (n / v) :=
        Real.one_sub_inv_le_log_of_pos (div_pos hn hv)
      have hinv : 1 - (n / v)⁻¹ = (n - v) / n := by field_simp
      rw [hinv] at hlog
      have h1 : v * ((n - v) / n) ≤ v * Real.log (n / v) := mul_le_mul_of_nonneg_left hlog hv.le
      have h2 : 1 / 4 * H ≤ v * ((n - v) / n) := by
        rw [mul_div_assoc', le_div_iff₀ hn]
        nlinarith
      calc 1 / 4 * H ≤ v * Real.log (n / v) := h2.trans h1
        _ ≤ |v * Real.log (n / v)| := le_abs_self _
    · have hlog : Real.log (n / v) ≤ n / v - 1 := Real.log_le_sub_one_of_pos (div_pos hn hv)
      have h1 : v * Real.log (n / v) ≤ v * (n / v - 1) := mul_le_mul_of_nonneg_left hlog hv.le
      have h2 : v * (n / v - 1) = n - v := by field_simp
      rw [h2] at h1
      calc 1 / 4 * H ≤ -(v * Real.log (n / v)) := by linarith
        _ ≤ |v * Real.log (n / v)| := neg_le_abs _

theorem abs_log_one_add_sub_self_le {z : ℝ} (hz : -1 < z) :
    |Real.log (1 + z) - z| ≤ z ^ 2 / (1 + z) := by
  have hpos : 0 < 1 + z := by linarith
  have hup := Real.log_le_sub_one_of_pos hpos
  have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hinv
  have hform : (1 + z)⁻¹ - 1 = -z / (1 + z) := by field_simp; ring
  rw [hform] at hinv
  have hlo : z / (1 + z) ≤ Real.log (1 + z) := by
    have hn := neg_le_neg hinv
    simpa [neg_div] using hn
  have hu : Real.log (1 + z) - z ≤ 0 := by linarith
  have hl : -(z ^ 2 / (1 + z)) ≤ Real.log (1 + z) - z := by
    have heq : z / (1 + z) - z = -(z ^ 2 / (1 + z)) := by field_simp; ring
    rw [← heq]
    linarith
  rw [abs_le]
  exact ⟨hl, hu.trans (div_nonneg (sq_nonneg z) hpos.le)⟩

theorem log_argument_error {Y H n v : ℝ} (hY : 0 < Y) (hv : 0 < v) (hn : Y ≤ n)
    (hnv : |n - v| ≤ H) :
    |v * Real.log (n / v) - (n - v)| ≤ H ^ 2 / Y := by
  have hnpos : 0 < n := hY.trans_le hn
  have hH : 0 ≤ H := (abs_nonneg _).trans hnv
  let z : ℝ := (n - v) / v
  have h1pz : 1 + z = n / v := by
    dsimp [z]; field_simp; ring
  have hz : -1 < z := by
    have htmp : 0 < 1 + z := by rw [h1pz]; exact div_pos hnpos hv
    linarith
  have ht := abs_log_one_add_sub_self_le hz
  have hsquare : (n - v) ^ 2 ≤ H ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hnv 2
  have hmain : v * |Real.log (1 + z) - z| ≤ H ^ 2 / Y := by
    calc _ ≤ v * (z ^ 2 / (1 + z)) := mul_le_mul_of_nonneg_left ht hv.le
      _ = (n - v) ^ 2 / n := by rw [h1pz]; dsimp [z]; field_simp
      _ ≤ H ^ 2 / n := div_le_div_of_nonneg_right hsquare hnpos.le
      _ ≤ H ^ 2 / Y := div_le_div_of_nonneg_left (sq_nonneg H) hY hn
  have hdiff : v * Real.log (n / v) - (n - v) = v * (Real.log (1 + z) - z) := by
    rw [h1pz]; dsimp [z]; field_simp
  rw [hdiff, abs_mul, abs_of_pos hv]
  exact hmain

theorem kernel_diff_le {L : NNReal} (hL : LipschitzWith L localKernel) {Y H n v : ℝ}
    (hY : 0 < Y) (hH : 0 < H) (hHY : H ≤ Y / 10)
    (hv1 : Y / 2 ≤ v) (hn1 : Y ≤ n) (hn2 : n ≤ 2 * Y) :
    |localKernel ((n - v) / H) - localKernel (v * Real.log (n / v) / H)| ≤ L * (H / Y) := by
  by_cases hnear : |n - v| ≤ H
  · have hv : 0 < v := by linarith
    have harg := log_argument_error hY hv hn1 hnear
    have hd : |(n - v) / H - v * Real.log (n / v) / H| ≤ H / Y := by
      rw [← sub_div, abs_div, abs_of_pos hH, div_le_iff₀ hH, abs_sub_comm]
      calc |v * Real.log (n / v) - (n - v)| ≤ H ^ 2 / Y := harg
        _ = H / Y * H := by ring
    have hlip := hL.dist_le_mul ((n - v) / H) (v * Real.log (n / v) / H)
    rw [Real.dist_eq, Real.dist_eq] at hlip
    exact hlip.trans (mul_le_mul_of_nonneg_left hd L.2)
  · obtain ⟨h1, h2⟩ := kernels_vanish_far hY hH hHY hv1 hn1 hn2 (lt_of_not_ge hnear)
    rw [h1, h2, sub_zero, abs_zero]
    positivity

/-- Indicator of `|n - v| ≤ H`. -/
def chi (H : ℝ) (n : ℕ) : ℝ → ℝ := Set.indicator (Set.Icc ((n : ℝ) - H) (n + H)) 1

theorem chi_apply (H : ℝ) (n : ℕ) (v : ℝ) :
    chi H n v = if |(n : ℝ) - v| ≤ H then 1 else 0 := by
  unfold chi
  rw [Set.indicator_apply]
  have : v ∈ Set.Icc ((n : ℝ) - H) (n + H) ↔ |(n : ℝ) - v| ≤ H := by
    rw [Set.mem_Icc, abs_le]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simp only [this, Pi.one_apply]

theorem chi_nonneg (H : ℝ) (n : ℕ) (v : ℝ) : 0 ≤ chi H n v := by
  rw [chi_apply]; split_ifs <;> norm_num

theorem chi_sq (H : ℝ) (n : ℕ) (v : ℝ) : chi H n v ^ 2 = chi H n v := by
  rw [chi_apply]; split_ifs <;> norm_num

theorem integrable_chi (H : ℝ) (n : ℕ) : Integrable (chi H n) := by
  unfold chi
  exact (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc

theorem integral_chi_le {H : ℝ} (hH : 0 ≤ H) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫ v in a..b, chi H n v ≤ 2 * H := by
  rw [intervalIntegral.integral_of_le hab]
  refine (setIntegral_le_integral (integrable_chi H n)
    (Filter.Eventually.of_forall (chi_nonneg H n))).trans ?_
  unfold chi
  rw [integral_indicator_one measurableSet_Icc]
  simp only [Measure.real, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith)]
  linarith

/-- At most `2H + 1` integers lie within `H` of `v`. -/
theorem sum_chi_le (s : Finset ℕ) {H v : ℝ} (hH : 0 ≤ H) (hvH : H ≤ v) :
    ∑ n ∈ s, chi H n v ≤ 2 * H + 1 := by
  simp_rw [chi_apply]
  rw [Finset.sum_boole]
  have hsub : s.filter (fun n : ℕ => |(n : ℝ) - v| ≤ H) ⊆ Finset.Icc ⌈v - H⌉₊ ⌊v + H⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨-, hn⟩ := hn
    rw [abs_le] at hn
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.ceil_le.mpr (by linarith [hn.2])
    · exact Nat.le_floor (by linarith [hn.1])
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hcast : ((s.filter (fun n : ℕ => |(n : ℝ) - v| ≤ H)).card : ℝ) ≤
      ((⌊v + H⌋₊ + 1 - ⌈v - H⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
  refine hcast.trans ?_
  have hfl : (⌊v + H⌋₊ : ℝ) ≤ v + H := Nat.floor_le (by linarith)
  have hce : v - H ≤ (⌈v - H⌉₊ : ℝ) := Nat.le_ceil _
  by_cases hle : ⌈v - H⌉₊ ≤ ⌊v + H⌋₊ + 1
  · rw [Nat.cast_sub hle]
    push_cast
    linarith
  · rw [Nat.sub_eq_zero_of_le (le_of_lt (lt_of_not_ge hle))]
    simp
    linarith

theorem localLogConvolution_continuousOn (s : Finset ℕ) (a : ℕ → ℂ) (H : ℝ) :
    ContinuousOn (localLogConvolution s a H) (Set.Ioi 0) := by
  unfold localLogConvolution
  apply continuousOn_finsetSum
  intro n hn
  unfold localLogConvolutionTerm
  apply ContinuousOn.mul continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  apply localKernel_continuous.comp_continuousOn
  apply ContinuousOn.div_const
  apply ContinuousOn.mul continuousOn_id
  by_cases hn0 : (n : ℝ) = 0
  · simp only [hn0, zero_div]; exact continuousOn_const
  · apply ContinuousOn.log
    · exact continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt hx)
    · intro x hx; exact div_ne_zero hn0 (ne_of_gt hx)

theorem diff_pointwise_sq {L : NNReal} (hL : LipschitzWith L localKernel) (s : Finset ℕ)
    (a : ℕ → ℂ) {Y H v : ℝ} (hY : 0 < Y) (hH1 : 1 ≤ H) (hHY : H ≤ Y / 10)
    (hs : ∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y) (hv1 : Y / 2 ≤ v) :
    ‖localConvolution s a H v - localLogConvolution s a H v‖ ^ 2 ≤
      (2 * H + 1) * ((L : ℝ) * (H / Y)) ^ 2 * ∑ n ∈ s, chi H n v * ‖a n‖ ^ 2 := by
  set δ : ℝ := (L : ℝ) * (H / Y) with hδ
  have hH : 0 < H := by linarith
  have hdiff : localConvolution s a H v - localLogConvolution s a H v =
      ∑ n ∈ s, a n * ((localKernel (((n : ℝ) - v) / H) : ℂ) -
        (localKernel (v * Real.log ((n : ℝ) / v) / H) : ℂ)) := by
    unfold localConvolution localLogConvolution localConvolutionTerm localLogConvolutionTerm
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have hterm : ∀ n ∈ s, ‖a n * ((localKernel (((n : ℝ) - v) / H) : ℂ) -
        (localKernel (v * Real.log ((n : ℝ) / v) / H) : ℂ))‖ ≤
      chi H n v * (chi H n v * (‖a n‖ * δ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := hs n hn
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, chi_apply]
    split_ifs with hnear
    · rw [one_mul, one_mul]
      exact mul_le_mul_of_nonneg_left (kernel_diff_le hL hY hH hHY hv1 hn1 hn2) (norm_nonneg _)
    · obtain ⟨h1, h2⟩ := kernels_vanish_far hY hH hHY hv1 hn1 hn2 (lt_of_not_ge hnear)
      rw [h1, h2]; simp
  have hnorm : ‖localConvolution s a H v - localLogConvolution s a H v‖ ≤
      ∑ n ∈ s, chi H n v * (chi H n v * (‖a n‖ * δ)) := by
    rw [hdiff]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s (fun n => chi H n v)
    (fun n => chi H n v * (‖a n‖ * δ))
  have e1 : ∑ n ∈ s, (chi H n v) ^ 2 = ∑ n ∈ s, chi H n v :=
    Finset.sum_congr rfl (fun n _ => chi_sq H n v)
  have e2 : ∑ n ∈ s, (chi H n v * (‖a n‖ * δ)) ^ 2 = δ ^ 2 * ∑ n ∈ s, chi H n v * ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun n _ => by rw [mul_pow, chi_sq]; ring)
  have hcount := sum_chi_le s hH.le (show H ≤ v by linarith)
  have hsum0 : 0 ≤ ∑ n ∈ s, chi H n v * ‖a n‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (chi_nonneg H n v) (sq_nonneg _))
  calc ‖localConvolution s a H v - localLogConvolution s a H v‖ ^ 2 ≤
      (∑ n ∈ s, chi H n v * (chi H n v * (‖a n‖ * δ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ n ∈ s, (chi H n v) ^ 2) * ∑ n ∈ s, (chi H n v * (‖a n‖ * δ)) ^ 2 := hCS
    _ = (∑ n ∈ s, chi H n v) * (δ ^ 2 * ∑ n ∈ s, chi H n v * ‖a n‖ ^ 2) := by rw [e1, e2]
    _ ≤ (2 * H + 1) * (δ ^ 2 * ∑ n ∈ s, chi H n v * ‖a n‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

/-- The squared `L²` norm of the kernel replacement error on `[Y/2, 5Y/2]`. -/
theorem error_energy {L : NNReal} (hL : LipschitzWith L localKernel) (s : Finset ℕ)
    (a : ℕ → ℂ) {Y H : ℝ} (hY : 0 < Y) (hH1 : 1 ≤ H) (hHY : H ≤ Y / 10)
    (hs : ∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y) :
    ∫ v in (Y / 2)..(5 * Y / 2),
        ‖localConvolution s a H v - localLogConvolution s a H v‖ ^ 2 ≤
      6 * (L : ℝ) ^ 2 * (H / Y) ^ 2 * H ^ 2 * sqNorm s a := by
  have hab : Y / 2 ≤ 5 * Y / 2 := by linarith
  have hH : 0 < H := by linarith
  have hsubset : Set.uIcc (Y / 2) (5 * Y / 2) ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hab]; intro x hx; exact lt_of_lt_of_le (by linarith) hx.1
  have hcont : ContinuousOn
      (fun v => ‖localConvolution s a H v - localLogConvolution s a H v‖ ^ 2)
      (Set.uIcc (Y / 2) (5 * Y / 2)) :=
    (((localConvolution_contDiff s a H).continuous.continuousOn.sub
      ((localLogConvolution_continuousOn s a H).mono hsubset)).norm).pow 2
  have hgint : Integrable (fun v => (2 * H + 1) * ((L : ℝ) * (H / Y)) ^ 2 *
      ∑ n ∈ s, chi H n v * ‖a n‖ ^ 2) :=
    (integrable_finset_sum s (fun n _ => (integrable_chi H n).mul_const _)).const_mul _
  have hsq0 : 0 ≤ sqNorm s a := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  calc ∫ v in (Y / 2)..(5 * Y / 2),
        ‖localConvolution s a H v - localLogConvolution s a H v‖ ^ 2 ≤
      ∫ v in (Y / 2)..(5 * Y / 2), (2 * H + 1) * ((L : ℝ) * (H / Y)) ^ 2 *
        ∑ n ∈ s, chi H n v * ‖a n‖ ^ 2 :=
        intervalIntegral.integral_mono_on hab hcont.intervalIntegrable hgint.intervalIntegrable
          (fun v hv => diff_pointwise_sq hL s a hY hH1 hHY hs hv.1)
    _ = (2 * H + 1) * ((L : ℝ) * (H / Y)) ^ 2 *
        ∑ n ∈ s, (∫ v in (Y / 2)..(5 * Y / 2), chi H n v) * ‖a n‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum
          (fun n _ => ((integrable_chi H n).mul_const _).intervalIntegrable)]
        congr 1
        exact Finset.sum_congr rfl (fun n _ => intervalIntegral.integral_mul_const _ _)
    _ ≤ (2 * H + 1) * ((L : ℝ) * (H / Y)) ^ 2 * ∑ n ∈ s, (2 * H) * ‖a n‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_right (integral_chi_le hH.le n hab) (sq_nonneg _)) (by positivity)
    _ = ((2 * H + 1) * (2 * H)) * ((L : ℝ) ^ 2 * (H / Y) ^ 2) * sqNorm s a := by
        rw [sqNorm, ← Finset.mul_sum]; ring
    _ ≤ (6 * H ^ 2) * ((L : ℝ) ^ 2 * (H / Y) ^ 2) * sqNorm s a := by
        apply mul_le_mul_of_nonneg_right _ hsq0
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
    _ = _ := by ring

end Erdos821.P5Energy
