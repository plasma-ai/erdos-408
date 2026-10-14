import Erdos821.P5Energy.ErrorStep
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Assembly of the local additive-to-Mellin energy bound `Erdos821.P5Core.LocalMellinEnergyTask`. -/

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory

namespace Erdos821.P5Energy
open Blueprint.Analytic

/-- The additive convolution vanishes off `[Y/2, 5Y/2]`. -/
theorem localConvolution_eq_zero_off {s : Finset ℕ} {a : ℕ → ℂ} {Y H v : ℝ} (hY : 0 < Y)
    (hH : 0 < H) (hHY : H ≤ Y / 10) (hs : ∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y)
    (hv : v ∉ Set.Icc (Y / 2) (5 * Y / 2)) : localConvolution s a H v = 0 := by
  unfold localConvolution
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn1, hn2⟩ := hs n hn
  unfold localConvolutionTerm
  rw [localKernel_eq_zero_of_far, Complex.ofReal_zero, mul_zero]
  rw [abs_div, abs_of_pos hH, le_div_iff₀ hH]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  rcases hv with hv | hv
  · rw [abs_of_pos (by linarith)]; linarith
  · rw [abs_of_neg (by linarith)]; linarith

theorem norm_sq_le_two (x y : ℂ) : ‖x‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
  have h : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
    calc ‖x‖ = ‖y + (x - y)‖ := by ring_nf
      _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
  have h0 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖y‖ - ‖x - y‖)]

theorem log_range_subset {u : ℝ} (hu : u ∈ Set.uIcc (Real.log (1 / 2)) (Real.log (5 / 2))) :
    |u| ≤ 1 := by
  have hlo : -1 ≤ Real.log (1 / 2) := by
    rw [one_div, Real.log_inv]
    have := Real.log_two_lt_d9
    linarith
  have hhi : Real.log (5 / 2) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    linarith
  have hle : Real.log (1 / 2) ≤ Real.log (5 / 2) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Set.uIcc_of_le hle] at hu
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2]

/-- The log-kernel convolution at `v = Y e^u`, as a Mellin transform in log coordinates. -/
theorem localLogConvolution_exp {s : Finset ℕ} {a : ℕ → ℂ} {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H)
    (hns : ∀ n ∈ s, 0 < (n : ℝ)) (u : ℝ) :
    localLogConvolution s a H (Y * Real.exp u) =
      ((H / (2 * Real.pi * (Y * Real.exp u)) : ℝ) : ℂ) *
        ∫ t : ℝ, ampE (H / Y) t u * (phase (-(t * Real.log Y)) * dp s a t) := by
  rw [localLogConvolution_fourier s a H (Y * Real.exp u) hH (by positivity) hns]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have harg : H / (2 * Real.pi * (Y * Real.exp u)) * t = H / Y * t / (2 * Real.pi) * Real.exp (-u) := by
    rw [Real.exp_neg]; field_simp
  have hmel : Blueprint.Analytic.mellin (Y * Real.exp u) (-t) = phase (-(t * u)) * phase (-(t * Real.log Y)) := by
    unfold Blueprint.Analytic.mellin phase
    rw [← Complex.exp_add, Real.log_mul hY.ne' (Real.exp_pos u).ne', Real.log_exp]
    congr 1
    push_cast
    ring
  rw [harg, hmel]
  unfold ampE amp
  ring

theorem continuous_dp (s : Finset ℕ) (a : ℕ → ℂ) : Continuous (dp s a) := by
  unfold dp Blueprint.Analytic.mellin
  fun_prop

theorem logCutoff_hasCompactSupport : HasCompactSupport logCutoff :=
  logCutoffBump.hasCompactSupport

/-- The log-kernel energy on `[Y/2, 5Y/2]` in log coordinates. -/
theorem logKernel_energy_le {s : Finset ℕ} {a : ℕ → ℂ} {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H)
    (hns : ∀ n ∈ s, 0 < (n : ℝ)) :
    ∫ v in (Y / 2)..(5 * Y / 2), ‖localLogConvolution s a H v‖ ^ 2 ≤
      H ^ 2 / (4 * Real.pi ^ 2 * Y) * ∫ u : ℝ, logCutoff u * Real.exp (-u) *
        ‖∫ t : ℝ, ampE (H / Y) t u * (phase (-(t * Real.log Y)) * dp s a t)‖ ^ 2 := by
  set g : ℝ → ℝ := fun v => ‖localLogConvolution s a H v‖ ^ 2 with hg
  set f : ℝ → ℝ := fun u => Y * Real.exp u with hf
  have hfc : Continuous f := by rw [hf]; fun_prop
  have hcov := intervalIntegral.integral_comp_mul_deriv' (a := Real.log (1 / 2))
    (b := Real.log (5 / 2)) (f := f) (f' := f) (g := g)
    (fun x _ => by simpa [hf] using (Real.hasDerivAt_exp x).const_mul Y)
    hfc.continuousOn
    (by
      apply ContinuousOn.pow
      apply ContinuousOn.norm
      apply (localLogConvolution_continuousOn s a H).mono
      rintro _ ⟨x, -, rfl⟩
      exact mul_pos hY (Real.exp_pos x))
  have hfa : f (Real.log (1 / 2)) = Y / 2 := by
    simp only [hf]; rw [Real.exp_log (by norm_num)]; ring
  have hfb : f (Real.log (5 / 2)) = 5 * Y / 2 := by
    simp only [hf]; rw [Real.exp_log (by norm_num)]; ring
  rw [hfa, hfb] at hcov
  rw [← hcov]
  -- the cutoff integrand
  set Φ : ℝ → ℝ := fun u => logCutoff u * (g (f u) * f u) with hΦ
  have hΦcont : Continuous Φ := by
    have hgf : Continuous (fun u => g (f u)) := by
      simp only [hg, hf]
      apply Continuous.pow
      apply Continuous.norm
      apply (localLogConvolution_continuousOn s a H).comp_continuous (by fun_prop)
      intro x; exact mul_pos hY (Real.exp_pos x)
    exact logCutoff_contDiff.continuous.mul (hgf.mul (by simp only [hf]; fun_prop))
  have hΦint : Integrable Φ :=
    hΦcont.integrable_of_hasCompactSupport (logCutoff_hasCompactSupport.mul_right)
  have hle : Real.log (1 / 2) ≤ Real.log (5 / 2) := Real.log_le_log (by norm_num) (by norm_num)
  have heq_on : ∫ x in Real.log (1 / 2)..Real.log (5 / 2), (g ∘ f) x * f x =
      ∫ x in Real.log (1 / 2)..Real.log (5 / 2), Φ x := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [Function.comp, hΦ, logCutoff_eq_one u (log_range_subset hu), one_mul]
  rw [heq_on, intervalIntegral.integral_of_le hle]
  have hΦnn : ∀ u, 0 ≤ Φ u := fun u => by
    simp only [hΦ, hg, hf]
    exact mul_nonneg (logCutoff_nonneg u) (mul_nonneg (sq_nonneg _) (by positivity))
  refine (setIntegral_le_integral hΦint (Filter.Eventually.of_forall hΦnn)).trans_eq ?_
  rw [← integral_const_mul]
  congr 1
  funext u
  simp only [hΦ, hg, hf]
  rw [localLogConvolution_exp hY hH hns u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  generalize ‖∫ (t : ℝ), ampE (H / Y) t u * (phase (-(t * Real.log Y)) * dp s a t)‖ = X
  rw [Real.exp_neg]
  field_simp
  ring

/-- The local additive-to-Mellin energy bound with explicit constants. -/
theorem local_mellin_energy (j : ℕ) (hj : 2 ≤ j) : ∃ K : ℝ, 0 < K ∧
    ∀ (Y H : ℝ) (s : Finset ℕ) (a : ℕ → ℂ),
      10 ≤ Y → 1 ≤ H → H ≤ Y / 10 →
      (∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y) →
      (∫ θ in (-1 / H)..(1 / H), ‖P5Core.localAdditivePolynomial s a θ‖ ^ 2) ≤
        K / Y * (∫ t : ℝ, (1 + |H / Y * t|) ^ (-(j : ℤ)) * ‖dp s a t‖ ^ 2) +
        K * (H / Y) ^ 2 * sqNorm s a := by
  obtain ⟨C, hC, hW⟩ := weighted_energy_bound j hj
  obtain ⟨L, hL⟩ := localKernel_lipschitz
  refine ⟨2 * C / Real.pi ^ 2 + 48 * (L : ℝ) ^ 2 + 1, by positivity, ?_⟩
  intro Y H s a hY10 hH1 hHY hs
  have hY : 0 < Y := by linarith
  have hH : 0 < H := by linarith
  have hns : ∀ n ∈ s, 0 < (n : ℝ) := fun n hn => hY.trans_le (hs n hn).1
  have hab : Y / 2 ≤ 5 * Y / 2 := by linarith
  set X := ∫ t : ℝ, (1 + |H / Y * t|) ^ (-(j : ℤ)) * ‖dp s a t‖ ^ 2 with hX
  have hA := localConvolution_energy_bound s a H hH
  have hsupp : ∫ v : ℝ, ‖localConvolution s a H v‖ ^ 2 =
      ∫ v in (Y / 2)..(5 * Y / 2), ‖localConvolution s a H v‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro v hv
    rw [localConvolution_eq_zero_off hY hH hHY hs hv]
    simp
  have hsubset : Set.uIcc (Y / 2) (5 * Y / 2) ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hab]; intro x hx; exact lt_of_lt_of_le (by linarith) hx.1
  have c1 : ContinuousOn (fun v => ‖localConvolution s a H v‖ ^ 2) (Set.uIcc (Y / 2) (5 * Y / 2)) :=
    ((localConvolution_contDiff s a H).continuous.norm.pow 2).continuousOn
  have c2 : ContinuousOn (fun v => ‖localLogConvolution s a H v‖ ^ 2)
      (Set.uIcc (Y / 2) (5 * Y / 2)) :=
    ((localLogConvolution_continuousOn s a H).mono hsubset).norm.pow 2
  have c3 : ContinuousOn
      (fun v => ‖localConvolution s a H v - localLogConvolution s a H v‖ ^ 2)
      (Set.uIcc (Y / 2) (5 * Y / 2)) :=
    (((localConvolution_contDiff s a H).continuous.continuousOn.sub
      ((localLogConvolution_continuousOn s a H).mono hsubset)).norm).pow 2
  have hsplit : ∫ v in (Y / 2)..(5 * Y / 2), ‖localConvolution s a H v‖ ^ 2 ≤
      2 * (∫ v in (Y / 2)..(5 * Y / 2), ‖localLogConvolution s a H v‖ ^ 2) +
      2 * (∫ v in (Y / 2)..(5 * Y / 2),
        ‖localConvolution s a H v - localLogConvolution s a H v‖ ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (c2.intervalIntegrable.const_mul 2)
        (c3.intervalIntegrable.const_mul 2)]
    exact intervalIntegral.integral_mono_on hab c1.intervalIntegrable
      ((c2.intervalIntegrable.const_mul 2).add (c3.intervalIntegrable.const_mul 2))
      (fun v _ => norm_sq_le_two _ _)
  have hlog := logKernel_energy_le (s := s) (a := a) hY hH hns
  have hJ := hW (H / Y) (div_pos hH hY) (fun t => phase (-(t * Real.log Y)) * dp s a t)
    (∑ n ∈ s, ‖a n‖) ((continuous_phase.comp (by fun_prop)).mul (continuous_dp s a))
    (fun t => by rw [norm_mul, norm_phase, one_mul]; exact norm_dp_le s a t)
  have hωX : ∫ t, omega (H / Y) j t * ‖phase (-(t * Real.log Y)) * dp s a t‖ ^ 2 = X := by
    rw [hX]; congr 1; funext t
    rw [norm_mul, norm_phase, one_mul, omega, zpow_neg, zpow_natCast]
  rw [hωX] at hJ
  have herr := error_energy hL s a hY hH1 hHY hs
  have hX0 : 0 ≤ X := integral_nonneg (fun t => by positivity)
  have hsq0 : 0 ≤ sqNorm s a := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hlogJ : ∫ v in (Y / 2)..(5 * Y / 2), ‖localLogConvolution s a H v‖ ^ 2 ≤
      H ^ 2 / (4 * Real.pi ^ 2 * Y) * (C * X) :=
    hlog.trans (mul_le_mul_of_nonneg_left hJ (by positivity))
  have hconv : ∫ v : ℝ, ‖localConvolution s a H v‖ ^ 2 ≤
      2 * (H ^ 2 / (4 * Real.pi ^ 2 * Y) * (C * X)) +
      2 * (6 * (L : ℝ) ^ 2 * (H / Y) ^ 2 * H ^ 2 * sqNorm s a) := by
    rw [hsupp]
    refine hsplit.trans ?_
    linarith
  have hK1 : 2 * C / Real.pi ^ 2 ≤ 2 * C / Real.pi ^ 2 + 48 * (L : ℝ) ^ 2 + 1 := by
    have : 0 ≤ 48 * (L : ℝ) ^ 2 := by positivity
    linarith
  have hK2 : 48 * (L : ℝ) ^ 2 ≤ 2 * C / Real.pi ^ 2 + 48 * (L : ℝ) ^ 2 + 1 := by
    have : 0 ≤ 2 * C / Real.pi ^ 2 := by positivity
    linarith
  calc (∫ θ in (-1 / H)..(1 / H), ‖P5Core.localAdditivePolynomial s a θ‖ ^ 2)
      ≤ 4 / H ^ 2 * ∫ v : ℝ, ‖localConvolution s a H v‖ ^ 2 := hA
    _ ≤ 4 / H ^ 2 * (2 * (H ^ 2 / (4 * Real.pi ^ 2 * Y) * (C * X)) +
        2 * (6 * (L : ℝ) ^ 2 * (H / Y) ^ 2 * H ^ 2 * sqNorm s a)) :=
        mul_le_mul_of_nonneg_left hconv (by positivity)
    _ = 2 * C / Real.pi ^ 2 / Y * X + 48 * (L : ℝ) ^ 2 * (H / Y) ^ 2 * sqNorm s a := by
        field_simp
        ring
    _ ≤ (2 * C / Real.pi ^ 2 + 48 * (L : ℝ) ^ 2 + 1) / Y * X +
        (2 * C / Real.pi ^ 2 + 48 * (L : ℝ) ^ 2 + 1) * (H / Y) ^ 2 * sqNorm s a := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK1 hY.le) hX0
        · apply mul_le_mul_of_nonneg_right _ hsq0
          exact mul_le_mul_of_nonneg_right hK2 (by positivity)

end Erdos821.P5Energy

namespace Erdos821.P5Core

/-- The frozen §4 local Fourier-to-Mellin energy task. -/
theorem LocalMellinEnergyTask_proof : LocalMellinEnergyTask :=
  Erdos821.P5Energy.local_mellin_energy

end Erdos821.P5Core
