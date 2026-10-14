import Erdos821.P5.LocalEnergyTask
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier


noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open MeasureTheory

namespace Erdos821.P5Energy
open Blueprint.Analytic P5Core

noncomputable def unitKernelBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / (16 * Real.pi), 1 / (8 * Real.pi), by positivity, by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [Real.pi_pos]⟩

noncomputable def localKernel : ℝ → ℝ := unitKernelBump.normed volume

theorem localKernel_nonneg (x : ℝ) : 0 ≤ localKernel x :=
  unitKernelBump.nonneg_normed x

theorem localKernel_integral : (∫ x : ℝ, localKernel x) = 1 :=
  unitKernelBump.integral_normed

theorem localKernel_integrable : Integrable localKernel :=
  unitKernelBump.integrable_normed

theorem localKernel_contDiff : ContDiff ℝ ∞ localKernel :=
  unitKernelBump.contDiff_normed

theorem localKernel_hasCompactSupport : HasCompactSupport localKernel :=
  unitKernelBump.hasCompactSupport_normed

noncomputable def complexKernelSchwartz : 𝓢(ℝ, ℂ) :=
  (localKernel_hasCompactSupport.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (by
      simpa [Function.comp_def] using
        (Complex.ofRealCLM.contDiff.comp localKernel_contDiff))

noncomputable def localKernelFourier (ξ : ℝ) : ℂ :=
  𝓕 complexKernelSchwartz ξ

theorem localKernelFourier_eq_integral (ξ : ℝ) :
    localKernelFourier ξ = ∫ x : ℝ, e (-(x * ξ)) * (localKernel x : ℂ) := by
  rw [localKernelFourier, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, e]
  congr 1
  funext x
  congr 1
  · push_cast
    ring_nf

theorem localKernel_fourier_inversion (x : ℝ) :
    (localKernel x : ℂ) = ∫ ξ : ℝ, e (x * ξ) * localKernelFourier ξ := by
  have hinv := complexKernelSchwartz.continuous.fourierInv_fourier_eq
    complexKernelSchwartz.integrable (𝓕 complexKernelSchwartz).integrable
  have hinvx := congrFun hinv x
  rw [Real.fourierInv_eq'] at hinvx
  simpa [localKernelFourier, complexKernelSchwartz, SchwartzMap.fourier_coe,
    e, Circle.smul_def, mul_comm, mul_left_comm, mul_assoc] using hinvx.symm

theorem localKernelFourier_decay (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖localKernelFourier ξ‖ ≤ C / (1 + |ξ|) ^ N := by
  let G : 𝓢(ℝ, ℂ) := 𝓕 complexKernelSchwartz
  let C₀ : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) G
  refine ⟨C₀ + 1, by dsimp [C₀]; positivity, ?_⟩
  intro ξ
  have hseminorm := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (E := ℝ) (F := ℂ)
    (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl G ξ
  have hdec : (1 + |ξ|) ^ N * ‖localKernelFourier ξ‖ ≤ C₀ := by
    simpa [C₀, G, localKernelFourier, Real.norm_eq_abs] using hseminorm
  have hpos : 0 < (1 + |ξ|) ^ N := pow_pos (by positivity) _
  have hnorm : ‖localKernelFourier ξ‖ * (1 + |ξ|) ^ N ≤ C₀ := by
    nlinarith [hdec]
  have h₀ : ‖localKernelFourier ξ‖ ≤ C₀ / (1 + |ξ|) ^ N :=
    (le_div_iff₀ hpos).2 hnorm
  have hconst : C₀ / (1 + |ξ|) ^ N ≤ (C₀ + 1) / (1 + |ξ|) ^ N :=
    (div_le_div_iff₀ hpos hpos).2 (by linarith)
  exact h₀.trans hconst

theorem localKernelFourier_iterated_decay (r N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖iteratedDeriv r localKernelFourier ξ‖ ≤ C / (1 + |ξ|) ^ N := by
  let G : 𝓢(ℝ, ℂ) := 𝓕 complexKernelSchwartz
  let C₀ : ℝ := 2 ^ N * (Finset.Iic (N, r)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) G
  refine ⟨C₀ + 1, by dsimp [C₀]; positivity, ?_⟩
  intro ξ
  have hseminorm := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (E := ℝ) (F := ℂ)
    (m := (N, r)) (k := N) (n := r) le_rfl le_rfl G ξ
  have hdec : (1 + |ξ|) ^ N * ‖iteratedDeriv r localKernelFourier ξ‖ ≤ C₀ := by
    rw [show localKernelFourier = fun ξ => (𝓕 complexKernelSchwartz) ξ by rfl]
    simpa [C₀, G, Real.norm_eq_abs,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hseminorm
  have hpos : 0 < (1 + |ξ|) ^ N := pow_pos (by positivity) _
  have hnorm : ‖iteratedDeriv r localKernelFourier ξ‖ * (1 + |ξ|) ^ N ≤ C₀ := by
    nlinarith [hdec]
  have h₀ : ‖iteratedDeriv r localKernelFourier ξ‖ ≤ C₀ / (1 + |ξ|) ^ N :=
    (le_div_iff₀ hpos).2 hnorm
  have hconst : C₀ / (1 + |ξ|) ^ N ≤ (C₀ + 1) / (1 + |ξ|) ^ N :=
    (div_le_div_iff₀ hpos hpos).2 (by linarith)
  exact h₀.trans hconst

noncomputable def logCutoffBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def logCutoff (u : ℝ) : ℝ := logCutoffBump u

theorem logCutoff_eq_one (u : ℝ) (hu : |u| ≤ 1) : logCutoff u = 1 := by
  apply logCutoffBump.one_of_mem_closedBall
  simpa [logCutoff, logCutoffBump, Metric.mem_closedBall, Real.dist_eq] using hu

theorem logCutoff_eq_zero (u : ℝ) (hu : 2 ≤ |u|) : logCutoff u = 0 := by
  apply logCutoffBump.zero_of_le_dist
  simpa [logCutoff, logCutoffBump, Metric.mem_closedBall, Real.dist_eq,
    dist_zero_right] using hu

theorem logCutoff_contDiff : ContDiff ℝ ∞ logCutoff := by
  exact logCutoffBump.contDiff

def logCompactWeight (u : ℝ) : ℂ :=
  (logCutoff u : ℂ) * Complex.exp ((-u : ℝ) : ℂ)

theorem logCompactWeight_contDiff : ContDiff ℝ ∞ logCompactWeight := by
  have hcut : ContDiff ℝ ∞ (fun u : ℝ => (logCutoff u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp logCutoff_contDiff
  have hexp : ContDiff ℝ ∞ (fun u : ℝ => Complex.exp ((-u : ℝ) : ℂ)) := by
    have hneg : ContDiff ℝ ∞ (fun u : ℝ => -u) := contDiff_neg.comp contDiff_id
    have harg : ContDiff ℝ ∞ (fun u : ℝ => ((-u : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hneg
    exact Complex.contDiff_exp.comp harg
  change ContDiff ℝ ∞ (fun u : ℝ => (logCutoff u : ℂ) *
    Complex.exp ((-u : ℝ) : ℂ))
  exact hcut.mul hexp

theorem logCompactWeight_support_subset :
    Function.support logCompactWeight ⊆ Set.Icc (-2 : ℝ) 2 := by
  intro u hu
  by_contra hnot
  have hout : u < -2 ∨ 2 < u := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hnot
  have hrad : 2 ≤ |u| := by
    rcases hout with hleft | hright
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  have hz : logCutoff u = 0 := logCutoff_eq_zero u hrad
  have hzero : logCompactWeight u = 0 := by simp [logCompactWeight, hz]
  exact hu hzero

theorem logCompactWeight_hasCompactSupport : HasCompactSupport logCompactWeight :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logCompactWeight_support_subset

noncomputable def logCompactWeightSchwartz : 𝓢(ℝ, ℂ) :=
  logCompactWeight_hasCompactSupport.toSchwartzMap logCompactWeight_contDiff

theorem logCompactWeight_deriv_bound (r : ℕ) (u : ℝ) :
    ‖iteratedDeriv r logCompactWeight u‖ ≤
      SchwartzMap.seminorm ℝ 0 r logCompactWeightSchwartz := by
  change ‖iteratedDeriv r (logCompactWeightSchwartz : ℝ → ℂ) u‖ ≤
    SchwartzMap.seminorm ℝ 0 r logCompactWeightSchwartz
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
    SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ logCompactWeightSchwartz r u

def logAmplitudeArgument (h t u : ℝ) : ℝ :=
  h * Real.exp (-u) * t / (2 * Real.pi)

def logAmplitude (h t u : ℝ) : ℂ :=
  logCompactWeight u * localKernelFourier (logAmplitudeArgument h t u)

theorem iteratedDeriv_exp_neg_one (u : ℝ) :
    iteratedDeriv 1 (fun x : ℝ => Real.exp ((-1 : ℝ) * x)) u =
      -Real.exp ((-1 : ℝ) * u) := by
  rw [iteratedDeriv_exp_const_mul]
  norm_num

theorem iteratedDeriv_exp_neg_two (u : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => Real.exp ((-1 : ℝ) * x)) u =
      Real.exp ((-1 : ℝ) * u) := by
  rw [iteratedDeriv_exp_const_mul]
  norm_num

theorem logAmplitudeArgument_deriv_one (h t u : ℝ) :
    iteratedDeriv 1 (logAmplitudeArgument h t) u = -logAmplitudeArgument h t u := by
  let c : ℝ := h * t / (2 * Real.pi)
  have heq : logAmplitudeArgument h t = fun u => c * Real.exp ((-1 : ℝ) * u) := by
    funext x
    dsimp [logAmplitudeArgument, c]
    rw [neg_eq_neg_one_mul]
    ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_one]
  ring

theorem logAmplitudeArgument_deriv_two (h t u : ℝ) :
    iteratedDeriv 2 (logAmplitudeArgument h t) u = logAmplitudeArgument h t u := by
  let c : ℝ := h * t / (2 * Real.pi)
  have heq : logAmplitudeArgument h t = fun u => c * Real.exp ((-1 : ℝ) * u) := by
    funext x
    dsimp [logAmplitudeArgument, c]
    rw [neg_eq_neg_one_mul]
    ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_exp_neg_two]

theorem localKernelFourier_contDiff : ContDiff ℝ ∞ localKernelFourier := by
  simpa [localKernelFourier] using (𝓕 complexKernelSchwartz).smooth ⊤

theorem logAmplitudeArgument_contDiff (h t : ℝ) :
    ContDiff ℝ ∞ (logAmplitudeArgument h t) := by
  have hneg : ContDiff ℝ ∞ (fun u : ℝ => -u) := contDiff_neg.comp contDiff_id
  have hexp : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) := Real.contDiff_exp.comp hneg
  unfold logAmplitudeArgument
  fun_prop

theorem logAmplitudeArgument_contDiff_two (h t : ℝ) :
    ContDiff ℝ 2 (logAmplitudeArgument h t) := by
  have hneg : ContDiff ℝ 2 (fun u : ℝ => -u) := contDiff_neg.comp contDiff_id
  have hexp : ContDiff ℝ 2 (fun u : ℝ => Real.exp (-u)) := Real.contDiff_exp.comp hneg
  unfold logAmplitudeArgument
  fun_prop

theorem localKernelFourier_contDiff_two :
    ContDiff ℝ 2 localKernelFourier := by
  simpa [localKernelFourier] using (𝓕 complexKernelSchwartz).smooth 2

theorem logAmplitudeKernel_iterated_two (h t u : ℝ) :
    iteratedDeriv 2 (fun u => localKernelFourier (logAmplitudeArgument h t u)) u =
      iteratedFDeriv ℝ 2 localKernelFourier (logAmplitudeArgument h t u)
        (fun _ => iteratedDeriv 1 (logAmplitudeArgument h t) u) +
      fderiv ℝ localKernelFourier (logAmplitudeArgument h t u)
        (iteratedDeriv 2 (logAmplitudeArgument h t) u) := by
  have hcomp := iteratedDeriv_vcomp_two
    (x := u)
    (localKernelFourier_contDiff_two.contDiffAt)
    ((logAmplitudeArgument_contDiff_two h t).contDiffAt)
  rw [← iteratedDeriv_one] at hcomp
  change iteratedDeriv 2 (localKernelFourier ∘ logAmplitudeArgument h t) u = _
  exact hcomp

theorem logAmplitude_contDiff (h t : ℝ) :
    ContDiff ℝ ∞ (logAmplitude h t) := by
  unfold logAmplitude
  exact logCompactWeight_contDiff.mul
    (localKernelFourier_contDiff.comp (logAmplitudeArgument_contDiff h t))

theorem logAmplitude_support_subset (h t : ℝ) :
    Function.support (logAmplitude h t) ⊆ Set.Icc (-2 : ℝ) 2 := by
  intro u hu
  have hW : u ∈ Function.support logCompactWeight := by
    apply Function.mem_support.mpr
    intro hz
    apply hu
    simp [logAmplitude, hz]
  exact logCompactWeight_support_subset hW

theorem logAmplitude_hasCompactSupport (h t : ℝ) :
    HasCompactSupport (logAmplitude h t) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (logAmplitude_support_subset h t)

noncomputable def logAmplitudeSchwartz (h t : ℝ) : 𝓢(ℝ, ℂ) :=
  (logAmplitude_hasCompactSupport h t).toSchwartzMap (logAmplitude_contDiff h t)

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [Complex.ofReal_add]
  rw [show 2 * (Real.pi : ℂ) * ((x : ℂ) + (y : ℂ)) * Complex.I =
      2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I +
        2 * (Real.pi : ℂ) * (y : ℂ) * Complex.I by ring,
    Complex.exp_add]

def localLogConvolutionTerm (n : ℕ) (c : ℂ) (H v : ℝ) : ℂ :=
  c * (localKernel (v * Real.log ((n : ℝ) / v) / H) : ℂ)

def localLogConvolution (s : Finset ℕ) (a : ℕ → ℂ) (H v : ℝ) : ℂ :=
  ∑ n ∈ s, localLogConvolutionTerm n (a n) H v

theorem localLogConvolutionTerm_fourier (n : ℕ) (c : ℂ) (H v : ℝ)
    (hH : 0 < H) (hv : 0 < v) (hn : 0 < (n : ℝ)) :
    localLogConvolutionTerm n c H v =
      ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
        ∫ t : ℝ, localKernelFourier (H / (2 * Real.pi * v) * t) *
          mellin v (-t) * (c * mellin n t) := by
  let q : ℝ := H / (2 * Real.pi * v)
  have hq : 0 < q := by
    dsimp [q]
    exact div_pos hH (mul_pos (by positivity) hv)
  have hqne : q ≠ 0 := hq.ne'
  have hscale : q * (v / H) = 1 / (2 * Real.pi) := by
    dsimp [q]
    field_simp [hH.ne', hv.ne', Real.pi_ne_zero]
  have hphase (t : ℝ) :
      e (q * t * (v / H * Real.log ((n : ℝ) / v))) = mellin v (-t) * mellin n t := by
    rw [Real.log_div hn.ne' hv.ne']
    have hqv : q * t * (v / H) = t / (2 * Real.pi) := by
      calc
        q * t * (v / H) = (q * (v / H)) * t := by ring
        _ = _ := by rw [hscale]; ring
    rw [show q * t * (v / H * (Real.log (n : ℝ) - Real.log v)) =
      (t / (2 * Real.pi)) * (Real.log (n : ℝ) - Real.log v) by
        calc
          _ = (q * t * (v / H)) * (Real.log (n : ℝ) - Real.log v) := by ring
          _ = _ := by rw [hqv]]
    rw [show t / (2 * Real.pi) * (Real.log (n : ℝ) - Real.log v) =
      t * Real.log (n : ℝ) / (2 * Real.pi) +
        (-(t * Real.log v / (2 * Real.pi))) by ring, e_add]
    have hmn : e (t * Real.log (n : ℝ) / (2 * Real.pi)) = mellin n t := by
      simp only [Blueprint.Analytic.mellin, e]
      congr 1 <;> push_cast <;> field_simp [Real.pi_ne_zero] <;> ring
    have hmv : e (-(t * Real.log v / (2 * Real.pi))) = mellin v (-t) := by
      simp only [Blueprint.Analytic.mellin, e]
      congr 1 <;> push_cast <;> field_simp [Real.pi_ne_zero] <;> ring
    rw [hmn, hmv]
    ring
  let F : ℝ → ℂ := fun ξ =>
    e (ξ * (v / H * Real.log ((n : ℝ) / v))) * localKernelFourier ξ
  have hEcont : Continuous (fun ξ : ℝ => e (ξ * (v / H * Real.log ((n : ℝ) / v)))) := by
    unfold e
    fun_prop
  have hFint : Integrable F := by
    have hKint : Integrable localKernelFourier := (𝓕 complexKernelSchwartz).integrable
    have hmul := hKint.bdd_mul (c := 1) hEcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by simp [e, Complex.norm_exp])
    exact hmul.congr (Filter.Eventually.of_forall fun ξ => by rfl)
  have hscaleInt : (∫ ξ : ℝ, F ξ) =
      (q : ℂ) * ∫ t : ℝ, F (q * t) := by
    have hcomp := MeasureTheory.Measure.integral_comp_div
      (fun t : ℝ => F (q * t)) q
    have hcomp' : (∫ ξ : ℝ, (fun t : ℝ => F (q * t)) (ξ / q)) =
        ∫ ξ : ℝ, F ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      congr 1
      field_simp [hqne]
    calc
      (∫ ξ : ℝ, F ξ) = ∫ ξ : ℝ, (fun t : ℝ => F (q * t)) (ξ / q) := hcomp'.symm
      _ = |q| • ∫ t : ℝ, F (q * t) := hcomp
      _ = (q : ℂ) * ∫ t : ℝ, F (q * t) := by
        rw [abs_of_pos hq]
        simp only [Complex.real_smul]
  have hinv := localKernel_fourier_inversion (v * Real.log ((n : ℝ) / v) / H)
  have harg (ξ : ℝ) :
      (v * Real.log ((n : ℝ) / v) / H) * ξ =
        ξ * (v / H * Real.log ((n : ℝ) / v)) := by ring
  have hleft : localLogConvolutionTerm n c H v = c * ∫ ξ : ℝ, F ξ := by
    rw [localLogConvolutionTerm, hinv]
    congr 1
    rw [show (fun ξ : ℝ => e ((v * Real.log ((n : ℝ) / v) / H) * ξ) *
        localKernelFourier ξ) = F by
      funext ξ
      dsimp [F]
      rw [harg]]
  rw [hleft, hscaleInt]
  change c * ((q : ℂ) * ∫ t : ℝ, F (q * t)) =
    (q : ℂ) * ∫ t : ℝ, localKernelFourier (q * t) *
      mellin v (-t) * (c * mellin n t)
  calc
    c * ((q : ℂ) * ∫ t : ℝ, F (q * t)) =
        (q : ℂ) * ∫ t : ℝ, c * F (q * t) := by
      rw [integral_const_mul]
      ring
    _ = (q : ℂ) *
          ∫ t : ℝ, localKernelFourier (q * t) *
            mellin v (-t) * (c * mellin n t) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      dsimp [F]
      rw [hphase]
      ring

theorem localLogConvolution_fourier (s : Finset ℕ) (a : ℕ → ℂ)
    (H v : ℝ) (hH : 0 < H) (hv : 0 < v)
    (hns : ∀ n ∈ s, 0 < (n : ℝ)) :
    localLogConvolution s a H v =
      ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
        ∫ t : ℝ, localKernelFourier (H / (2 * Real.pi * v) * t) *
          mellin v (-t) * dp s a t := by
  let q : ℝ := H / (2 * Real.pi * v)
  have hq : 0 < q := div_pos hH (mul_pos (by positivity) hv)
  have hnormMellin (x t : ℝ) : ‖mellin x t‖ = 1 := by
    simp [Blueprint.Analytic.mellin, Complex.norm_exp]
  have hKint : Integrable (fun t : ℝ => localKernelFourier (q * t)) := by
    simpa [q, localKernelFourier] using
      (𝓕 complexKernelSchwartz).integrable.comp_mul_left' hq.ne'
  have htermInt (n : ℕ) : Integrable (fun t : ℝ =>
      localKernelFourier (q * t) * mellin v (-t) * (a n * mellin n t)) := by
    have hcont : Continuous (fun t : ℝ => mellin v (-t) * (a n * mellin n t)) := by
      unfold Blueprint.Analytic.mellin
      fun_prop
    have hbound : ∀ t : ℝ,
        ‖mellin v (-t) * (a n * mellin n t)‖ ≤ ‖a n‖ := by
      intro t
      rw [norm_mul, hnormMellin, norm_mul, hnormMellin]
      simp
    have hmul := hKint.bdd_mul (c := ‖a n‖) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
    exact hmul.congr (Filter.Eventually.of_forall fun t => by ring)
  have hsumInt : Integrable (fun t : ℝ =>
      ∑ n ∈ s, localKernelFourier (q * t) * mellin v (-t) *
        (a n * mellin n t)) :=
    integrable_finsetSum s (fun n hn => htermInt n)
  have hsum : (∑ n ∈ s,
      ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
        ∫ t : ℝ, localKernelFourier (q * t) * mellin v (-t) *
          (a n * mellin n t)) =
      ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
        ∫ t : ℝ, ∑ n ∈ s, localKernelFourier (q * t) * mellin v (-t) *
          (a n * mellin n t) := by
    calc
      _ = ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
          ∑ n ∈ s, ∫ t : ℝ, localKernelFourier (q * t) * mellin v (-t) *
            (a n * mellin n t) := by rw [← Finset.mul_sum]
      _ = _ := by rw [integral_finsetSum s (fun n hn => htermInt n)]
  calc
    localLogConvolution s a H v =
        ∑ n ∈ s, ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
          ∫ t : ℝ, localKernelFourier (q * t) * mellin v (-t) *
            (a n * mellin n t) := by
      unfold localLogConvolution
      apply Finset.sum_congr rfl
      intro n hn
      simpa [q] using localLogConvolutionTerm_fourier n (a n) H v hH hv (hns n hn)
    _ = ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
          ∫ t : ℝ, ∑ n ∈ s, localKernelFourier (q * t) * mellin v (-t) *
            (a n * mellin n t) := hsum
    _ = ((H / (2 * Real.pi * v) : ℝ) : ℂ) *
          ∫ t : ℝ, localKernelFourier (q * t) * mellin v (-t) * dp s a t := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [Blueprint.Analytic.dp]
      rw [Finset.mul_sum]

theorem localKernel_eq_zero_of_radius (x : ℝ)
    (hx : 1 / (8 * Real.pi) ≤ |x|) : localKernel x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support localKernel := Function.mem_support.mpr hne
  change x ∈ Function.support (unitKernelBump.normed volume) at hmem
  rw [unitKernelBump.support_normed_eq] at hmem
  have hxsmall : |x| < 1 / (8 * Real.pi) := by
    simpa [Metric.mem_ball, Real.dist_eq, unitKernelBump] using hmem
  linarith

theorem localKernel_phase_bound (x ξ : ℝ) (hξ : |ξ| ≤ 1)
    (hx : |x| < 1 / (8 * Real.pi)) :
    ‖e (-(x * ξ)) - 1‖ ≤ 1 / 2 := by
  let z : ℂ := ((2 * Real.pi * (-(x * ξ)) : ℝ) : ℂ) * Complex.I
  have hprod : |x * ξ| ≤ 1 / (8 * Real.pi) := by
    rw [abs_mul]
    calc
      |x| * |ξ| ≤ |x| * 1 := mul_le_mul_of_nonneg_left hξ (abs_nonneg x)
      _ ≤ 1 / (8 * Real.pi) := by simpa using le_of_lt hx
  have hz : ‖z‖ ≤ 1 / 4 := by
    dsimp [z]
    rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_neg]
    simp only [mul_one]
    calc
      2 * Real.pi * |x * ξ| ≤ 2 * Real.pi * (1 / (8 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 1 / 4 := by field_simp [Real.pi_ne_zero]; norm_num
  have hz1 : ‖z‖ ≤ 1 := hz.trans (by norm_num)
  have h := Complex.norm_exp_sub_one_le hz1
  have he : e (-(x * ξ)) = Complex.exp z := by
    simp [e, z]
  rw [he]
  calc
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := h
    _ ≤ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hz (by norm_num)
    _ = 1 / 2 := by norm_num

theorem localKernel_phase_sub_one_mul_bound (ξ : ℝ) (hξ : |ξ| ≤ 1) (x : ℝ) :
    ‖(e (-(x * ξ)) - 1) * (localKernel x : ℂ)‖ ≤ (1 / 2) * localKernel x := by
  by_cases hk : localKernel x = 0
  · simp [hk]
  have hmem : x ∈ Function.support localKernel := Function.mem_support.mpr hk
  change x ∈ Function.support (unitKernelBump.normed volume) at hmem
  rw [unitKernelBump.support_normed_eq] at hmem
  have hx : |x| < 1 / (8 * Real.pi) := by
    simpa [Metric.mem_ball, Real.dist_eq, unitKernelBump] using hmem
  have hphase := localKernel_phase_bound x ξ hξ hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (localKernel_nonneg x)]
  exact mul_le_mul_of_nonneg_right hphase (localKernel_nonneg x)

theorem localKernel_complex_integrable :
    Integrable (fun x : ℝ => (localKernel x : ℂ)) := by
  exact complexKernelSchwartz.integrable

theorem localKernel_phase_integrable (ξ : ℝ) :
    Integrable (fun x : ℝ => e (-(x * ξ)) * (localKernel x : ℂ)) := by
  have hk := localKernel_complex_integrable
  have hecont : Continuous (fun x : ℝ => e (-(x * ξ))) := by
    unfold e
    fun_prop
  exact hk.bdd_mul (c := 1) hecont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simp [e, Complex.norm_exp])

theorem localKernel_complex_integral :
    (∫ x : ℝ, (localKernel x : ℂ)) = 1 := by
  rw [integral_complex_ofReal, localKernel_integral]
  norm_num

theorem localKernelFourier_close_one (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    ‖localKernelFourier ξ - 1‖ ≤ 1 / 2 := by
  have hk := localKernel_complex_integrable
  have hp := localKernel_phase_integrable ξ
  have hsub : Integrable (fun x : ℝ =>
      e (-(x * ξ)) * (localKernel x : ℂ) - (localKernel x : ℂ)) := hp.sub hk
  have hbound : Integrable (fun x : ℝ => (1 / 2) * localKernel x) := by
    simpa [mul_comm] using localKernel_integrable.const_mul (1 / 2)
  have heq : localKernelFourier ξ - 1 =
      ∫ x : ℝ, e (-(x * ξ)) * (localKernel x : ℂ) - (localKernel x : ℂ) := by
    rw [localKernelFourier_eq_integral, ← localKernel_complex_integral,
      ← integral_sub hp hk]
  rw [heq]
  calc
    ‖∫ x : ℝ, e (-(x * ξ)) * (localKernel x : ℂ) - (localKernel x : ℂ)‖ ≤
        ∫ x : ℝ, ‖e (-(x * ξ)) * (localKernel x : ℂ) - (localKernel x : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (1 / 2) * localKernel x := by
      apply integral_mono hsub.norm hbound
      intro x
      have h := localKernel_phase_sub_one_mul_bound ξ hξ x
      have he : e (-(x * ξ)) * (localKernel x : ℂ) - (localKernel x : ℂ) =
          (e (-(x * ξ)) - 1) * (localKernel x : ℂ) := by ring
      calc
        ‖e (-(x * ξ)) * (localKernel x : ℂ) - (localKernel x : ℂ)‖ =
            ‖(e (-(x * ξ)) - 1) * (localKernel x : ℂ)‖ := congrArg norm he
        _ ≤ (1 / 2) * localKernel x := h
    _ = 1 / 2 := by rw [integral_const_mul, localKernel_integral]; norm_num

theorem localKernelFourier_norm_lower (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    1 / 2 ≤ ‖localKernelFourier ξ‖ := by
  have h := localKernelFourier_close_one ξ hξ
  have ht := norm_sub_le (localKernelFourier ξ) (localKernelFourier ξ - 1)
  have heq : localKernelFourier ξ - (localKernelFourier ξ - 1) = 1 := by ring
  rw [heq, norm_one] at ht
  linarith

def localConvolutionTerm (n : ℕ) (c : ℂ) (H v : ℝ) : ℂ :=
  c * (localKernel (((n : ℝ) - v) / H) : ℂ)

def localConvolution (s : Finset ℕ) (a : ℕ → ℂ) (H v : ℝ) : ℂ :=
  ∑ n ∈ s, localConvolutionTerm n (a n) H v

theorem localConvolution_support_subset (s : Finset ℕ) (a : ℕ → ℂ)
    (H : ℝ) (hH : 0 < H) :
    Function.support (localConvolution s a H) ⊆
      Set.Icc (-(1 / (8 * Real.pi)) * H)
        (((s.sup id : ℕ) : ℝ) + (1 / (8 * Real.pi)) * H) := by
  intro v hv
  by_contra hvin
  have hvout : v < -(1 / (8 * Real.pi)) * H ∨
      ((s.sup id : ℕ) : ℝ) + (1 / (8 * Real.pi)) * H < v := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hvin
  have hzero : localConvolution s a H v = 0 := by
    unfold localConvolution
    apply Finset.sum_eq_zero
    intro n hn
    have hnle : n ≤ s.sup id := Finset.le_sup (f := id) hn
    have hrH : 0 < (1 / (8 * Real.pi)) * H := mul_pos (by positivity) hH
    have hrad : 1 / (8 * Real.pi) ≤ |((n : ℝ) - v) / H| := by
      have hdiff : 1 / (8 * Real.pi) * H ≤ |(n : ℝ) - v| := by
        rcases hvout with hleft | hright
        · have hpos : 0 < (n : ℝ) - v := by
            have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
            nlinarith [hrH]
          rw [abs_of_pos hpos]
          nlinarith [hrH]
        · have hpos : 0 < v - (n : ℝ) := by
            have hnle' : (n : ℝ) ≤ ((s.sup id : ℕ) : ℝ) := by exact_mod_cast hnle
            nlinarith [hrH]
          have hnle' : (n : ℝ) ≤ ((s.sup id : ℕ) : ℝ) := by exact_mod_cast hnle
          have hsum : (n : ℝ) + (1 / (8 * Real.pi)) * H ≤
              ((s.sup id : ℕ) : ℝ) + (1 / (8 * Real.pi)) * H := by linarith
          have hmain : (n : ℝ) + (1 / (8 * Real.pi)) * H < v := hsum.trans_lt hright
          have hneg : (n : ℝ) - v < 0 := by linarith
          rw [abs_of_neg hneg]
          linarith [hmain]
      rw [abs_div, abs_of_pos hH]
      exact (le_div_iff₀ hH).2 hdiff
    simp [localConvolutionTerm, localKernel_eq_zero_of_radius _ hrad]
  exact hv hzero

theorem localConvolution_contDiff (s : Finset ℕ) (a : ℕ → ℂ) (H : ℝ) :
    ContDiff ℝ ∞ (localConvolution s a H) := by
  unfold localConvolution
  apply ContDiff.sum
  intro n hn
  have harg : ContDiff ℝ ∞ (fun v : ℝ => ((n : ℝ) - v) / H) := by fun_prop
  have hK : ContDiff ℝ ∞ (fun v : ℝ => localKernel (((n : ℝ) - v) / H)) :=
    localKernel_contDiff.comp harg
  have hKc : ContDiff ℝ ∞ (fun v : ℝ => (localKernel (((n : ℝ) - v) / H) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hK
  simpa [localConvolutionTerm] using contDiff_const.mul hKc

theorem localConvolutionTerm_support_subset (n : ℕ) (c : ℂ) (H : ℝ)
    (hH : 0 < H) :
    Function.support (localConvolutionTerm n c H) ⊆
      Set.Icc ((n : ℝ) - (1 / (8 * Real.pi)) * H)
        ((n : ℝ) + (1 / (8 * Real.pi)) * H) := by
  intro v hv
  by_contra hvin
  have hvout : v < (n : ℝ) - (1 / (8 * Real.pi)) * H ∨
      (n : ℝ) + (1 / (8 * Real.pi)) * H < v := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hvin
  have hrad : 1 / (8 * Real.pi) ≤ |((n : ℝ) - v) / H| := by
    have hrH : 0 < (1 / (8 * Real.pi)) * H := mul_pos (by positivity) hH
    have hdiff : (1 / (8 * Real.pi)) * H ≤ |(n : ℝ) - v| := by
      rcases hvout with hleft | hright
      · have hpos : 0 < (n : ℝ) - v := by linarith [hrH]
        rw [abs_of_pos hpos]
        linarith [hrH]
      · have hpos : 0 < v - (n : ℝ) := by linarith [hrH]
        have hneg : (n : ℝ) - v < 0 := by linarith [hpos]
        rw [abs_of_neg hneg]
        linarith [hrH]
    rw [abs_div, abs_of_pos hH]
    exact (le_div_iff₀ hH).2 hdiff
  have hzero : localConvolutionTerm n c H v = 0 := by
    simp [localConvolutionTerm, localKernel_eq_zero_of_radius _ hrad]
  exact hv hzero

theorem localConvolutionTerm_contDiff (n : ℕ) (c : ℂ) (H : ℝ) :
    ContDiff ℝ ∞ (localConvolutionTerm n c H) := by
  unfold localConvolutionTerm
  have harg : ContDiff ℝ ∞ (fun v : ℝ => ((n : ℝ) - v) / H) := by fun_prop
  have hK : ContDiff ℝ ∞ (fun v : ℝ => localKernel (((n : ℝ) - v) / H)) :=
    localKernel_contDiff.comp harg
  have hKc : ContDiff ℝ ∞ (fun v : ℝ => (localKernel (((n : ℝ) - v) / H) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hK
  simpa using contDiff_const.mul hKc

theorem localConvolutionTerm_integrable (n : ℕ) (c : ℂ) (H : ℝ)
    (hH : 0 < H) : Integrable (localConvolutionTerm n c H) := by
  have hcs : HasCompactSupport (localConvolutionTerm n c H) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (localConvolutionTerm_support_subset n c H hH)
  exact (localConvolutionTerm_contDiff n c H).continuous.integrable_of_hasCompactSupport hcs

theorem localConvolutionTerm_phase_integrable (n : ℕ) (c : ℂ) (H θ : ℝ)
    (hH : 0 < H) :
    Integrable (fun v : ℝ => e (-(v * θ)) * localConvolutionTerm n c H v) := by
  have hterm := localConvolutionTerm_integrable n c H hH
  have hecont : Continuous (fun v : ℝ => e (-(v * θ))) := by
    unfold e
    fun_prop
  exact hterm.bdd_mul (c := 1) hecont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by simp [e, Complex.norm_exp])

theorem localConvolutionTerm_fourier (n : ℕ) (c : ℂ) (H θ : ℝ)
    (hH : 0 < H) :
    (∫ v : ℝ, e (-(v * θ)) * localConvolutionTerm n c H v) =
      c * e (-((n : ℝ) * θ)) * (H : ℂ) * localKernelFourier (-(H * θ)) := by
  let g : ℝ → ℂ := fun u => e (u * (H * θ)) * (localKernel u : ℂ)
  have hphase (v : ℝ) :
      e (-(v * θ)) * localConvolutionTerm n c H v =
        c * e (-((n : ℝ) * θ)) * g (((n : ℝ) - v) / H) := by
    have harg : -(v * θ) = -((n : ℝ) * θ) +
        (((n : ℝ) - v) / H) * (H * θ) := by
      field_simp [hH.ne']
      ring
    unfold localConvolutionTerm g
    rw [harg, e_add]
    ring
  have htermIntegral :
      (∫ v : ℝ, e (-(v * θ)) * localConvolutionTerm n c H v) =
        c * e (-((n : ℝ) * θ)) * (∫ v : ℝ, g (((n : ℝ) - v) / H)) := by
    calc
      _ = ∫ v : ℝ, c * e (-((n : ℝ) * θ)) * g (((n : ℝ) - v) / H) := by
        apply integral_congr_ae
        filter_upwards with v
        exact hphase v
      _ = _ := by rw [integral_const_mul]
  have hsubst : (∫ v : ℝ, g (((n : ℝ) - v) / H)) =
      (H : ℂ) * (∫ u : ℝ, g u) := by
    have hshift : (∫ v : ℝ, g (-(v - (n : ℝ)) / H)) =
        ∫ v : ℝ, g (-v / H) := by
      simpa [sub_eq_add_neg] using
        (MeasureTheory.integral_add_right_eq_self
          (fun v : ℝ => g (-v / H)) (-(n : ℝ)))
    have hscale : (∫ v : ℝ, g (-v / H)) =
        |(-1 / H : ℝ)⁻¹| • (∫ u : ℝ, g u) := by
      have heq : (fun v : ℝ => g (-v / H)) = fun v => g ((-1 / H) * v) := by
        funext v
        congr 1
        ring
      rw [heq, MeasureTheory.Measure.integral_comp_mul_left]
    calc
      _ = ∫ v : ℝ, g (-(v - (n : ℝ)) / H) := by
        apply integral_congr_ae
        filter_upwards with v
        congr 1
        ring
      _ = ∫ v : ℝ, g (-v / H) := hshift
      _ = |(-1 / H : ℝ)⁻¹| • (∫ u : ℝ, g u) := hscale
      _ = (H : ℂ) * (∫ u : ℝ, g u) := by
        have hinv : (-1 / H : ℝ)⁻¹ = -H := by field_simp
        rw [hinv, abs_neg, abs_of_pos hH]
        simp
  have hg : (∫ u : ℝ, g u) = localKernelFourier (-(H * θ)) := by
    rw [localKernelFourier_eq_integral]
    apply integral_congr_ae
    filter_upwards with u
    change e (u * (H * θ)) * (localKernel u : ℂ) =
      e (-(u * (-(H * θ)))) * (localKernel u : ℂ)
    congr 1
    congr 1
    ring
  rw [htermIntegral, hsubst, hg]
  ring

noncomputable def localConvolutionSchwartz (s : Finset ℕ) (a : ℕ → ℂ)
    (H : ℝ) (hH : 0 < H) : 𝓢(ℝ, ℂ) :=
  (HasCompactSupport.of_support_subset_isCompact
      isCompact_Icc
      (localConvolution_support_subset s a H hH)).toSchwartzMap
    (localConvolution_contDiff s a H)


theorem fourierSchwartz_eq_e_integral (f : 𝓢(ℝ, ℂ)) (θ : ℝ) :
    (𝓕 f) θ = ∫ v : ℝ, e (-(v * θ)) * f v := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  congr 1
  funext v
  simp only [e]
  congr 1
  push_cast
  ring_nf

theorem localConvolutionFourier_eq (s : Finset ℕ) (a : ℕ → ℂ)
    (H θ : ℝ) (hH : 0 < H) :
    (𝓕 (localConvolutionSchwartz s a H hH)) θ =
      (H : ℂ) * localKernelFourier (-(H * θ)) * localAdditivePolynomial s a (-θ) := by
  rw [fourierSchwartz_eq_e_integral]
  calc
    _ = ∫ v : ℝ, ∑ n ∈ s,
        e (-(v * θ)) * localConvolutionTerm n (a n) H v := by
      apply integral_congr_ae
      filter_upwards with v
      change e (-(v * θ)) *
          (∑ n ∈ s, localConvolutionTerm n (a n) H v) =
        ∑ n ∈ s, e (-(v * θ)) * localConvolutionTerm n (a n) H v
      rw [Finset.mul_sum]
    _ = ∑ n ∈ s, ∫ v : ℝ,
        e (-(v * θ)) * localConvolutionTerm n (a n) H v :=
      integral_finsetSum s (fun n hn => localConvolutionTerm_phase_integrable n (a n) H θ hH)
    _ = ∑ n ∈ s,
        a n * e (-((n : ℝ) * θ)) * (H : ℂ) * localKernelFourier (-(H * θ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact localConvolutionTerm_fourier n (a n) H θ hH
    _ = (H : ℂ) * localKernelFourier (-(H * θ)) * localAdditivePolynomial s a (-θ) := by
      rw [localAdditivePolynomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hfreq : -((n : ℝ) * θ) = (-θ) * (n : ℝ) := by ring
      rw [hfreq]
      ring

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp [e, Complex.norm_exp]

@[simp] theorem norm_mellin (x t : ℝ) : ‖mellin x t‖ = 1 := by
  simp [Blueprint.Analytic.mellin, Complex.norm_exp]

theorem norm_localAdditivePolynomial_le (s : Finset ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    ‖localAdditivePolynomial s a θ‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  unfold localAdditivePolynomial
  calc
    ‖∑ n ∈ s, a n * e (θ * n)‖ ≤ ∑ n ∈ s, ‖a n * e (θ * n)‖ := norm_sum_le _ _
    _ = ∑ n ∈ s, ‖a n‖ := by simp [norm_e]

theorem continuous_localAdditivePolynomial (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (localAdditivePolynomial s a) := by
  unfold localAdditivePolynomial
  exact continuous_finsetSum _ (fun n _ => continuous_const.mul (by
    unfold e
    fun_prop))

theorem integrable_norm_sq_schwartz (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) := by
  have hnorm : Integrable (fun x : ℝ => ‖f x‖) := f.integrable.norm
  have hbound (x : ℝ) : ‖‖f x‖‖ ≤ (SchwartzMap.seminorm ℝ 0 0) f := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact SchwartzMap.norm_le_seminorm ℝ f x
  have hsq := hnorm.bdd_mul (f.continuous.norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall hbound)
  simpa [pow_two] using hsq

set_option maxHeartbeats 1000000 in
theorem localConvolution_energy_bound (s : Finset ℕ) (a : ℕ → ℂ)
    (H : ℝ) (hH : 0 < H) :
    (∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial s a θ‖ ^ 2) ≤
      4 / H ^ 2 * (∫ v : ℝ, ‖localConvolution s a H v‖ ^ 2) := by
  let lo : ℝ := -1 / H
  let hi : ℝ := 1 / H
  let F : 𝓢(ℝ, ℂ) := localConvolutionSchwartz s a H hH
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    have hp : 0 < 1 / H := one_div_pos.mpr hH
    have hstrict : -(1 / H) < 1 / H := by linarith [hp]
    simpa only [neg_div] using hstrict.le
  have hθBound (θ : ℝ) (hmem : θ ∈ Set.Icc lo hi) : |H * θ| ≤ 1 := by
    have hθabs : |θ| ≤ 1 / H := by
      have hθ' := hmem.1
      have hθ'' := hmem.2
      dsimp [lo, hi] at hθ' hθ''
      have hlow : -(1 / H) ≤ θ := by simpa only [neg_div] using hθ'
      exact abs_le.mpr ⟨hlow, hθ''⟩
    rw [abs_mul, abs_of_pos hH]
    calc
      H * |θ| ≤ H * (1 / H) := mul_le_mul_of_nonneg_left hθabs hH.le
      _ = 1 := by field_simp [hH.ne']
  have hpoint (θ : ℝ) (hmem : θ ∈ Set.Icc lo hi) :
      ‖localAdditivePolynomial s a (-θ)‖ ^ 2 ≤
        4 / H ^ 2 * ‖(𝓕 F) θ‖ ^ 2 := by
    have hlow := localKernelFourier_norm_lower (-(H * θ)) (by
      simpa only [abs_neg] using hθBound θ hmem)
    have hFEq : (𝓕 F) θ =
        (H : ℂ) * localKernelFourier (-(H * θ)) * localAdditivePolynomial s a (-θ) := by
      dsimp [F]
      exact localConvolutionFourier_eq s a H θ hH
    have hnorm : ‖(𝓕 F) θ‖ = H *
        ‖localKernelFourier (-(H * θ))‖ *
        ‖localAdditivePolynomial s a (-θ)‖ := by
      rw [hFEq, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hH]
    have hlin : ‖localAdditivePolynomial s a (-θ)‖ ≤
        (2 / H) * ‖(𝓕 F) θ‖ := by
      rw [hnorm]
      have hK : 1 ≤ 2 * ‖localKernelFourier (-(H * θ))‖ := by linarith
      calc
        ‖localAdditivePolynomial s a (-θ)‖ = 1 * ‖localAdditivePolynomial s a (-θ)‖ := by ring
        _ ≤ (2 * ‖localKernelFourier (-(H * θ))‖) *
            ‖localAdditivePolynomial s a (-θ)‖ :=
          mul_le_mul_of_nonneg_right hK (norm_nonneg _)
        _ = (2 / H) *
            (H * ‖localKernelFourier (-(H * θ))‖ *
              ‖localAdditivePolynomial s a (-θ)‖) := by
          field_simp [hH.ne']
    have hsq : ‖localAdditivePolynomial s a (-θ)‖ ^ 2 ≤
        ((2 / H) * ‖(𝓕 F) θ‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hlin 2
    have hcoef : (2 / H) ^ 2 = 4 / H ^ 2 := by field_simp [hH.ne']; ring
    rw [mul_pow] at hsq
    rw [hcoef] at hsq
    exact hsq
  let A : ℝ → ℝ := fun θ => ‖localAdditivePolynomial s a (-θ)‖ ^ 2
  let B : ℝ → ℝ := fun θ => (4 / H ^ 2) * ‖(𝓕 F) θ‖ ^ 2
  have hleftCont : Continuous A := by
    dsimp [A]
    exact ((continuous_localAdditivePolynomial s a).comp continuous_neg).norm.pow 2
  have hFourierCont : Continuous
      (fun θ : ℝ => (𝓕 F) θ) := by fun_prop
  have hrightCont : Continuous B := by
    dsimp [B]
    exact continuous_const.mul (hFourierCont.norm.pow 2)
  have hpoint' : ∀ θ ∈ Set.Icc lo hi, A θ ≤ B θ := by
    intro θ hθ
    exact hpoint θ hθ
  have hintervalCore : (∫ θ in lo..hi, A θ) ≤ ∫ θ in lo..hi, B θ := by
    apply intervalIntegral.integral_mono_on hlohi
      (hleftCont.intervalIntegrable lo hi) (hrightCont.intervalIntegrable lo hi)
    exact hpoint'
  have hinterval :
      (∫ θ in lo..hi, ‖localAdditivePolynomial s a (-θ)‖ ^ 2) ≤
        ∫ θ in lo..hi, B θ := by
    have hA : (∫ θ in lo..hi, ‖localAdditivePolynomial s a (-θ)‖ ^ 2) =
        ∫ θ in lo..hi, A θ := rfl
    rw [hA]
    exact hintervalCore
  have hsym :
      (∫ θ in lo..hi, ‖localAdditivePolynomial s a θ‖ ^ 2) =
        (∫ θ in lo..hi, ‖localAdditivePolynomial s a (-θ)‖ ^ 2) := by
    let G : ℝ → ℝ := fun θ => ‖localAdditivePolynomial s a θ‖ ^ 2
    change (∫ θ in lo..hi, G θ) = ∫ θ in lo..hi, G (-θ)
    have hstart : -hi = lo := by simp [lo, hi, neg_div]
    have hend : -lo = hi := by simp [lo, hi, neg_div]
    have hcomp := intervalIntegral.integral_comp_neg (f := G) (a := lo) (b := hi)
    have hcomp' : (∫ θ in lo..hi, G (-θ)) = ∫ θ in lo..hi, G θ := by
      simpa only [hstart, hend] using hcomp
    exact hcomp'.symm
  have hFint : Integrable (fun θ : ℝ => ‖(𝓕 F) θ‖ ^ 2) := by
    exact integrable_norm_sq_schwartz (𝓕 F)
  have hBint : Integrable B := by
    dsimp [B]
    simpa [mul_comm] using hFint.const_mul (4 / H ^ 2)
  have hBset : (∫ θ in Set.Ioc lo hi, B θ) ≤ ∫ θ : ℝ, B θ :=
    setIntegral_le_integral hBint (Filter.Eventually.of_forall fun θ => by positivity)
  have hBinterval : (∫ θ in lo..hi, B θ) ≤ ∫ θ : ℝ, B θ := by
    rw [intervalIntegral.integral_of_le hlohi]
    exact hBset
  have hBfull : (∫ θ : ℝ, B θ) =
      4 / H ^ 2 * (∫ θ : ℝ, ‖(𝓕 F) θ‖ ^ 2) := by
    dsimp [B]
    rw [integral_const_mul]
  calc
    _ = ∫ θ in lo..hi, ‖localAdditivePolynomial s a θ‖ ^ 2 := by
      dsimp [lo, hi]
    _ = ∫ θ in lo..hi, ‖localAdditivePolynomial s a (-θ)‖ ^ 2 := hsym
    _ ≤ ∫ θ in lo..hi, B θ := hinterval
    _ ≤ ∫ θ : ℝ, B θ := hBinterval
    _ = 4 / H ^ 2 * (∫ θ : ℝ, ‖(𝓕 F) θ‖ ^ 2) := hBfull
    _ = 4 / H ^ 2 * (∫ v : ℝ, ‖F v‖ ^ 2) := by
      rw [SchwartzMap.integral_norm_sq_fourier]

theorem norm_dp_le (s : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖dp s a t‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  unfold dp
  calc
    ‖∑ n ∈ s, a n * mellin n t‖ ≤ ∑ n ∈ s, ‖a n * mellin n t‖ := norm_sum_le _ _
    _ = ∑ n ∈ s, ‖a n‖ := by simp [norm_mellin]


end Erdos821.P5Energy
