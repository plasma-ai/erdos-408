import Erdos821.P5Energy.Kernel

/-! The Mellin kernel `M(t,t')`, its decay, and the Schur bound for the weighted
`u`-energy of the log-coordinate amplitude transform. -/

noncomputable section
open scoped BigOperators ContDiff FourierTransform
open MeasureTheory

namespace Erdos821.P5Energy
open Blueprint.Analytic

/-- `e^{i x}`. -/
def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  simp [phase, Complex.norm_exp_ofReal_mul_I]

theorem continuous_phase : Continuous phase := by
  unfold phase; fun_prop

/-- The amplitude with its oscillation, in log coordinates. -/
def ampE (h t u : ℝ) : ℂ := amp (h * t / (2 * Real.pi)) u * phase (-(t * u))

/-- Polynomial decay weight. -/
def omega (h : ℝ) (N : ℕ) (t : ℝ) : ℝ := ((1 + |h * t|) ^ N)⁻¹

/-- Schur kernel. -/
def kern (ξ : ℝ) : ℝ := (1 + ξ ^ 2)⁻¹

theorem omega_nonneg (h : ℝ) (N : ℕ) (t : ℝ) : 0 ≤ omega h N t := by
  unfold omega; positivity

theorem omega_le_one (h : ℝ) (N : ℕ) (t : ℝ) : omega h N t ≤ 1 := by
  unfold omega
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [abs_nonneg (h * t)])

theorem continuous_omega (h : ℝ) (N : ℕ) : Continuous (omega h N) := by
  unfold omega
  apply Continuous.inv₀ (by fun_prop)
  intro t; positivity

theorem integrable_omega {h : ℝ} (hh : h ≠ 0) {N : ℕ} (hN : 2 ≤ N) :
    Integrable (omega h N) := by
  have hint : Integrable (fun t : ℝ => (1 + (h * t) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hh
  refine hint.mono' (continuous_omega h N).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (omega_nonneg h N t)]
  unfold omega
  apply inv_anti₀ (by positivity)
  have h1 : 1 ≤ 1 + |h * t| := by linarith [abs_nonneg (h * t)]
  calc 1 + (h * t) ^ 2 ≤ (1 + |h * t|) ^ 2 := by
        nlinarith [sq_abs (h * t), abs_nonneg (h * t)]
    _ ≤ (1 + |h * t|) ^ N := pow_le_pow_right₀ h1 hN

theorem kern_nonneg (ξ : ℝ) : 0 ≤ kern ξ := by unfold kern; positivity

theorem continuous_kern : Continuous kern := by
  unfold kern
  apply Continuous.inv₀ (by fun_prop)
  intro t; positivity

theorem integrable_kern : Integrable kern := integrable_inv_one_add_sq

theorem integral_kern_sub (t : ℝ) : ∫ t' : ℝ, kern (t - t') = Real.pi := by
  rw [integral_sub_left_eq_self (fun x => kern x) volume t]
  exact integral_univ_inv_one_add_sq

/-- The Mellin kernel. -/
def Mker (h t t' : ℝ) : ℂ :=
  ∫ u : ℝ, logCompactWeight u * (ampE h t u * (starRingEnd ℂ) (ampE h t' u))

theorem Mker_eq_fourier (h t t' : ℝ) :
    Mker h t t' = 𝓕 (gfun (h * t / (2 * Real.pi)) (h * t' / (2 * Real.pi)))
      ((t - t') / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Mker]
  congr 1
  funext u
  have he : phase (-(t * u)) * (starRingEnd ℂ) (phase (-(t' * u))) =
      Complex.exp (((-2 * Real.pi * u * ((t - t') / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) := by
    unfold phase
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    field_simp
    ring
  rw [smul_eq_mul, ← he]
  unfold ampE gfun
  rw [map_mul]
  ring

theorem Mker_bound (N : ℕ) : ∃ Cm : ℝ, 0 < Cm ∧ ∀ h t t' : ℝ,
    ‖Mker h t t'‖ ≤ Cm * (omega h N t * omega h N t') * kern (t - t') := by
  obtain ⟨A, hA, hg⟩ := gfun_iter_bound N
  refine ⟨8 * A * (2 * Real.pi) ^ N * (2 * Real.pi) ^ N, by positivity, ?_⟩
  intro h t t'
  set c := h * t / (2 * Real.pi) with hc
  set c' := h * t' / (2 * Real.pi) with hc'
  have hpc : 0 < (1 + |c|) ^ N := by positivity
  have hpc' : 0 < (1 + |c'|) ^ N := by positivity
  have hdec := fourier_decay_of_compact (gfun_contDiff c c') (gfun_support c c')
    (A := A / ((1 + |c|) ^ N * (1 + |c'|) ^ N)) (fun i hi u => hg c c' i hi u)
    ((t - t') / (2 * Real.pi))
  have h2pi : 2 * Real.pi * ((t - t') / (2 * Real.pi)) = t - t' := by
    field_simp
  rw [h2pi, ← Mker_eq_fourier] at hdec
  -- compare the scales `c` and `h t`
  have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hscale : ∀ x : ℝ, (1 + |h * x|) ^ N ≤
      (2 * Real.pi) ^ N * (1 + |h * x / (2 * Real.pi)|) ^ N := by
    intro x
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : |h * x| = 2 * Real.pi * |h * x / (2 * Real.pi)| := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      field_simp
    rw [this]
    nlinarith [abs_nonneg (h * x / (2 * Real.pi))]
  have hw : ∀ x : ℝ, ((1 + |h * x / (2 * Real.pi)|) ^ N)⁻¹ ≤
      (2 * Real.pi) ^ N * omega h N x := by
    intro x
    unfold omega
    have hp1 : 0 < (1 + |h * x|) ^ N := by positivity
    have hp2 : 0 < (1 + |h * x / (2 * Real.pi)|) ^ N := by positivity
    rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ hp2, div_mul_eq_mul_div, le_div_iff₀ hp1]
    linarith [hscale x]
  have hk : 0 < 1 + (t - t') ^ 2 := by positivity
  have hM : ‖Mker h t t'‖ ≤ 8 * (A / ((1 + |c|) ^ N * (1 + |c'|) ^ N)) * kern (t - t') := by
    unfold kern
    rw [← div_eq_mul_inv, le_div_iff₀ hk]
    linarith
  refine hM.trans ?_
  have hwc := hw t
  have hwc' := hw t'
  rw [← hc] at hwc
  rw [← hc'] at hwc'
  have hprod : A / ((1 + |c|) ^ N * (1 + |c'|) ^ N) ≤
      A * ((2 * Real.pi) ^ N * omega h N t) * ((2 * Real.pi) ^ N * omega h N t') := by
    rw [div_eq_mul_inv, mul_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hwc hwc' (by positivity) (mul_nonneg (by positivity) (omega_nonneg _ _ _))) hA.le
  have hk0 := kern_nonneg (t - t')
  calc 8 * (A / ((1 + |c|) ^ N * (1 + |c'|) ^ N)) * kern (t - t') ≤
      8 * (A * ((2 * Real.pi) ^ N * omega h N t) * ((2 * Real.pi) ^ N * omega h N t')) *
        kern (t - t') := by gcongr
    _ = _ := by ring

end Erdos821.P5Energy
