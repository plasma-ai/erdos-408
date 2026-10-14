import Erdos821.P5Energy.Mellin

/-! Schur bound for the weighted `u`-energy of the log-coordinate amplitude transform:
expanding the square, Fubini, the Mellin kernel decay and AM–GM. No Plancherel or
Minkowski inequality in `u` is needed. -/

noncomputable section
open scoped BigOperators ContDiff FourierTransform ComplexConjugate
open MeasureTheory

namespace Erdos821.P5Energy
open Blueprint.Analytic

theorem inv_scale_le_omega (h : ℝ) (N : ℕ) (x : ℝ) :
    ((1 + |h * x / (2 * Real.pi)|) ^ N)⁻¹ ≤ (2 * Real.pi) ^ N * omega h N x := by
  have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hscale : (1 + |h * x|) ^ N ≤ (2 * Real.pi) ^ N * (1 + |h * x / (2 * Real.pi)|) ^ N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : |h * x| = 2 * Real.pi * |h * x / (2 * Real.pi)| := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      field_simp
    rw [this]
    nlinarith [abs_nonneg (h * x / (2 * Real.pi))]
  unfold omega
  have hp1 : 0 < (1 + |h * x|) ^ N := by positivity
  have hp2 : 0 < (1 + |h * x / (2 * Real.pi)|) ^ N := by positivity
  rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ hp2, div_mul_eq_mul_div, le_div_iff₀ hp1]
  linarith

theorem ampE_le_omega (N : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ h t u : ℝ, u ≤ 2 →
    ‖ampE h t u‖ ≤ B * omega h N t := by
  obtain ⟨B, hB, hamp⟩ := amp_iter_bound_le_two N
  refine ⟨B * (2 * Real.pi) ^ N, by positivity, ?_⟩
  intro h t u hu
  have h0 := hamp 0 (by norm_num) (h * t / (2 * Real.pi)) u hu
  rw [norm_iteratedFDeriv_zero] at h0
  rw [ampE, norm_mul, norm_phase, mul_one]
  refine h0.trans ?_
  rw [div_eq_mul_inv, mul_assoc]
  exact mul_le_mul_of_nonneg_left (inv_scale_le_omega h N t) hB.le

theorem logCompactWeight_integrable : Integrable logCompactWeight :=
  logCompactWeight_contDiff.continuous.integrable_of_hasCompactSupport
    logCompactWeight_hasCompactSupport

theorem logCutoff_nonneg (u : ℝ) : 0 ≤ logCutoff u := logCutoffBump.nonneg

/-- Integrand of the log-coordinate amplitude transform. -/
def EE (h : ℝ) (P : ℝ → ℂ) (u t : ℝ) : ℂ := ampE h t u * P t

/-- Weighted density in the Schur bound. -/
def FF (h : ℝ) (N : ℕ) (P : ℝ → ℂ) (t : ℝ) : ℝ := omega h N t ^ 2 * ‖P t‖ ^ 2

/-- The weighted energy bound in log coordinates. -/
theorem weighted_energy_bound (N : ℕ) (hN : 2 ≤ N) : ∃ C : ℝ, 0 < C ∧
    ∀ (h : ℝ), 0 < h → ∀ (P : ℝ → ℂ) (S : ℝ), Continuous P → (∀ t, ‖P t‖ ≤ S) →
      (∫ u : ℝ, logCutoff u * Real.exp (-u) * ‖∫ t : ℝ, ampE h t u * P t‖ ^ 2) ≤
        C * ∫ t : ℝ, omega h N t * ‖P t‖ ^ 2 := by
  obtain ⟨Cm, hCm, hM⟩ := Mker_bound N
  obtain ⟨B, hB, hamp⟩ := ampE_le_omega N
  refine ⟨Cm * Real.pi, by positivity, ?_⟩
  intro h hh P S hP hS
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  set w := logCompactWeight with hw_def
  set E : ℝ → ℝ → ℂ := EE h P with hE_def
  set I : ℝ → ℂ := fun u => ∫ t, E u t with hI_def
  set F : ℝ → ℝ := FF h N P with hF_def
  have homega := integrable_omega hh.ne' hN
  -- continuity facts
  have hKc : Continuous localKernelFourier := localKernelFourier_contDiff.continuous
  have hwc : Continuous w := logCompactWeight_contDiff.continuous
  have hEc : Continuous (fun q : ℝ × ℝ => E q.1 q.2) := by
    simp only [E, EE, ampE, amp, phase]
    fun_prop
  have hFc : Continuous F := by
    simp only [F, FF]
    exact ((continuous_omega h N).pow 2).mul (hP.norm.pow 2)
  -- pointwise bound on E on the support of the weight
  have hEb : ∀ u t, w u ≠ 0 → ‖E u t‖ ≤ B * omega h N t * S := by
    intro u t hu
    have hu2 : u ≤ 2 := (logCompactWeight_support_subset (Function.mem_support.mpr hu)).2
    simp only [E, EE, norm_mul]
    exact mul_le_mul (hamp h t u hu2) (hS t) (norm_nonneg _)
      (mul_nonneg hB.le (omega_nonneg _ _ _))
  -- Step 1: the real energy as a complex integral
  have hkey : ∀ u, ((logCutoff u * Real.exp (-u) * ‖I u‖ ^ 2 : ℝ) : ℂ) =
      w u * (I u * conj (I u)) := by
    intro u
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [w, logCompactWeight, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
  -- Step 2: the square as a double integral
  have hsq : ∀ u, I u * conj (I u) = ∫ p : ℝ × ℝ, E u p.1 * conj (E u p.2) := by
    intro u
    simp only [I]
    rw [← integral_conj, Measure.volume_eq_prod]
    exact (integral_prod_mul (E u) (fun t => conj (E u t))).symm
  -- Step 3: Fubini
  let f3 : ℝ → ℝ × ℝ → ℂ := fun u p => w u * (E u p.1 * conj (E u p.2))
  have hint3 : Integrable (Function.uncurry f3) (volume.prod volume) := by
    have hmaj : Integrable (fun q : ℝ × (ℝ × ℝ) =>
        ‖w q.1‖ * ((B * S) ^ 2 * (omega h N q.2.1 * omega h N q.2.2))) (volume.prod volume) := by
      refine logCompactWeight_integrable.norm.mul_prod
        (g := fun p : ℝ × ℝ => (B * S) ^ 2 * (omega h N p.1 * omega h N p.2)) ?_
      rw [Measure.volume_eq_prod]
      exact (homega.mul_prod homega).const_mul _
    refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · apply Continuous.aestronglyMeasurable
      simp only [f3]
      have h1 : Continuous (fun q : ℝ × (ℝ × ℝ) => E q.1 q.2.1) :=
        hEc.comp (f := fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.1)) (by fun_prop)
      have h2 : Continuous (fun q : ℝ × (ℝ × ℝ) => E q.1 q.2.2) :=
        hEc.comp (f := fun q : ℝ × (ℝ × ℝ) => (q.1, q.2.2)) (by fun_prop)
      exact (hwc.comp continuous_fst).mul (h1.mul (Complex.continuous_conj.comp h2))
    · simp only [Function.uncurry, f3, norm_mul, Complex.norm_conj]
      by_cases hw0 : w q.1 = 0
      · rw [hw0, norm_zero, zero_mul, zero_mul]
      · have e1 := hEb q.1 q.2.1 hw0
        have e2 := hEb q.1 q.2.2 hw0
        have : ‖E q.1 q.2.1‖ * ‖E q.1 q.2.2‖ ≤
            (B * S) ^ 2 * (omega h N q.2.1 * omega h N q.2.2) := by
          calc ‖E q.1 q.2.1‖ * ‖E q.1 q.2.2‖ ≤
              (B * omega h N q.2.1 * S) * (B * omega h N q.2.2 * S) :=
                mul_le_mul e1 e2 (norm_nonneg _)
                  (mul_nonneg (mul_nonneg hB.le (omega_nonneg _ _ _)) hS0)
            _ = _ := by ring
        exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  -- Step 4: the inner integral is the Mellin kernel
  have hinner : ∀ p : ℝ × ℝ, ∫ u, f3 u p = P p.1 * conj (P p.2) * Mker h p.1 p.2 := by
    intro p
    rw [Mker, ← integral_const_mul]
    congr 1
    funext u
    simp only [f3, E, EE, map_mul]
    ring
  have hJ : ((∫ u : ℝ, logCutoff u * Real.exp (-u) * ‖I u‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, P p.1 * conj (P p.2) * Mker h p.1 p.2 := by
    rw [← integral_complex_ofReal]
    simp_rw [hkey, hsq]
    calc (∫ u, w u * ∫ p : ℝ × ℝ, E u p.1 * conj (E u p.2)) = ∫ u, ∫ p, f3 u p := by
          congr 1; funext u; rw [← integral_const_mul]
      _ = ∫ p, ∫ u, f3 u p := by
          exact integral_integral_swap hint3
      _ = _ := by congr 1; funext p; exact hinner p
  -- Step 5: Schur majorant
  have hFint : Integrable F := by
    refine (homega.const_mul (S ^ 2)).mono' hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [F, FF]
    have ho := omega_nonneg h N t
    have ho1 := omega_le_one h N t
    have hPt : ‖P t‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hS t) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc omega h N t ^ 2 * ‖P t‖ ^ 2 ≤ omega h N t * S ^ 2 := by
          apply mul_le_mul _ hPt (by positivity) ho
          nlinarith
      _ = S ^ 2 * omega h N t := by ring
  let G1 : ℝ × ℝ → ℝ := fun p => F p.1 * kern (p.1 - p.2)
  let G2 : ℝ × ℝ → ℝ := fun p => F p.2 * kern (p.1 - p.2)
  have hG1int : Integrable G1 (volume.prod volume) := by
    rw [integrable_prod_iff]
    · constructor
      · exact Filter.Eventually.of_forall fun t =>
          (integrable_kern.comp_sub_left t).const_mul (F t)
      · have : (fun t => ∫ t', ‖G1 (t, t')‖) = fun t => F t * Real.pi := by
          funext t
          simp only [G1]
          have hF0 : 0 ≤ F t := by simp only [F, FF]; positivity
          simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hF0 (kern_nonneg _))]
          rw [integral_const_mul, integral_kern_sub]
        rw [this]
        exact hFint.mul_const _
    · exact (hFc.comp continuous_fst |>.mul (continuous_kern.comp (by fun_prop))).aestronglyMeasurable
  have hG2eq : G2 = G1 ∘ Prod.swap := by
    funext p
    simp only [G1, G2, Function.comp, Prod.fst_swap, Prod.snd_swap, kern]
    congr 2
    ring
  have hG2int : Integrable G2 (volume.prod volume) := by
    rw [hG2eq]; exact hG1int.swap
  have hG1 : ∫ p, G1 p ∂(volume.prod volume) = Real.pi * ∫ t, F t := by
    rw [integral_prod G1 hG1int]
    simp only [G1]
    simp_rw [integral_const_mul, integral_kern_sub]
    rw [integral_mul_const]; ring
  have hG2 : ∫ p, G2 p ∂(volume.prod volume) = Real.pi * ∫ t, F t := by
    rw [hG2eq, ← hG1]
    exact integral_prod_swap G1
  have hpt : ∀ p : ℝ × ℝ, ‖P p.1 * conj (P p.2) * Mker h p.1 p.2‖ ≤
      Cm / 2 * (G1 p + G2 p) := by
    intro p
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hMp := hM h p.1 p.2
    have hk := kern_nonneg (p.1 - p.2)
    have ha := mul_nonneg (norm_nonneg (P p.1)) (omega_nonneg h N p.1)
    have hb := mul_nonneg (norm_nonneg (P p.2)) (omega_nonneg h N p.2)
    have hamgm : (‖P p.1‖ * omega h N p.1) * (‖P p.2‖ * omega h N p.2) ≤
        ((‖P p.1‖ * omega h N p.1) ^ 2 + (‖P p.2‖ * omega h N p.2) ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖P p.1‖ * omega h N p.1 - ‖P p.2‖ * omega h N p.2)]
    calc ‖P p.1‖ * ‖P p.2‖ * ‖Mker h p.1 p.2‖ ≤
        ‖P p.1‖ * ‖P p.2‖ * (Cm * (omega h N p.1 * omega h N p.2) * kern (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_left hMp (by positivity)
      _ = Cm * kern (p.1 - p.2) *
          ((‖P p.1‖ * omega h N p.1) * (‖P p.2‖ * omega h N p.2)) := by ring
      _ ≤ Cm * kern (p.1 - p.2) *
          (((‖P p.1‖ * omega h N p.1) ^ 2 + (‖P p.2‖ * omega h N p.2) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hamgm (by positivity)
      _ = Cm / 2 * (G1 p + G2 p) := by simp only [G1, G2, F, FF]; ring
  have hnorm : ‖∫ p : ℝ × ℝ, P p.1 * conj (P p.2) * Mker h p.1 p.2‖ ≤
      Cm * Real.pi * ∫ t, F t := by
    rw [Measure.volume_eq_prod]
    refine (norm_integral_le_of_norm_le ((hG1int.add hG2int).const_mul (Cm / 2))
      (Filter.Eventually.of_forall hpt)).trans_eq ?_
    rw [integral_const_mul]
    change Cm / 2 * ∫ a, (G1 a + G2 a) ∂(volume.prod volume) = _
    rw [integral_add hG1int hG2int, hG1, hG2]
    ring
  -- Step 6: conclude
  have hJle : (∫ u : ℝ, logCutoff u * Real.exp (-u) * ‖I u‖ ^ 2) ≤ Cm * Real.pi * ∫ t, F t := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hJ]
    exact hnorm
  have hFle : ∫ t, F t ≤ ∫ t, omega h N t * ‖P t‖ ^ 2 := by
    apply integral_mono hFint
    · refine (homega.const_mul (S ^ 2)).mono'
        ((continuous_omega h N).mul (hP.norm.pow 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ?_)
      have ho := omega_nonneg h N t
      have hPt : ‖P t‖ ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hS t) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith
    · intro t
      simp only [F, FF]
      have ho := omega_nonneg h N t
      have ho1 := omega_le_one h N t
      have : omega h N t ^ 2 ≤ omega h N t := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
  exact hJle.trans (mul_le_mul_of_nonneg_left hFle (by positivity))

end Erdos821.P5Energy
