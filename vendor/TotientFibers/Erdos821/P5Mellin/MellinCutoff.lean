import Erdos821.P5.MellinCutoffTask
import Erdos821.P5Mellin.FourierBridge

open MeasureTheory Filter
open scoped BigOperators ContDiff

namespace Erdos821.P5Mellin

open Erdos821.Blueprint.Analytic

noncomputable section

theorem mellinCutoffTask_proof : Erdos821.P5Core.MellinCutoffTask := by
  intro hFourier C lo hi bounds hC hlo hlohi hbounds
  let R : ℝ := |Real.log lo| + |Real.log hi| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  let bounds₁ : ℕ → ℝ := fun j => piExpCompDerivativeConstant hi bounds j
  have hbounds₁ : ∀ j, 0 ≤ bounds₁ j := by
    intro j
    exact piExpCompDerivativeConstant_nonneg hi bounds hbounds j
  obtain ⟨Cf, K, hCf, hK, hFourierA⟩ :=
    hFourier 1 C R hC hR bounds₁ hbounds₁
  have hCfpos : 0 < Cf := lt_trans hC hCf
  refine ⟨Cf, K, hCfpos, hK, ?_⟩
  intro A hA
  obtain ⟨KA, hKA, hEvent⟩ := hFourierA A hA
  refine ⟨KA, hKA, ?_⟩
  have hLlarge : ∀ᶠ x : ℝ in atTop, 1 ≤ L x := by
    apply Filter.eventually_atTop.2
    refine ⟨Real.exp 1, ?_⟩
    intro x hx
    change 1 ≤ Real.log x
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 1) hx
  filter_upwards [hEvent, hLlarge] with x hx hL
  intro Ψ hcut
  let F : (Fin 1 → ℝ) → ℂ := (Ψ ∘ Real.exp) ∘ coordinateEval
  have hFsmooth : ContDiff ℝ ∞ F := by
    dsimp [F]
    exact (hcut.1.comp Real.contDiff_exp).comp_continuousLinearMap
      (g := coordinateEval)
  have hFsupport : Function.support F ⊆ Metric.closedBall 0 R := by
    intro y hy
    have hFne : F y ≠ 0 := Function.mem_support.mp hy
    have hΨne : Ψ (Real.exp (y 0)) ≠ 0 := by
      simpa [F, coordinateEval] using hFne
    have hinterval := hcut.2.1 (Function.mem_support.mpr hΨne)
    have hloglo : Real.log lo ≤ y 0 := by
      calc
        Real.log lo ≤ Real.log (Real.exp (y 0)) := Real.log_le_log hlo hinterval.1
        _ = y 0 := Real.log_exp _
    have hloghi : y 0 ≤ Real.log hi := by
      calc
        y 0 = Real.log (Real.exp (y 0)) := (Real.log_exp _).symm
        _ ≤ Real.log hi := Real.log_le_log (Real.exp_pos _) hinterval.2
    have habs : |y 0| ≤ R := by
      apply abs_le.mpr
      constructor <;> dsimp [R] <;>
        nlinarith [neg_abs_le (Real.log lo), le_abs_self (Real.log hi),
          abs_nonneg (Real.log lo), abs_nonneg (Real.log hi)]
    have hyNorm : ‖y‖ ≤ R := by
      apply (pi_norm_le_iff_of_nonneg (x := y) (r := R) hR.le).2
      intro i
      have hi0 : i = 0 := Subsingleton.elim i 0
      subst i
      change |y 0| ≤ R
      exact habs
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    exact hyNorm
  have hFderiv : ∀ j y,
      ‖iteratedFDeriv ℝ j F y‖ ≤ bounds₁ j * L x ^ (C * ((j : ℝ) + 1)) := by
    intro j y
    change ‖iteratedFDeriv ℝ j ((Ψ ∘ Real.exp) ∘ coordinateEval) y‖ ≤ _
    exact pi_exp_comp_iteratedFDeriv_bound x C lo hi bounds Ψ hC hbounds hcut hL j y
  obtain ⟨a, ha, hMass, hRepresentation, hTail⟩ :=
    hx  F hFsmooth hFsupport hFderiv
  refine ⟨a, ha, hMass, ?_, hTail⟩
  intro t ht
  let y : Fin 1 → ℝ := fun _ => Real.log t
  calc
    Ψ t = F y := by
      simp [F, y, coordinateEval, Real.exp_log ht]
    _ = ∫ ξ, a ξ * e (∑ i, ξ i * y i) := hRepresentation y
    _ = ∫ ξ, a ξ * mellin t (2 * Real.pi * ξ 0) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [show e (∑ i, ξ i * y i) = mellin t (2 * Real.pi * ξ 0) by
        simpa [y] using mellinCharacter_eq_fourier ξ t]

end
end Erdos821.P5Mellin

