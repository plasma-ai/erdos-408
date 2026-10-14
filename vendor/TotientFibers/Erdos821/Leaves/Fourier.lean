import Mathlib
import Erdos821.Blueprint.Graph
import Erdos821.Blueprint.Analytic

open scoped BigOperators
open MeasureTheory intervalIntegral

attribute [local instance] Classical.propDecidable

namespace Erdos821.Blueprint.Graph

/-- §1 phase orthogonality on [0,1]: integral is 1 at h=0, else 0. -/
theorem return_fourier (h : ℤ) :
    (∫ θ : ℝ in (0 : ℝ)..1, phase (θ * h)) = if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst hh
    simp [phase]
  · simp only [hh, ite_false]
    set c : ℂ := 2 * Real.pi * (h : ℂ) * Complex.I with hc_def
    have hc_ne : c ≠ 0 := by
      rw [hc_def]
      apply mul_ne_zero
      apply mul_ne_zero
      apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
      · exact_mod_cast hh
      · exact Complex.I_ne_zero
    have hintegrand : (fun θ : ℝ => phase (θ * (h : ℝ)))
        = (fun θ : ℝ => Complex.exp (c * (θ : ℂ))) := by
      funext θ
      simp only [phase, hc_def]
      congr 1
      push_cast
      ring
    have hexp1 : Complex.exp c = 1 := by
      rw [hc_def]
      have hrew : (2 : ℂ) * Real.pi * (h : ℂ) * Complex.I
          = (h : ℂ) * (2 * Real.pi * Complex.I) := by ring
      rw [hrew]
      exact Complex.exp_int_mul_two_pi_mul_I h
    rw [hintegrand, integral_exp_mul_complex hc_ne]
    simp [hexp1]

example : @Erdos821.Blueprint.Graph.return_fourier =
    @Erdos821.Blueprint.Graph.return_fourier := rfl

end Erdos821.Blueprint.Graph
