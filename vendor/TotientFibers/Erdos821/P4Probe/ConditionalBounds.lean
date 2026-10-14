import Erdos821.P4Probe.Probability

set_option autoImplicit false
open scoped BigOperators

namespace Erdos821.P4Probe

lemma weighted_error_sum_bound {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) (unit error : ι → ℂ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hu : ∀ i, ‖unit i‖ ≤ 1) (hε : 0 ≤ ε)
    (he : ∀ i, ‖error i‖ ≤ ε * Real.sqrt (a i) * Real.sqrt (b i)) :
    ‖∑ i, (w i : ℂ) * unit i * error i‖ ≤
      ε * Real.sqrt (∑ i, w i * a i) * Real.sqrt (∑ i, w i * b i) := by
  calc
    _ ≤ ∑ i, ‖(w i : ℂ) * unit i * error i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ε * (w i * Real.sqrt (a i) * Real.sqrt (b i)) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      calc
        _ ≤ w i * ‖unit i‖ * (ε * Real.sqrt (a i) * Real.sqrt (b i)) :=
          mul_le_mul_of_nonneg_left (he i) (mul_nonneg (hw i) (norm_nonneg _))
        _ ≤ w i * 1 * (ε * Real.sqrt (a i) * Real.sqrt (b i)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hu i) (hw i)) (by positivity)
        _ = _ := by ring
    _ = ε * ∑ i, w i * Real.sqrt (a i) * Real.sqrt (b i) := (Finset.mul_sum ..).symm
    _ ≤ ε * (Real.sqrt (∑ i, w i * a i) * Real.sqrt (∑ i, w i * b i)) :=
      mul_le_mul_of_nonneg_left (weighted_sqrt_cauchy w a b hw ha hb) hε
    _ = _ := (mul_assoc ..).symm

end Erdos821.P4Probe
