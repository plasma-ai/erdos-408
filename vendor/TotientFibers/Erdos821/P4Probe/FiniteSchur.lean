import Erdos821.P4Probe.FinitePairing

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma finite_schur {β : Type*} [Fintype β] (mass : β → ℝ) (K : β → β → ℂ) (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hC : 0 ≤ C)
    (hrow : ∀ a, ∑ b, ‖K a b‖ ≤ C)
    (hcol : ∀ b, ∑ a, mass a * ‖K a b‖ ≤ C * mass b) :
    NormBound mass K C := by
  apply normBound_of_full_pair
  intro f g
  let w : β × β → ℝ := fun z => mass z.1 * ‖K z.1 z.2‖
  have hw : ∀ z, 0 ≤ w z := fun z => mul_nonneg (hm z.1) (norm_nonneg _)
  have hu : (∑ z : β × β, w z * ‖f z.1‖ ^ 2) ≤ C * ∑ a, mass a * ‖f a‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    dsimp [w]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    calc
      (∑ b, mass a * ‖K a b‖ * ‖f a‖ ^ 2) =
          mass a * ‖f a‖ ^ 2 * ∑ b, ‖K a b‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ ≤ mass a * ‖f a‖ ^ 2 * C :=
        mul_le_mul_of_nonneg_left (hrow a) (mul_nonneg (hm a) (sq_nonneg _))
      _ = _ := by ring
  have hv : (∑ z : β × β, w z * ‖g z.2‖ ^ 2) ≤ C * ∑ b, mass b * ‖g b‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    dsimp [w]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    calc
      (∑ a, mass a * ‖K a b‖ * ‖g b‖ ^ 2) =
          (∑ a, mass a * ‖K a b‖) * ‖g b‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (C * mass b) * ‖g b‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hcol b) (sq_nonneg _)
      _ = _ := by ring
  have hcs := weighted_sqrt_cauchy w (fun z => ‖f z.1‖ ^ 2) (fun z => ‖g z.2‖ ^ 2)
    hw (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hnorm : ‖∑ a, ∑ b, (mass a : ℂ) * star (f a) * K a b * g b‖ ≤
      ∑ z : β × β, w z * Real.sqrt (‖f z.1‖ ^ 2) * Real.sqrt (‖g z.2‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    simp only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ∑ a, ∑ b, ‖(mass a : ℂ) * star (f a) * K a b * g b‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hm a), w]
        ring
  have hNF : 0 ≤ ∑ a, mass a * ‖f a‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hm a) (sq_nonneg _))
  have hNG : 0 ≤ ∑ b, mass b * ‖g b‖ ^ 2 :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (hm b) (sq_nonneg _))
  calc
    _ ≤ Real.sqrt (∑ z : β × β, w z * ‖f z.1‖ ^ 2) *
        Real.sqrt (∑ z : β × β, w z * ‖g z.2‖ ^ 2) := hnorm.trans hcs
    _ ≤ Real.sqrt (C * ∑ a, mass a * ‖f a‖ ^ 2) *
        Real.sqrt (C * ∑ b, mass b * ‖g b‖ ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hC, Real.sqrt_mul hC]
      calc
        _ = (Real.sqrt C) ^ 2 * Real.sqrt (∑ a, mass a * ‖f a‖ ^ 2) *
            Real.sqrt (∑ b, mass b * ‖g b‖ ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hC]

end
end Erdos821.P4Probe
