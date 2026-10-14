import Erdos821.S34.Probability

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

theorem weighted_l1_le_l2 {α : Type*} [Fintype α] (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hprob : ∑ x, w x = 1) (f : α → ℂ) :
    (∑ x, w x * ‖f x‖) ≤ Real.sqrt (∑ x, w x * ‖f x‖ ^ 2) := by
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun x => w x * ‖f x‖) (f := w) (g := fun x => w x * ‖f x‖ ^ 2)
    (fun x _ => hw x) (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => le_of_eq (by ring))
  rw [hprob, one_mul] at hc
  have hn : 0 ≤ ∑ x, w x * ‖f x‖ := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (norm_nonneg _)
  have he : 0 ≤ ∑ x, w x * ‖f x‖ ^ 2 := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hs := Real.sq_sqrt he
  nlinarith [Real.sqrt_nonneg (∑ x, w x * ‖f x‖ ^ 2)]

theorem independent_pairing_bound {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (hwprob : ∑ x, w x = 1) (hvprob : ∑ y, v y = 1)
    (f : β → ℂ) (g : α → ℂ) (R : α → β → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hR : ∀ x y, ‖R x y‖ ≤ E) :
    ‖∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y‖ ≤
      E * Real.sqrt (∑ x, w x * ‖g x‖ ^ 2) * Real.sqrt (∑ y, v y * ‖f y‖ ^ 2) := by
  have hlw := weighted_l1_le_l2 w hw hwprob g
  have hlv := weighted_l1_le_l2 v hv hvprob f
  calc
    _ ≤ ∑ x, ∑ y, ‖(w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x, ∑ y, E * (w x * ‖g x‖) * (v y * ‖f y‖) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw x), abs_of_nonneg (hv y)]
      have h := mul_le_mul_of_nonneg_left (hR x y)
        (mul_nonneg (mul_nonneg (mul_nonneg (hw x) (hv y)) (norm_nonneg (f y))) (norm_nonneg (g x)))
      convert h using 1 <;> ring
    _ = E * (∑ x, w x * ‖g x‖) * (∑ y, v y * ‖f y‖) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ _ := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlw hE) hlv
        (Finset.sum_nonneg fun y _ => mul_nonneg (hv y) (norm_nonneg _)) (by positivity)

end Erdos821.S34Core
