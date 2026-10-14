import Erdos821.S34.Core

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34.Proofs

theorem norm_weighted_sum_sq {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (f : α → ℂ) :
    ‖∑ x, (w x : ℂ) * f x‖ ^ 2 ≤ (∑ x, w x) * (∑ x, w x * ‖f x‖ ^ 2) := by
  have hn : ‖∑ x, (w x : ℂ) * f x‖ ≤ ∑ x, w x * ‖f x‖ := by
    calc
      _ ≤ ∑ x, ‖(w x : ℂ) * f x‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        simp [abs_of_nonneg (hw x)]
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun x => w x * ‖f x‖) (f := w) (g := fun x => w x * ‖f x‖ ^ 2)
    (fun x _ => hw x) (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => le_of_eq (by ring))
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc

theorem finite_collapse_l2 {α β : Type*} [Fintype α] [DecidableEq β]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (P : α → β) (f : α → ℂ)
    (s : Finset β) (R : ℝ) (hR : 0 ≤ R)
    (hρ : ∀ n ∈ s, (∑ x, if P x = n then w x else 0) ≤ R) :
    (∑ n ∈ s, ‖∑ x, if P x = n then (w x : ℂ) * f x else 0‖ ^ 2) ≤
      R * (∑ x, w x * ‖f x‖ ^ 2) := by
  have hcs (n : β) :
      ‖∑ x, if P x = n then (w x : ℂ) * f x else 0‖ ^ 2 ≤
        (∑ x, if P x = n then w x else 0) *
          (∑ x, if P x = n then w x * ‖f x‖ ^ 2 else 0) := by
    have h := norm_weighted_sum_sq (fun x => if P x = n then w x else 0)
      (fun x => by split_ifs <;> first | exact hw x | exact le_rfl) f
    simpa [apply_ite, ite_mul] using h
  have henergy :
      (∑ n ∈ s, ∑ x, if P x = n then w x * ‖f x‖ ^ 2 else 0) ≤
        ∑ x, w x * ‖f x‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro x _
    have hwf : 0 ≤ w x * ‖f x‖ ^ 2 := mul_nonneg (hw x) (sq_nonneg _)
    by_cases hx : P x ∈ s
    · simp [hx]
    · simp [hx, hwf]
  calc
    _ ≤ ∑ n ∈ s, R * (∑ x, if P x = n then w x * ‖f x‖ ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      exact (hcs n).trans (mul_le_mul_of_nonneg_right (hρ n hn)
        (Finset.sum_nonneg (fun x _ => by
          split_ifs
          · exact mul_nonneg (hw x) (sq_nonneg _)
          · exact le_rfl)))
    _ = R * (∑ n ∈ s, ∑ x, if P x = n then w x * ‖f x‖ ^ 2 else 0) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left henergy hR

theorem mass_nonneg (G : Core.PrimeGroups) (g : Fin G.size) : 0 ≤ Core.mass G g := by
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem mu_nonneg (G : Core.PrimeGroups) (g : Fin G.size) (p : ℕ) : 0 ≤ Core.mu G g p := by
  have h := mass_nonneg G g
  unfold Core.mu
  positivity

theorem tupleWeight_nonneg (G : Core.PrimeGroups) (k : Fin G.size → ℕ) (z : Core.Tuple G k) :
    0 ≤ Core.tupleWeight G k z := by
  exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun j _ => mu_nonneg G g (z g j).val

theorem tupleNorm_sq (G : Core.PrimeGroups) (k : Fin G.size → ℕ) (f : Core.Tuple G k → ℂ) :
    Core.tupleNorm G k f ^ 2 = ∑ z, Core.tupleWeight G k z * ‖f z‖ ^ 2 := by
  exact Real.sq_sqrt (Finset.sum_nonneg fun z _ =>
    mul_nonneg (tupleWeight_nonneg G k z) (sq_nonneg _))

/-- §3's fiber collapse bound for a test on the entire ordered tuple. -/
theorem collapse_l2 (G : Core.PrimeGroups) (k : Fin G.size → ℕ)
    (f : Core.Tuple G k → ℂ) (s : Finset ℕ) (R : ℝ)
    (hR : 0 ≤ R) (hρ : ∀ n ∈ s, Core.rho G k n ≤ R) :
    Core.sqNorm s (Core.collapse G k f) ≤ R * (Core.tupleNorm G k f) ^ 2 := by
  rw [tupleNorm_sq]
  have h := finite_collapse_l2 (Core.tupleWeight G k) (tupleWeight_nonneg G k)
    (Core.product G k) f s R hR hρ
  simpa [Core.sqNorm, Core.collapse, Core.expect, mul_ite] using h

end Erdos821.S34.Proofs
