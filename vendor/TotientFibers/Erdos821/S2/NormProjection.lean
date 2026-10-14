import Erdos821.Blueprint.Graph

/-! Restricting both endpoint states preserves a nonnegative weighted norm bound. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem normBound_project {α : Type*} (mass : α → ℝ) (K : α → α → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hm : ∀ a, 0 ≤ mass a)
    (hK : NormBound mass K C) (keep : α → Prop) :
    NormBound mass (projectKernel keep K) C := by
  intro s t f g
  have he :
      (∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) * projectKernel keep K a b * g b) =
        ∑ a ∈ s.filter keep, ∑ b ∈ t.filter keep,
          (mass a : ℂ) * star (f a) * K a b * g b := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : keep a
    · simp only [ha, ite_true]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : keep b <;> simp [projectKernel, ha, hb]
    · simp [projectKernel, ha]
  rw [he]
  have hs : (∑ a ∈ s.filter keep, mass a * ‖f a‖ ^ 2) ≤
      ∑ a ∈ s, mass a * ‖f a‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => mul_nonneg (hm a) (sq_nonneg _))
  have ht : (∑ b ∈ t.filter keep, mass b * ‖g b‖ ^ 2) ≤
      ∑ b ∈ t, mass b * ‖g b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b _ _ => mul_nonneg (hm b) (sq_nonneg _))
  calc
    _ ≤ C * Real.sqrt (∑ a ∈ s.filter keep, mass a * ‖f a‖ ^ 2) *
        Real.sqrt (∑ b ∈ t.filter keep, mass b * ‖g b‖ ^ 2) := hK _ _ f g
    _ ≤ C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
        Real.sqrt (∑ b ∈ t.filter keep, mass b * ‖g b‖ ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) hC) (Real.sqrt_nonneg _)
    _ ≤ C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
        Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht) (mul_nonneg hC (Real.sqrt_nonneg _))


end Erdos821.S2Core
