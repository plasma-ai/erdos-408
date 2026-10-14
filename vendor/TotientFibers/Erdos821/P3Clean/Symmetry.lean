import Erdos821.P3Clean.Contractions

/-! Endpoint reindexing and finite convex averaging for the clean symmetrizations. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem normBound_relabel {α : Type*} (mass : α → ℝ)
    (K : α → α → ℂ) (C : ℝ) (hK : NormBound mass K C) (e d : α ≃ α)
    (he : ∀ a, mass (e a) = mass a) (hd : ∀ a, mass (d a) = mass a) :
    NormBound mass (fun a b => K (e a) (d b)) C := by
  classical
  intro s t f g
  have h := hK (s.map e.toEmbedding) (t.map d.toEmbedding)
    (fun a => f (e.symm a)) (fun b => g (d.symm b))
  simpa only [Finset.sum_map, Equiv.toEmbedding_apply,
    e.symm_apply_apply, d.symm_apply_apply, he, hd] using h

theorem normBound_convex_sum {α β : Type*} [Fintype β]
    (mass : α → ℝ) (K : β → α → α → ℂ) (w : β → ℝ) (C : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (hK : ∀ j, NormBound mass (K j) C) :
    NormBound mass (fun a b => ∑ j, (w j : ℂ) * K j a b) C := by
  intro s t f g
  have hform : (∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) *
      (∑ j, (w j : ℂ) * K j a b) * g b) =
      ∑ j, (w j : ℂ) * ∑ a ∈ s, ∑ b ∈ t,
        (mass a : ℂ) * star (f a) * K j a b * g b := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hform]
  calc
    _ ≤ ∑ j, ‖(w j : ℂ) * ∑ a ∈ s, ∑ b ∈ t,
        (mass a : ℂ) * star (f a) * K j a b * g b‖ := norm_sum_le _ _
    _ = ∑ j, w j * ‖∑ a ∈ s, ∑ b ∈ t,
        (mass a : ℂ) * star (f a) * K j a b * g b‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]
    _ ≤ ∑ j, w j * (C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
        Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hK j s t f g) (hw j)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]


end Erdos821.P3Clean
