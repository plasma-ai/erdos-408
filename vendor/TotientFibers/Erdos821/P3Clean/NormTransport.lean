import Erdos821.P3Clean.Contractions

/-! Equivalence and cutoff-subtype transport for finite-support norms. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem normBound_equiv {alpha beta : Type*} (mass : alpha → ℝ)
    (K : alpha → alpha → ℂ) (C : ℝ) (e : beta ≃ alpha) (hK : NormBound mass K C) :
    NormBound (fun b => mass (e b)) (fun a b => K (e a) (e b)) C := by
  classical
  intro s t f g
  have h := hK (s.map e.toEmbedding) (t.map e.toEmbedding)
    (fun a => f (e.symm a)) (fun b => g (e.symm b))
  simpa only [Finset.sum_map, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using h

theorem normBound_subtype_project {alpha : Type*} (mass : alpha → ℝ)
    (K : alpha → alpha → ℂ) (keep : alpha → Prop) (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hC : 0 ≤ C)
    (hK : NormBound (fun a : {a // keep a} => mass a.val) (fun a b => K a.val b.val) C) :
    NormBound mass (projectKernel keep K) C := by
  classical
  intro s t f g
  have h := hK (s.subtype keep) (t.subtype keep) (fun a => f a.val) (fun b => g b.val)
  rw [Finset.sum_subtype_eq_sum_filter (fun a => mass a * ‖f a‖ ^ 2),
    Finset.sum_subtype_eq_sum_filter (fun b => mass b * ‖g b‖ ^ 2)] at h
  have hform : (∑ a ∈ s.subtype keep, ∑ b ∈ t.subtype keep,
      (mass a.val : ℂ) * star (f a.val) * K a.val b.val * g b.val) =
      ∑ a ∈ s.filter keep, ∑ b ∈ t.filter keep,
        (mass a : ℂ) * star (f a) * K a b * g b := by
    have hi (a : alpha) : (∑ b ∈ t.subtype keep,
        (mass a : ℂ) * star (f a) * K a b.val * g b.val) =
        ∑ b ∈ t.filter keep, (mass a : ℂ) * star (f a) * K a b * g b :=
      Finset.sum_subtype_eq_sum_filter (fun b => (mass a : ℂ) * star (f a) * K a b * g b)
    simp only [hi]
    exact Finset.sum_subtype_eq_sum_filter
      (fun a => ∑ b ∈ t.filter keep, (mass a : ℂ) * star (f a) * K a b * g b)
  rw [hform] at h
  have he : (∑ a ∈ s, ∑ b ∈ t,
      (mass a : ℂ) * star (f a) * projectKernel keep K a b * g b) =
      ∑ a ∈ s.filter keep, ∑ b ∈ t.filter keep,
        (mass a : ℂ) * star (f a) * K a b * g b := by
    simp only [Finset.sum_filter, projectKernel]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : keep a
    · simp only [if_pos ha, true_and]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : keep b <;> simp [ha, hb]
    · simp [ha]
  rw [he]
  have hs : (∑ a ∈ s.filter keep, mass a * ‖f a‖ ^ 2) ≤ ∑ a ∈ s, mass a * ‖f a‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => mul_nonneg (hm a) (sq_nonneg _))
  have ht : (∑ b ∈ t.filter keep, mass b * ‖g b‖ ^ 2) ≤ ∑ b ∈ t, mass b * ‖g b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b _ _ => mul_nonneg (hm b) (sq_nonneg _))
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) hC)
    (Real.sqrt_le_sqrt ht) (Real.sqrt_nonneg _)
    (mul_nonneg hC (Real.sqrt_nonneg _)))


end Erdos821.P3Clean
