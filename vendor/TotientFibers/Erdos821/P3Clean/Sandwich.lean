import Erdos821.P3Clean.Contractions

/-! The norm consequence of an exact conditioned bilinear-form identity. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem normBound_conditioned_form {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    (mass : α → ℝ) (targetMass : β → ℝ) (K : α → α → ℂ)
    (H : δ → β → β → ℂ) (P : δ → (α → ℂ) → β → ℂ) (C S : ℝ)
    (hm : ∀ b, 0 ≤ targetMass b) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hH : ∀ d, NormBound targetMass (H d) C)
    (hP : ∀ f, (∑ d, ∑ b, targetMass b * ‖P d f b‖ ^ 2) ≤
      S * ∑ a, mass a * ‖f a‖ ^ 2)
    (hform : ∀ f g,
      (∑ a, ∑ b, (mass a : ℂ) * star (f a) * K a b * g b) =
        ∑ d, ∑ a, ∑ b, (targetMass a : ℂ) * star (P d f a) * H d a b * P d g b) :
    NormBound mass K (C * S) := by
  apply (normBound_iff_univ _ _ _).mpr
  intro f g
  rw [hform]
  have h := sum_fibre_forms_bound targetMass H C hm hC hH
    (fun d => P d f) (fun d => P d g)
  have hbound := h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hP f)) hC)
    (Real.sqrt_le_sqrt (hP g)) (Real.sqrt_nonneg _)
    (mul_nonneg hC (Real.sqrt_nonneg _)))
  rw [Real.sqrt_mul hS, Real.sqrt_mul hS] at hbound
  have heq (U V : ℝ) : C * (Real.sqrt S * Real.sqrt U) * (Real.sqrt S * Real.sqrt V) =
      (C * S) * Real.sqrt U * Real.sqrt V := by
    calc
      _ = (C * (Real.sqrt S) ^ 2) * Real.sqrt U * Real.sqrt V := by ring
      _ = _ := by rw [Real.sq_sqrt hS]
  simpa only [heq] using hbound


end Erdos821.P3Clean
