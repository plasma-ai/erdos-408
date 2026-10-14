import Erdos821.P3Clean.Sandwich

/-! Recover a conditioned bilinear form from an entrywise matrix factorization. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

def finiteLinearMap {α β : Type*} [Fintype α] (B : β → α → ℂ) (f : α → ℂ) (y : β) : ℂ :=
  ∑ a, B y a * f a

theorem finiteLinearMap_form_entry {α β : Type*} [Fintype α]
    (B : β → α → ℂ) (mass : β → ℝ) (H : β → β → ℂ)
    (f g : α → ℂ) (y z : β) :
    (mass y : ℂ) * star (finiteLinearMap B f y) * H y z * finiteLinearMap B g z =
      ∑ a, ∑ b, star (f a) * ((mass y : ℂ) * star (B y a) * H y z * B z b) * g b := by
  simp only [finiteLinearMap, star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrixSandwich_form {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    (mass : α → ℝ) (targetMass : β → ℝ) (K : α → α → ℂ)
    (H : δ → β → β → ℂ) (B : δ → β → α → ℂ)
    (hentry : ∀ a b, (mass a : ℂ) * K a b =
      ∑ d, ∑ y, ∑ z, (targetMass y : ℂ) * star (B d y a) * H d y z * B d z b)
    (f g : α → ℂ) :
    (∑ a, ∑ b, (mass a : ℂ) * star (f a) * K a b * g b) =
      ∑ d, ∑ y, ∑ z, (targetMass y : ℂ) *
        star (finiteLinearMap (B d) f y) * H d y z * finiteLinearMap (B d) g z := by
  have he (a b : α) : (mass a : ℂ) * star (f a) * K a b * g b =
      ∑ d, ∑ y, ∑ z, star (f a) *
        ((targetMass y : ℂ) * star (B d y a) * H d y z * B d z b) * g b := by
    calc
      _ = star (f a) * ((mass a : ℂ) * K a b) * g b := by ring
      _ = _ := by rw [hentry]; simp only [Finset.mul_sum, Finset.sum_mul]
  simp only [he, finiteLinearMap_form_entry]
  calc
    (∑ a, ∑ b, ∑ d, ∑ y, ∑ z, star (f a) *
        ((targetMass y : ℂ) * star (B d y a) * H d y z * B d z b) * g b) =
        ∑ a, ∑ d, ∑ y, ∑ z, ∑ b, star (f a) *
          ((targetMass y : ℂ) * star (B d y a) * H d y z * B d z b) * g b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]

theorem normBound_matrixSandwich {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    (mass : α → ℝ) (targetMass : β → ℝ) (K : α → α → ℂ)
    (H : δ → β → β → ℂ) (B : δ → β → α → ℂ) (C S : ℝ)
    (hm : ∀ y, 0 ≤ targetMass y) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hH : ∀ d, NormBound targetMass (H d) C)
    (hB : ∀ f, (∑ d, ∑ y, targetMass y * ‖finiteLinearMap (B d) f y‖ ^ 2) ≤
      S * ∑ a, mass a * ‖f a‖ ^ 2)
    (hentry : ∀ a b, (mass a : ℂ) * K a b =
      ∑ d, ∑ y, ∑ z, (targetMass y : ℂ) * star (B d y a) * H d y z * B d z b) :
    NormBound mass K (C * S) := by
  exact normBound_conditioned_form mass targetMass K H
    (fun d => finiteLinearMap (B d)) C S hm hC hS hH hB
    (matrixSandwich_form mass targetMass K H B hentry)


end Erdos821.P3Clean
