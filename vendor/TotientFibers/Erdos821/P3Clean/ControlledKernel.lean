import Erdos821.P3Clean.ActionLifting

/-! Kernel formulation of the finite weighted action norm bridge. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

def controlledKernel {α G V : Type*} [Fintype G]
    (H : α → α → G → ℂ) (act : G → V ≃ V) (a b : α × V) : ℂ :=
  ∑ r : G, if act r a.2 = b.2 then H a.1 b.1 r else 0

theorem controlledKernel_row {α G V : Type*} [Fintype α] [Fintype G] [Fintype V]
    (H : α → α → G → ℂ) (act : G → V ≃ V) (g : α × V → ℂ) (a : α × V) :
    (∑ b : α × V, controlledKernel H act a b * g b) =
      ∑ b : α, ∑ r : G, H a.1 b r * g (b, act r a.2) := by
  classical
  simp only [Fintype.sum_prod_type, controlledKernel, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  simp [ite_mul]

theorem controlledKernel_form {α G V : Type*} [Fintype α] [Fintype G] [Fintype V]
    (mass : α → ℝ) (weight : V → ℝ) (H : α → α → G → ℂ) (act : G → V ≃ V)
    (f g : α × V → ℂ) :
    (∑ a : α × V, ∑ b : α × V,
      (mass a.1 * weight a.2 : ℝ) * star (f a) * controlledKernel H act a b * g b) =
      ∑ a : α, ∑ b : α, ∑ r : G, ∑ v : V,
        (weight v : ℂ) * ((mass a : ℂ) * star (f (a, v)) * H a b r * g (b, act r v)) := by
  have he (a : α × V) :
      (∑ b : α × V, (mass a.1 * weight a.2 : ℝ) * star (f a) * controlledKernel H act a b * g b) =
      (mass a.1 * weight a.2 : ℝ) * star (f a) *
        ∑ b : α, ∑ r : G, H a.1 b r * g (b, act r a.2) := by
    rw [← controlledKernel_row H act g a]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [he, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro v _
  simp only [Complex.ofReal_mul]
  ring

theorem normBound_controlledKernel {α G V : Type*} [Fintype α] [AddCommGroup G]
    [Fintype G] [Fintype V] (mass : α → ℝ) (weight : V → ℝ)
    (act : G → V ≃ V) (hw : ∀ r v, weight (act r v) = weight v)
    (hact : ∀ r d v, act (r + d) v = act d (act r v))
    (H : α → α → G → ℂ) (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hw0 : ∀ v, 0 ≤ weight v) (hC : 0 ≤ C)
    (hH : ∀ psi : AddChar G ℂ, NormBound mass (fourierFibre H psi) C) :
    NormBound (fun a : α × V => mass a.1 * weight a.2) (controlledKernel H act) C := by
  apply (normBound_iff_univ _ _ _).mpr
  intro f g
  rw [controlledKernel_form]
  exact controlled_translation_form_bound mass weight act hw hact H C hm hw0 hC hH f g


end Erdos821.P3Clean
