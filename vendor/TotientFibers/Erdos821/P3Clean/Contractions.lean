import Erdos821.S2.EdgeTasks

/-! Contractions in the finite-support formulation of the clean norm. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem normBound_mono {α : Type*} {mass : α → ℝ} {K : α → α → ℂ}
    {C D : ℝ} (hK : NormBound mass K C) (hCD : C ≤ D) : NormBound mass K D := by
  intro s t f g
  exact (hK s t f g).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

theorem normBound_mul_endpoints {α : Type*} {mass : α → ℝ} {K : α → α → ℂ}
    {C : ℝ} (hm : ∀ a, 0 ≤ mass a) (hC : 0 ≤ C) (hK : NormBound mass K C)
    (u v : α → ℂ) (hu : ∀ a, ‖u a‖ ≤ 1) (hv : ∀ a, ‖v a‖ ≤ 1) :
    NormBound mass (fun a b => u a * K a b * v b) C := by
  intro s t f g
  have hf : (∑ a ∈ s, mass a * ‖star (u a) * f a‖ ^ 2) ≤
      ∑ a ∈ s, mass a * ‖f a‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (hm a)
    apply pow_le_pow_left₀ (norm_nonneg _) _
    simpa only [norm_mul, norm_star, one_mul] using
      mul_le_mul_of_nonneg_right (hu a) (norm_nonneg (f a))
  have hg : (∑ b ∈ t, mass b * ‖v b * g b‖ ^ 2) ≤
      ∑ b ∈ t, mass b * ‖g b‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro b _
    apply mul_le_mul_of_nonneg_left _ (hm b)
    apply pow_le_pow_left₀ (norm_nonneg _) _
    simpa only [norm_mul, one_mul] using
      mul_le_mul_of_nonneg_right (hv b) (norm_nonneg (g b))
  have h := hK s t (fun a => star (u a) * f a) (fun b => v b * g b)
  simp only [star_mul, star_star] at h
  have heq : (∑ a ∈ s, ∑ b ∈ t,
      (mass a : ℂ) * (star (f a) * u a) * K a b * (v b * g b)) =
      ∑ a ∈ s, ∑ b ∈ t,
        (mass a : ℂ) * star (f a) * (u a * K a b * v b) * g b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [heq] at h
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf) hC)
    (Real.sqrt_le_sqrt hg) (Real.sqrt_nonneg _)
    (mul_nonneg hC (Real.sqrt_nonneg _)))

theorem normBound_project {α : Type*} {mass : α → ℝ} {K : α → α → ℂ}
    {C : ℝ} (hm : ∀ a, 0 ≤ mass a) (hC : 0 ≤ C) (hK : NormBound mass K C)
    (keep : α → Prop) : NormBound mass (projectKernel keep K) C := by
  classical
  have h := normBound_mul_endpoints hm hC hK
    (fun a => if keep a then 1 else 0) (fun a => if keep a then 1 else 0)
    (by intro a; split_ifs <;> simp) (by intro a; split_ifs <;> simp)
  have heq : (fun a b => (if keep a then (1 : ℂ) else 0) * K a b *
      (if keep b then (1 : ℂ) else 0)) = projectKernel keep K := by
    funext a b
    by_cases ha : keep a <;> by_cases hb : keep b <;> simp [projectKernel, ha, hb]
  rw [heq] at h
  exact h

theorem normBound_iff_univ {α : Type*} [Fintype α] (mass : α → ℝ)
    (K : α → α → ℂ) (C : ℝ) : NormBound mass K C ↔
      ∀ f g : α → ℂ,
        ‖∑ a, ∑ b, (mass a : ℂ) * star (f a) * K a b * g b‖ ≤
          C * Real.sqrt (∑ a, mass a * ‖f a‖ ^ 2) *
            Real.sqrt (∑ b, mass b * ‖g b‖ ^ 2) := by
  classical
  constructor
  · intro h f g
    exact h Finset.univ Finset.univ f g
  · intro h s t f g
    have hh := h (fun a => if a ∈ s then f a else 0)
      (fun b => if b ∈ t then g b else 0)
    simpa [apply_ite, ite_pow, mul_ite, ite_mul, Finset.sum_ite_mem] using hh

theorem sum_fibre_forms_bound {α β : Type*} [Fintype α] [Fintype β]
    (mass : α → ℝ) (K : β → α → α → ℂ) (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hC : 0 ≤ C)
    (hK : ∀ j, NormBound mass (K j) C) (f g : β → α → ℂ) :
    ‖∑ j, ∑ a, ∑ b, (mass a : ℂ) * star (f j a) * K j a b * g j b‖ ≤
      C * Real.sqrt (∑ j, ∑ a, mass a * ‖f j a‖ ^ 2) *
        Real.sqrt (∑ j, ∑ b, mass b * ‖g j b‖ ^ 2) := by
  have hf (j : β) : 0 ≤ ∑ a, mass a * ‖f j a‖ ^ 2 :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hm a) (sq_nonneg _))
  have hg (j : β) : 0 ≤ ∑ b, mass b * ‖g j b‖ ^ 2 :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (hm b) (sq_nonneg _))
  calc
    _ ≤ ∑ j, ‖∑ a, ∑ b, (mass a : ℂ) * star (f j a) * K j a b * g j b‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, C * Real.sqrt (∑ a, mass a * ‖f j a‖ ^ 2) *
        Real.sqrt (∑ b, mass b * ‖g j b‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact hK j Finset.univ Finset.univ (f j) (g j)
    _ = C * ∑ j, Real.sqrt (∑ a, mass a * ‖f j a‖ ^ 2) *
        Real.sqrt (∑ b, mass b * ‖g j b‖ ^ 2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Finset.univ hf hg) hC


end Erdos821.P3Clean
