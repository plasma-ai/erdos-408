import Erdos821.S2.PhysicalPathTask

/-! Finite root averaging preserves the relative CRT error term by term. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem finite_average_product {α β : Type*} [Fintype α] (s : Finset β)
    (d : ℝ) (c : α → ℂ) (f : β → α → ℝ) :
    (d : ℂ) * (∑ z ∈ s, ∑ a : α, c a * (f z a : ℂ)) =
      ∑ a : α, c a * ((d * ∑ z ∈ s, f z a : ℝ) : ℂ) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  ring

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m) (n : ℕ)

def closedPathCoefficient (Q : ResiduePath A n) : ℂ :=
  if Q.Valid ∧ Q.offset (Fin.last n) = 0 then
    (P.markMass (J + F.ell) : ℂ) * ∏ i : Fin n, Q.edgeCoefficient 0 i
  else 0

def closedResidueExpression : ℂ :=
  ∑ Q : ResiduePath A n, closedPathCoefficient A n Q *
    (P.residueExpectation n (visitQ F.q n) Q.offset Q.active : ℂ)

def closedAbsoluteResidueExpression : ℝ :=
  ∑ Q : ResiduePath A n, ‖closedPathCoefficient A n Q‖ *
    P.residueExpectation n (visitQ F.q n) Q.offset Q.active

theorem closedPhysicalExpression_eq :
    ∀ z, closedPhysicalExpression A n z =
      ∑ Q : ResiduePath A n, closedPathCoefficient A n Q *
        (P.pathFactor n (visitQ F.q n) Q.offset Q.active z : ℂ) := by
  intro z
  apply Finset.sum_congr rfl
  intro Q _
  by_cases h : Q.Valid ∧ Q.offset (Fin.last n) = 0 <;>
    simp [closedPathCoefficient, h]

theorem closed_replacement_bound (X epsilon : ℝ)
    (hreplace : ∀ Q : ResiduePath A n, Q.Valid →
      |((dyad X).card : ℝ)⁻¹ * ∑ z ∈ dyad X,
          P.pathFactor n (visitQ F.q n) Q.offset Q.active z -
        P.residueExpectation n (visitQ F.q n) Q.offset Q.active| ≤
      epsilon * P.residueExpectation n (visitQ F.q n) Q.offset Q.active) :
    ‖Complex.ofReal (((dyad X).card : ℝ)⁻¹) *
        (∑ z ∈ dyad X, closedPhysicalExpression A n z) - closedResidueExpression A n‖ ≤
      epsilon * closedAbsoluteResidueExpression A n := by
  let avg (Q : ResiduePath A n) : ℝ := ((dyad X).card : ℝ)⁻¹ *
    ∑ z ∈ dyad X, P.pathFactor n (visitQ F.q n) Q.offset Q.active z
  let res (Q : ResiduePath A n) : ℝ :=
    P.residueExpectation n (visitQ F.q n) Q.offset Q.active
  have he : Complex.ofReal (((dyad X).card : ℝ)⁻¹) *
        (∑ z ∈ dyad X, closedPhysicalExpression A n z) - closedResidueExpression A n =
      ∑ Q : ResiduePath A n, closedPathCoefficient A n Q * ((avg Q - res Q : ℝ) : ℂ) := by
    simp_rw [closedPhysicalExpression_eq]
    rw [finite_average_product]
    unfold closedResidueExpression
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro Q _
    simp only [Complex.ofReal_sub]
    ring
  rw [he]
  calc
    _ ≤ ∑ Q : ResiduePath A n,
        ‖closedPathCoefficient A n Q * ((avg Q - res Q : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ Q : ResiduePath A n,
        ‖closedPathCoefficient A n Q‖ * (epsilon * res Q) := by
      apply Finset.sum_le_sum
      intro Q _
      by_cases hv : Q.Valid ∧ Q.offset (Fin.last n) = 0
      · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hreplace Q hv.1) (norm_nonneg _)
      · simp only [closedPathCoefficient, ite_eq_right hv, norm_zero, zero_mul, le_refl]
    _ = epsilon * closedAbsoluteResidueExpression A n := by
      unfold closedAbsoluteResidueExpression
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro Q _
      dsimp only [res]
      ring


end Erdos821.S2Core
