import Erdos821.P3Edge.ColFinite
import Erdos821.P3Edge.RowSummable

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

lemma col_kernel_support_subset (A : Model F P J m) {n : ℕ} (rho theta : ℝ) (i : Fin n)
    (t : P.MemoryState (J + F.ell)) :
    {s | absoluteMemoryEdgeKernel A n rho theta i .all s t ≠ 0} ⊆
      {s | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} := by
  intro s hs
  simp only [Set.mem_setOf_eq] at hs ⊢
  rw [absKernel_eq] at hs
  have hfac := edgeSymmetryFactor_ne_zero P (J + F.ell)
  have hsum : (∑ c : EdgeChoice A s, if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) ≠ 0 := by
    intro h0
    apply hs
    rw [h0, mul_zero]
  by_contra hnone
  push Not at hnone
  have hall : ∀ c : EdgeChoice A s, (if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) = 0 := by
    intro c
    have hn := hnone c
    simp [hn]
  have hsum0 : (∑ c : EdgeChoice A s, if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) = 0 := by
    simp [hall]
  exact hsum hsum0

lemma col_kernel_set_finite (A : Model F P J m) {n : ℕ} (rho theta : ℝ) (i : Fin n)
    (t : P.MemoryState (J + F.ell)) :
    Set.Finite {s | absoluteMemoryEdgeKernel A n rho theta i .all s t ≠ 0} := by
  exact (col_valid_set_finite A i t).subset (col_kernel_support_subset A rho theta i t)

lemma col_summable (F : FixedData) (r : MemoryParameters F)
    (A : Model F P J m) (n : ℕ) (theta : ℝ) (i : Fin n)
    (t : P.MemoryState (J + F.ell)) :
    Summable (fun s => P.memoryMass F J n s * ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v s) := by
  classical
  have hfin := col_kernel_set_finite A r.rho theta i t
  have hsup : Function.support (fun s => P.memoryMass F J n s * ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v s) ⊆
      {s | absoluteMemoryEdgeKernel A n r.rho theta i .all s t ≠ 0} := by
    intro s hs
    simp only [Function.support, Set.mem_setOf_eq] at hs ⊢
    intro h0
    apply hs
    rw [h0]
    simp
  have hfin2 : Function.HasFiniteSupport (fun s => P.memoryMass F J n s * ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v s) :=
    hfin.subset hsup
  exact summable_of_hasFiniteSupport hfin2

end Erdos821.P3Edge
