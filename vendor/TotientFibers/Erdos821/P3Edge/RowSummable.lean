import Erdos821.P3Edge.RowFinite

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

lemma edgeSymmetryFactor_pos (P : PrimeGroups) (M : ℕ) :
    0 < edgeSymmetryFactor P M := by
  unfold edgeSymmetryFactor
  have hcard : 0 < (Fintype.card (P.Permutations M) : ℝ) := by
    have h1 : 0 < Fintype.card (P.Permutations M) := Fintype.card_pos
    exact Nat.cast_pos.mpr h1
  positivity

lemma edgeSymmetryFactor_ne_zero (P : PrimeGroups) (M : ℕ) :
    edgeSymmetryFactor P M ≠ 0 :=
  ne_of_gt (edgeSymmetryFactor_pos P M)

lemma absKernel_eq (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    absoluteMemoryEdgeKernel A n rho theta i .all s t =
      edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
        if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := rfl

lemma row_kernel_support_subset (A : Model F P J m) {n : ℕ} (rho theta : ℝ) (i : Fin n)
    (s : P.MemoryState (J + F.ell)) :
    {t | absoluteMemoryEdgeKernel A n rho theta i .all s t ≠ 0} ⊆
      {t | ∃ c : EdgeChoice A s, edgeChoiceValid A .all i s t c} := by
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [absKernel_eq] at ht
  have hfac := edgeSymmetryFactor_ne_zero P (J + F.ell)
  have hsum : (∑ c : EdgeChoice A s, if edgeChoiceValid A .all i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) ≠ 0 := by
    intro h0
    apply ht
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

lemma row_kernel_set_finite (A : Model F P J m) {n : ℕ} (rho theta : ℝ) (i : Fin n)
    (s : P.MemoryState (J + F.ell)) :
    Set.Finite {t | absoluteMemoryEdgeKernel A n rho theta i .all s t ≠ 0} := by
  exact (row_valid_set_finite A i s).subset (row_kernel_support_subset A rho theta i s)

lemma row_summable (F : FixedData) (r : MemoryParameters F)
    (A : Model F P J m) (n : ℕ) (theta : ℝ) (i : Fin n)
    (s : P.MemoryState (J + F.ell)) :
    Summable (fun t => ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v t) := by
  classical
  have hfin := row_kernel_set_finite A r.rho theta i s
  have hw : ∀ t : P.MemoryState (J + F.ell), P.memoryWeight r.v t ≠ 0 := by
    intro t
    unfold PrimeGroups.memoryWeight
    apply pow_ne_zero
    have hv : 0 < r.v := lt_trans zero_lt_one r.v_gt
    exact ne_of_gt hv
  have hsup : Function.support (fun t => ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v t) ⊆
      {t | absoluteMemoryEdgeKernel A n r.rho theta i .all s t ≠ 0} := by
    intro t ht
    simp only [Function.support, Set.mem_setOf_eq] at ht ⊢
    intro h0
    apply ht
    rw [h0]
    simp
  have hfin2 : Function.HasFiniteSupport (fun t => ‖((absoluteMemoryEdgeKernel A n r.rho theta i .all s t : ℝ) : ℂ)‖ * P.memoryWeight r.v t) :=
    hfin.subset hsup
  exact summable_of_hasFiniteSupport hfin2

end Erdos821.P3Edge
