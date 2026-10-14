import Erdos821.S2.RankExpansion
import Erdos821.P3Tail.MemoryTail

/-! Exact cutoff decomposition with finite-support convergence and the concrete tail bound. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem distinct_history_guard_hasFiniteSupport {β : Type*} [Zero β]
    (A : Model F P J m) (n : ℕ) (guard : MemoryHistory A n → Prop)
    (f : MemoryHistory A n → β) :
    Function.HasFiniteSupport (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.DistinctBirths ∧ guard H then f H else 0) := by
  have hf : Set.Finite {H : MemoryHistory A n | H.Valid ∧ H.DistinctBirths} :=
    @Set.toFinite (MemoryHistory A n) {H | H.Valid ∧ H.DistinctBirths}
      (MemoryHistory.valid_distinct_finite A n)
  apply hf.subset
  intro H hH
  change (if H.Valid ∧ H.DistinctBirths ∧ guard H then f H else 0) ≠ 0 at hH
  by_contra hn
  exact hH (ite_eq_right (fun hp => hn ⟨hp.1, hp.2.1⟩))

def memoryTailExpression (A : Model F P J m) (n B : ℕ) (rho theta : ℝ) : ℂ :=
  ∑' H : MemoryHistory A n,
    if H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B then H.Weight rho theta else 0

theorem memoryTailExpression_summable (A : Model F P J m) (n B : ℕ) (rho theta : ℝ) :
    Summable (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B then H.Weight rho theta else 0) := by
  apply summable_of_hasFiniteSupport
  convert distinct_history_guard_hasFiniteSupport A n (fun H => ¬ H.Truncated B)
    (fun H => H.Weight rho theta) using 1
  ext H
  by_cases h : H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B <;> simp [h]

theorem memoryTailExpression_abs_summable (A : Model F P J m) (n B : ℕ) (rho theta : ℝ) :
    Summable (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B then ‖H.Weight rho theta‖ else 0) := by
  apply summable_of_hasFiniteSupport
  convert distinct_history_guard_hasFiniteSupport A n (fun H => ¬ H.Truncated B)
    (fun H => ‖H.Weight rho theta‖) using 1
  ext H
  by_cases h : H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B <;> simp [h]

theorem truncatedDistinctMemoryExpression_summable (A : Model F P J m) (n B : ℕ)
    (rho theta : ℝ) :
    Summable (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.Truncated B ∧ H.DistinctBirths then H.Weight rho theta else 0) := by
  apply summable_of_hasFiniteSupport
  convert distinct_history_guard_hasFiniteSupport A n (fun H => H.Truncated B)
    (fun H => H.Weight rho theta) using 1
  ext H
  by_cases hv : H.Valid <;> by_cases hd : H.DistinctBirths <;> by_cases ht : H.Truncated B <;>
    simp [hv, hd, ht]

theorem distinctMemoryExpression_split (A : Model F P J m) (n B : ℕ) (rho theta : ℝ) :
    distinctMemoryExpression A n rho theta =
      truncatedDistinctMemoryExpression A n B rho theta + memoryTailExpression A n B rho theta := by
  unfold distinctMemoryExpression truncatedDistinctMemoryExpression memoryTailExpression
  rw [← (truncatedDistinctMemoryExpression_summable A n B rho theta).tsum_add
    (memoryTailExpression_summable A n B rho theta)]
  apply tsum_congr
  intro H
  by_cases hv : H.Valid <;> by_cases hd : H.DistinctBirths <;> by_cases ht : H.Truncated B <;>
    simp [hv, hd, ht]

theorem memoryTailExpression_norm_le (A : Model F P J m) (n B : ℕ) (rho theta : ℝ) :
    ‖memoryTailExpression A n B rho theta‖ ≤
      ∑' H : MemoryHistory A n,
        if H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B then ‖H.Weight rho theta‖ else 0 := by
  let f (H : MemoryHistory A n) : ℂ :=
    if H.Valid ∧ H.DistinctBirths ∧ ¬ H.Truncated B then H.Weight rho theta else 0
  have hs : Summable (fun H => ‖f H‖) := by
    simpa only [f, apply_ite norm, norm_zero] using memoryTailExpression_abs_summable A n B rho theta
  simpa only [memoryTailExpression, f, apply_ite norm, norm_zero] using norm_tsum_le_tsum_norm hs

theorem distinctMemoryExpression_norm_le_cutoff (A : Model F P J m) (n B : ℕ)
    (rho v theta CG CE : ℝ) (hv : 1 ≤ v) (hCG : 0 ≤ CG) (hCE : 0 ≤ CE)
    (hG : ∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n rho 2 i s t * P.memoryWeight v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n rho 2 i s t * P.memoryWeight v t) ≤
        CG * P.memoryWeight v s)
    (hE : ∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel A n rho theta i .all s t * P.memoryWeight v t) ∧
      (∑' t, absoluteMemoryEdgeKernel A n rho theta i .all s t * P.memoryWeight v t) ≤
        CE * P.memoryWeight v s) :
    ‖distinctMemoryExpression A n rho theta‖ ≤
      ‖truncatedDistinctMemoryExpression A n B rho theta‖ +
        (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
          CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n := by
  rw [distinctMemoryExpression_split A n B rho theta]
  apply (norm_add_le _ _).trans
  exact add_le_add le_rfl ((memoryTailExpression_norm_le A n B rho theta).trans
    (MemoryTailTask_proof F P J m n A rho v theta CG CE hv hCG hCE hG hE B))


end Erdos821.S2Core
