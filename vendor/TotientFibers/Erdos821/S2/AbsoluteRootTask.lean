import Erdos821.S2.MemoryIdentity
import Erdos821.S2.ClosedPaths
import Erdos821.S2.MemoryTailTask

/-! Absolute closed paths from the same finite history fibers and absolute rows. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def AbsoluteClosedRootTask : Prop :=
  HistoryStructureProofs → SpanGhostWeightTask → SpanMarkWeightTask → SpanSumTask →
  ResidueFactorizationTask →
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m), 0 < n →
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) →
    (∀ g, P.V g ≠ 0) →
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) →
    ∀ rho v CG CE : ℝ, rho ≠ 0 → 1 ≤ v → 0 ≤ CG → 0 ≤ CE →
    (∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n rho 2 i s t * P.memoryWeight v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n rho 2 i s t * P.memoryWeight v t) ≤
        CG * P.memoryWeight v s) →
    (∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel A n rho 0 i .all s t * P.memoryWeight v t) ∧
      (∑' t, absoluteMemoryEdgeKernel A n rho 0 i .all s t * P.memoryWeight v t) ≤
        CE * P.memoryWeight v s) →
      closedAbsoluteResidueExpression A n ≤
        CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n


end Erdos821.S2Core
