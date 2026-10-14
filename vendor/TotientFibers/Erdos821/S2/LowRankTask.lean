import Erdos821.S2.HistoryBirths
import Erdos821.S2.HistoryFinite
import Erdos821.S2.MemoryTailTask

/-! Equality phases affect only the local operations containing their births. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def lowRankHistoryExpression {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n B : ℕ) (rho theta : ℝ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))) : ℂ :=
  ∑' H : MemoryHistory A n,
    if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
      H.Weight rho theta else 0

def LowRankMemoryTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n B : ℕ) (A : Model F P J m)
    (rho theta CG CE CA : ℝ), 0 ≤ CG → 0 < CE → CE ≤ CA →
    (∀ s : P.MemoryState (J + F.ell), 0 ≤ P.memoryMass F J n s) →
    (∀ (i : Fin (n + 1))
      (phi : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ),
      (∀ s t c, ‖phi s t c‖ ≤ 1) →
      NormBound (P.memoryMass F J n)
        (projectKernel (fun s => P.memorySize s ≤ B)
          (memoryGhostKernel F J n rho i phi)) CG) →
    (∀ (i : Fin n)
      (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ),
      (∀ s t c, ‖phi s t c‖ ≤ 1) →
      NormBound (P.memoryMass F J n)
        (projectKernel (fun s => P.memorySize s ≤ B)
          (memoryEdgeKernel A n rho theta i .all phi)) CA) →
    (∀ i : Fin n,
      NormBound (P.memoryMass F J n)
        (projectKernel (fun s => P.memorySize s ≤ B)
          (memoryEdgeKernel A n rho theta i .all (fun _ _ _ => 1))) CE) →
    ∀ pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B)))),
      BirthCollection pi →
      ‖lowRankHistoryExpression A n B rho theta pi‖ ≤
        initialMemoryBoundaryMass A n * CG ^ (n + 1) * CE ^ n *
          (CA / CE) ^ (2 * birthRank pi)


end Erdos821.S2Core
