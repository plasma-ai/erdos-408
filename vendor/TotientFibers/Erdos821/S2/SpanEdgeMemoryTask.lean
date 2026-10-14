import Erdos821.S2.SpanEdge

/-! The remaining inverse-edge equality, separated from gates and hit tests. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

/-- Source stores, surviving old memory and promotions give exactly the
pending set before the next ghost. Numerical coincidences are retained by indices. -/
def SpanEdgeMemoryTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (Q : ResiduePath A n) (S : LifespanAssignment P n), Q.Valid → Q.lifespanValid S →
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) →
    ∀ i : Fin n, ∀ g : P.BigGroup,
      Q.memoryBefore S i.succ g = translateMemory (Q.step i)
        (deleteMemoryIndices (Q.memoryAfter S i.castSucc g)
          (retrievedIndices (Q.reconstructedTransferChoice S (fun _ _ => 0) i) g) +
          storedMemory (Q.source i g.val) (Q.storeSlots S i g))


end Erdos821.S2Core
