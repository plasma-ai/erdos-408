import Erdos821.S2.HistoryOrders
import Erdos821.S2.LifespanClassificationTask

/-! Surjectivity of the lifespan construction, retaining ordered ghost fibers. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def HistoryReconstructionTask : Prop :=
  LifespanClassificationTask → HistoryAnchorTask →
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (H : MemoryHistory A n),
    0 < n → H.Valid → H.DistinctBirths →
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) →
    ∃ S : LifespanAssignment P n, ∃ hS : H.toResiduePath.lifespanValid S,
      H.toResiduePath.SmallCompatible (H.before 0).1 ∧
      ∃ sigma : (H.toResiduePath.reconstructedHistory S hS (H.before 0).1).BatchOrders,
        H = (H.toResiduePath.reconstructedHistory S hS (H.before 0).1).reorderBatches sigma


end Erdos821.S2Core
