import Erdos821.S2.SpanLifecycle

/-! The forward classification of a literal distinct history into prime spans. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

/-- The structural anchor theorem is an explicit input. The task reconstructs
all pending memories; coefficients, analytic estimates and permutations of ghost
batches are left to the lead's weighted fiber identity. -/
def LifespanClassificationTask : Prop :=
  HistoryAnchorTask →
    ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
      (H : MemoryHistory A n), H.Valid → H.DistinctBirths →
      ∃ S : LifespanAssignment P n,
        H.toResiduePath.lifespanValid S ∧
        ∀ (i : Fin (n + 1)) (g : P.BigGroup),
          H.toResiduePath.memoryBefore S i g = (H.before i).2.2 g ∧
          H.toResiduePath.memoryAfter S i g = (H.after i).2.2 g


end Erdos821.S2Core
