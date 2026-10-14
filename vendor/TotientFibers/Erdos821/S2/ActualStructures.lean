import Erdos821.S2.ConfigurationSum
import Erdos821.P3Live.Anchors
import Erdos821.P3Live.SpanMemory

/-! Instantiate the accepted anchor and inverse edge-memory proofs. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem historyStructureProofsOfTasks (hBirth : SpanBirthTask)
    (hClass : LifespanClassificationTask) (hReconstruct : HistoryReconstructionTask) :
    HistoryStructureProofs :=
  ⟨SpanEdgeMemoryTask_proof, hBirth, hClass, HistoryAnchorTask_proof, hReconstruct⟩

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

theorem reconstructedHistory_valid_of_lifespans (S : LifespanAssignment P n)
    (hq : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (y : P.SmallResidues) (hy : Q.SmallCompatible y) :
    (Q.reconstructedHistory S hS y).Valid :=
  Q.reconstructedHistory_valid SpanEdgeMemoryTask_proof S hq hS hk y hy


end ResiduePath


end Erdos821.S2Core
