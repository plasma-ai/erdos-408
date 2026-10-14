import Erdos821.S2.MemoryIdentity
import Erdos821.P3Live.Anchors
import Erdos821.P3Live.SpanMemory
import Erdos821.P3Span.LifespanClassification
import Erdos821.P3Birth.SpanBirthTask
import Erdos821.P3GW.SpanGhostWeight
import Erdos821.P3Mark.SpanMarkWeight
import Erdos821.P3Sum.SpanSumTask

/-! Instantiate all completed structural and local-weight leaves of the memory identity. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem historyStructure_of_reconstruction (hRec : HistoryReconstructionTask) : HistoryStructureProofs :=
  ⟨SpanEdgeMemoryTask_proof, SpanBirthTask_proof, LifespanClassificationTask_proof,
    HistoryAnchorTask_proof, hRec⟩

theorem memory_identity_of_remaining_tasks {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (hRec : HistoryReconstructionTask) (hRes : ResidueFactorizationTask) (A : Model F P J m)
    (n : ℕ) (hn : 0 < n)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g, P.V g ≠ 0)
    (hbp : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, baselinePrime F n p.val ≠ 0)
    (rho theta : ℝ) (hrho : rho ≠ 0) :
    residueExpression A n theta = (bigBaseline F P n : ℂ) * distinctMemoryExpression A n rho theta :=
  memory_identity_of_tasks (historyStructure_of_reconstruction hRec)
    Erdos821.P3Gw.SpanGhostWeightTask_proof Erdos821.P3Mark.SpanMarkWeightTask_proof
    SpanSumTask_proof hRes A n hn hk hV hbp rho theta hrho


end Erdos821.S2Core
