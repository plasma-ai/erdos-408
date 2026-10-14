import Erdos821.S2.ConcreteMemory
import Erdos821.S2.ConcreteNorms
import Erdos821.S2.PacketAdapters
import Erdos821.S2Nondiv.BigPrimeNondiv

/-! Assemble completed task proofs into the exact final transference proof packet. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

/-- Each field is a still-needed proof, never an owned blueprint placeholder. -/
structure RemainingP3Proofs : Prop where
  boundary : EmptyBoundaryMassTask
  rare : ∀ (F : FixedData) (r : MemoryParameters F), MemoryRareTask F r
  high : ∀ (F : FixedData) (r : MemoryParameters F), HighRankMemoryTask F r
  fullNorm : ∀ (F : FixedData) (r : MemoryParameters F), FullMemoryNormTask F r
  reconstruction : HistoryReconstructionTask
  residues : ResidueFactorizationTask
  physicalPaths : PhysicalPathExpansionTask
  absoluteRoot : AbsoluteClosedRootTask
  crt : Erdos821.Blueprint.Graph.uniform_residue_replacement_statement

theorem concrete_transference_proofs (h : RemainingP3Proofs) : MemoryTransferenceProofs := by
  exact {
    ghostParameters := Erdos821.S2Gpar.GhostAnalyticParametersTask_proof
    emptyBoundary := h.boundary
    nondiv := Erdos821.S2Nondiv.BigPrimeNondivTask_proof
    absoluteEdge := MemoryEdgeAbsoluteTask_proof
    fullMemory := fun F r => concrete_full_memory_estimate F r h.boundary (h.rare F r)
      (h.high F r) (h.fullNorm F r)
    structureProofs := historyStructure_of_reconstruction h.reconstruction
    ghostWeights := Erdos821.P3Gw.SpanGhostWeightTask_proof
    markWeights := Erdos821.P3Mark.SpanMarkWeightTask_proof
    spanSum := SpanSumTask_proof
    residues := h.residues
    physicalPaths := h.physicalPaths
    absoluteRoot := h.absoluteRoot
    crt := h.crt }

theorem local_transference_of_remaining (hAssembly : LocalTransferenceAssemblyTask)
    (h : RemainingP3Proofs) : Erdos821.Blueprint.Graph.local_transference_statement :=
  hAssembly (concrete_transference_proofs h)

theorem transference_inputs_of_remaining (hAbs : AbsolutePhysicalPacketTask)
    (hAssembly : LocalTransferenceAssemblyTask) (h : RemainingP3Proofs) :
    Erdos821.Blueprint.TransferenceInputs :=
  transferenceInputs_of_local hAbs (local_transference_of_remaining hAssembly h)

end Erdos821.S2Core
