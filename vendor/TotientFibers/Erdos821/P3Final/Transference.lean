import Erdos821.S2.ConcreteTransference
import Erdos821.S2Empty.Final
import Erdos821.P3High.Final
import Erdos821.S2Full.FullMemoryNorm
import Erdos821.S2Hist.HistoryReconstruction
import Erdos821.S2Resid.ResidueFactorization
import Erdos821.P3Phys.PhysicalPathExpansion
import Erdos821.S2Root.AbsoluteClosedRootProof
import Erdos821.P3.ResidueReplacement
import Erdos821.S2Packet.AbsolutePhysicalPacket
import Erdos821.S2Ltrans.TransferenceAssembly

/-! P3 assembled from all accepted task proofs; only the rare-edge task remains an input. -/

set_option autoImplicit false

namespace Erdos821.P3Final

open Erdos821.S2Core
open Erdos821.Blueprint.Graph

/-- Every completed P3 input, leaving only `MemoryRareTask`. -/
theorem remaining_of_rare
    (hrare : ∀ (F : FixedData) (r : MemoryParameters F), MemoryRareTask F r) :
    RemainingP3Proofs where
  boundary := Erdos821.S2Empty.EmptyBoundaryMassTask_proof
  rare := hrare
  high := Erdos821.S2Core.HighRankMemoryTask_proof
  fullNorm := Erdos821.S2Full.FullMemoryNormTask_proof
  reconstruction := Erdos821.S2Hist.HistoryReconstructionTask_proof
  residues := Erdos821.S2Resid.residueFactorizationTask_proof
  physicalPaths := Erdos821.S2Core.PhysicalPathExpansionTask_proof
  absoluteRoot := Erdos821.S2Root.AbsoluteClosedRootTask_proof
  crt := @Erdos821.P3Core.uniform_residue_replacement_proof

theorem transference_inputs_of_rare
    (hrare : ∀ (F : FixedData) (r : MemoryParameters F), MemoryRareTask F r)
    (_hc : Erdos821.Blueprint.ClassicalInputs) : Erdos821.Blueprint.TransferenceInputs :=
  transference_inputs_of_remaining Erdos821.S2Packet.AbsolutePhysicalPacketTask_proof
    Erdos821.S2Ltrans.LocalTransferenceAssemblyTask_proof (remaining_of_rare hrare)


end Erdos821.P3Final
