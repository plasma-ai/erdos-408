import Erdos821.S2.FullNormTask
import Erdos821.S2.AbsoluteRootTask
import Erdos821.S2.PhysicalPathTask

/-! Exact final §2 theorem from explicit memory, physical and CRT proof inputs. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

structure MemoryTransferenceProofs : Prop where
  ghostParameters : ∀ (F : FixedData) (r : MemoryParameters F), GhostAnalyticParametersTask F r
  emptyBoundary : EmptyBoundaryMassTask
  nondiv : BigPrimeNondivTask
  absoluteEdge : ∀ (F : FixedData) (r : MemoryParameters F), MemoryEdgeAbsoluteTask F r
  fullMemory : ∀ (F : FixedData) (r : MemoryParameters F), UniformFullMemoryEstimate F r
  structureProofs : HistoryStructureProofs
  ghostWeights : SpanGhostWeightTask
  markWeights : SpanMarkWeightTask
  spanSum : SpanSumTask
  residues : ResidueFactorizationTask
  physicalPaths : PhysicalPathExpansionTask
  absoluteRoot : AbsoluteClosedRootTask
  crt : Erdos821.Blueprint.Graph.uniform_residue_replacement_statement

def LocalTransferenceAssemblyTask : Prop :=
  MemoryTransferenceProofs → Erdos821.Blueprint.Graph.local_transference_statement

def AbsolutePhysicalPacketTask : Prop := AbsolutePhysicalBounds

end Erdos821.S2Core
