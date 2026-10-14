module

public import Erdos821.S2.FullNormTask
public import Erdos821.P3Restore.Restoration
public import Erdos821.P3Edge.Proof
public import Erdos821.P3Clean.Proof
public import Erdos821.P3LowRank.LowRank
public import Erdos821.S2Contr.Contraction
public import Erdos821.S2Gpar.GhostAnalyticParameters
public import Erdos821.S2Tail.TailAbsorption

/-! Use all completed memory norm leaves while retaining the remaining proof inputs. -/

@[expose] public section

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem concrete_truncated_memory_estimate (F : FixedData) (r : MemoryParameters F)
    (hBoundary : EmptyBoundaryMassTask) (hRare : MemoryRareTask F r)
    (hHigh : HighRankMemoryTask F r) : UniformTruncatedMemoryEstimate F r :=
  RestoredMemoryNormTask_proof F r
    (Erdos821.S2Gpar.GhostAnalyticParametersTask_proof F r) hBoundary
    (MemoryEdgeAbsoluteTask_proof F r) hRare (MemoryCleanTask_proof F r)
    (Erdos821.S2Contr.WholeEdgeContractionTask_proof F r) LowRankMemoryTask_proof hHigh

theorem concrete_full_memory_estimate (F : FixedData) (r : MemoryParameters F)
    (hBoundary : EmptyBoundaryMassTask) (hRare : MemoryRareTask F r)
    (hHigh : HighRankMemoryTask F r) (hFull : FullMemoryNormTask F r) :
    UniformFullMemoryEstimate F r :=
  hFull (Erdos821.S2Gpar.GhostAnalyticParametersTask_proof F r) hBoundary
    (MemoryEdgeAbsoluteTask_proof F r) (concrete_truncated_memory_estimate F r hBoundary hRare hHigh)
    Erdos821.S2Tail.TailAbsorptionTask_proof


end Erdos821.S2Core
