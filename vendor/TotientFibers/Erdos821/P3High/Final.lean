import Erdos821.P3High.Proof
import Erdos821.S2Empty.Final

/-! The exact frozen high-rank task. -/

set_option autoImplicit false

open Erdos821.Blueprint.Graph

theorem Erdos821.S2Core.HighRankMemoryTask_proof (F : FixedData) (r : MemoryParameters F) :
    Erdos821.S2Core.HighRankMemoryTask F r :=
  Erdos821.P3High.highRank_of_boundary F r Erdos821.S2Empty.EmptyBoundaryMassTask_proof

example : ∀ (F : FixedData) (r : MemoryParameters F), Erdos821.S2Core.HighRankMemoryTask F r :=
  Erdos821.S2Core.HighRankMemoryTask_proof

