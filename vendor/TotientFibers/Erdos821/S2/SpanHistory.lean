import Erdos821.S2.SpanEdgeValidity

/-! A literal history reconstructed from a residue path and prime lifespans. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def reconstructedHistory (S : LifespanAssignment P n) (hS : Q.lifespanValid S)
    (y : P.SmallResidues) : MemoryHistory A n where
  before := Q.stateBefore S y
  after := Q.stateAfter S y
  ghost := Q.reconstructedGhostChoice S hS y
  edge := fun i => ⟨Q.sourcePerm i, Q.targetPerm i, Q.pattern i, Q.free i,
    Q.reconstructedTransferChoice S y i⟩

theorem reconstructedHistory_valid (hMem : SpanEdgeMemoryTask)
    (S : LifespanAssignment P n) (hq : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (y : P.SmallResidues) (hy : Q.SmallCompatible y) :
    (Q.reconstructedHistory S hS y).Valid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    exact Q.memoryBefore_zero S g
  · intro g
    exact Q.memoryAfter_last S g
  · intro i
    exact ⟨rfl, rfl, Q.reconstructedGhostChoice_valid S hS y i⟩
  · intro i
    exact ⟨Q.reconstructedTransferChoice_valid hMem S hq hS hk y hy i, trivial⟩

theorem reconstructedHistory_projection (S : LifespanAssignment P n)
    (hS : Q.lifespanValid S) (y : P.SmallResidues) :
    (Q.reconstructedHistory S hS y).toResiduePath = Q := by
  cases Q
  rfl


end ResiduePath
end Erdos821.S2Core
