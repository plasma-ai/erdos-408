import Erdos821.S2.SpanEdgeMemoryTask

/-! All inverse-edge gates follow once the pending-memory equality is known. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def SmallCompatible (y : P.SmallResidues) : Prop :=
  ∀ i, P.smallPhysical (translateSmallResidues (Q.offset i) y) (Q.labels i)

theorem reconstructedTransferChoice_valid (hMem : SpanEdgeMemoryTask)
    (S : LifespanAssignment P n) (hq : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (y : P.SmallResidues) (hy : Q.SmallCompatible y) (i : Fin n) :
    rawEdgeValid A (A.pattern (Q.pattern i)) (edgeForward i) (Q.free i)
      (permuteActive (Q.sourcePerm i) (Q.stateAfter S y i.castSucc))
      (permuteActive (Q.targetPerm i) (Q.stateBefore S y i.succ))
      (Q.reconstructedTransferChoice S y i) := by
  dsimp only [rawEdgeValid, permuteActive, stateAfter, stateBefore, reconstructedTransferChoice]
  refine ⟨?_, ?_, (hq.2 i).1, (hq.2 i).2, ?_, ?_⟩
  · exact (smallPhysical_act_iff _ _ _).mpr (hy i.castSucc)
  · exact (smallPhysical_act_iff _ _ _).mpr (hy i.succ)
  · change translateSmallResidues (Q.offset i.succ) y =
      translateSmallResidues (Q.step i) (translateSmallResidues (Q.offset i.castSucc) y)
    rw [residuePath_offset_succ, translateSmallResidues_add]
  · intro g
    refine ⟨?_, ?_, Q.promotionIndex_injective S hq i g, ?_, ?_⟩
    · intro j hj
      exact Q.store_slot_allowed S hq i g j hj
    · intro j hj
      exact (Q.promotion_slot_allowed S hq i g ⟨j, hj⟩).1
    · intro j
      refine ⟨Q.promotionIndex_spec S i g j, Q.promotion_translated_zero S hS i g j, ?_⟩
      have he := Q.promotionIndex_spec S i g j
      rw [he]
      exact (Q.promotion_slot_allowed S hq i g j).2
    · exact hMem F P J m n A Q S hq hS hk i g

end ResiduePath


end Erdos821.S2Core
