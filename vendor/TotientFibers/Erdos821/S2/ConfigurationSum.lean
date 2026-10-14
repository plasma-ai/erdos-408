import Erdos821.S2.SpanConfigurations
import Erdos821.S2.HistoryReconstructionTask
import Erdos821.S2.HistoryFinite

/-! The finite lifespan/history equivalence and its ordered factorial fibers. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

/-- The structural tasks are explicit proof inputs, never blueprint stubs. -/
structure HistoryStructureProofs : Prop where
  edgeMemory : SpanEdgeMemoryTask
  births : SpanBirthTask
  classification : LifespanClassificationTask
  anchors : HistoryAnchorTask
  reconstruction : HistoryReconstructionTask

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace SpanConfiguration

variable {A : Model F P J m} {n : ℕ}

def toValidHistory (h : HistoryStructureProofs)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (c : SpanConfiguration A n) : ValidDistinctHistory A n :=
  ⟨c.history, c.history_valid h.edgeMemory hk, c.history_distinct h.births hk⟩

theorem toValidHistory_injective (h : HistoryStructureProofs)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) :
    Function.Injective (toValidHistory (n := n) h hk) := by
  intro c d he
  exact history_injective (A := A) (n := n)
    (congrArg (fun H : ValidDistinctHistory A n => H.val) he)

theorem toValidHistory_surjective (h : HistoryStructureProofs) (hn : 0 < n)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) :
    Function.Surjective (toValidHistory (n := n) h hk) := by
  intro H
  obtain ⟨S, hS, hy, sigma, he⟩ := h.reconstruction h.classification h.anchors
    F P J m n A H.val hn H.property.1 H.property.2 hk
  have hQ := H.val.toResiduePath_valid_of_distinct hn H.property.1 H.property.2
  let c : SpanConfiguration A n :=
    ⟨⟨H.val.toResiduePath, hQ⟩, ⟨S, hS⟩, ⟨(H.val.before 0).1, hy⟩, sigma⟩
  refine ⟨c, Subtype.ext ?_⟩
  exact he.symm

def historyEquiv (h : HistoryStructureProofs) (hn : 0 < n)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k) :
    SpanConfiguration A n ≃ ValidDistinctHistory A n :=
  Equiv.ofBijective (toValidHistory h hk)
    ⟨toValidHistory_injective h hk, toValidHistory_surjective h hn hk⟩

end SpanConfiguration

theorem distinctMemoryExpression_eq_configurations (h : HistoryStructureProofs)
    (A : Model F P J m) (n : ℕ) (hn : 0 < n)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (rho theta : ℝ) :
    distinctMemoryExpression A n rho theta =
      ∑ c : SpanConfiguration A n, c.history.Weight rho theta := by
  rw [distinctMemoryExpression_eq_finite_sum]
  exact (Fintype.sum_equiv (SpanConfiguration.historyEquiv h hn hk)
    (fun c => c.history.Weight rho theta) (fun H => H.val.Weight rho theta)
    (fun _ => rfl)).symm

theorem distinctMemoryExpression_eq_lifespans (h : HistoryStructureProofs)
    (A : Model F P J m) (n : ℕ) (hn : 0 < n)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (rho theta : ℝ) :
    distinctMemoryExpression A n rho theta =
      ∑ Q : {Q : ResiduePath A n // Q.Valid},
        ∑ S : {S : LifespanAssignment P n // Q.val.lifespanValid S},
          ∑ y : {y : P.SmallResidues // Q.val.SmallCompatible y},
            ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
              (Q.val.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
              (Q.val.reconstructedHistory S.val S.property y.val).Weight rho theta := by
  rw [distinctMemoryExpression_eq_configurations h A n hn hk rho theta]
  simp only [SpanConfiguration, Fintype.sum_sigma, SpanConfiguration.history]
  apply Finset.sum_congr rfl
  intro Q _
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro y _
  simpa only [ResiduePath.reconstructedHistory, ResiduePath.reconstructedGhostChoice] using
    (Q.val.reconstructedHistory S.val S.property y.val).reorderBatches_weight_sum rho theta


end Erdos821.S2Core
