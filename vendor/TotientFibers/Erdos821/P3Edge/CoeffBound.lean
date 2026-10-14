import Erdos821.S2.MemoryEdge

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Every pattern coefficient is bounded by the model pattern mass. -/
lemma coeff_le_patternMass (A : Model F P J m) (v : Fin A.patternCount)
    (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    ‖(A.pattern v).coefficient a b u‖ ≤ A.patternMass := by
  classical
  have hmem : ‖(A.pattern v).coefficient a b u‖ ∈
      Set.range (fun z : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) × P.BigAux J =>
        ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖) :=
    Set.mem_range_self (⟨a, b, u⟩ : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) ×
      P.BigAux J)
  have hbdd : BddAbove
      (Set.range (fun z : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) × P.BigAux J =>
        ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖)) :=
    (Set.finite_range _).bddAbove
  have hnn : ∀ v' : Fin A.patternCount, 0 ≤ sSup
      (Set.range (fun z : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) × P.BigAux J =>
        ‖(A.pattern v').coefficient z.1 z.2.1 z.2.2‖)) := by
    intro v'
    rcases Set.eq_empty_or_nonempty (Set.range (fun z : P.BigLabels (J + F.ell) ×
        P.BigLabels (J + F.ell) × P.BigAux J =>
        ‖(A.pattern v').coefficient z.1 z.2.1 z.2.2‖)) with h | h
    · simp [h]
    · obtain ⟨y, hy⟩ := h
      obtain ⟨z, rfl⟩ := Set.mem_range.mp hy
      exact le_trans (norm_nonneg _) (le_csSup (Set.finite_range _).bddAbove
        (Set.mem_range_self z))
  calc ‖(A.pattern v).coefficient a b u‖
      ≤ sSup (Set.range (fun z : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) ×
          P.BigAux J => ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖)) :=
        le_csSup hbdd hmem
    _ ≤ A.patternMass := by
        unfold Model.patternMass
        exact Finset.single_le_sum (fun v' _ => hnn v') (Finset.mem_univ v)

end Erdos821.P3Edge
