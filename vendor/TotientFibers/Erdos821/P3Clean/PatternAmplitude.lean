import Erdos821.P3Clean.TiltedIdealKernel

/-! The finite coefficient supremum used by the literal pattern-mass hypothesis. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def patternAmplitude (A : Model F P J m) (v : Fin A.patternCount) : ℝ :=
  sSup (Set.range (fun z : P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) × P.BigAux J =>
    ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖))

theorem coefficient_norm_le_amplitude (A : Model F P J m) (v : Fin A.patternCount)
    (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    ‖(A.pattern v).coefficient a b u‖ ≤ patternAmplitude A v := by
  apply le_csSup (Set.finite_range _).bddAbove
  exact ⟨(a, b, u), rfl⟩

theorem patternAmplitude_nonneg (A : Model F P J m) (v : Fin A.patternCount) :
    0 ≤ patternAmplitude A v := by
  classical
  let T := P.BigLabels (J + F.ell) × P.BigLabels (J + F.ell) × P.BigAux J
  cases isEmpty_or_nonempty T with
  | inl h =>
    letI : IsEmpty T := h
    have hr : Set.range (fun z : T => ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖) = ∅ := by
      ext x
      simp
    change 0 ≤ sSup (Set.range (fun z : T => ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖))
    rw [hr]
    simp
  | inr h =>
    obtain ⟨a, b, u⟩ := h.some
    exact (norm_nonneg _).trans (coefficient_norm_le_amplitude A v a b u)

theorem sum_patternAmplitude (A : Model F P J m) :
    (∑ v : Fin A.patternCount, patternAmplitude A v) = A.patternMass := rfl


end Erdos821.P3Clean
