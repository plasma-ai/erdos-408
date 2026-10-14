import Erdos821.P3Clean.SmallNormalization
import Erdos821.P3Clean.ResidueAction

/-! Exact coordinates and mass factors for a clean edge. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups}

def stateCoordinates (P : PrimeGroups) (M : ℕ) :
    P.MemoryState M ≃ SmallLabels P M × P.BigLabels M × PendingState P where
  toFun s := (restrictSmall s.2.1, P.restrictBig s.2.1, s.1, s.2.2)
  invFun c := (c.2.2.1, joinLabels c.1 c.2.1, c.2.2.2)
  left_inv := by
    intro s
    have h := (splitLabels P M).left_inv s.2.1
    change joinLabels (restrictSmall s.2.1) (P.restrictBig s.2.1) = s.2.1 at h
    change (s.1, joinLabels (restrictSmall s.2.1) (P.restrictBig s.2.1), s.2.2) = s
    rw [h]
  right_inv := by
    intro c
    apply Prod.ext
    · funext g
      exact joinLabels_small c.1 c.2.1 g
    · apply Prod.ext
      · funext g
        exact joinLabels_big c.1 c.2.1 g
      · rfl

def cutoffStateCoordinates (P : PrimeGroups) (M B : ℕ) :
    {s : P.MemoryState M // P.memorySize s ≤ B} ≃
      SmallLabels P M × P.BigLabels M × CutPendingState P B where
  toFun s := (restrictSmall s.val.2.1, P.restrictBig s.val.2.1,
    ⟨(s.val.1, s.val.2.2), s.property⟩)
  invFun c := ⟨(c.2.2.val.1, joinLabels c.1 c.2.1, c.2.2.val.2), c.2.2.property⟩
  left_inv := by
    intro s
    apply Subtype.ext
    exact (stateCoordinates P M).left_inv s.val
  right_inv := by
    intro c
    apply Prod.ext
    · funext g
      exact joinLabels_small c.1 c.2.1 g
    · apply Prod.ext
      · funext g
        exact joinLabels_big c.1 c.2.1 g
      · apply Subtype.ext
        rfl

theorem mem_smallArrayStates (M : ℕ) (y : P.SmallResidues) (a : SmallLabels P M) :
    a ∈ smallArrayStates P M y ↔
      ∀ g : P.SmallGroup, Function.Injective (a g) ∧ ∀ i, y g (a g i) = 0 := by
  simp only [smallArrayStates, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem smallPhysical_join {M : ℕ} (y : P.SmallResidues)
    (a : SmallLabels P M) (b : P.BigLabels M) :
    P.smallPhysical y (joinLabels a b) ↔ a ∈ smallArrayStates P M y := by
  rw [mem_smallArrayStates]
  unfold PrimeGroups.smallPhysical
  apply forall_congr'
  intro g
  exact iff_of_eq (congrArg
    (fun f : Fin M → P.Prime g.val => Function.Injective f ∧ ∀ i, y g (f i) = 0)
    (joinLabels_small a b g))

def tiltedIdealMass (F : FixedData) (n : ℕ) {M : ℕ} (a : P.BigLabels M) : ℝ :=
  ∏ g : P.BigGroup, ∏ i, tiltedMu F P n g.val (a g i)

theorem memoryMass_coordinates (F : FixedData) (J n : ℕ)
    (a : SmallLabels P (J + F.ell)) (b : P.BigLabels (J + F.ell)) (u : PendingState P) :
    P.memoryMass F J n (u.1, joinLabels a b, u.2) =
      (if a ∈ smallArrayStates P (J + F.ell) u.1 then smallMarkMass P (J + F.ell) else 0) *
        tiltedIdealMass F n b * pendingMass F n u := by
  classical
  simp only [PrimeGroups.memoryMass, smallPhysical_join, joinLabels_big,
    smallMarkMass, tiltedIdealMass, pendingMass]
  split_ifs <;> ring


end Erdos821.P3Clean
