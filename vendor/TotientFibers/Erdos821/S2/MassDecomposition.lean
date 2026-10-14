import Erdos821.S2.SpanCoefficients

/-! The original small and big mark normalizations split without extra charges. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem primeGroups_prod_split {R : Type*} [CommMonoid R] (P : PrimeGroups)
    (f : P.Group → R) :
    (∏ g : P.Group, f g) = (∏ g : P.SmallGroup, f g.val) * ∏ g : P.BigGroup, f g.val := by
  let e : {g : P.Group // ¬ P.big g = false} ≃ P.BigGroup :=
    Equiv.subtypeEquivRight (fun g => by cases P.big g <;> simp)
  have hc : (∏ g : {g : P.Group // ¬ P.big g = false}, f g.val) =
      ∏ g : P.BigGroup, f g.val := Fintype.prod_equiv e _ _ (fun _ => rfl)
  have he := Fintype.prod_subtype_mul_prod_subtype (fun g : P.Group => P.big g = false) f
  rw [hc] at he
  exact he.symm

theorem markMass_split (P : PrimeGroups) (M : ℕ) :
    P.markMass M = (∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℤ))) *
      ∏ g : P.BigGroup, (P.V g.val) ^ (-(M : ℤ)) :=
  primeGroups_prod_split P _

theorem physicalTargetMass_split {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (nu : Pattern P J F.ell m) :
    nu.physicalTargetMass = smallTargetFactor (P := P) F *
      ∏ g : P.BigGroup, (P.V g.val) ^ (-(nu.t g.val : ℤ)) := by
  unfold Pattern.physicalTargetMass smallTargetFactor
  rw [primeGroups_prod_split]
  congr 1
  apply Finset.prod_congr rfl
  intro g _
  simp only [Pattern.t, nu.small g.val g.property, Finset.card_empty, Nat.add_zero]

theorem memoryMass_empty {F : FixedData} {P : PrimeGroups} (J n : ℕ)
    (y : P.SmallResidues) (a : P.Labels (J + F.ell)) :
    P.memoryMass F J n (y, a, fun _ => 0) =
      if P.smallPhysical y a then
        (Fintype.card P.SmallResidues : ℝ)⁻¹ *
          (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
          (∏ g : P.BigGroup, ∏ j : Fin (J + F.ell), tiltedMu F P n g.val (a g.val j))
      else 0 := by
  simp [PrimeGroups.memoryMass, PrimeGroups.groupMemoryMass]

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

theorem stateBefore_initial (S : LifespanAssignment P n) (y : P.SmallResidues) :
    Q.stateBefore S y 0 = (y, Q.labels 0, fun _ => 0) := by
  apply Prod.ext
  · change translateSmallResidues (Q.offset 0) y = y
    rw [offset_zero, translateSmallResidues_zero]
  · apply Prod.ext
    · rfl
    · funext g
      exact Q.memoryBefore_zero S g

theorem reconstructed_initial_mass (S : LifespanAssignment P n) (y : P.SmallResidues)
    (hy : Q.SmallCompatible y) :
    P.memoryMass F J n (Q.stateBefore S y 0) =
      (Fintype.card P.SmallResidues : ℝ)⁻¹ *
        (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
        (∏ g : P.BigGroup, ∏ j : Fin (J + F.ell), tiltedMu F P n g.val (Q.labels 0 g.val j)) := by
  rw [Q.stateBefore_initial, memoryMass_empty]
  have hp := hy 0
  rw [offset_zero, translateSmallResidues_zero] at hp
  exact ite_eq_left hp


end ResiduePath


end Erdos821.S2Core
