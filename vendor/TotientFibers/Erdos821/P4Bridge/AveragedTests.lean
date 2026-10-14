import Erdos821.P4Bridge.ConditionalTests

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

lemma bigAverage_congr_outside (M : ℕ) (S : P.BigGroup → Finset (Fin M))
    (f : P.BigLabels M → ℂ) (a b : P.BigLabels M)
    (hab : ∀ g i, i ∉ S g → a g i = b g i) :
    bigCoordinateAverage P M S f a = bigCoordinateAverage P M S f b := by
  unfold bigCoordinateAverage
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  funext g i
  by_cases hi : i ∈ S g
  · simp [hi]
  · simp [hi, hab g i hi]

@[simp] lemma labelJoin_slot (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) (g : P.BigGroup) (i : Fin J) :
    labelJoin ν block s a b t g (ν.slot i) =
      rowJoin ν block s (tupleRowPartial _ a) (tupleRowPartial _ b) g i := by
  change Fin.addCases (motive := fun _ => P.Prime g.val) (rowJoin ν block s (tupleRowPartial _ a) (tupleRowPartial _ b) g)
    (t g) (Fin.castAdd ell i) = _
  simp

@[simp] lemma labelJoin_tail (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) (g : P.BigGroup) (i : Fin ell) :
    labelJoin ν block s a b t g (Fin.natAdd J i) = t g i := by
  change Fin.addCases (motive := fun _ => P.Prime g.val) (rowJoin ν block s (tupleRowPartial _ a) (tupleRowPartial _ b) g)
    (t g) (Fin.natAdd J i) = _
  simp

lemma bigAverage_join_false (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (f : P.BigLabels (J + ell) → ℂ) (s : SharedRows ν)
    (a a' : SideTuple ν block false) (b : SideTuple ν block true) (t : P.BigLabels ell) :
    bigCoordinateAverage P (J + ell) (patternSideCoordinates ν block false) f
      (labelJoin ν block s a b t) =
    bigCoordinateAverage P (J + ell) (patternSideCoordinates ν block false) f
      (labelJoin ν block s a' b t) := by
  apply bigAverage_congr_outside
  intro g i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hnot
    have hs : Fin.castAdd ell j = ν.slot j := rfl
    rw [hs] at hnot ⊢
    rw [labelJoin_slot, labelJoin_slot]
    by_cases hi : j ∈ ν.changed g.val
    · by_cases hb : block g = false
      · have hmem : ν.slot j ∈ patternSideCoordinates ν block false g := by
          simp only [patternSideCoordinates, hb, ite_true]
          exact Finset.mem_image.mpr ⟨j, hi, rfl⟩
        exact False.elim (hnot hmem)
      · simp [rowJoin, hi, hb]
    · simp only [rowJoin, hi, dite_false]
  · intro _
    simp only [labelJoin_tail]

lemma bigAverage_join_true (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (f : P.BigLabels (J + ell) → ℂ) (s : SharedRows ν)
    (a : SideTuple ν block false) (b b' : SideTuple ν block true) (t : P.BigLabels ell) :
    bigCoordinateAverage P (J + ell) (patternSideCoordinates ν block true) f
      (labelJoin ν block s a b t) =
    bigCoordinateAverage P (J + ell) (patternSideCoordinates ν block true) f
      (labelJoin ν block s a b' t) := by
  apply bigAverage_congr_outside
  intro g i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hnot
    have hs : Fin.castAdd ell j = ν.slot j := rfl
    rw [hs] at hnot ⊢
    rw [labelJoin_slot, labelJoin_slot]
    by_cases hi : j ∈ ν.changed g.val
    · by_cases hb : block g = false
      · simp only [rowJoin, hi, hb, dite_true]
      · have htrue : block g = true := by cases h : block g <;> simp_all
        have hmem : ν.slot j ∈ patternSideCoordinates ν block true g := by
          simp only [patternSideCoordinates, htrue, ite_true]
          exact Finset.mem_image.mpr ⟨j, hi, rfl⟩
        exact False.elim (hnot hmem)
    · simp only [rowJoin, hi, dite_false]
  · intro _
    simp only [labelJoin_tail]

end
end Erdos821.P4Bridge
