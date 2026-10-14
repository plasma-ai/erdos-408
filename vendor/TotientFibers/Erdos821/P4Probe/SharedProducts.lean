import Erdos821.P4Probe.GraphSharedPairing

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

local instance sharedProductSiteDecidableEq (P : PrimeGroups) (M : ℕ) :
    DecidableEq (BigSite P M) := Classical.decEq _

lemma shared_slot_iff (ν : Pattern P J ell m) (g : P.Group) (i : Fin J) :
    ν.shared g (ν.slot i) ↔ i ∉ ν.changed g := by
  constructor
  · rintro ⟨j, hj, hn⟩
    have hv : (ν.slot j).val = (ν.slot i).val := congrArg Fin.val hj
    have he : j = i := Fin.ext hv
    simpa [he] using hn
  · intro hn
    exact ⟨i, rfl, hn⟩

lemma shared_castAdd_iff (ν : Pattern P J ell m) (g : P.Group) (i : Fin J) :
    ν.shared g (Fin.castAdd ell i) ↔ i ∉ ν.changed g := by
  have hs : ν.slot i = Fin.castAdd ell i := by apply Fin.ext; rfl
  rw [← hs, shared_slot_iff]

lemma not_shared_natAdd (ν : Pattern P J ell m) (g : P.Group) (i : Fin ell) :
    ¬ν.shared g (Fin.natAdd J i) := by
  rintro ⟨j, hj, _⟩
  have he := congrArg Fin.val hj
  change j.val = J + i.val at he
  have hi := j.isLt
  omega

def sharedNaturalProduct (ν : Pattern P J ell m)
    (s : PartialSample (bigSharedSet ν) (BigAlphabet P (J + ell))) : ℕ :=
  ∏ z, (s z).val

lemma sharedNaturalProduct_pos (ν : Pattern P J ell m)
    (s : PartialSample (bigSharedSet ν) (BigAlphabet P (J + ell))) :
    0 < sharedNaturalProduct ν s := by
  apply Finset.prod_pos
  intro z _
  exact (P.prime z.val.1.val _ (s z).property).pos

lemma sharedNaturalProduct_restrict (ν : Pattern P J ell m)
    (a : P.BigLabels (J + ell)) :
    sharedNaturalProduct ν (fun z => flattenBig P (J + ell) a z.val) = sharedPrefixProduct ν a := by
  let f := fun z : BigSite P (J + ell) => (a z.1 z.2).val
  change (∏ z : {z // z ∈ bigSharedSet ν}, f z.val) = _
  calc
    _ = ∏ z ∈ bigSharedSet ν, f z := Finset.prod_coe_sort _ _
    _ = ∏ z : BigSite P (J + ell), if ν.shared z.1.val z.2 then f z else 1 := by
      rw [bigSharedSet, Finset.prod_filter]
    _ = ∏ g : P.BigGroup, ∏ i : Fin (J + ell),
        if ν.shared g.val i then (a g i).val else 1 := Fintype.prod_prod_type _
    _ = _ := by
      unfold sharedPrefixProduct
      apply Finset.prod_congr rfl
      intro g _
      rw [Fin.prod_univ_add]
      have ht : (∏ i : Fin ell, if ν.shared g.val (Fin.natAdd J i)
          then (a g (Fin.natAdd J i)).val else 1) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        rw [if_neg (not_shared_natAdd ν g.val i)]
      rw [ht, mul_one]
      apply Finset.prod_congr rfl
      intro i _
      rw [shared_castAdd_iff]
      have hs : ν.slot i = Fin.castAdd ell i := by apply Fin.ext; rfl
      by_cases hi : i ∈ ν.changed g.val <;> simp [hi, hs]

lemma sharedPrefixProduct_join (ν : Pattern P J ell m)
    (s : PartialSample (bigSharedSet ν) (BigAlphabet P (J + ell)))
    (u : FreshSample (bigSharedSet ν) (BigAlphabet P (J + ell))) :
    sharedPrefixProduct ν ((flattenBig P (J + ell)).symm (joinSharedFresh (bigSharedSet ν) s u)) =
      sharedNaturalProduct ν s := by
  rw [← sharedNaturalProduct_restrict]
  congr 1
  funext z
  simp [flattenBig, joinSharedFresh, Equiv.piEquivPiSubtypeProd, z.property]

end
end Erdos821.P4Probe
