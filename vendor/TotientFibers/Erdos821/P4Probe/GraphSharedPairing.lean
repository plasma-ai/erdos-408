import Erdos821.P4Probe.SharedPairingTask
import Erdos821.P4Probe.PatternMasses
import Erdos821.P4Probe.BigAveraging

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

local instance graphSharedSiteDecidableEq (P : PrimeGroups) (M : ℕ) :
    DecidableEq (BigSite P M) := Classical.decEq _

def bigSharedSet (ν : Pattern P J ell m) : Finset (BigSite P (J + ell)) :=
  Finset.univ.filter (fun z => ν.shared z.1.val z.2)

lemma sameShared_flat_iff (ν : Pattern P J ell m) (a b : P.BigLabels (J + ell)) :
    sameShared (bigSharedSet ν) (flattenBig P (J + ell) a) (flattenBig P (J + ell) b) ↔
      ν.matchesBig a b := by
  simp [sameShared, bigSharedSet, Pattern.matchesBig, flattenBig, Prod.forall]

lemma freshProductWeight_flat_eq (ν : Pattern P J ell m) (b : P.BigLabels (J + ell)) :
    freshProductWeight (bigFlatWeight P (J + ell)) (bigSharedSet ν)
      (flattenBig P (J + ell) b) = ν.freshMass b := by
  unfold freshProductWeight bigSharedSet Pattern.freshMass
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Fintype.prod_prod_type _

lemma graph_shared_pairing_of_task (htask : SharedPairingTask)
    (ν : Pattern P J ell m) (H : P.BigLabels (J + ell) → P.BigLabels (J + ell) → ℂ) :
    (∑ a, ∑ b, if ν.matchesBig a b then
      ((P.idealMass a * ν.freshMass b : ℝ) : ℂ) * H a b else 0) =
      ∑ s : PartialSample (bigSharedSet ν) (BigAlphabet P (J + ell)),
        ∑ u : FreshSample (bigSharedSet ν) (BigAlphabet P (J + ell)),
          ∑ v : FreshSample (bigSharedSet ν) (BigAlphabet P (J + ell)),
            ((partialProductWeight (bigFlatWeight P (J + ell)) (bigSharedSet ν) s *
              productWeight (fun i : {i // i ∉ bigSharedSet ν} => bigFlatWeight P (J + ell) i.val) u *
              productWeight (fun i : {i // i ∉ bigSharedSet ν} => bigFlatWeight P (J + ell) i.val) v : ℝ) : ℂ) *
                H ((flattenBig P (J + ell)).symm (joinSharedFresh (bigSharedSet ν) s u))
                  ((flattenBig P (J + ell)).symm (joinSharedFresh (bigSharedSet ν) s v)) := by
  have ht := htask (BigSite P (J + ell)) (BigAlphabet P (J + ell))
    (bigFlatWeight P (J + ell)) (bigSharedSet ν)
    (fun x y => H ((flattenBig P (J + ell)).symm x) ((flattenBig P (J + ell)).symm y))
  rw [← ht]
  apply Fintype.sum_equiv (flattenBig P (J + ell))
  intro a
  apply Fintype.sum_equiv (flattenBig P (J + ell))
  intro b
  rw [sameShared_flat_iff, bigFlatWeight_eq, freshProductWeight_flat_eq]
  simp

end
end Erdos821.P4Probe
