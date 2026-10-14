import Erdos821.P4Probe.Probability

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def splitBigLabels (P : PrimeGroups) (J ell : ℕ) :
    P.BigLabels (J + ell) ≃ P.BigLabels J × P.BigLabels ell where
  toFun a := (fun g i => a g (Fin.castAdd ell i), fun g i => a g (Fin.natAdd J i))
  invFun a := fun g => Fin.addCases (a.1 g) (a.2 g)
  left_inv a := by
    funext g i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  right_inv a := by
    apply Prod.ext <;> funext g i <;> simp

lemma idealMass_split (P : PrimeGroups) (J ell : ℕ) (a : P.BigLabels (J + ell)) :
    P.idealMass a = P.idealMass ((splitBigLabels P J ell a).1) *
      P.idealMass ((splitBigLabels P J ell a).2) := by
  unfold PrimeGroups.idealMass
  simp only [Fin.prod_univ_add]
  rw [Finset.prod_mul_distrib]
  rfl

lemma raw_shared_iff {P : PrimeGroups} {J ell m : ℕ} (g : P.Group) (i : Fin (J + ell)) :
    (rawPattern P J ell m).shared g i ↔ i.val < J := by
  constructor
  · rintro ⟨j, hj, _⟩
    have h := congrArg Fin.val hj
    exact h ▸ j.isLt
  · intro hi
    refine ⟨⟨i.val, hi⟩, ?_, ?_⟩
    · apply Fin.ext
      rfl
    · simp [rawPattern]

lemma raw_matches_prefix {P : PrimeGroups} {J ell m : ℕ}
    (a b : P.BigLabels (J + ell)) :
    (rawPattern P J ell m).matchesBig a b ↔
      (splitBigLabels P J ell a).1 = (splitBigLabels P J ell b).1 := by
  constructor
  · intro h
    funext g j
    exact h g (Fin.castAdd ell j) ((raw_shared_iff g.val _).mpr j.isLt)
  · intro h g i hi
    have hj : i.val < J := (raw_shared_iff g.val i).mp hi
    let j : Fin J := ⟨i.val, hj⟩
    have he : Fin.castAdd ell j = i := by apply Fin.ext; rfl
    have hv := congrFun (congrFun h g) j
    change a g (Fin.castAdd ell j) = b g (Fin.castAdd ell j) at hv
    rwa [he] at hv

lemma raw_freshMass_tail {P : PrimeGroups} {J ell m : ℕ} (b : P.BigLabels (J + ell)) :
    (rawPattern P J ell m).freshMass b = P.idealMass ((splitBigLabels P J ell b).2) := by
  unfold Pattern.freshMass PrimeGroups.idealMass
  apply Finset.prod_congr rfl
  intro g _
  rw [Fin.prod_univ_add]
  have hp : (∏ i : Fin J, if (rawPattern P J ell m).shared g.val (Fin.castAdd ell i)
      then (1 : ℝ) else P.mu g.val (b g (Fin.castAdd ell i))) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [if_pos ((raw_shared_iff g.val _).mpr i.isLt)]
  rw [hp, one_mul]
  apply Finset.prod_congr rfl
  intro i _
  have hi : ¬(rawPattern P J ell m).shared g.val (Fin.natAdd J i) := by
    rw [raw_shared_iff]
    change ¬J + i.val < J
    omega
  rw [if_neg hi]
  rfl

def prefixProduct {P : PrimeGroups} {J : ℕ} (a : P.BigLabels J) : ℕ :=
  ∏ g, ∏ i, (a g i).val

lemma raw_DBig_prefix {P : PrimeGroups} {J ell m : ℕ}
    (a : P.BigLabels (J + ell)) (u : P.BigAux J) :
    (rawPattern P J ell m).DBig a u = prefixProduct ((splitBigLabels P J ell a).1) := by
  unfold Pattern.DBig prefixProduct
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  simp only [rawPattern, Finset.notMem_empty, ite_false]
  rfl

end
end Erdos821.P4Probe
