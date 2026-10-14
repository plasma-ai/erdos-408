import Erdos821.P4Probe.RawLabels

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

def sharedPrefixProduct (ν : Pattern P J ell m) (a : P.BigLabels (J + ell)) : ℕ :=
  ∏ g, ∏ i : Fin J, if i ∈ ν.changed g.val then 1 else (a g (ν.slot i)).val

lemma DBig_split (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (a : P.BigLabels (J + ell)) (u : P.BigAux J) :
    ν.DBig a u = sharedPrefixProduct ν a *
      selectedProduct ν block false u * selectedProduct ν block true u := by
  unfold Pattern.DBig sharedPrefixProduct selectedProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hb : block g <;> by_cases hi : i ∈ ν.changed g.val <;> simp [hb, hi]

lemma prefixProduct_split (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (a : P.BigLabels (J + ell)) :
    prefixProduct ((splitBigLabels P J ell a).1) = sharedPrefixProduct ν a *
      selectedEndpoint ν block false a * selectedEndpoint ν block true a := by
  unfold prefixProduct sharedPrefixProduct selectedEndpoint
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hs : ν.slot i = Fin.castAdd ell i := by apply Fin.ext; rfl
  cases hb : block g <;> by_cases hi : i ∈ ν.changed g.val <;>
    simp [hb, hi, splitBigLabels, hs]

lemma sharedPrefixProduct_matches (ν : Pattern P J ell m)
    {a b : P.BigLabels (J + ell)} (hab : ν.matchesBig a b) :
    sharedPrefixProduct ν a = sharedPrefixProduct ν b := by
  unfold sharedPrefixProduct
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ν.changed g.val
  · simp [hi]
  · simp only [hi, ite_false]
    rw [hab g (ν.slot i) ⟨i, rfl, hi⟩]

lemma sharedPrefixProduct_pos (ν : Pattern P J ell m)
    (a : P.BigLabels (J + ell)) : 0 < sharedPrefixProduct ν a := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact Nat.zero_lt_one
  · exact (P.prime g.val _ (a g (ν.slot i)).property).pos

lemma selectedProduct_pos (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (side : Bool) (u : P.BigAux J) : 0 < selectedProduct ν block side u := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact (P.prime g.val _ (u g i).property).pos
  · exact Nat.zero_lt_one

lemma selectedEndpoint_pos (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (side : Bool) (a : P.BigLabels (J + ell)) : 0 < selectedEndpoint ν block side a := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact (P.prime g.val _ (a g (ν.slot i)).property).pos
  · exact Nat.zero_lt_one

end
end Erdos821.P4Probe
