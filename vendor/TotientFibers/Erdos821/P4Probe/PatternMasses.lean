import Erdos821.P4Probe.PatternProducts

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

def sharedLabelMass (ν : Pattern P J ell m) (a : P.BigLabels (J + ell)) : ℝ :=
  ∏ g, ∏ i, if ν.shared g.val i then P.mu g.val (a g i) else 1

lemma sharedLabelMass_mul_freshMass (ν : Pattern P J ell m)
    (a : P.BigLabels (J + ell)) :
    sharedLabelMass ν a * ν.freshMass a = P.idealMass a := by
  unfold sharedLabelMass Pattern.freshMass PrimeGroups.idealMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

lemma sharedLabelMass_pos (ν : Pattern P J ell m) (hV : ∀ g, 0 < P.V g)
    (a : P.BigLabels (J + ell)) : 0 < sharedLabelMass ν a := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact graph_mu_pos P g.val (hV g.val) (a g i)
  · exact zero_lt_one

lemma sharedLabelMass_matches (ν : Pattern P J ell m)
    {a b : P.BigLabels (J + ell)} (hab : ν.matchesBig a b) :
    sharedLabelMass ν a = sharedLabelMass ν b := by
  unfold sharedLabelMass
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : ν.shared g.val i
  · rw [if_pos hi, if_pos hi, hab g i hi]
  · simp [hi]

lemma freshMass_eq_div_shared (ν : Pattern P J ell m) (hV : ∀ g, 0 < P.V g)
    {a b : P.BigLabels (J + ell)} (hab : ν.matchesBig a b) :
    ν.freshMass b = P.idealMass b / sharedLabelMass ν a := by
  apply (eq_div_iff (sharedLabelMass_pos ν hV a).ne').mpr
  rw [sharedLabelMass_matches ν hab]
  simpa [mul_comm] using sharedLabelMass_mul_freshMass ν b

lemma idealRaw_eq_targetMass {F : FixedData} (A : Model F P J m)
    (hV : ∀ g, 0 < P.V g) (θ : ℝ) (a b : P.BigLabels (J + F.ell)) :
    A.idealRaw θ a b = (P.idealMass b : ℂ) *
      ∑ v : Fin A.patternCount, ∑ u : P.BigAux J,
        if (A.pattern v).matchesBig a b then
          ((A.pattern v).bigAuxMass u / sharedLabelMass (A.pattern v) a : ℝ) *
            (A.pattern v).coefficient a b u * imaginaryPower ((A.pattern v).DBig a u) A.zeta *
            phase (θ * (A.pattern v).DBig a u)
        else 0 := by
  unfold Model.idealRaw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hab : (A.pattern v).matchesBig a b
  · rw [if_pos hab, if_pos hab, freshMass_eq_div_shared (A.pattern v) hV hab]
    simp only [Complex.ofReal_mul, Complex.ofReal_div]
    ring
  · simp [hab]

end
end Erdos821.P4Probe
