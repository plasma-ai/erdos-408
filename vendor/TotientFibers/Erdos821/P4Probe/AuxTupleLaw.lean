import Erdos821.P4Probe.SelectedTuples
import Erdos821.P4Independent.DisjointMarginal

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

local instance auxTupleSiteDecidableEq (P : PrimeGroups) (J : ℕ) :
    DecidableEq (BigSite P J) := Classical.decEq _

local instance auxAnalyticTupleFintype (P : PrimeGroups) (k : P.Group → ℕ) :
    Fintype (Blueprint.Analytic.Tuple (analyticGroups P) k) :=
  inferInstanceAs (Fintype (∀ g : P.Group, Fin (k g) → P.Prime g))

lemma auxSideSets_disjoint (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    Disjoint (bigFlatSet P J (patternAuxCoordinates ν block false))
      (bigFlatSet P J (patternAuxCoordinates ν block true)) := by
  rw [Finset.disjoint_left]
  intro z hzF hzT
  have hF : block z.1 = false := by
    by_contra hh
    have hz := (Finset.mem_filter.mp hzF).2
    change z.2 ∈ (if block z.1 = false then ν.changed z.1.val else ∅) at hz
    rw [if_neg hh] at hz
    exact Finset.notMem_empty _ hz
  have hT : block z.1 = true := by
    by_contra hh
    have hz := (Finset.mem_filter.mp hzT).2
    change z.2 ∈ (if block z.1 = true then ν.changed z.1.val else ∅) at hz
    rw [if_neg hh] at hz
    exact Finset.notMem_empty _ hz
  cases hF.symm.trans hT

lemma bigAux_selected_pair_expect (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g)
    (H : Blueprint.Analytic.Tuple (analyticGroups P)
        (selectedCounts (patternAuxCoordinates ν block false)) →
      Blueprint.Analytic.Tuple (analyticGroups P)
        (selectedCounts (patternAuxCoordinates ν block true)) → ℂ) :
    (∑ u : P.BigAux J, (ν.bigAuxMass u : ℂ) *
      H (selectedAuxTuple ν block false u) (selectedAuxTuple ν block true u)) =
        ∑ a : Blueprint.Analytic.Tuple (analyticGroups P)
            (selectedCounts (patternAuxCoordinates ν block false)),
          ∑ b : Blueprint.Analytic.Tuple (analyticGroups P)
              (selectedCounts (patternAuxCoordinates ν block true)),
            ((Blueprint.Analytic.tupleWeight (analyticGroups P)
              (selectedCounts (patternAuxCoordinates ν block false)) a *
              Blueprint.Analytic.tupleWeight (analyticGroups P)
              (selectedCounts (patternAuxCoordinates ν block true)) b : ℝ) : ℂ) * H a b := by
  let SF := patternAuxCoordinates ν block false
  let ST := patternAuxCoordinates ν block true
  let eF := (flatPartialRows SF).trans (rowPartialTupleEquiv SF)
  let eT := (flatPartialRows ST).trans (rowPartialTupleEquiv ST)
  have hind := DisjointMarginalTask_proof (BigSite P J) (BigAlphabet P J)
    (bigFlatWeight P J) (bigFlatSet P J SF) (bigFlatSet P J ST)
    (fun z => graph_mu_sum P z.1.val (hV z.1.val)) (auxSideSets_disjoint ν block)
    (fun a b => H (eF a) (eT b))
  have hl : (∑ u : P.BigAux J, (ν.bigAuxMass u : ℂ) *
      H (selectedAuxTuple ν block false u) (selectedAuxTuple ν block true u)) =
      ∑ y : ProductSample (BigAlphabet P J), (productWeight (bigFlatWeight P J) y : ℂ) *
        H (eF (fun i => y i.val)) (eT (fun i => y i.val)) := by
    apply Fintype.sum_equiv (flattenBig P J)
    intro u
    rw [bigFlatWeight_eq]
    rfl
  rw [hl, hind]
  letI : Fintype (Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts SF)) :=
    inferInstanceAs (Fintype (∀ g : P.Group, Fin (selectedCounts SF g) → P.Prime g))
  letI : Fintype (Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts ST)) :=
    inferInstanceAs (Fintype (∀ g : P.Group, Fin (selectedCounts ST g) → P.Prime g))
  apply Fintype.sum_equiv eF
  intro a
  apply Fintype.sum_equiv eT
  intro b
  have hwF : partialProductWeight (bigFlatWeight P J) (bigFlatSet P J SF) a =
      Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts SF) (eF a) :=
    (partialProductWeight_rows SF a).trans (rowPartialTuple_weight SF (flatPartialRows SF a)).symm
  have hwT : partialProductWeight (bigFlatWeight P J) (bigFlatSet P J ST) b =
      Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts ST) (eT b) :=
    (partialProductWeight_rows ST b).trans (rowPartialTuple_weight ST (flatPartialRows ST b)).symm
  exact congrArg (fun r : ℝ => (r : ℂ) * H (eF a) (eT b))
    (congrArg₂ (fun r s : ℝ => r * s) hwF hwT)

end
end Erdos821.P4Probe
