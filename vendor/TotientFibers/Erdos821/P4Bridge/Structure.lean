import Erdos821.P4Bridge.Sites
import Erdos821.P4Bridge.Support

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

def sharedRows (ν : Pattern P J ell m) (g : P.BigGroup) : Finset (Fin J) :=
  Finset.univ \ ν.changed g.val

abbrev SharedRows (ν : Pattern P J ell m) := BigRowPartial (sharedRows ν)
abbrev SideRows (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (side : Bool) :=
  BigRowPartial (patternAuxCoordinates ν block side)

lemma mem_sideRows (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (side : Bool) (g : P.BigGroup) (i : Fin J) :
    i ∈ patternAuxCoordinates ν block side g ↔ block g = side ∧ i ∈ ν.changed g.val := by
  unfold patternAuxCoordinates
  by_cases hb : block g = side <;> simp [hb]

def rowJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideRows ν block false) (b : SideRows ν block true) :
    P.BigLabels J := fun g i =>
  if hi : i ∈ ν.changed g.val then
    if hb : block g = false then a g ⟨i, (mem_sideRows ν block false g i).mpr ⟨hb, hi⟩⟩
    else b g ⟨i, (mem_sideRows ν block true g i).mpr ⟨by cases h : block g <;> simp_all, hi⟩⟩
  else s g ⟨i, by simp [sharedRows, hi]⟩

@[simp] lemma rowJoin_shared (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideRows ν block false) (b : SideRows ν block true)
    (g : P.BigGroup) (i : {i // i ∈ sharedRows ν g}) :
    rowJoin ν block s a b g i.val = s g i := by
  have hi : i.val ∉ ν.changed g.val := by simpa [sharedRows] using i.property
  simp [rowJoin, hi]

@[simp] lemma rowJoin_false (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideRows ν block false) (b : SideRows ν block true)
    (g : P.BigGroup) (i : {i // i ∈ patternAuxCoordinates ν block false g}) :
    rowJoin ν block s a b g i.val = a g i := by
  have hi := (mem_sideRows ν block false g i.val).mp i.property
  simp [rowJoin, hi.1, hi.2]

@[simp] lemma rowJoin_true (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideRows ν block false) (b : SideRows ν block true)
    (g : P.BigGroup) (i : {i // i ∈ patternAuxCoordinates ν block true g}) :
    rowJoin ν block s a b g i.val = b g i := by
  have hi := (mem_sideRows ν block true g i.val).mp i.property
  simp [rowJoin, hi.1, hi.2]

def rowSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    P.BigLabels J ≃ SharedRows ν × SideRows ν block false × SideRows ν block true where
  toFun u := (fun g i => u g i.val, (fun g i => u g i.val), fun g i => u g i.val)
  invFun z := rowJoin ν block z.1 z.2.1 z.2.2
  left_inv u := by
    funext g i
    dsimp only
    unfold rowJoin
    dsimp only
    split_ifs <;> rfl
  right_inv z := by
    apply Prod.ext
    · funext g i
      exact rowJoin_shared ν block z.1 z.2.1 z.2.2 g i
    · apply Prod.ext
      · funext g i
        exact rowJoin_false ν block z.1 z.2.1 z.2.2 g i
      · funext g i
        exact rowJoin_true ν block z.1 z.2.1 z.2.2 g i

def rowWeight (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) : ℝ :=
  ∏ g, ∏ i, P.mu g.val (x g i)

def rowProduct (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) : ℕ :=
  ∏ g, ∏ i, (x g i).val

lemma rowWeight_sum (hV : ∀ g, 0 < P.V g) (S : P.BigGroup → Finset (Fin J)) :
    ∑ x : BigRowPartial S, rowWeight S x = 1 := by
  unfold rowWeight
  trans ∏ g : P.BigGroup, ∑ x : {i // i ∈ S g} → P.Prime g.val,
    ∏ i, P.mu g.val (x i)
  · exact (Fintype.prod_sum (fun (g : P.BigGroup)
      (x : {i // i ∈ S g} → P.Prime g.val) => ∏ i, P.mu g.val (x i))).symm
  apply Finset.prod_eq_one
  intro g _
  trans ∏ _i : {i // i ∈ S g}, ∑ x : P.Prime g.val, P.mu g.val x
  · exact (Fintype.prod_sum (fun (_i : {i // i ∈ S g}) (x : P.Prime g.val) =>
      P.mu g.val x)).symm
  · simp only [graph_mu_sum P g.val (hV g.val), Finset.prod_const_one]

lemma rowWeight_pos (hV : ∀ g, 0 < P.V g) (S : P.BigGroup → Finset (Fin J))
    (x : BigRowPartial S) : 0 < rowWeight S x := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  exact graph_mu_pos P g.val (hV g.val) _

lemma rowProduct_pos (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) :
    0 < rowProduct S x := by
  apply Finset.prod_pos
  intro g _
  apply Finset.prod_pos
  intro i _
  exact (P.prime g.val _ (x g i).property).pos

lemma row_split_product {R : Type*} [CommMonoid R] (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (v : ∀ g : P.BigGroup, Fin J → R) :
    (∏ g, ∏ i, v g i) =
      (∏ g, ∏ i : {i // i ∈ sharedRows ν g}, v g i.val) *
      (∏ g, ∏ i : {i // i ∈ patternAuxCoordinates ν block false g}, v g i.val) *
      (∏ g, ∏ i : {i // i ∈ patternAuxCoordinates ν block true g}, v g i.val) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  simp only [Finset.prod_coe_sort]
  unfold sharedRows patternAuxCoordinates
  cases hb : block g <;> simp only [hb, ite_true, Bool.false_eq_true,
    Bool.true_eq_false, ite_false, Finset.prod_empty, mul_one, one_mul]
  all_goals
    rw [← Finset.prod_union (Finset.sdiff_disjoint), Finset.sdiff_union_of_subset (Finset.subset_univ _)]

def sideCounts (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (side : Bool) :=
  selectedCounts (patternAuxCoordinates ν block side)
abbrev SideTuple (ν : Pattern P J ell m) (block : P.BigGroup → Bool) (side : Bool) :=
  Blueprint.Analytic.Tuple (analyticGroups P) (sideCounts ν block side)

instance analyticTupleFintype (P : PrimeGroups) (k : P.Group → ℕ) :
    Fintype (Blueprint.Analytic.Tuple (analyticGroups P) k) :=
  inferInstanceAs (Fintype (∀ g : P.Group, Fin (k g) → P.Prime g))

def prefixSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    P.BigLabels J ≃ SharedRows ν × SideTuple ν block false × SideTuple ν block true :=
  (rowSplit ν block).trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr (rowPartialTupleEquiv _) (rowPartialTupleEquiv _)))

def labelSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool) :
    P.BigLabels (J + ell) ≃
      (SharedRows ν × SideTuple ν block false × SideTuple ν block true) × P.BigLabels ell :=
  (splitBigLabels P J ell).trans (Equiv.prodCongr (prefixSplit ν block) (Equiv.refl _))

def labelJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : P.BigLabels (J + ell) :=
  (labelSplit ν block).symm ((s, a, b), t)

lemma idealMass_rowSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (u : P.BigLabels J) :
    P.idealMass u = rowWeight (sharedRows ν) ((rowSplit ν block u).1) *
      rowWeight (patternAuxCoordinates ν block false) ((rowSplit ν block u).2.1) *
      rowWeight (patternAuxCoordinates ν block true) ((rowSplit ν block u).2.2) :=
  row_split_product ν block (fun g i => P.mu g.val (u g i))

lemma idealMass_prefixSplit (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (u : P.BigLabels J) :
    P.idealMass u = rowWeight (sharedRows ν) ((prefixSplit ν block u).1) *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false)
        ((prefixSplit ν block u).2.1) *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true)
        ((prefixSplit ν block u).2.2) := by
  rw [idealMass_rowSplit ν block u]
  change _ = rowWeight (sharedRows ν) ((rowSplit ν block u).1) *
    Blueprint.Analytic.tupleWeight (analyticGroups P) _
      (rowPartialTuple _ ((rowSplit ν block u).2.1)) *
    Blueprint.Analytic.tupleWeight (analyticGroups P) _
      (rowPartialTuple _ ((rowSplit ν block u).2.2))
  rw [rowPartialTuple_weight, rowPartialTuple_weight]
  rfl

lemma idealMass_labelJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) :
    P.idealMass (labelJoin ν block s a b t) = rowWeight (sharedRows ν) s *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b * P.idealMass t := by
  rw [idealMass_split, idealMass_prefixSplit ν block]
  have he := (labelSplit ν block).apply_symm_apply ((s, a, b), t)
  change ((prefixSplit ν block) ((splitBigLabels P J ell (labelJoin ν block s a b t)).1),
    (splitBigLabels P J ell (labelJoin ν block s a b t)).2) = ((s, a, b), t) at he
  have hp : (prefixSplit ν block) ((splitBigLabels P J ell
      (labelJoin ν block s a b t)).1) = (s, a, b) := congrArg Prod.fst he
  have ht : (splitBigLabels P J ell (labelJoin ν block s a b t)).2 = t :=
    congrArg Prod.snd he
  rw [hp, ht]

end
end Erdos821.P4Bridge
