import Erdos821.P4Bridge.Structure

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

@[simp] lemma prefixSplit_apply (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (u : P.BigLabels J) :
    prefixSplit ν block u = ((fun g i => u g i.val),
      selectedAuxTuple ν block false u, selectedAuxTuple ν block true u) := rfl

@[simp] lemma labelSplit_apply (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (u : P.BigLabels (J + ell)) :
    labelSplit ν block u = ((fun g i => u g (ν.slot i.val),
      selectedLabelTuple ν block false u, selectedLabelTuple ν block true u),
      (splitBigLabels P J ell u).2) := rfl

@[simp] lemma labelSplit_join (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : labelSplit ν block (labelJoin ν block s a b t) = ((s, a, b), t) :=
  (labelSplit ν block).apply_symm_apply _

@[simp] lemma selectedLabelTuple_join_false (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : selectedLabelTuple ν block false (labelJoin ν block s a b t) = a :=
  congrArg (fun z => z.1.2.1) (labelSplit_join ν block s a b t)

@[simp] lemma selectedLabelTuple_join_true (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : selectedLabelTuple ν block true (labelJoin ν block s a b t) = b :=
  congrArg (fun z => z.1.2.2) (labelSplit_join ν block s a b t)

lemma sideWeight_sum (hV : ∀ g, 0 < P.V g) (S : P.BigGroup → Finset (Fin J)) :
    (∑ a : Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S),
      Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts S) a) = 1 := by
  have he : (∑ x : BigRowPartial S, rowWeight S x) =
      ∑ a : Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S),
        Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts S) a := by
    apply Fintype.sum_equiv (rowPartialTupleEquiv S)
    intro x
    exact (rowPartialTuple_weight S x).symm
  rw [← he, rowWeight_sum hV S]

lemma sideWeight_pos (hV : ∀ g, 0 < P.V g) (S : P.BigGroup → Finset (Fin J))
    (a : Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S)) :
    0 < Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts S) a := by
  rw [← (rowPartialTupleEquiv S).apply_symm_apply a]
  change 0 < Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts S)
    (rowPartialTuple S ((rowPartialTupleEquiv S).symm a))
  rw [rowPartialTuple_weight]
  exact rowWeight_pos hV S _

lemma sideProduct_pos (S : P.BigGroup → Finset (Fin J))
    (a : Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S)) :
    0 < Blueprint.Analytic.product (analyticGroups P) (selectedCounts S) a := by
  rw [← (rowPartialTupleEquiv S).apply_symm_apply a]
  change 0 < Blueprint.Analytic.product (analyticGroups P) (selectedCounts S)
    (rowPartialTuple S ((rowPartialTupleEquiv S).symm a))
  rw [rowPartialTuple_product]
  exact rowProduct_pos S _

lemma prod_sharedRows {R : Type*} [CommMonoid R] (ν : Pattern P J ell m)
    (g : P.BigGroup) (v : Fin J → R) :
    (∏ i : {i // i ∈ sharedRows ν g}, v i.val) =
      ∏ i : Fin J, if i ∈ ν.changed g.val then 1 else v i := by
  rw [Finset.prod_coe_sort]
  have hs : sharedRows ν g = Finset.univ.filter (fun i => i ∉ ν.changed g.val) := by
    ext i
    simp [sharedRows]
  rw [hs, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ν.changed g.val <;> simp [hi]

lemma sharedPrefixProduct_rows (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (a : P.BigLabels (J + ell)) :
    sharedPrefixProduct ν a = rowProduct (sharedRows ν) ((labelSplit ν block a).1.1) := by
  unfold sharedPrefixProduct rowProduct
  apply Finset.prod_congr rfl
  intro g _
  exact (prod_sharedRows ν g (fun i => (a g (ν.slot i)).val)).symm

lemma sharedLabelMass_rows (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (a : P.BigLabels (J + ell)) :
    sharedLabelMass ν a = rowWeight (sharedRows ν) ((labelSplit ν block a).1.1) := by
  unfold sharedLabelMass rowWeight
  apply Finset.prod_congr rfl
  intro g _
  rw [Fin.prod_univ_add]
  have ht : (∏ i : Fin ell, if ν.shared g.val (Fin.natAdd J i)
      then P.mu g.val (a g (Fin.natAdd J i)) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    rw [if_neg (not_shared_natAdd ν g.val i)]
  rw [ht, mul_one]
  change _ = ∏ i : {i // i ∈ sharedRows ν g}, P.mu g.val (a g (ν.slot i.val))
  rw [prod_sharedRows ν g (fun i => P.mu g.val (a g (ν.slot i)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [shared_castAdd_iff]
  by_cases hi : i ∈ ν.changed g.val <;> simp [hi] <;> rfl

lemma matchesBig_rows (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (a b : P.BigLabels (J + ell)) :
    ν.matchesBig a b ↔ (labelSplit ν block a).1.1 = (labelSplit ν block b).1.1 := by
  constructor
  · intro hab
    funext g i
    have hi : i.val ∉ ν.changed g.val := by simpa [sharedRows] using i.property
    exact hab g (ν.slot i.val) ⟨i.val, rfl, hi⟩
  · intro hab g i hi
    obtain ⟨j, rfl, hj⟩ := hi
    have hz : j ∈ sharedRows ν g := by simp [sharedRows, hj]
    exact congrFun (congrFun hab g) ⟨j, hz⟩

@[simp] lemma matchesBig_join (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s s' : SharedRows ν) (a a' : SideTuple ν block false)
    (b b' : SideTuple ν block true) (t t' : P.BigLabels ell) :
    ν.matchesBig (labelJoin ν block s a b t) (labelJoin ν block s' a' b' t') ↔ s = s' := by
  rw [matchesBig_rows ν block]
  simp only [labelSplit_join]

lemma freshMass_join (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g) (s : SharedRows ν) (a : SideTuple ν block false)
    (b : SideTuple ν block true) (t : P.BigLabels ell) :
    ν.freshMass (labelJoin ν block s a b t) =
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b * P.idealMass t := by
  rw [freshMass_eq_div_shared ν hV (fun _ _ _ => rfl), idealMass_labelJoin,
    sharedLabelMass_rows ν block, labelSplit_join]
  have hn := (rowWeight_pos hV (sharedRows ν) s).ne'
  field_simp [hn]

lemma selectedEndpoint_join_false (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : selectedEndpoint ν block false (labelJoin ν block s a b t) =
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a := by
  rw [← selectedLabelTuple_product, selectedLabelTuple_join_false]
  rfl

lemma selectedEndpoint_join_true (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : selectedEndpoint ν block true (labelJoin ν block s a b t) =
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b := by
  rw [← selectedLabelTuple_product, selectedLabelTuple_join_true]
  rfl

lemma sharedPrefixProduct_join_rows (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : sharedPrefixProduct ν (labelJoin ν block s a b t) =
      rowProduct (sharedRows ν) s := by
  rw [sharedPrefixProduct_rows ν block, labelSplit_join]

lemma selectedAuxTuple_prefixJoin_false (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true) :
    selectedAuxTuple ν block false ((prefixSplit ν block).symm (s, a, b)) = a :=
  congrArg (fun z => z.2.1) ((prefixSplit ν block).apply_symm_apply (s, a, b))

lemma selectedAuxTuple_prefixJoin_true (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true) :
    selectedAuxTuple ν block true ((prefixSplit ν block).symm (s, a, b)) = b :=
  congrArg (fun z => z.2.2) ((prefixSplit ν block).apply_symm_apply (s, a, b))

lemma idealMass_prefixJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true) :
    P.idealMass ((prefixSplit ν block).symm (s, a, b)) = rowWeight (sharedRows ν) s *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a *
      Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b := by
  rw [idealMass_prefixSplit ν block, Equiv.apply_symm_apply]

lemma prefixProduct_labelJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) :
    prefixProduct ((splitBigLabels P J ell (labelJoin ν block s a b t)).1) =
      rowProduct (sharedRows ν) s *
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a *
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b := by
  rw [prefixProduct_split ν block, sharedPrefixProduct_join_rows,
    selectedEndpoint_join_false, selectedEndpoint_join_true]

lemma DBig_labelJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s s' : SharedRows ν) (a a' : SideTuple ν block false) (b b' : SideTuple ν block true)
    (t : P.BigLabels ell) :
    ν.DBig (labelJoin ν block s a b t) ((prefixSplit ν block).symm (s', a', b')) =
      rowProduct (sharedRows ν) s *
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a' *
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b' := by
  rw [DBig_split ν block, sharedPrefixProduct_join_rows, ← selectedAuxTuple_product,
    ← selectedAuxTuple_product, selectedAuxTuple_prefixJoin_false, selectedAuxTuple_prefixJoin_true]
  rfl

lemma splitBigLabels_labelJoin (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (s : SharedRows ν) (a : SideTuple ν block false) (b : SideTuple ν block true)
    (t : P.BigLabels ell) : splitBigLabels P J ell (labelJoin ν block s a b t) =
      ((prefixSplit ν block).symm (s, a, b), t) := by
  change splitBigLabels P J ell ((splitBigLabels P J ell).symm
    ((prefixSplit ν block).symm (s, a, b), t)) = _
  exact (splitBigLabels P J ell).apply_symm_apply _

lemma multiplier_factor (C D E : ℕ) (hC : 0 < C) (hD : 0 < D) (hE : 0 < E)
    (θ ζ : ℝ) :
    imaginaryPower (C * D * E) ζ * phase (θ * (C * D * E)) =
      Blueprint.Analytic.mellin C ζ *
        (Blueprint.Analytic.mellin ((D : ℝ) * E) ζ *
          Blueprint.Analytic.e ((θ * C) * D * E)) := by
  rw [Nat.mul_assoc, imaginaryPower_mul C (D * E) hC (Nat.mul_pos hD hE)]
  simp only [imaginaryPower_eq_mellin, Nat.cast_mul, phase_mul_shift, mul_assoc]

end
end Erdos821.P4Bridge
