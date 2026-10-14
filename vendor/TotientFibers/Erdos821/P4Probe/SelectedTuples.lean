import Erdos821.P4Probe.BigAveraging
import Erdos821.P4Probe.ProductMarginals
import Erdos821.P4Probe.Bridge

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

variable {P : PrimeGroups} {J : ℕ}

abbrev BigRowPartial (S : P.BigGroup → Finset (Fin J)) :=
  ∀ g : P.BigGroup, {i // i ∈ S g} → P.Prime g.val

def selectedCounts (S : P.BigGroup → Finset (Fin J)) (g : P.Group) : ℕ :=
  if hg : P.big g = true then (S ⟨g, hg⟩).card else 0

def rowPartialTuple (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) :
    Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S) := fun g i => by
  by_cases hg : P.big g = true
  · exact x ⟨g, hg⟩ ((S ⟨g, hg⟩).equivFin.symm (Fin.cast (by simp [selectedCounts, hg]) i))
  · have hi := i.isLt
    simp [selectedCounts, hg] at hi

def tupleRowPartial (S : P.BigGroup → Finset (Fin J))
    (x : Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S)) : BigRowPartial S :=
  fun g i => x g.val (Fin.cast (by simp [selectedCounts, g.property]) ((S g).equivFin i))

def rowPartialTupleEquiv (S : P.BigGroup → Finset (Fin J)) :
    BigRowPartial S ≃ Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S) where
  toFun := rowPartialTuple S
  invFun := tupleRowPartial S
  left_inv x := by
    funext g i
    simp [rowPartialTuple, tupleRowPartial, g.property]
  right_inv x := by
    funext g i
    by_cases hg : P.big g = true
    · simp [rowPartialTuple, tupleRowPartial, hg]
    · have hi := i.isLt
      simp [selectedCounts, hg] at hi

def selectedRowIndex (S : P.BigGroup → Finset (Fin J)) (g : P.BigGroup) :
    Fin (selectedCounts S g.val) ≃ {i // i ∈ S g} :=
  (finCongr (by simp [selectedCounts, g.property])).trans (S g).equivFin.symm

local instance selectedSiteDecidableEq : DecidableEq (BigSite P J) := Classical.decEq _

def flatPartialRows (S : P.BigGroup → Finset (Fin J)) :
    PartialSample (bigFlatSet P J S) (BigAlphabet P J) ≃ BigRowPartial S where
  toFun x g i := x ⟨(g, i.val), by simp [bigFlatSet, i.property]⟩
  invFun x z := x z.val.1 ⟨z.val.2, by simpa [bigFlatSet] using z.property⟩
  left_inv x := by funext z; rfl
  right_inv x := by funext g i; rfl

def flatSelectedSiteEquiv (S : P.BigGroup → Finset (Fin J)) :
    {z // z ∈ bigFlatSet P J S} ≃ (Σ g : P.BigGroup, {i // i ∈ S g}) where
  toFun z := ⟨z.val.1, ⟨z.val.2, by simpa [bigFlatSet] using z.property⟩⟩
  invFun z := ⟨(z.1, z.2.val), by simp [bigFlatSet, z.2.property]⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma partialProductWeight_rows (S : P.BigGroup → Finset (Fin J))
    (x : PartialSample (bigFlatSet P J S) (BigAlphabet P J)) :
    partialProductWeight (bigFlatWeight P J) (bigFlatSet P J S) x =
      ∏ g : P.BigGroup, ∏ i : {i // i ∈ S g}, P.mu g.val (flatPartialRows S x g i) := by
  unfold partialProductWeight
  calc
    _ = ∏ z : (Σ g : P.BigGroup, {i // i ∈ S g}),
        P.mu z.1.val (flatPartialRows S x z.1 z.2) := by
      apply Fintype.prod_equiv (flatSelectedSiteEquiv S)
      intro z
      rfl
    _ = _ := Fintype.prod_sigma _

lemma rowPartialTuple_product (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) :
    Blueprint.Analytic.product (analyticGroups P) (selectedCounts S) (rowPartialTuple S x) =
      ∏ g : P.BigGroup, ∏ i : {i // i ∈ S g}, (x g i).val := by
  unfold Blueprint.Analytic.product
  change (∏ g : P.Group, ∏ i : Fin (selectedCounts S g), (rowPartialTuple S x g i).val) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun g : P.Group => P.big g = true)]
  have hempty : (∏ g : {g : P.Group // ¬P.big g = true},
      ∏ i : Fin (selectedCounts S g.val), (rowPartialTuple S x g.val i).val) = 1 := by
    apply Finset.prod_eq_one
    intro g _
    have hk : selectedCounts S g.val = 0 := by simp [selectedCounts, g.property]
    haveI : IsEmpty (Fin (selectedCounts S g.val)) := ⟨fun i => by have hi := i.isLt; omega⟩
    exact Fintype.prod_empty _
  rw [hempty, mul_one]
  apply Finset.prod_congr rfl
  intro g _
  apply Fintype.prod_equiv (selectedRowIndex S g)
  intro i
  simp [rowPartialTuple, selectedRowIndex, g.property]

lemma rowPartialTuple_weight (S : P.BigGroup → Finset (Fin J)) (x : BigRowPartial S) :
    Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts S) (rowPartialTuple S x) =
      ∏ g : P.BigGroup, ∏ i : {i // i ∈ S g}, P.mu g.val (x g i) := by
  unfold Blueprint.Analytic.tupleWeight
  change (∏ g : P.Group, ∏ i : Fin (selectedCounts S g),
    Blueprint.Analytic.mu (analyticGroups P) g (rowPartialTuple S x g i).val) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun g : P.Group => P.big g = true)]
  have hempty : (∏ g : {g : P.Group // ¬P.big g = true},
      ∏ i : Fin (selectedCounts S g.val),
        Blueprint.Analytic.mu (analyticGroups P) g.val (rowPartialTuple S x g.val i).val) = 1 := by
    apply Finset.prod_eq_one
    intro g _
    have hk : selectedCounts S g.val = 0 := by simp [selectedCounts, g.property]
    haveI : IsEmpty (Fin (selectedCounts S g.val)) := ⟨fun i => by have hi := i.isLt; omega⟩
    exact Fintype.prod_empty _
  rw [hempty, mul_one]
  apply Finset.prod_congr rfl
  intro g _
  apply Fintype.prod_equiv (selectedRowIndex S g)
  intro i
  simp [rowPartialTuple, selectedRowIndex, g.property, Blueprint.Analytic.mu, PrimeGroups.mu, one_div]

lemma partial_expectation_real {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι) (H : PartialSample S α → ℝ) :
    (∑ y : ProductSample α, productWeight w y * H (fun i => y i.val)) =
      ∑ a : PartialSample S α, partialProductWeight w S a * H a := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) α
  let R : PartialSample S α × (∀ i : {i // i ∉ S}, α i.val) → ℝ := fun z =>
    partialProductWeight w S z.1 * H z.1 *
      productWeight (fun i : {i // i ∉ S} => w i.val) z.2
  have he : (∑ y : ProductSample α, productWeight w y * H (fun i => y i.val)) = ∑ z, R z := by
    apply Fintype.sum_equiv e
    intro y
    dsimp [e, R, Equiv.piEquivPiSubtypeProd]
    rw [productWeight_split w S y]
    ring
  have ht : (∑ b : ∀ i : {i // i ∉ S}, α i.val,
      productWeight (fun i : {i // i ∉ S} => w i.val) b) = 1 := by
    convert productWeight_total (fun i : {i // i ∉ S} => w i.val)
      (fun i => hsum i.val) using 1 <;> congr! 2
  rw [he, Fintype.sum_prod_type R]
  apply Finset.sum_congr rfl
  intro a _
  dsimp [R]
  rw [← Finset.mul_sum, ht, mul_one]

lemma partial_expectation_complex {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι) (H : PartialSample S α → ℂ) :
    (∑ y : ProductSample α, (productWeight w y : ℂ) * H (fun i => y i.val)) =
      ∑ a : PartialSample S α, (partialProductWeight w S a : ℂ) * H a := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) α
  let R : PartialSample S α × (∀ i : {i // i ∉ S}, α i.val) → ℂ := fun z =>
    (partialProductWeight w S z.1 : ℂ) * H z.1 *
      (productWeight (fun i : {i // i ∉ S} => w i.val) z.2 : ℂ)
  have he : (∑ y : ProductSample α, (productWeight w y : ℂ) * H (fun i => y i.val)) = ∑ z, R z := by
    apply Fintype.sum_equiv e
    intro y
    dsimp [e, R, Equiv.piEquivPiSubtypeProd]
    rw [productWeight_split w S y, Complex.ofReal_mul]
    ring
  have ht : (∑ b : ∀ i : {i // i ∉ S}, α i.val,
      (productWeight (fun i : {i // i ∉ S} => w i.val) b : ℂ)) = 1 := by
    have ht' : (∑ b : ∀ i : {i // i ∉ S}, α i.val,
        productWeight (fun i : {i // i ∉ S} => w i.val) b) = 1 := by
      convert productWeight_total (fun i : {i // i ∉ S} => w i.val)
        (fun i => hsum i.val) using 1 <;> congr! 2
    exact_mod_cast ht'
  rw [he, Fintype.sum_prod_type R]
  apply Finset.sum_congr rfl
  intro a _
  dsimp [R]
  rw [← Finset.mul_sum, ht, mul_one]

def patternAuxCoordinates {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (g : P.BigGroup) : Finset (Fin J) :=
  if block g = side then ν.changed g.val else ∅

lemma selectedProduct_rows {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (u : P.BigAux J) :
    selectedProduct ν block side u =
      ∏ g : P.BigGroup, ∏ i : {i // i ∈ patternAuxCoordinates ν block side g}, (u g i.val).val := by
  unfold selectedProduct
  apply Finset.prod_congr rfl
  intro g _
  rw [Finset.prod_coe_sort (patternAuxCoordinates ν block side g) (fun i => (u g i).val)]
  by_cases hg : block g = side
  · simp only [hg, true_and, patternAuxCoordinates, ite_true]
    exact (Finset.prod_filter (p := fun i => i ∈ ν.changed g.val)
      (f := fun i => (u g i).val)).symm.trans (by simp)
  · simp [patternAuxCoordinates, hg]

def selectedAuxTuple {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (u : P.BigAux J) :
    Blueprint.Analytic.Tuple (analyticGroups P)
      (selectedCounts (patternAuxCoordinates ν block side)) :=
  rowPartialTuple (patternAuxCoordinates ν block side) (fun g i => u g i.val)

def selectedLabelTuple {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (a : P.BigLabels (J + ell)) :
    Blueprint.Analytic.Tuple (analyticGroups P)
      (selectedCounts (patternAuxCoordinates ν block side)) :=
  rowPartialTuple (patternAuxCoordinates ν block side) (fun g i => a g (ν.slot i.val))

lemma selectedAuxTuple_product {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (u : P.BigAux J) :
    Blueprint.Analytic.product (analyticGroups P)
      (selectedCounts (patternAuxCoordinates ν block side)) (selectedAuxTuple ν block side u) =
        selectedProduct ν block side u := by
  rw [selectedProduct_rows]
  exact rowPartialTuple_product _ _

lemma selectedLabelTuple_product {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (a : P.BigLabels (J + ell)) :
    Blueprint.Analytic.product (analyticGroups P)
      (selectedCounts (patternAuxCoordinates ν block side)) (selectedLabelTuple ν block side a) =
        selectedEndpoint ν block side a := by
  change Blueprint.Analytic.product (analyticGroups P)
      (selectedCounts (patternAuxCoordinates ν block side))
      (selectedAuxTuple ν block side (fun g i => a g (ν.slot i))) = _
  exact selectedAuxTuple_product ν block side _

lemma selectedCellMass_eq {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (hV : ∀ g, 0 < P.V g) (h : ℝ) (j : ℤ) :
    selectedCellMass ν block side h j =
      Blueprint.Analytic.cellMass (analyticGroups P)
        (selectedCounts (patternAuxCoordinates ν block side)) h j := by
  let S := patternAuxCoordinates ν block side
  let H : PartialSample (bigFlatSet P J S) (BigAlphabet P J) → ℝ := fun x =>
    if Blueprint.Analytic.cell h (∏ g : P.BigGroup,
      ∏ i : {i // i ∈ S g}, (flatPartialRows S x g i).val) = j then 1 else 0
  have hnorm := partial_expectation_real (bigFlatWeight P J)
    (fun z => graph_mu_sum P z.1.val (hV z.1.val)) (bigFlatSet P J S) H
  have hleft : selectedCellMass ν block side h j =
      ∑ y : ProductSample (BigAlphabet P J),
        productWeight (bigFlatWeight P J) y * H (fun i => y i.val) := by
    unfold selectedCellMass
    apply Fintype.sum_equiv (flattenBig P J)
    intro u
    rw [bigFlatWeight_eq, selectedProduct_rows]
    change (if Blueprint.Analytic.cell h
        (∏ g : P.BigGroup, ∏ i : {i // i ∈ S g}, (u g i.val).val) = j
        then P.idealMass u else 0) =
      P.idealMass u * (if Blueprint.Analytic.cell h
        (∏ g : P.BigGroup, ∏ i : {i // i ∈ S g}, (u g i.val).val) = j then 1 else 0)
    split_ifs <;> simp
  rw [hleft, hnorm]
  unfold Blueprint.Analytic.cellMass
  letI : Fintype (Blueprint.Analytic.Tuple (analyticGroups P) (selectedCounts S)) :=
    inferInstanceAs (Fintype (∀ g : P.Group, Fin (selectedCounts S g) → P.Prime g))
  apply Fintype.sum_equiv ((flatPartialRows S).trans (rowPartialTupleEquiv S))
  intro x
  change partialProductWeight (bigFlatWeight P J) (bigFlatSet P J S) x * H x =
    if Blueprint.Analytic.cell h
      (Blueprint.Analytic.product (analyticGroups P) (selectedCounts S)
        (rowPartialTuple S (flatPartialRows S x))) = j then
      Blueprint.Analytic.tupleWeight (analyticGroups P) (selectedCounts S)
        (rowPartialTuple S (flatPartialRows S x)) else 0
  rw [partialProductWeight_rows, rowPartialTuple_product, rowPartialTuple_weight]
  dsimp only [H]
  split_ifs <;> simp

lemma selectedKernel_eq {ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (hV : ∀ g, 0 < P.V g)
    (Q : ℕ) (h ξ : ℝ) (D X : ℕ) :
    selectedKernel ν block side Q h ξ D X =
      Blueprint.Analytic.cellKernel (analyticGroups P)
        (selectedCounts (patternAuxCoordinates ν block side)) Q h ξ D X := by
  unfold selectedKernel Blueprint.Analytic.cellKernel
  rw [selectedCellMass_eq ν block side hV]

end
end Erdos821.P4Probe
