import Erdos821.P5.ResidualCoefficient
import Erdos821.P4Char.Basic

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The free product in one comparison block, with no shared coordinates. -/
def comparisonFreeProduct {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (u : FreeDraw ν) : ℕ :=
  ∏ g : G.BigGroup, ∏ i : Fin J,
    if hi : block g = side ∧ i ∈ ν.changed g.val then
      (u ⟨g.val, ⟨i, hi.2⟩⟩).val else 1

/-- Only the specified big unshared marks occur in this endpoint product. -/
def comparisonMarkProduct {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (r : UnsharedDraw ν) : ℕ :=
  ∏ g : G.BigGroup, ∏ i : Fin J,
    if hi : block g = side ∧ i ∈ ν.changed g.val then
      (r g.val ⟨ν.slot i, changed_slot_unshared ν g.val i hi.2⟩).val else 1

theorem selectedProduct_assembleAux {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (u : FreeDraw ν) (z : SharedDraw ν) :
    selectedProduct ν block side (fun g => assembleAux ν u z g.val) =
      comparisonFreeProduct ν block side u := by
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hc : block g = side ∧ i ∈ ν.changed g.val
  · rw [ite_eq_left hc, dite_eq_left hc]
    exact congrArg Subtype.val (assembleAux_free ν u z g.val ⟨i, hc.2⟩)
  · rw [ite_eq_right hc, dite_eq_right hc]

theorem selectedEndpoint_assembleLabels {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (r : UnsharedDraw ν) (z : SharedDraw ν) :
    selectedEndpoint ν block side (G.restrictBig (assembleLabels ν z r)) =
      comparisonMarkProduct ν block side r := by
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hc : block g = side ∧ i ∈ ν.changed g.val
  · rw [ite_eq_left hc, dite_eq_left hc]
    change (assembleLabels ν z r g.val (ν.slot i)).val = _
    exact congrArg Subtype.val
      (assembleLabels_unshared ν z r g.val
        ⟨ν.slot i, changed_slot_unshared ν g.val i hc.2⟩)
  · rw [ite_eq_right hc, dite_eq_right hc]

theorem comparisonMarkProduct_big_ext {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (r s : UnsharedDraw ν) (hrs : ∀ g : G.BigGroup, r g.val = s g.val) :
    comparisonMarkProduct ν block side r = comparisonMarkProduct ν block side s := by
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp only [hrs g]

theorem freeProduct_eq_selectedProducts {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (u : G.Aux J) :
    freeProduct ν u = selectedProduct ν block false (fun g => u g.val) *
      selectedProduct ν block true (fun g => u g.val) := by
  let f : G.Group → ℕ := fun g =>
    ∏ i : Fin J, if i ∈ ν.changed g then (u g i).val else 1
  have hall : freeProduct ν u = ∏ g, f g := by
    unfold freeProduct f
    apply Finset.prod_congr rfl
    intro g hg
    rw [← Finset.prod_filter]
    simp
  have hbig : (∏ g, f g) = ∏ g : G.BigGroup, f g.val := by
    calc
      _ = ∏ g ∈ G.bigGroups, f g := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro g hg hgb
        have hfalse : G.big g = false := by
          simpa [Blueprint.Graph.PrimeGroups.bigGroups] using hgb
        simp [f, ν.small g hfalse]
      _ = _ := Finset.prod_subtype G.bigGroups
        (fun g => by simp [Blueprint.Graph.PrimeGroups.bigGroups]) f
  rw [hall, hbig]
  unfold selectedProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g hg
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only [f]
  cases block g <;> by_cases hc : i ∈ ν.changed g.val <;> simp [hc]

/-- The actual stripped displacement is the product of the two blocks. -/
theorem freeDrawProduct_eq_comparisonProducts {G : Blueprint.Graph.PrimeGroups}
    {J ell m : ℕ} (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (u : FreeDraw ν) (z : SharedDraw ν) :
    freeDrawProduct ν u = comparisonFreeProduct ν block false u *
      comparisonFreeProduct ν block true u := by
  rw [← freeProduct_assembleAux ν u z, freeProduct_eq_selectedProducts,
    selectedProduct_assembleAux, selectedProduct_assembleAux]

def comparisonCellCharacter {Q : ℕ} (h : ℝ) (j : ℤ)
    (χ : CharacterIndex Q) (n : ℕ) : ℂ :=
  if cell h n = j then charValue χ n else 0

theorem comparisonCellCharacter_norm_le {Q : ℕ} (h : ℝ) (j : ℤ)
    (χ : CharacterIndex Q) (n : ℕ) : ‖comparisonCellCharacter h j χ n‖ ≤ 1 := by
  unfold comparisonCellCharacter
  split_ifs
  · exact P4Char.norm_part Q χ n
  · simp

/-- Retained-cell normalization. It is zero on discarded cells. -/
def comparisonCellInverse {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (h ξ : ℝ) (j : ℤ) : ℂ :=
  if ξ ≤ selectedCellMass ν block side h j then
    (selectedCellMass ν block side h j : ℂ)⁻¹ else 0

theorem comparisonCellInverse_norm_le {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (h ξ : ℝ) (j : ℤ) (hξ : 0 < ξ) :
    ‖comparisonCellInverse ν block side h ξ j‖ ≤ ξ⁻¹ := by
  unfold comparisonCellInverse
  split_ifs with hv
  · have hpos : 0 < selectedCellMass ν block side h j := hξ.trans_le hv
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    exact inv_le_inv₀ hpos hξ |>.mpr hv
  · simp only [norm_zero]
    positivity

/-- Fixing the free cell separates the kernel into a free character value
and an endpoint mark function. This includes zero-mass and discarded cells. -/
theorem selectedKernel_cell_expansion {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (Q : ℕ) (h ξ : ℝ) (j : ℤ) (D X : ℕ) (hD : cell h D = j) :
    selectedKernel ν block side Q h ξ D X =
      comparisonCellInverse ν block side h ξ j *
        ∑ χ ∈ primitiveCharacters Q,
          star (charValue χ D) * comparisonCellCharacter h j χ X := by
  by_cases hX : cell h X = j
  · simp only [selectedKernel, hD, hX, comparisonCellInverse,
      comparisonCellCharacter, ite_true, true_and]
    split_ifs <;> simp
  · have hDX : ¬cell h D = cell h X := by simpa only [hD, eq_comm] using hX
    simp [selectedKernel, hDX, comparisonCellCharacter, hX]

end Erdos821.P5Core
