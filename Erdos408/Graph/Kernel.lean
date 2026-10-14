module

public import Erdos408.Graph.Pattern
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The comparison kernels as cell-character sums

Upstream's comparison patterns (`Family.Residual`) have coefficient
`±K_false(D_A, X_A) K_true(D_B, X_B)`, where `A`, `B` are the changed slots of
the big groups in the two blocks, `D_A, D_B` the products of the auxiliary
labels there, `X_A` the product of the target labels in `A` and `X_B` of the
source labels in `B`. Each `selectedKernel` is
`K(D, X) = ∑_{j good, χ} [cell D = j] χ̄(D) · v_j⁻¹ [cell X = j] χ(X)`
(`selectedKernel_eq_sum`), where the good cells are those of mass
`v_j ≥ ξ`. There are at most `ξ⁻¹` of them (`card_goodCells_le`), at most
`Q²` characters (`card_primitiveCharacters_le`), and a cell of log-width
`h ≤ 1` lies in `[U, eU]` (`mem_cell`).
-/

@[expose] public section

namespace Erdos408.Graph

open Erdos821.Blueprint.Graph
open Erdos821.Blueprint.Analytic (cell charValue primitiveCharacters CharacterIndex)
open scoped Classical

variable {G : PrimeGroups} {J m : ℕ}

/-! ### The two blocks -/

/-- The block of a group: upstream's block for big groups, `true` otherwise. -/
def side (block : G.BigGroup → Bool) (g : G.Group) : Bool :=
  if hg : G.big g = true then block ⟨g, hg⟩ else true

/-- The changed slots of `ν` in the groups of block `s`. -/
def blockSlots (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool) (g : G.Group) :
    Finset (Fin J) :=
  if side block g = s then ν.changed g else ∅

/-- The products over big groups of block `s` are slot products over
`blockSlots`. -/
lemma prod_block_eq (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool)
    (x : Fin G.count → Fin J → ℕ) :
    ∏ g : G.BigGroup, ∏ i : Fin J, (if block g = s ∧ i ∈ ν.changed g.val then x g i else 1) =
      slotProduct (blockSlots ν block s) x := by
  unfold slotProduct
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun g : G.Group => G.big g = true)]
  have hsmall : ∏ g : {g : G.Group // ¬ G.big g = true}, ∏ i ∈ blockSlots ν block s g.val,
      x g i = 1 := by
    refine Finset.prod_eq_one fun g _ => ?_
    have : ν.changed g.val = ∅ := ν.small g.val (by simpa using g.property)
    simp [blockSlots, this]
  rw [hsmall, mul_one]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hside : side block g.val = block g := by simp [side, g.property]
  by_cases hb : block g = s
  · simp only [blockSlots, hside, hb, true_and, ite_true]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  · simp [blockSlots, hside, hb]

/-- Upstream's selected product of the auxiliary labels is the slot product of
their trimmed values. -/
lemma selectedProduct_eq (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool)
    (u : G.Aux J) :
    selectedProduct ν block s (fun g => u g.val) =
      slotProduct (blockSlots ν block s) (trim ν.changed u) := by
  rw [selectedProduct, ← prod_block_eq]
  refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
  by_cases h : block g = s ∧ i ∈ ν.changed g.val
  · rw [ite_eq_left h, ite_eq_left h, trim, ite_eq_left h.2]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Upstream's selected endpoint is the slot product of the label values. -/
lemma selectedEndpoint_eq (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool)
    (a : G.Labels (J + 1)) :
    selectedEndpoint ν block s (G.restrictBig a) =
      slotProduct (blockSlots ν block s) fun h i => vals a h i.castSucc := by
  rw [selectedEndpoint, ← prod_block_eq]
  rfl

/-- The block slots are disjoint and cover the changed slots. -/
lemma blockSlots_disjoint_union (ν : Pattern G J 1 m) (block : G.BigGroup → Bool)
    (g : G.Group) :
    Disjoint (blockSlots ν block false g) (blockSlots ν block true g) ∧
      blockSlots ν block false g ∪ blockSlots ν block true g = ν.changed g := by
  cases h : side block g <;> simp [blockSlots, h]

/-! ### Good cells -/

/-- The cells of mass at least `ξ` for the selected product of block `s`. -/
noncomputable def goodCells (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool)
    (h ξ : ℝ) : Finset ℤ :=
  (Finset.univ.image fun u : G.BigAux J => cell h (selectedProduct ν block s u)).filter
    fun j => ξ ≤ selectedCellMass ν block s h j

/-- The auxiliary mass of the big groups is a probability. -/
lemma sum_bigAuxMass (ν : Pattern G J 1 m) (hV : ∀ g, G.V g ≠ 0) :
    ∑ u : G.BigAux J, ν.bigAuxMass u = 1 := by
  unfold Pattern.bigAuxMass
  calc _ = ∏ g : G.BigGroup, ∑ y : Fin J → G.Prime g.val, ∏ i, G.mu g.val (y i) := by
        convert (Fintype.prod_sum fun (g : G.BigGroup) (y : Fin J → G.Prime g.val) =>
          ∏ i, G.mu g.val (y i)).symm
    _ = 1 := by
        refine Finset.prod_eq_one fun g _ => ?_
        rw [← Fintype.prod_sum (fun i (y : G.Prime g.val) => G.mu g.val y)]
        refine Finset.prod_eq_one fun i _ => ?_
        have hsum : ∑ y : G.Prime g.val, G.mu g.val y =
            ∑ p ∈ G.primes g.val, (G.V g.val * p)⁻¹ :=
          Finset.sum_coe_sort (G.primes g.val) fun p : ℕ => (G.V g.val * p)⁻¹
        rw [hsum]
        simp_rw [mul_inv]
        rw [← Finset.mul_sum]
        exact inv_mul_cancel₀ (hV g.val)

/-- The selected cell masses are nonnegative. -/
lemma selectedCellMass_nonneg (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool)
    (h : ℝ) (j : ℤ) : 0 ≤ selectedCellMass ν block s h j := by
  refine Finset.sum_nonneg fun u _ => ?_
  split_ifs
  · exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ =>
      inv_nonneg.mpr (mul_nonneg (Finset.sum_nonneg fun p _ => by positivity) (by positivity))
  · exact le_rfl

/-- A cell of positive mass is the cell of some selected product. -/
lemma mem_image_of_selectedCellMass_pos {ν : Pattern G J 1 m} {block : G.BigGroup → Bool}
    {s : Bool} {h : ℝ} {j : ℤ} (hj : 0 < selectedCellMass ν block s h j) :
    j ∈ Finset.univ.image fun u : G.BigAux J => cell h (selectedProduct ν block s u) := by
  by_contra hc
  refine hj.ne' (Finset.sum_eq_zero fun u _ => ite_eq_right fun hu => hc ?_)
  exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩

/-- There are at most `ξ⁻¹` good cells. -/
lemma card_goodCells_le (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool)
    {h ξ : ℝ} (hξ : 0 < ξ) (hV : ∀ g, G.V g ≠ 0) :
    ((goodCells ν block s h ξ).card : ℝ) ≤ ξ⁻¹ := by
  -- the cell masses over the image of the selected product sum to one
  have hsum : ∑ j ∈ Finset.univ.image (fun u : G.BigAux J => cell h (selectedProduct ν block s u)),
      selectedCellMass ν block s h j = 1 := by
    rw [← sum_bigAuxMass ν hV]
    unfold selectedCellMass
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_image_of_mem _ (Finset.mem_univ u))]
  have hle : (goodCells ν block s h ξ).card • ξ ≤ 1 := by
    refine (Finset.card_nsmul_le_sum _ _ _ fun j hj => (Finset.mem_filter.mp hj).2).trans ?_
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => selectedCellMass_nonneg ν block s h j
  rw [nsmul_eq_mul] at hle
  rw [← one_div, le_div_iff₀ hξ]
  exact hle

/-! ### The cell-character expansion -/

/-- The auxiliary factor of a kernel term: `[D > 0, cell D = j] χ̄(D)`. -/
noncomputable def cellTest (h : ℝ) {Q : ℕ} (j : ℤ) (χ : CharacterIndex Q) (n : ℕ) : ℂ :=
  if 0 < n ∧ cell h n = j then star (charValue χ n) else 0

/-- The mark factor of a kernel term: `[cell X = j] χ(X)`. -/
noncomputable def cellMark (h : ℝ) {Q : ℕ} (j : ℤ) (χ : CharacterIndex Q) (n : ℕ) : ℂ :=
  if cell h n = j then charValue χ n else 0

/-- For `D > 0`, the selected kernel is the sum over good cells `j` and
characters `χ` of `v_j⁻¹ [cell D = j] χ̄(D) [cell X = j] χ(X)`. -/
lemma selectedKernel_eq_sum (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (s : Bool)
    (Q : ℕ) {h ξ : ℝ} (hξ : 0 < ξ) {D : ℕ} (hD : 0 < D) (X : ℕ) :
    selectedKernel ν block s Q h ξ D X =
      ∑ j ∈ goodCells ν block s h ξ, ∑ χ ∈ primitiveCharacters Q,
        ((selectedCellMass ν block s h j)⁻¹ : ℂ) * (cellTest h j χ D * cellMark h j χ X) := by
  unfold selectedKernel
  dsimp only
  by_cases hc : cell h D = cell h X ∧ ξ ≤ selectedCellMass ν block s h (cell h X)
  · rw [ite_eq_left hc]
    have hmem : cell h X ∈ goodCells ν block s h ξ := Finset.mem_filter.mpr
      ⟨mem_image_of_selectedCellMass_pos (hξ.trans_le hc.2), hc.2⟩
    rw [Finset.sum_eq_single_of_mem _ hmem fun j _ hj =>
      Finset.sum_eq_zero fun χ _ => by simp [cellMark, Ne.symm hj], Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp [cellTest, cellMark, hD, hc.1]
  · rw [ite_eq_right hc]
    refine (Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun χ _ => ?_).symm
    unfold cellTest cellMark
    by_cases h₁ : cell h X = j
    · have h₂ : ¬ cell h D = j := fun h₂ =>
        hc ⟨h₂.trans h₁.symm, h₁ ▸ (Finset.mem_filter.mp hj).2⟩
      simp [h₂]
    · simp [h₁]

/-- A cell of log-width `h ≤ 1` lies in `[U, eU]`, `U = e^{jh}`. -/
lemma mem_cell {h : ℝ} (hh₀ : 0 < h) (hh₁ : h ≤ 1) {n : ℕ} (hn : 0 < n) {j : ℤ}
    (hj : cell h n = j) :
    Real.exp (j * h) ≤ n ∧ (n : ℝ) ≤ Real.exp 1 * Real.exp (j * h) := by
  have h₁ := Int.floor_le (Real.log n / h)
  have h₂ := Int.lt_floor_add_one (Real.log n / h)
  rw [show ⌊Real.log n / h⌋ = j from hj] at h₁ h₂
  rw [le_div_iff₀ hh₀] at h₁
  rw [div_lt_iff₀ hh₀] at h₂
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · calc Real.exp (j * h) ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr h₁
      _ = n := Real.exp_log hn'
  · calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn').symm
      _ ≤ Real.exp (1 + j * h) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp 1 * Real.exp (j * h) := Real.exp_add _ _

/-- The auxiliary factor is bounded by one. -/
lemma norm_cellTest_le (h : ℝ) {Q : ℕ} (j : ℤ) (χ : CharacterIndex Q) (n : ℕ) :
    ‖cellTest h j χ n‖ ≤ 1 := by
  unfold cellTest charValue
  split_ifs
  · rw [norm_star]
    exact DirichletCharacter.norm_le_one _ _
  · simp

/-- The mark factor is bounded by one. -/
lemma norm_cellMark_le (h : ℝ) {Q : ℕ} (j : ℤ) (χ : CharacterIndex Q) (n : ℕ) :
    ‖cellMark h j χ n‖ ≤ 1 := by
  unfold cellMark charValue
  split_ifs
  · exact DirichletCharacter.norm_le_one _ _
  · simp

/-- There are at most `Q²` primitive characters of modulus at most `Q`. -/
lemma card_primitiveCharacters_le (Q : ℕ) : (primitiveCharacters Q).card ≤ Q ^ 2 := by
  calc (primitiveCharacters Q).card ≤ Fintype.card (CharacterIndex Q) :=
        (Finset.card_filter_le _ _).trans_eq Finset.card_univ
    _ = ∑ r : Fin Q, Fintype.card (DirichletCharacter ℂ (r.val + 1)) := Fintype.card_sigma
    _ ≤ ∑ _r : Fin Q, Q := Finset.sum_le_sum fun r _ => by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
        exact (Nat.totient_le _).trans r.isLt
    _ = Q ^ 2 := by simp [sq]

/-! ### Each term costs at most the pattern's supremum -/

/-- On the diagonal `D = X` in a good cell, the selected kernel has norm at
least `v_j⁻¹`: the character of modulus `1` contributes `1`. -/
lemma inv_le_norm_selectedKernel (ν : Pattern G J 1 m) (block : G.BigGroup → Bool)
    (s : Bool) {Q : ℕ} (hQ : 0 < Q) {h ξ : ℝ} {j : ℤ} (hj : j ∈ goodCells ν block s h ξ)
    {D : ℕ} (hD : cell h D = j) :
    (selectedCellMass ν block s h j)⁻¹ ≤ ‖selectedKernel ν block s Q h ξ D D‖ := by
  unfold selectedKernel
  dsimp only
  rw [hD, ite_eq_left ⟨rfl, (Finset.mem_filter.mp hj).2⟩]
  have hsum : ∑ χ ∈ primitiveCharacters Q, star (charValue χ D) * charValue χ D =
      ((∑ χ ∈ primitiveCharacters Q, ‖charValue χ D‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  -- the character of modulus `1`
  let χ₁ : CharacterIndex Q := ⟨⟨0, hQ⟩, 1⟩
  have hχ₁ : χ₁ ∈ primitiveCharacters Q :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, DirichletCharacter.isPrimitive_one_level_one⟩
  have hone : ‖charValue χ₁ D‖ = 1 := by
    simp [χ₁, charValue, MulChar.one_apply (isUnit_of_subsingleton _)]
  have hv := selectedCellMass_nonneg ν block s h j
  rw [hsum, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hv,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
  refine le_mul_of_one_le_right (inv_nonneg.mpr hv) ?_
  calc (1 : ℝ) = ‖charValue χ₁ D‖ ^ 2 := by rw [hone, one_pow]
    _ ≤ _ := Finset.single_le_sum (f := fun χ => ‖charValue χ D‖ ^ 2)
        (fun _ _ => by positivity) hχ₁

/-- For a comparison pattern of upstream's residual form, each pair of good
cells has `v_j⁻¹ v_{j'}⁻¹` at most the supremum of the coefficient. -/
lemma inv_mul_inv_le_sSup (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) {Q : ℕ}
    (hQ : 0 < Q) {h ξ : ℝ} (hJ : 0 < J)
    (hcoef : ∀ a b u, ν.coefficient a b u =
      -((-1 : ℂ) ^ (∑ g, (ν.changed g).card)) *
        selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
          (selectedEndpoint ν block false b) *
        selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
          (selectedEndpoint ν block true a))
    {j j' : ℤ} (hj : j ∈ goodCells ν block false h ξ) (hj' : j' ∈ goodCells ν block true h ξ) :
    (selectedCellMass ν block false h j)⁻¹ * (selectedCellMass ν block true h j')⁻¹ ≤
      sSup (Set.range fun z : G.BigLabels (J + 1) × G.BigLabels (J + 1) × G.BigAux J =>
        ‖ν.coefficient z.1 z.2.1 z.2.2‖) := by
  obtain ⟨u₁, -, hu₁⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hj).1
  obtain ⟨u₂, -, hu₂⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hj').1
  -- auxiliary labels from `u₁` in block `false` and from `u₂` in block `true`
  let u : G.BigAux J := fun g => if block g = false then u₁ g else u₂ g
  have hp₁ : selectedProduct ν block false u = selectedProduct ν block false u₁ := by
    refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
    by_cases hb : block g = false <;> simp [u, hb]
  have hp₂ : selectedProduct ν block true u = selectedProduct ν block true u₂ := by
    refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
    by_cases hb : block g = false <;> simp [u, hb]
  -- labels repeating `u` in the first `J` slots
  let e : G.BigLabels (J + 1) := fun g k =>
    if hk : k.val < J then u g ⟨k.val, hk⟩ else u g ⟨0, hJ⟩
  have he : ∀ s, selectedEndpoint ν block s e = selectedProduct ν block s u := by
    intro s
    refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
    simp [e, Pattern.slot]
  have hval : ‖ν.coefficient e e u‖ ≥
      (selectedCellMass ν block false h j)⁻¹ * (selectedCellMass ν block true h j')⁻¹ := by
    rw [hcoef, he, he, hp₁, hp₂, norm_mul, norm_mul, norm_neg, norm_pow, norm_neg, norm_one,
      one_pow, one_mul]
    exact mul_le_mul (inv_le_norm_selectedKernel ν block false hQ hj hu₁)
      (inv_le_norm_selectedKernel ν block true hQ hj' hu₂)
      (inv_nonneg.mpr (selectedCellMass_nonneg ν block true h j')) (norm_nonneg _)
  exact hval.trans (le_csSup (Set.finite_range _).bddAbove ⟨(e, e, u), rfl⟩)

end Erdos408.Graph
