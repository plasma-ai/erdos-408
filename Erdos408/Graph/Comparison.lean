module

public import Erdos408.Graph.Kernel

/-!
# Comparison patterns as sums of product terms

A comparison pattern of upstream's residual family has coefficient
`-(-1)^{Σ|C|} K_false(D_A, X_A) K_true(D_B, X_B)`. Expanding both kernels over
good cells and characters (`selectedKernel_eq_sum`) writes it as a sum over
`terms` of `β φ(D_A) φ'(D_B) ψ(X_A) ψ'(X_B)` (`termKernel`), with
`|β| = v_j⁻¹ v_{j'}⁻¹`. As `patternPairing` is linear in its kernel
(`patternPairing_sum`), the pattern's pairing is the sum of the term pairings
(`rawPairing_comparison`). Each term weight is at most the pattern's
supremum (`inv_mul_inv_le_sSup`), and there are at most `ξ⁻² Q⁴` terms, so the
term weights of a comparison pattern sum to at most `ξ⁻² Q⁴` times its
supremum (`sum_norm_termWeight_le`).
-/

@[expose] public section

namespace Erdos408.Graph

open Erdos821.Blueprint.Graph
open Erdos821.Blueprint.Analytic (cell charValue primitiveCharacters CharacterIndex)
open scoped Classical

variable {G : PrimeGroups} {J m : ℕ}

/-! ### Linearity of `patternPairing` -/

/-- `patternPairing` is additive in its kernel. -/
lemma patternPairing_add {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (q₀ : ℝ) {J : ℕ} (C : ι → Finset (Fin J))
    (K K' : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ) (ζ : ℝ)
    (S : Finset ℕ) (f g : ℕ → ℂ) :
    patternPairing P q₀ C (fun p p' a => K p p' a + K' p p' a) ζ S f g =
      patternPairing P q₀ C K ζ S f g + patternPairing P q₀ C K' ζ S f g := by
  simp only [patternPairing, mul_add, add_mul, Finset.sum_add_distrib]

/-- `patternPairing` vanishes for the zero kernel. -/
lemma patternPairing_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (q₀ : ℝ) {J : ℕ} (C : ι → Finset (Fin J)) (ζ : ℝ) (S : Finset ℕ) (f g : ℕ → ℂ) :
    patternPairing P q₀ C (fun _ _ _ => 0) ζ S f g = 0 := by
  simp [patternPairing]

/-- `patternPairing` is linear in its kernel. -/
lemma patternPairing_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (q₀ : ℝ) {J : ℕ} (C : ι → Finset (Fin J)) {α : Type*} (T : Finset α)
    (K : α → (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ) (ζ : ℝ)
    (S : Finset ℕ) (f g : ℕ → ℂ) :
    patternPairing P q₀ C (fun p p' a => ∑ τ ∈ T, K τ p p' a) ζ S f g =
      ∑ τ ∈ T, patternPairing P q₀ C (K τ) ζ S f g := by
  induction T using Finset.induction_on with
  | empty => simpa using patternPairing_zero P q₀ C ζ S f g
  | insert τ T hτ ih =>
    simp_rw [Finset.sum_insert hτ]
    rw [patternPairing_add, ih]

/-! ### The terms of a comparison pattern -/

/-- The terms of a comparison pattern: a good cell and a character for each
block. -/
noncomputable def terms (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) (Q : ℕ)
    (h ξ : ℝ) : Finset (ℤ × CharacterIndex Q × ℤ × CharacterIndex Q) :=
  goodCells ν block false h ξ ×ˢ primitiveCharacters Q ×ˢ goodCells ν block true h ξ ×ˢ
    primitiveCharacters Q

/-- The weight `β = -(-1)^{Σ|C|} v_j⁻¹ v_{j'}⁻¹` of a term. -/
noncomputable def termWeight (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) {Q : ℕ}
    (h : ℝ) (τ : ℤ × CharacterIndex Q × ℤ × CharacterIndex Q) : ℂ :=
  -((-1 : ℂ) ^ (∑ g, (ν.changed g).card)) *
    (((selectedCellMass ν block false h τ.1)⁻¹ : ℝ) *
      ((selectedCellMass ν block true h τ.2.2.1)⁻¹ : ℝ) : ℂ)

/-- The kernel `β φ(D_A) φ'(D_B) ψ(X_A) ψ'(X_B)` of a term, with `A, B` the
block slots, `D` the auxiliary labels, `X_A` the target and `X_B` the source
labels. -/
noncomputable def termKernel (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) {Q : ℕ}
    (h : ℝ) (τ : ℤ × CharacterIndex Q × ℤ × CharacterIndex Q)
    (p p' : Fin G.count → Fin (J + 1) → ℕ) (a : Fin G.count → Fin J → ℕ) : ℂ :=
  termWeight ν block h τ * cellTest h τ.1 τ.2.1 (slotProduct (blockSlots ν block false) a) *
    cellTest h τ.2.2.1 τ.2.2.2 (slotProduct (blockSlots ν block true) a) *
    cellMark h τ.1 τ.2.1 (slotProduct (blockSlots ν block false) fun g i => p' g i.castSucc) *
    cellMark h τ.2.2.1 τ.2.2.2 (slotProduct (blockSlots ν block true) fun g i => p g i.castSucc)

/-- The slot product of trimmed upstream auxiliary labels is positive. -/
lemma slotProduct_trim_pos (C A : Fin G.count → Finset (Fin J)) (u : G.Aux J) :
    0 < slotProduct A (trim C u) := by
  refine Finset.prod_pos fun g _ => Finset.prod_pos fun i _ => ?_
  unfold trim
  split_ifs
  · exact (G.prime g _ (u g i).property).pos
  · exact one_pos

/-- A product of two double sums is a sum over the four-fold product. -/
private lemma sum_mul_sum_four {α β γ δ : Type*} (s : Finset α) (t : Finset β) (s' : Finset γ)
    (t' : Finset δ) (x : α → β → ℂ) (y : γ → δ → ℂ) :
    (∑ i ∈ s, ∑ k ∈ t, x i k) * (∑ i' ∈ s', ∑ k' ∈ t', y i' k') =
      ∑ τ ∈ s ×ˢ t ×ˢ s' ×ˢ t', x τ.1 τ.2.1 * y τ.2.2.1 τ.2.2.2 := by
  simp_rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

variable {q₀ c₀ C₀ vlo vhi : ℝ} {hq₀ : 0 < q₀} {hq₁ : q₀ < 1} {hc₀ : 0 < c₀} {hvlo : 0 < vlo}

/-- The pairing of a comparison pattern of upstream's residual form is the sum
of its term pairings. -/
theorem rawPairing_comparison (B : Family (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo) G J m)
    (ζ : ℝ) (v : Fin B.count) (block : G.BigGroup → Bool) (Q : ℕ) {h ξ : ℝ} (hξ : 0 < ξ)
    (hcoef : ∀ a b u, (B.pattern v).coefficient a b u =
      -((-1 : ℂ) ^ (∑ g, ((B.pattern v).changed g).card)) *
        selectedKernel (B.pattern v) block false Q h ξ
          (selectedProduct (B.pattern v) block false u)
          (selectedEndpoint (B.pattern v) block false b) *
        selectedKernel (B.pattern v) block true Q h ξ
          (selectedProduct (B.pattern v) block true u)
          (selectedEndpoint (B.pattern v) block true a))
    (hV : ∀ g, G.V g ≠ 0) (S S' : Finset ℕ) (f g : ℕ → ℂ) (hg : ∀ n ∉ S', g n = 0) :
    rawPairing (B.model 1 ζ) v S S' f g =
      ∑ τ ∈ terms (B.pattern v) block Q h ξ,
        patternPairing G.primes q₀ (B.pattern v).changed (termKernel (B.pattern v) block h τ)
          ζ S f g := by
  rw [← patternPairing_sum]
  refine rawPairing_eq B ζ v _ (fun a b u => ?_) hV S S' f g hg
  rw [hcoef, selectedProduct_eq, selectedProduct_eq, selectedEndpoint_eq, selectedEndpoint_eq,
    selectedKernel_eq_sum _ _ _ _ hξ (slotProduct_trim_pos _ _ u),
    selectedKernel_eq_sum _ _ _ _ hξ (slotProduct_trim_pos _ _ u), mul_assoc,
    sum_mul_sum_four, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [termKernel, termWeight]
  push_cast
  ring

/-! ### The term weights -/

/-- The supremum of a pattern's coefficient is nonnegative. -/
lemma sSup_norm_nonneg (ν : Pattern G J 1 m) :
    0 ≤ sSup (Set.range fun z : G.BigLabels (J + 1) × G.BigLabels (J + 1) × G.BigAux J =>
      ‖ν.coefficient z.1 z.2.1 z.2.2‖) :=
  Real.sSup_nonneg fun _ ⟨_, hz⟩ => hz ▸ norm_nonneg _

/-- The term weights of a comparison pattern sum to at most `ξ⁻² Q⁴` times its
supremum. -/
lemma sum_norm_termWeight_le (ν : Pattern G J 1 m) (block : G.BigGroup → Bool) {Q : ℕ}
    {h ξ : ℝ} (hξ : 0 < ξ) (hV : ∀ g, G.V g ≠ 0) (hJ : 0 < J)
    (hcoef : ∀ a b u, ν.coefficient a b u =
      -((-1 : ℂ) ^ (∑ g, (ν.changed g).card)) *
        selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
          (selectedEndpoint ν block false b) *
        selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
          (selectedEndpoint ν block true a)) :
    ∑ τ ∈ terms ν block Q h ξ, ‖termWeight ν block h τ‖ ≤
      ξ⁻¹ ^ 2 * (Q : ℝ) ^ 4 *
        sSup (Set.range fun z : G.BigLabels (J + 1) × G.BigLabels (J + 1) × G.BigAux J =>
          ‖ν.coefficient z.1 z.2.1 z.2.2‖) := by
  -- each term weight is at most the supremum
  have hterm : ∀ τ ∈ terms ν block Q h ξ, ‖termWeight ν block h τ‖ ≤
      sSup (Set.range fun z : G.BigLabels (J + 1) × G.BigLabels (J + 1) × G.BigAux J =>
        ‖ν.coefficient z.1 z.2.1 z.2.2‖) := by
    intro τ hτ
    simp only [terms, Finset.mem_product] at hτ
    have hQ : 0 < Q := Fin.pos τ.2.1.1
    rw [termWeight, norm_mul, norm_neg, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (selectedCellMass_nonneg _ _ _ _ _)),
      Real.norm_of_nonneg (inv_nonneg.mpr (selectedCellMass_nonneg _ _ _ _ _))]
    exact inv_mul_inv_le_sSup ν block hQ hJ hcoef hτ.1 hτ.2.2.1
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (sSup_norm_nonneg ν)
  have hg₁ := card_goodCells_le ν block false (h := h) hξ hV
  have hg₂ := card_goodCells_le ν block true (h := h) hξ hV
  have hχ : ((primitiveCharacters Q).card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast card_primitiveCharacters_le Q
  simp only [terms, Finset.card_product]
  push_cast
  calc ((goodCells ν block false h ξ).card : ℝ) * ((primitiveCharacters Q).card *
        ((goodCells ν block true h ξ).card * (primitiveCharacters Q).card))
      ≤ ξ⁻¹ * ((Q : ℝ) ^ 2 * (ξ⁻¹ * (Q : ℝ) ^ 2)) := by gcongr
    _ = ξ⁻¹ ^ 2 * (Q : ℝ) ^ 4 := by ring

end Erdos408.Graph
