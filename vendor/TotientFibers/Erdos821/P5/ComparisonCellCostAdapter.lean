import Erdos821.P5CellCost.Proof
import Erdos821.P5.ComparisonCellScales

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The accepted diagonal cost theorem applies to the actual occupied cell,
using an assembled free/shared auxiliary draw. -/
theorem comparison_cell_inverse_product_le_patternCost
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (hQ : 1 ≤ Q) (hξ : 0 < ξ) (hc : HasComparisonCoefficient ν block Q h ξ)
    (a₀ : G.BigLabels (J + ell)) (z : SharedDraw ν)
    (j : ℤ × ℤ) (hj : j ∈ comparisonCells ν block h) :
    ‖comparisonCellInverse ν block false h ξ j.1 *
      comparisonCellInverse ν block true h ξ j.2‖ ≤ patternCost ν := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
  have hd := P5Cell.comparisonCellCostTask_proof G J ell m Q ν block h ξ hQ hξ hc a₀
    (fun g => assembleAux ν u z g.val)
  simp_rw [selectedProduct_assembleAux ν block] at hd
  exact hd

theorem comparison_cell_signed_cost_le_patternCost
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (hQ : 1 ≤ Q) (hξ : 0 < ξ) (hc : HasComparisonCoefficient ν block Q h ξ)
    (a₀ : G.BigLabels (J + ell)) (z : SharedDraw ν)
    (j : ℤ × ℤ) (hj : j ∈ comparisonCells ν block h) :
    ‖comparisonSign ν * comparisonCellInverse ν block false h ξ j.1 *
      comparisonCellInverse ν block true h ξ j.2‖ ≤ patternCost ν := by
  rw [mul_assoc, norm_mul, comparisonSign_norm, one_mul]
  exact comparison_cell_inverse_product_le_patternCost ν block Q h ξ hQ hξ hc a₀ z j hj

/-- Cell and character costs sum linearly through the actual pattern cost,
without a bound on the residual family's number of patterns. -/
theorem comparison_cell_character_sum_norm_le
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (hQ : 1 ≤ Q) (hξ : 0 < ξ) (hc : HasComparisonCoefficient ν block Q h ξ)
    (a₀ : G.BigLabels (J + ell)) (z : SharedDraw ν)
    (f : (ℤ × ℤ) → CharacterIndex Q → CharacterIndex Q → ℂ) :
    ‖∑ j ∈ comparisonCells ν block h, ∑ χA ∈ primitiveCharacters Q,
      ∑ χB ∈ primitiveCharacters Q,
        (comparisonSign ν * comparisonCellInverse ν block false h ξ j.1 *
          comparisonCellInverse ν block true h ξ j.2) * f j χA χB‖ ≤
    patternCost ν * ∑ j ∈ comparisonCells ν block h, ∑ χA ∈ primitiveCharacters Q,
      ∑ χB ∈ primitiveCharacters Q, ‖f j χA χB‖ := by
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro χA hχA
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro χB hχB
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (comparison_cell_signed_cost_le_patternCost ν block Q h ξ hQ hξ hc a₀ z j hj) (norm_nonneg _)

end Erdos821.P5Core
