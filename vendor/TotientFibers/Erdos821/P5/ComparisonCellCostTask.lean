import Erdos821.P5.ComparisonRowExpansion
import Erdos821.P5.PatternCosts

noncomputable section

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- §4 comparison normalizations must be paid linearly by the actual
coefficient supremum; Family.Residual supplies no pattern-count bound.

Extend u to a full big endpoint list using a₀ for the final ell slots.
Its selected endpoint products equal its selected auxiliary products.
At this diagonal each character term is the nonnegative real |χ(D)|².
The primitive conductor-one character belongs to the packet when Q≥1,
so each diagonal character sum is at least one. Retained cell masses are
positive since ξ>0. Thus the diagonal coefficient norm dominates the
product of the two cell inverses. If either cell is discarded the desired
left side is zero. Finish with coefficient_norm_le_patternCost.

This is independent of the scale lemmas, P1/P2 inputs and J bounds. -/
def ComparisonCellCostTask : Prop :=
  ∀ (G : Blueprint.Graph.PrimeGroups) (J ell m Q : ℕ)
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (h ξ : ℝ),
    1 ≤ Q → 0 < ξ → HasComparisonCoefficient ν block Q h ξ →
    ∀ (_a₀ : G.BigLabels (J + ell)) (u : G.BigAux J),
      ‖comparisonCellInverse ν block false h ξ (cell h (selectedProduct ν block false u)) *
        comparisonCellInverse ν block true h ξ (cell h (selectedProduct ν block true u))‖ ≤
        patternCost ν

end Erdos821.P5Core
