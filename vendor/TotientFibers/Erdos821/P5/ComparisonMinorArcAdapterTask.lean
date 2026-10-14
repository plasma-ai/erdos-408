import Erdos821.P5.ComparisonScaleAsymptotics
import Erdos821.P5.MinorArcTask

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The actual free-draw multiplier on one occupied comparison cell.
The two tests depend only on their respective products. -/
def comparisonMultiplier {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (fA fB : ℕ → ℂ) (k : ℤ) (θ : ℝ) : ℂ :=
  ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j,
    (freeDrawLaw ν u : ℂ) *
      fA (comparisonFreeProduct ν block false u) *
      fB (comparisonFreeProduct ν block true u) *
      e (-(k : ℝ) * θ * comparisonFreeProduct ν block false u *
        comparisonFreeProduct ν block true u)

/-- Adapter from actual free labels to the accepted minor-arc estimate.
Split the free coordinates by block and reindex each side as its selected
tuple. Its slot counts are at most m and vanish on small groups. Use the
proved product-atom and collapse estimates to get square sums L^C/U and
L^C/V, including the two cell indicators and bounded tests. The cell
scales lie in [U,2U] and [V,2V], exceed exp(L^(c/2)), and UV<=x^2.
Apply MinorArcTask after increasing its C to pay the fixed atom exponent.
No endpoint, discrepancy, mark normalization or pattern-count bound enters.
Export precisely this proposition; report a defect rather than changing it. -/
def ComparisonMinorArcAdapterTask : Prop :=
  MinorArcTask →
  ∀ (P : Geometry) (m : ℕ) (C A hexp : ℝ),
    0 < C → 0 < A → 0 < hexp →
    ∃ Carc K : ℝ, 0 < Carc ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J ell : ℕ) (ν : Pattern G.graph J ell m)
          (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ)
          (fA fB : ℕ → ℂ) (k : ℤ) (θ : ℝ),
          Admissible P x G →
          (∀ side : Bool, ∃ g : G.graph.BigGroup,
            block g = side ∧ (ν.changed g.val).Nonempty) →
          j ∈ comparisonCells ν block (L x ^ (-hexp)) →
          (∀ n, ‖fA n‖ ≤ 1 ∧ ‖fB n‖ ≤ 1) →
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
          (∀ (r : ℕ) (u : ℤ), 1 ≤ r → (r : ℝ) ≤ L x ^ Carc →
            L x ^ Carc / comparisonJointScale (L x ^ (-hexp)) j <
              |θ - (u : ℝ) / r|) →
          ‖comparisonMultiplier ν block (L x ^ (-hexp)) j fA fB k θ‖ ≤
            K * L x ^ (-A)

end Erdos821.P5Core
