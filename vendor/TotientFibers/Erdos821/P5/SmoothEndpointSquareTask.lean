import Erdos821.P5.ComparisonSmoothEndpoints

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The actual smooth comparison endpoints have fixed-power square norms,
uniformly in the lift depth, characters and Mellin frequencies. Use
eventual_comparisonMarkedEndpoint_bound for both marks; their tests have
norm<=1 even when Q is large. The target size cutoff has norm<=1; the
source cutoff forces n/Y>=lo/2, so its harmonic factor Y/n<=2/lo.
Use endpoint_norm_sq_le and groupFreePart_divisors_card_le with D=1,
then sum a fourth divisor moment up to a fixed multiple of Y. On the
stated Y range, log(const*Y)<=O(log x); all constants are absorbed into
K and a fixed nonnegative exponent before J. No other unfinished task
is an input. Empty root intervals are included. Export this type exactly. -/
def SmoothEndpointSquareTask : Prop :=
  ∀ (P : Geometry) (m : ℕ) (C τ η lo hi : ℝ),
    0 < C → 0 < lo → lo < hi →
    ∃ C₂ K : ℝ, 0 ≤ C₂ ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J Q : ℕ) (ν : Pattern G.graph J P.ell m)
          (block : G.graph.BigGroup → Bool) (h : ℝ) (j : ℤ)
          (χ : CharacterIndex Q) (E : Endpoint) (Y a v : ℝ)
          (hlo : 0 < lo) (hhi : lo < hi),
          Admissible P x G → EndpointBound x C τ η E →
          x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) →
          sqNorm (comparisonCommonRoots lo hi Y)
              (comparisonSmoothSource G x Y a v lo hi hlo hhi E
                (comparisonMarkedEndpoint ν block true h j χ)) ≤ K * Y * L x ^ C₂ ∧
          sqNorm (Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊)
              (comparisonSmoothTarget G x Y a lo hi hlo hhi E
                (comparisonMarkedEndpoint ν block false h j χ)) ≤ K * Y * L x ^ C₂

end Erdos821.P5Core
