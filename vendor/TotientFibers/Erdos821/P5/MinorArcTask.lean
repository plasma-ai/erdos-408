import Erdos821.Blueprint.Analytic

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The minor-arc multiplier estimate after the two free products have
been collapsed to integer weights. The input is only the proved integer
bilinear theorem, not a placeholder value. Use Dirichlet approximation
to k*theta with Q=floor(U*V/L^C'). A denominator <=L^C' contradicts the
arc exclusion after division by k. Otherwise L^C'<r<=U*V/L^C'; the
normalized bilinear square is bounded by a fixed multiple of
L^(2C)*(1/V+1/r+r*log(2r)/(U*V)+log(2r)/U). Superlogarithmic U,V absorb
the first and last terms, and C' gives any saving in the other terms.
The upper product bound controls log(2r) by O(log x). -/
def MinorArcTask : Prop :=
  (Erdos821.Blueprint.Analytic.integer_bilinear_statement) →
  ∀ (C δ A : ℝ), 0 < C → 0 < δ → 0 < A →
    ∃ Carc K : ℝ, 0 < Carc ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (U V θ : ℝ) (k : ℤ) (s t : Finset ℤ) (a b : ℤ → ℂ),
          Real.exp (L x ^ δ) ≤ U → Real.exp (L x ^ δ) ≤ V → U * V ≤ x ^ (2 : ℕ) →
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
          (∀ n ∈ s, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U) →
          (∀ n ∈ t, V ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * V) →
          (∑ n ∈ s, ‖a n‖ ^ 2) ≤ L x ^ C / U →
          (∑ n ∈ t, ‖b n‖ ^ 2) ≤ L x ^ C / V →
          (∀ (r : ℕ) (u : ℤ), 1 ≤ r → (r : ℝ) ≤ L x ^ Carc →
            L x ^ Carc / (U * V) < |θ - (u : ℝ) / r|) →
          ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * e (-(k : ℝ) * θ * n * v)‖ ≤ K * L x ^ (-A)

end Erdos821.P5Core
