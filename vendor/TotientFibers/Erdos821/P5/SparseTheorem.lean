import Erdos821.P5.SparseResidual
import Erdos821.P5Gram.Bridge

noncomputable section
open scoped BigOperators

namespace Erdos821.Blueprint.Analytic

/-- §4 sparse residual estimate, using the proved full-interval Gram bound. -/
theorem sparse_residual_proof : ∃ K Y₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧
    ∀ (Y U A : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (E : Finset ℤ),
      Y₀ ≤ Y → Y ^ (0.6 : ℝ) ≤ U → U ≤ Y → 0 ≤ A →
      (∀ n ∈ s, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U) →
      sqNorm s c ≤ A / U → (E.card : ℝ) ≤ Y ^ (0.05 : ℝ) →
      (∀ j ∈ E, |(j : ℝ)| ≤ Y) →
      ∑ j ∈ E, ⨆ t : Set.Icc (j : ℝ) ((j : ℝ) + 1), ‖dp s c t‖ ^ 2 ≤
        K * A * Real.log (2 * Y) :=
  P5Core.sparse_residual_of_gram P5Core.sparseGramKernelTask_proof

example : Erdos821.Blueprint.Analytic.sparse_residual_statement := @sparse_residual_proof

end Erdos821.Blueprint.Analytic
