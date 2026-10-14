import Erdos821.Blueprint.Analytic
import Erdos821.Blueprint.Classical

noncomputable section
open scoped BigOperators
open MeasureTheory Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Logarithmic Fourier inversion of a fixed positive-interval cutoff.
The cutoff frequency is chosen before the requested tail saving. Keeping
Fin 1 coordinates avoids an unnecessary measure-transport interface. -/
def MellinCutoffTask : Prop :=
  Blueprint.FourierSeparation →
  ∀ (C lo hi : ℝ) (bounds : ℕ → ℝ),
    0 < C → 0 < lo → lo < hi → (∀ j, 0 ≤ bounds j) →
    ∃ Cf K : ℝ, 0 < Cf ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧
        ∀ᶠ x : ℝ in atTop, ∀ Ψ : ℝ → ℂ,
          CutoffBound x C lo hi Ψ bounds →
          ∃ a : (Fin 1 → ℝ) → ℂ,
            Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ K ∧
            (∀ y : ℝ, 0 < y →
              Ψ y = ∫ ξ, a ξ * mellin y (2 * Real.pi * ξ 0)) ∧
            (∫ ξ in {ξ : Fin 1 → ℝ | L x ^ Cf < ‖ξ‖}, ‖a ξ‖) ≤
              KA * L x ^ (-A)

end Erdos821.P5Core

