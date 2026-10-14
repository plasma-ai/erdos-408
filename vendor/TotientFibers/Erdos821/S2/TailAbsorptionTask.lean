import Erdos821.Blueprint.Graph

/-! The exponential memory-cutoff gain absorbs every fixed path cost. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def TailAbsorptionTask : Prop :=
  ∀ Ccap Cpath E : ℝ, 0 < Ccap → 0 ≤ Cpath → 0 < E →
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ cap : ℕ,
      (cap : ℝ) ≤ Ccap * (N x : ℝ) * T x →
      (2 : ℝ) ^ ((cap : ℤ) - (memoryCutoff x : ℤ)) *
          (L x) ^ (Cpath * (N x + 1 : ℕ)) ≤
        (L x) ^ (-E * (N x : ℝ))


end Erdos821.S2Core
