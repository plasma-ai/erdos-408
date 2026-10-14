import Erdos821.S2.RestorationTask
import Erdos821.S2.TailAbsorptionTask

/-! The final tail integration preserves the transference parameter order. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def UniformTruncatedMemoryEstimate (F : FixedData) (r : MemoryParameters F) : Prop :=
  ∀ E : ℝ, 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ C₂ : ℝ, ∃ x₀ : ℝ,
      ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
      0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      (∀ theta : ℝ, NormBound P.idealMass (A.idealKernel theta) ((L x) ^ (-Eid))) →
      ∀ theta : ℝ,
        ‖truncatedDistinctMemoryExpression A (N x) (memoryCutoff x) r.rho theta‖ ≤
          (L x) ^ (-E * (N x : ℝ))

def UniformFullMemoryEstimate (F : FixedData) (r : MemoryParameters F) : Prop :=
  ∀ E : ℝ, 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ C₂ : ℝ, ∃ x₀ : ℝ,
      ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
      0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      (∀ theta : ℝ, NormBound P.idealMass (A.idealKernel theta) ((L x) ^ (-Eid))) →
      ∀ theta : ℝ,
        ‖distinctMemoryExpression A (N x) r.rho theta‖ ≤ (L x) ^ (-E * (N x : ℝ))

def FullMemoryNormTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  GhostAnalyticParametersTask F r → EmptyBoundaryMassTask → MemoryEdgeAbsoluteTask F r →
    UniformTruncatedMemoryEstimate F r → TailAbsorptionTask → UniformFullMemoryEstimate F r


end Erdos821.S2Core
