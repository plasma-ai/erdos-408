import Erdos821.S2.RankExpansion
import Erdos821.S2.ContractionTask
import Erdos821.S2.AnalyticParametersTasks

/-! Quantitative assembly of the high/low equality-rank restoration. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def RestoredMemoryNormTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  GhostAnalyticParametersTask F r → EmptyBoundaryMassTask →
  MemoryEdgeAbsoluteTask F r → MemoryRareTask F r → MemoryCleanTask F r →
  WholeEdgeContractionTask F r → LowRankMemoryTask → HighRankMemoryTask F r →
  ∀ E : ℝ, 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ C₂ : ℝ, ∃ x₀ : ℝ,
      ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
      0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      (∀ theta : ℝ, NormBound P.idealMass (A.idealKernel theta) ((L x) ^ (-Eid))) →
      ∀ theta : ℝ,
        ‖truncatedDistinctMemoryExpression A (N x) (memoryCutoff x) r.rho theta‖ ≤
          (L x) ^ (-E * (N x : ℝ))


end Erdos821.S2Core
