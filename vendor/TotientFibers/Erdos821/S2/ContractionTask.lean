import Erdos821.S2.EdgeTasks
import Erdos821.S2.CountableSchur

/-! Quantifier-preserving parameter choice for whole truncated edge contraction. -/

noncomputable section
namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def WholeEdgeContractionTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  MemoryRareTask F r → MemoryCleanTask F r →
  ∀ G : ℝ, 0 < G → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ C₂ : ℝ, ∃ x₀ : ℝ,
      ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
      0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      (∀ theta : ℝ, NormBound P.idealMass (A.idealKernel theta) ((L x) ^ (-Eid))) →
      ∀ (theta : ℝ) (i : Fin (N x)),
        NormBound (P.memoryMass F J (N x))
          (projectKernel (fun s => P.memorySize s ≤ memoryCutoff x)
            (memoryEdgeKernel A (N x) r.rho theta i .all (fun _ _ _ => 1)))
          ((L x) ^ (-G))


end Erdos821.S2Core
