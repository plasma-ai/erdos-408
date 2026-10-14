import Erdos821.S2.MemoryEdge

/-! Frozen statements of the three edge estimates in source §2. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

/-- Absolute kernels before any combination of signed local choices.
The exponent is independent of J. This includes both countable summability claims. -/
def MemoryEdgeAbsoluteTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  ∀ (m : ℕ) (C₁ : ℝ), ∃ Ca : ℝ, ∀ J : ℕ, ∃ x₀ : ℝ,
    ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
    ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
    ∀ (theta : ℝ) (i : Fin (N x)),
      WeightedBounds (P.memoryMass F J (N x)) (P.memoryWeight r.v)
        (fun s t => (absoluteMemoryEdgeKernel A (N x) r.rho theta i .all s t : ℂ))
        ((L x) ^ Ca)

/-- The truncation gain from averaging small source omissions in rows and
small target omissions in columns. Local multipliers are allowed before sums. -/
def MemoryRareTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  ∀ (m : ℕ) (C₁ : ℝ), ∃ Ca : ℝ, ∀ J : ℕ, ∀ C₂ : ℝ, ∃ x₀ : ℝ,
    ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
    ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
    0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
    ∀ (theta : ℝ) (i : Fin (N x)),
    ∀ phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ,
    (∀ s t c, ‖phi s t c‖ ≤ 1) →
      NormBound (P.memoryMass F J (N x))
        (projectKernel (fun s => P.memorySize s ≤ memoryCutoff x)
          (memoryEdgeKernel A (N x) r.rho theta i .dirty phi))
        (2 * (L x) ^ Ca * Real.sqrt ((memoryCutoff x : ℝ) / omissionNumber F P J))

/-- Signed clean norm. Cs is chosen before m, C₁, J and Eid.
No arbitrary choice multiplier is admitted here: it could destroy cancellation. -/
def MemoryCleanTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  ∃ Cs : ℝ, ∀ (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ Eid : ℝ), 0 < Eid → ∃ x₀ : ℝ,
    ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
    ∀ A : Model F P J m, A.patternMass ≤ (L x) ^ C₁ →
    0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
    (∀ theta : ℝ, NormBound P.idealMass (A.idealKernel theta) ((L x) ^ (-Eid))) →
    ∀ (theta : ℝ) (i : Fin (N x)),
      NormBound (P.memoryMass F J (N x))
        (projectKernel (fun s => P.memorySize s ≤ memoryCutoff x)
          (memoryEdgeKernel A (N x) r.rho theta i .clean (fun _ _ _ => 1)))
        (2 * (L x) ^ (-Eid + Cs))

end Erdos821.S2Core

