import Erdos821.S2.MemoryTailTask

/-! Eventual analytic facts needed to instantiate the literal memory estimates. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

def GhostAnalyticParametersTask (F : FixedData) (r : MemoryParameters F) : Prop :=
  ∃ Cv : ℝ, 0 ≤ Cv ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups,
    P.Admissible F x →
    (∀ g, 0 < P.V g ∧ P.V g ≤ F.vMax) ∧
    (∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F (N x) p.val) ∧
    (∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P (N x) g.val p ≤ 2) ∧
    (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card ≤ (L x) ^ Cv

def EmptyBoundaryMassTask : Prop :=
  ∀ (F : FixedData) (J : ℕ), ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups,
    P.Admissible F x → ∀ m : ℕ, ∀ A : Model F P J m,
      initialMemoryBoundaryMass A (N x) ≤ 2

def BigPrimeNondivTask : Prop :=
  ∀ (F : FixedData) (C₂ : ℝ), ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups,
    P.Admissible F x → ∀ k : ℤ, 0 < |k| → (|k| : ℝ) ≤ (L x) ^ C₂ →
      ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ k


end Erdos821.S2Core
