import Erdos821.Blueprint.Adapters

noncomputable section
open Filter
namespace Erdos821.Blueprint
open Analytic

/-- §4 thm:shift, including all sequence restrictions in the discrepancy input. -/
def ShiftEstimate : Prop :=
  ∀ (P : Geometry) (D C τ η lo hi : ℝ) (bounds : ℕ → ℝ),
    0 < D → 0 < C → 0 < lo ∧ lo < hi →
      ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ᶠ x in atTop,
        ∀ (G : PrimeGroups) (F H : Endpoint) (k : ℤ) (Z a₁ a₂ : ℝ) (Ψ : ℝ → ℂ),
          Admissible P x G → EndpointBound x C τ η F → EndpointBound x C τ η H →
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C → x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
          |a₁| ≤ L x ^ C → |a₂| ≤ L x ^ C → CutoffBound x C lo hi Ψ bounds →
          discrepancy x B F.alpha →
          ‖shiftCorrelation P G x Z a₁ a₂ k F H Ψ lo hi‖ ≤ K * L x ^ (-D)

/-- P5 boundary. Long rough integers and sparse Fourier energy are internal to this package. -/
abbrev shifted_cancellation_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (_hs : SieveInputs)
    (_ht : TransferenceInputs) (_hi : IdealInputs),
    ShiftEstimate
end Erdos821.Blueprint
