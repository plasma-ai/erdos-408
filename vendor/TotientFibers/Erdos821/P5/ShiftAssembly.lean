import Erdos821.P5.ComparisonFamilyCancellation
import Erdos821.P5.RawCorrelationBound
import Erdos821.P5SmoothSquare.Proof
import Erdos821.Blueprint.Shift

set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Combine the raw lift and the signed comparison family at one fixed
lift depth. All analytic costs precede the discrepancy exponent. -/
theorem shiftEstimate_of_tasks
    (hsep : Blueprint.FourierSeparation) (ht : Blueprint.TransferenceInputs)
    (hid : IdealConstruction) (hfourier : FourierArcTask)
    (hadapter : ComparisonMinorArcAdapterTask) (henergy : MarkedEndpointEnergyTask)
    (hsquare : SmoothEndpointSquareTask) : Blueprint.ShiftEstimate := by
  intro P D C τ η lo hi bounds hD hC hI
  by_cases hτ : 0 < τ ∧ τ ≤ 1
  · let bounds' : ℕ → ℝ := fun j => max 0 (bounds j)
    have hb : ∀ j, 0 ≤ bounds' j := fun j => le_max_left _ _
    obtain ⟨m, J₀, C₁, qexp, hexp, ξexp, hq, hh, hξ, hraw⟩ :=
      residual_family_shiftCorrelation_bound hsep ht hid P D C τ η lo hi bounds'
        hD hC hτ.1 hτ.2 hI.1 hI.2 hb
    obtain ⟨Kr, hKr, hraw⟩ := hraw J₀ le_rfl
    obtain ⟨Bdisc, Kc, hBdisc, hKc, hcomparison⟩ :=
      eventual_comparison_family_cancellation hsep hfourier hadapter henergy hsquare
        P m D C C₁ τ η lo hi qexp hexp ξexp bounds'
        hD hC hI.1 hI.2 hq hh hb
    refine ⟨Bdisc, Kc + Kr, hBdisc, add_pos hKc hKr, ?_⟩
    filter_upwards [hraw, hcomparison,
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hraw hcomparison hL
    change 1 ≤ L x at hL
    intro G E H k Z a₁ a₂ Ψ hG hE hH hk hkb hZlo hZhi ha₁ ha₂ hΨ hdisc
    have hΨ' : CutoffBound x C lo hi Ψ bounds' := by
      refine ⟨hΨ.1, hΨ.2.1, ?_⟩
      intro j y
      exact (hΨ.2.2 j y).trans (mul_le_mul_of_nonneg_right
        (le_max_right 0 (bounds j)) (Real.rpow_nonneg (by linarith : 0 ≤ L x) _))
    obtain ⟨B, hres, hmass, hraw⟩ := hraw G hG
    obtain ⟨raw, he, hc, hcomparison⟩ := hcomparison G J₀ B hG hres hmass
    have hV (g : Fin G.size) : G.graph.V g ≠ 0 := by
      rw [graph_mass]
      exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).ne'
    let z₀ : (v : Fin B.count) → SharedDraw (B.pattern v) :=
      fun v => unusedAuxDraw (B.pattern v) hV
    calc
      _ ≤ ‖strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀‖ +
          Kr * L x ^ (-D) :=
        hraw raw he hc E H k Z a₁ a₂ Ψ z₀ hE hH hk hkb hZlo hZhi ha₁ ha₂ hΨ'
      _ ≤ Kc * L x ^ (-D) + Kr * L x ^ (-D) :=
        add_le_add
          (hcomparison E H Z a₁ a₂ Ψ k z₀ hE hH hk hkb hZlo hZhi ha₁ hΨ' hdisc) le_rfl
      _ = (Kc + Kr) * L x ^ (-D) := by ring
  · refine ⟨1, 1, by norm_num, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro x G E H k Z a₁ a₂ Ψ hG hE
    exact False.elim (hτ ⟨hE.1, by linarith [hE.2.1, hE.2.2.1]⟩)

theorem shifted_cancellation_of_remaining_tasks
    (hfourier : FourierArcTask) (hadapter : ComparisonMinorArcAdapterTask)
    (henergy : MarkedEndpointEnergyTask) (hc : Blueprint.ClassicalInputs)
    (_hs : Blueprint.SieveInputs) (ht : Blueprint.TransferenceInputs)
    (hi : Blueprint.IdealInputs) : Blueprint.ShiftEstimate :=
  shiftEstimate_of_tasks hc.separation ht hi.construction hfourier hadapter henergy
    P5Ssq.smoothEndpointSquareTask_proof

example (hsep : Blueprint.FourierSeparation) (ht : Blueprint.TransferenceInputs)
    (hid : IdealConstruction) (hfourier : FourierArcTask)
    (hadapter : ComparisonMinorArcAdapterTask) (henergy : MarkedEndpointEnergyTask)
    (hsquare : SmoothEndpointSquareTask) : Erdos821.Blueprint.Analytic.lifted_shift_statement :=
  shiftEstimate_of_tasks hsep ht hid hfourier hadapter henergy hsquare

example (hfourier : FourierArcTask) (hadapter : ComparisonMinorArcAdapterTask)
    (henergy : MarkedEndpointEnergyTask) : Erdos821.Blueprint.shifted_cancellation_statement :=
  shifted_cancellation_of_remaining_tasks hfourier hadapter henergy

end Erdos821.P5Core
