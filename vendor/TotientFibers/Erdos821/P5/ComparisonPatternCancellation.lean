import Erdos821.P5.MellinCellCancellation
import Erdos821.P5.ComparisonSummationCosts

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Each actual comparison pattern has arbitrary-log cancellation paid
linearly by its coefficient supremum. The finite cell and character
counts are absorbed before discrepancy and the lift depth are chosen. -/
theorem eventual_comparison_pattern_cancellation
    (hsep : Blueprint.FourierSeparation) (hfourier : FourierArcTask)
    (hadapter : ComparisonMinorArcAdapterTask) (henergy : MarkedEndpointEnergyTask)
    (hsquare : SmoothEndpointSquareTask)
    (P : Geometry) (m : ℕ) (D C τ η lo hi qexp hexp ξexp : ℝ) (bounds : ℕ → ℝ)
    (hD : 0 < D) (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi)
    (hq : 0 < qexp) (hh : 0 < hexp) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Bdisc K : ℝ, 0 < Bdisc ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J : ℕ) (B : Family P.graph G.graph J m)
          (v : Fin B.count) (block : G.graph.BigGroup → Bool) (z : SharedDraw (B.pattern v))
          (E H : Endpoint) (Z a₁ a₂ : ℝ) (Ψ : ℝ → ℂ) (k : ℤ),
          Admissible P x G →
          (∀ side : Bool, ∃ g : G.graph.BigGroup,
            block g = side ∧ ((B.pattern v).changed g.val).Nonempty) →
          HasComparisonCoefficient (B.pattern v) block ⌊L x ^ qexp⌋₊
            (L x ^ (-hexp)) (L x ^ (-ξexp)) →
          EndpointBound x C τ η E → EndpointBound x C τ η H →
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
          x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C → |a₁| ≤ L x ^ C →
          CutoffBound x C lo hi Ψ bounds → discrepancy x Bdisc E.alpha →
          ‖residualStrippedLift B v x Z a₁ a₂ E H Ψ k z
            (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))‖ ≤
            (K * L x ^ (-D)) * patternCost (B.pattern v) := by
  let Csum := 2 * (P.d + hexp + 1) + 4 * qexp
  have hCsum : 0 < Csum := by
    have hd : 0 < P.d := by rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩; linarith
    dsimp only [Csum]
    positivity
  obtain ⟨Bdisc, K, hBdisc, hK, hcell⟩ := eventual_comparison_cell_cancellation
    hsep hfourier hadapter henergy hsquare P m (D + Csum) C τ η lo hi hexp bounds
    (by positivity) hC hlo hhi hh hb
  refine ⟨Bdisc, K, hBdisc, hK, ?_⟩
  filter_upwards [hcell, eventual_comparison_summation_count P m qexp hexp hh,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hcell hcount hL
  change 1 ≤ L x at hL
  have hLp : 0 < L x := by linarith
  have hQ : 1 ≤ ⌊L x ^ qexp⌋₊ := Nat.le_floor
    (by simpa using Real.one_le_rpow hL hq.le)
  have hξ : 0 < L x ^ (-ξexp) := Real.rpow_pos_of_pos hLp _
  intro G J B v block z E H Z a₁ a₂ Ψ k hG hne hc hE hH hk hkb hZlo hZhi ha hΨ hdisc
  let Q := ⌊L x ^ qexp⌋₊
  let f : (ℤ × ℤ) → CharacterIndex Q → CharacterIndex Q → ℂ :=
    fun j χA χB => comparisonCellCorrelation (B.pattern v) block (L x ^ (-hexp))
    j χA χB x Z a₁ a₂ E H Ψ k
    (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))
  let a₀ : G.graph.BigLabels (J + P.ell) := Classical.choice
    (admissible_full_big_labels P G x (J + P.ell) hG)
  rw [residualStrippedLift_comparison_cell_expansion B v block Q (L x ^ (-hexp))
    (L x ^ (-ξexp)) hc x Z a₁ a₂ E H Ψ k z]
  have hsum := comparison_cell_character_sum_norm_le_constant (B.pattern v) block Q
    (L x ^ (-hexp)) (L x ^ (-ξexp)) (K * L x ^ (-(D + Csum))) hQ hξ hc a₀ z f
    (fun j hj χA hχA χB hχB => hcell G J Q (B.pattern v) block j χA χB z
      E H Z a₁ a₂ Ψ k hG hne hj hE hH hk hkb hZlo hZhi ha hΨ hdisc)
  apply hsum.trans
  have hcN := hcount G J P.ell (B.pattern v) block hG
  calc
    _ = patternCost (B.pattern v) *
        (((comparisonCells (B.pattern v) block (L x ^ (-hexp))).card : ℝ) *
          ((primitiveCharacters Q).card : ℝ) ^ 2) *
        (K * L x ^ (-(D + Csum))) := by ring
    _ ≤ patternCost (B.pattern v) * L x ^ Csum *
        (K * L x ^ (-(D + Csum))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcN (patternCost_nonneg _)) (by positivity)
    _ = _ := by
      calc
        _ = (K * patternCost (B.pattern v)) *
            (L x ^ Csum * L x ^ (-(D + Csum))) := by ring
        _ = _ := by rw [← Real.rpow_add hLp, show Csum + -(D + Csum) = -D by ring]; ring

end Erdos821.P5Core
