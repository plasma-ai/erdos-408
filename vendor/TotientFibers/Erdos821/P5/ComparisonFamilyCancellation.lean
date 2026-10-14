import Erdos821.P5.ComparisonPatternCancellation
import Erdos821.P5.RawReduction

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The actual signed comparison sum has arbitrary-log cancellation,
using only the residual family's linear pattern mass. The raw pattern
and comparison block are selected before any endpoint or cutoff. -/
theorem eventual_comparison_family_cancellation
    (hsep : Blueprint.FourierSeparation) (hfourier : FourierArcTask)
    (hadapter : ComparisonMinorArcAdapterTask) (henergy : MarkedEndpointEnergyTask)
    (hsquare : SmoothEndpointSquareTask)
    (P : Geometry) (m : ℕ) (D C C₁ τ η lo hi qexp hexp ξexp : ℝ) (bounds : ℕ → ℝ)
    (hD : 0 < D) (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi)
    (hq : 0 < qexp) (hh : 0 < hexp) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Bdisc K : ℝ, 0 < Bdisc ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J : ℕ) (B : Family P.graph G.graph J m),
          Admissible P x G →
          B.Residual ⌊L x ^ qexp⌋₊ (L x ^ (-hexp)) (L x ^ (-ξexp)) →
          (B.model 1 0).patternMass ≤ L x ^ C₁ →
          ∃ raw : Fin B.count,
            (∀ g, (B.pattern raw).changed g = ∅) ∧
            (∀ a b u, (B.pattern raw).coefficient a b u = 1) ∧
            ∀ (E H : Endpoint) (Z a₁ a₂ : ℝ) (Ψ : ℝ → ℂ) (k : ℤ)
              (z₀ : (v : Fin B.count) → SharedDraw (B.pattern v)),
              EndpointBound x C τ η E → EndpointBound x C τ η H →
              k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
              x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C → |a₁| ≤ L x ^ C →
              CutoffBound x C lo hi Ψ bounds → discrepancy x Bdisc E.alpha →
              ‖strippedComparisonSum B raw x Z a₁ a₂ lo hi E H Ψ k z₀‖ ≤ K * L x ^ (-D) := by
  let Ds := D + |C₁| + 1
  obtain ⟨Bdisc, K, hBdisc, hK, hpattern⟩ := eventual_comparison_pattern_cancellation
    hsep hfourier hadapter henergy hsquare P m Ds C τ η lo hi qexp hexp ξexp bounds
    (by dsimp only [Ds]; positivity) hC hlo hhi hq hh hb
  refine ⟨Bdisc, K, hBdisc, hK, ?_⟩
  filter_upwards [hpattern, Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hpattern hL
  change 1 ≤ L x at hL
  have hLp : 0 < L x := by linarith
  intro G J B hG hB hmass
  obtain ⟨raw, block, he, hc, hv⟩ := residual_comparison_coefficients B hB
  refine ⟨raw, he, hc, ?_⟩
  intro E H Z a₁ a₂ Ψ k z₀ hE hH hk hkb hZlo hZhi ha hΨ hdisc
  have hcoef : 0 ≤ K * L x ^ (-Ds) := by positivity
  have hterm (v : Fin B.count) (hvraw : v ≠ raw) :
      ‖residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
        (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))‖ ≤
          (K * L x ^ (-Ds)) * patternCost (B.pattern v) :=
    hpattern G J B v block (z₀ v) E H Z a₁ a₂ Ψ k hG (hv v hvraw).2.1 (hv v hvraw).2.2
      hE hH hk hkb hZlo hZhi ha hΨ hdisc
  unfold strippedComparisonSum
  calc
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin B.count)).erase raw,
        ‖residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
          (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))‖ := norm_sum_le _ _
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin B.count)).erase raw,
        (K * L x ^ (-Ds)) * patternCost (B.pattern v) :=
      Finset.sum_le_sum (fun v hv => hterm v (Finset.mem_erase.mp hv).1)
    _ = (K * L x ^ (-Ds)) * ∑ v ∈ (Finset.univ : Finset (Fin B.count)).erase raw,
        patternCost (B.pattern v) := by rw [Finset.mul_sum]
    _ ≤ (K * L x ^ (-Ds)) * ∑ v : Fin B.count, patternCost (B.pattern v) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset raw _)
          (fun v hv hnot => patternCost_nonneg _)) hcoef
    _ = (K * L x ^ (-Ds)) * (B.model 1 0).patternMass := by
      rw [sum_patternCost_eq_patternMass B 1 0]
    _ ≤ (K * L x ^ (-Ds)) * L x ^ C₁ := mul_le_mul_of_nonneg_left hmass hcoef
    _ = K * L x ^ (-Ds + C₁) := by rw [mul_assoc, ← Real.rpow_add hLp]
    _ ≤ K * L x ^ (-D) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by dsimp only [Ds]; linarith [le_abs_self C₁])) hK.le

end Erdos821.P5Core
