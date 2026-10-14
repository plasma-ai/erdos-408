import Erdos821.P5.SmoothCellCancellation
import Erdos821.P5.SmoothCellIntegrability
import Erdos821.P5.SmoothComparisonSeparation
import Erdos821.P5.MellinFrequencyBounds
import Erdos821.P5.FullLiftNumerics

noncomputable section
open scoped BigOperators Classical
open Filter MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The actual cell correlation with the original coupled cutoff has
arbitrary logarithmic saving. Fourier mass and the absolute tail cost
are fixed before the saving, discrepancy and lift depth. -/
theorem eventual_comparison_cell_cancellation
    (hsep : Blueprint.FourierSeparation) (hfourier : FourierArcTask)
    (hadapter : ComparisonMinorArcAdapterTask) (henergy : MarkedEndpointEnergyTask)
    (hsquare : SmoothEndpointSquareTask)
    (P : Geometry) (m : ℕ) (D C τ η lo hi hexp : ℝ) (bounds : ℕ → ℝ)
    (hD : 0 < D) (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi)
    (hh : 0 < hexp) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J Q : ℕ) (ν : Pattern G.graph J P.ell m)
          (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ)
          (χA χB : CharacterIndex Q) (z : SharedDraw ν)
          (E H : Endpoint) (Z a₁ a₂ : ℝ) (Ψ : ℝ → ℂ) (k : ℤ),
          Admissible P x G →
          (∀ side : Bool, ∃ g : G.graph.BigGroup,
            block g = side ∧ (ν.changed g.val).Nonempty) →
          j ∈ comparisonCells ν block (L x ^ (-hexp)) →
          EndpointBound x C τ η E → EndpointBound x C τ η H →
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
          x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C → |a₁| ≤ L x ^ C →
          CutoffBound x C lo hi Ψ bounds → discrepancy x B E.alpha →
          ‖comparisonCellCorrelation ν block (L x ^ (-hexp)) j χA χB
            x Z a₁ a₂ E H Ψ k (fun u => cutoffRoots lo hi Z (freeDrawProduct ν u))‖ ≤
            K * L x ^ (-D) := by
  obtain ⟨Cf, Kcost, hCf, hKcost, hsepA⟩ := comparison_smooth_cutoff_separation hsep
    C lo hi hexp bounds hC hlo hhi hh hb
  obtain ⟨C₂, Ktail, hC₂, hKtail, hall⟩ := eventual_smooth_cell_all_frequency_bound
    hfourier hsquare P m C τ η lo hi hexp hC hlo hhi hh
  let Rcost := C₂ + 1
  obtain ⟨B, Kmain, hB, hKmain, hmain⟩ := eventual_smooth_comparison_cell_cancellation
    hfourier hadapter henergy hsquare P m (D + Kcost + 1) C (max C Cf + 1)
    τ η lo hi hexp (by positivity) hC hlo hhi hh
  obtain ⟨KA, hKA, hseparate⟩ := hsepA (D + |Rcost| + 1) (by positivity)
  refine ⟨B, Kmain + KA, hB, add_pos hKmain hKA, ?_⟩
  filter_upwards [hall, hmain, hseparate, (eventual_mellin_shift_frequency_bound C Cf hC).2,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop Ktail] with x hall hmain hsep hfreq hL htailcost
  change 1 ≤ L x at hL
  change Ktail ≤ L x at htailcost
  have hLp : 0 < L x := by linarith
  intro G J Q ν block j χA χB z E H Z a₁ a₂ Ψ k hG hne hj hE hH hk hkb hZlo hZhi ha hΨ hdisc
  obtain ⟨α, hα, hαmass, hαtail, heq⟩ := hsep Ψ hΨ
  let Y := Z * comparisonJointScale (L x ^ (-hexp)) j
  let F := fun ξ : Fin 1 → ℝ => smoothComparisonCellCorrelation ν block
    (L x ^ (-hexp)) j χA χB x Y a₁ a₂ (mellinFrequency ξ) lo hi hlo hhi E H k
  let S : Set (Fin 1 → ℝ) := {ξ | ‖ξ‖ ≤ L x ^ Cf}
  have hS : MeasurableSet S := measurableSet_le measurable_norm measurable_const
  have htail : (∫ ξ in Sᶜ, ‖α ξ‖) ≤ KA * L x ^ (-(D + |Rcost| + 1)) := by
    simpa only [S, Set.compl_setOf, not_le] using hαtail
  have hv (ξ : Fin 1 → ℝ) (hξ : ξ ∈ S) : |mellinFrequency ξ| ≤ L x ^ (max C Cf + 1) := by
    have hz : |(0 : ℝ)| ≤ L x ^ C := by simp; positivity
    simpa only [sub_zero, zero_sub, abs_neg] using hfreq 0 0 0 ξ hz hz (by ring) hξ
  have hmain' (ξ : Fin 1 → ℝ) (hξ : ξ ∈ S) :
      ‖F ξ‖ ≤ Kmain * L x ^ (-(D + Kcost + 1)) :=
    hmain G J Q ν block j χA χB z E H Z a₁ a₂ (mellinFrequency ξ) k
      hG hne hj hE hH hk hkb hZlo hZhi ha (hv ξ hξ) hdisc
  have hall' (ξ : Fin 1 → ℝ) : ‖F ξ‖ ≤ L x ^ Rcost := by
    have ht := hall G J Q ν block j χA χB z E H Z a₁ a₂ (mellinFrequency ξ) k
      hG hne hj hE hH hZlo hZhi hkb
    apply ht.trans
    calc
      _ ≤ L x * L x ^ C₂ := mul_le_mul_of_nonneg_right htailcost (Real.rpow_nonneg hLp.le _)
      _ = _ := by rw [Real.rpow_add hLp, Real.rpow_one]; ring
  rw [heq P G J m Q ν block j χA χB z Z a₁ a₂ E H k hZlo hkb]
  have hbound := mellin_main_tail_integral_bound α F hα
    (smooth_comparison_cell_integrable ν block _ j χA χB x Y a₁ a₂ lo hi hlo hhi E H k α hα)
    S hS (Kmain * L x ^ (-(D + Kcost + 1))) (L x ^ Rcost) (by positivity) hmain' hall'
  have hnum := logarithmic_main_tail_bound (L x) 1 (∫ ξ, ‖α ξ‖)
    (∫ ξ in Sᶜ, ‖α ξ‖) 1 Kmain KA Kcost Rcost D hL (by norm_num) hKmain.le hKA.le
    (by simpa only [one_mul] using hL) hαmass htail
  exact hbound.trans (by simpa only [one_mul] using hnum)

end Erdos821.P5Core
