import Erdos821.P5.FullLiftNumerics

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The raw-plus-comparison physical lift has arbitrary logarithmic
saving for one actual residual family. The family precedes endpoints,
cutoffs, shifts and all their frequencies. -/
theorem residual_family_full_lift_bound (hsep : Blueprint.FourierSeparation)
    (ht : Blueprint.TransferenceInputs) (hid : IdealConstruction)
    (P : Geometry) (D C τ η lo hi : ℝ) (bounds : ℕ → ℝ)
    (hD : 0 < D) (hC : 0 < C) (hτ : 0 < τ) (hτhi : τ ≤ 1)
    (hlo : 0 < lo) (hhi : lo < hi) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ m J₀ : ℕ, ∃ C₁ qexp hexp ξexp : ℝ,
      0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ J : ℕ, J₀ ≤ J → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups), Admissible P x G → ∃ B : Family P.graph G.graph J m,
          B.Residual ⌊L x ^ qexp⌋₊ (L x ^ (-hexp)) (L x ^ (-ξexp)) ∧
          (B.model 1 0).patternMass ≤ L x ^ C₁ ∧
          ∀ (E H : Endpoint) (k : ℤ) (Z a₁ a₂ ζ : ℝ) (Ψ : ℝ → ℂ)
            (unused : (v : Fin B.count) → SharedDraw (B.pattern v)),
            EndpointBound x C τ η E → EndpointBound x C τ η H →
            k ≠ 0 → |(k : ℝ)| ≤ L x ^ C → 0 < Z →
            |a₁| ≤ L x ^ C → |a₂| ≤ L x ^ C → ζ = -a₁ - a₂ →
            CutoffBound x C lo hi Ψ bounds →
            ‖fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused‖ ≤ K * L x ^ (-D) := by
  obtain ⟨Cf, Kcost, hCf, hKcost, hcutoff⟩ :=
    mellinCutoffTask_proof hsep C lo hi bounds hC hlo hhi hbounds
  have hmainD : 0 < D + Kcost + 1 := by linarith
  obtain ⟨m, J₀, C₁, qexp, hexp, ξexp, hq, hh, hξ, hfamily⟩ :=
    residual_family_main_dyadic_bound ht.pairing hid P C τ η Cf (D + Kcost + 1)
      hC hτ hτhi hmainD
  obtain ⟨c, hc⟩ := eventual_dyadic_mellin_absolute_bound ht.absolute P C τ η hτ
  obtain ⟨Cabs, habs⟩ := hc m C₁
  let Rcost : ℝ := Cabs + 2 * c
  have htailD : 0 < D + |Rcost| + 1 := by positivity
  obtain ⟨KA, hKA, hfourier⟩ := hcutoff (D + |Rcost| + 1) htailD
  let Cdyad : ℝ := 2 / Real.log 2 + 1
  have hCdyad : 0 < Cdyad := by dsimp [Cdyad]; positivity
  refine ⟨m, J₀, C₁, qexp, hexp, ξexp, hq, hh, hξ, ?_⟩
  intro J hJ
  obtain ⟨Kmain, hKmain, hmain⟩ := hfamily J hJ
  refine ⟨Cdyad * (Kmain + KA), mul_pos hCdyad (add_pos hKmain hKA), ?_⟩
  filter_upwards [hmain, habs J, hfourier, eventual_retainedSourceDyads_bounds P J C τ hτ,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hmain habs hfourier hdyad hL
  change 1 ≤ L x at hL
  intro G hG
  obtain ⟨B, hres, hmass, hmain⟩ := hmain G hG
  refine ⟨B, hres, hmass, ?_⟩
  intro E H k Z a₁ a₂ ζ Ψ unused hE hH hk hkbound hZ ha₁ ha₂ hζ hΨ
  obtain ⟨α, hα, hαmass, hrep, hαtail⟩ := hfourier Ψ hΨ
  let S : Set (Fin 1 → ℝ) := {ξ | ‖ξ‖ ≤ L x ^ Cf}
  have hS : MeasurableSet S := measurableSet_le measurable_norm measurable_const
  have hV (g : Fin G.size) : G.graph.V g ≠ 0 := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).ne'
  have htail : (∫ ξ in Sᶜ, ‖α ξ‖) ≤ KA * L x ^ (-(D + |Rcost| + 1)) := by
    simpa only [S, Set.compl_setOf, not_le] using hαtail
  have hfull := fullResidualLift_norm_le_main_tail B x Z a₁ a₂ C τ η E H Ψ k ζ unused
    hE hdyad.2.1 hV hZ (hdyad.2.2.2 G m B k hG hkbound) α hα hrep S hS
    (Kmain * L x ^ (-(D + Kcost + 1))) (L x ^ Rcost)
    (mul_nonneg hKmain.le (Real.rpow_nonneg (by linarith : 0 ≤ L x) _))
    (fun ξ hξ i hi => hmain E H k Z a₁ a₂ ζ ξ i hE hH hk hkbound ha₁ ha₂ hζ hξ hi)
    (fun ξ i hi => habs G B E H k Z a₁ a₂ ζ (mellinFrequency ξ) i hG hE hH hmass hi)
  exact hfull.trans (logarithmic_main_tail_bound (L x) ((retainedSourceDyads x τ).card : ℝ)
    (∫ ξ, ‖α ξ‖) (∫ ξ in Sᶜ, ‖α ξ‖) Cdyad Kmain KA Kcost Rcost D
    hL (Nat.cast_nonneg _) hKmain.le hKA.le hdyad.2.2.1 hαmass htail)

end Erdos821.P5Core
