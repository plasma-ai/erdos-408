import Erdos821.P5.FullLiftCancellation
import Erdos821.P5.RawReduction

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Cancellation of the actual signed stripped family, uniformly over
both endpoint data and the arbitrary unused shared draws. -/
theorem residual_family_stripped_lift_bound (hsep : Blueprint.FourierSeparation)
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
          ∀ (E H : Endpoint) (k : ℤ) (Z a₁ a₂ : ℝ) (Ψ : ℝ → ℂ)
            (z₀ : (v : Fin B.count) → SharedDraw (B.pattern v)),
            EndpointBound x C τ η E → EndpointBound x C τ η H →
            k ≠ 0 → |(k : ℝ)| ≤ L x ^ C → x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
            |a₁| ≤ L x ^ C → |a₂| ≤ L x ^ C → CutoffBound x C lo hi Ψ bounds →
            ‖∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
              (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))‖ ≤ K * L x ^ (-D) := by
  obtain ⟨m, J₀, C₁, qexp, hexp, ξexp, hq, hh, hξ, hfamily⟩ :=
    residual_family_full_lift_bound hsep ht hid P D C τ η lo hi bounds
      hD hC hτ hτhi hlo hhi hbounds
  refine ⟨m, J₀, C₁, qexp, hexp, ξexp, hq, hh, hξ, ?_⟩
  intro J hJ
  obtain ⟨K, hK, hfull⟩ := hfamily J hJ
  refine ⟨K + 1, by linarith, ?_⟩
  filter_upwards [hfull, full_residual_stripping_negligible P J m D C C₁ τ η lo hi bounds hC hlo hhi,
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hfull hstrip hx hL
  change 1 ≤ L x at hL
  intro G hG
  obtain ⟨B, hres, hmass, hfull⟩ := hfull G hG
  refine ⟨B, hres, hmass, ?_⟩
  intro E H k Z a₁ a₂ Ψ z₀ hE hH hk hkbound hZlo hZhi ha₁ ha₂ hΨ
  have hZ : 0 < Z := (mul_pos (by linarith : 0 < x)
    (Real.rpow_pos_of_pos (by linarith : 0 < L x) (-C))).trans_le hZlo
  have hnorm := hfull E H k Z a₁ a₂ (-a₁ - a₂) Ψ z₀ hE hH hk hkbound hZ ha₁ ha₂ rfl hΨ
  have herr := hstrip G ⌊L x ^ qexp⌋₊ (L x ^ (-hexp)) (L x ^ (-ξexp)) B Z a₁ a₂ E H Ψ k
    (-a₁ - a₂) z₀ z₀ hG hres hE hH hmass hkbound hZlo hZhi hΨ rfl
  let S := ∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
    (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))
  let F := fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k (-a₁ - a₂) z₀
  change ‖S‖ ≤ (K + 1) * L x ^ (-D)
  calc
    _ = ‖F - (F - S)‖ := by congr 1; ring
    _ ≤ ‖F‖ + ‖F - S‖ := norm_sub_le _ _
    _ ≤ K * L x ^ (-D) + L x ^ (-D) := add_le_add hnorm herr
    _ = _ := by ring

end Erdos821.P5Core
