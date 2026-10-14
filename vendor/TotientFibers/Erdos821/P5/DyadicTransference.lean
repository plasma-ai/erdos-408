import Erdos821.P5.DyadicLiftIntegral

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem norm_normalized_pairing_le (X K R : ℝ) (w : ℂ) (hX : 0 < X)
    (hw : ‖w‖ ≤ K * X * R) : ‖(X : ℂ)⁻¹ * w‖ ≤ K * R := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
  calc
    _ ≤ X⁻¹ * (K * X * R) := mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hX.le)
    _ = _ := by field_simp

/-- A normalized dyadic saving from P3, conditional on the actual ideal
kernel at the shifted Mellin frequency. The endpoint exponent is chosen
before the requested saving, ideal accuracy, probes and J. -/
theorem dyadic_mellin_transference (ht : TransferencePairing)
    (P : Geometry) (C τ η : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hτhi : τ ≤ 1)
    (D : ℝ) (hD : 0 < D) :
    ∃ Eid : ℝ, 0 < Eid ∧ ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ,
      ∀ J : ℕ, J₀ ≤ J → ∃ K : ℝ, 0 < K ∧
        ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups) (B : Family P.graph G.graph J m)
          (E H : Endpoint) (k : ℤ) (Z a₁ a₂ ζ v : ℝ) (i : ℕ),
          Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
          (B.model 1 0).patternMass ≤ L x ^ C₁ →
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C →
          (∀ θ : ℝ, NormBound (G.graph.idealMass (M := J + P.ell))
            ((B.model 1 (ζ - v)).idealKernel θ) (L x ^ (-Eid))) →
          i ∈ retainedSourceDyads x τ →
          ‖dyadicMellinPairing B x Z a₁ a₂ E H k ζ i v‖ ≤ K * L x ^ (-D) := by
  obtain ⟨c, hc⟩ := eventual_dyadic_endpoint_bounds P C
  let saving : ℝ := D + 2 * |c|
  have hsaving : 0 < saving := by dsimp [saving]; positivity
  obtain ⟨Eid, hEid, htransfer⟩ := ht P.graph saving hsaving
  refine ⟨Eid, hEid, ?_⟩
  intro m C₁
  obtain ⟨J₀, hJ₀⟩ := htransfer m C₁
  refine ⟨J₀, ?_⟩
  intro J hJ
  obtain ⟨K, hK, hpair⟩ := hJ₀ J hJ (τ / 2) C c (2 + 6 * Real.log 2) (by linarith) hC
  refine ⟨K, hK, ?_⟩
  filter_upwards [hpair, hc J m (τ / 2) (by linarith),
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hpair hnorm hx hL
  intro G B E H k Z a₁ a₂ ζ v i hG hE hH hmass hk hkbound hideal hi
  have hscale := (mem_retainedSourceDyads x τ i).mp hi
  have hrange := retainedSourceDyads_transfer_range x τ hx hτ hτhi i hi
  have hnorms := hnorm G (B.model k (ζ - v)) ((2 : ℝ) ^ i) Z τ η a₁ a₂ v E H
    (positiveRoots (x ^ (2 : ℕ))) (positiveRoots (x ^ (2 : ℕ))) hG hE hH
    hscale.2.1 hscale.2.2
  have hp := hpair G.graph (B.model k (ζ - v)) ((2 : ℝ) ^ i)
    ((positiveRoots (x ^ (2 : ℕ)) ∩ comparableRoots ((2 : ℝ) ^ i)).product Finset.univ)
    (mellinPairingSource ((2 : ℝ) ^ i) Z
      (rootMask (positiveRoots (x ^ (2 : ℕ))) (liftedEndpoint (B.model k ζ) x E (-a₁))) v)
    (fun z => liftedEndpoint (B.model k ζ) x H a₂ z.1)
    (graph_admissible P x G hG) hmass hk hkbound hideal hrange.1 hrange.2
    hnorms.1 hnorms.2.1 hnorms.2.2
  have hnormal := norm_normalized_pairing_le ((2 : ℝ) ^ i) K (L x ^ (-saving + 2 * c)) _
    (pow_pos (by norm_num) _) hp
  have hexp : -saving + 2 * c ≤ -D := by
    dsimp [saving]
    linarith [le_abs_self c]
  exact hnormal.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hL hexp) hK.le)

end Erdos821.P5Core
