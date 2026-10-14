import Erdos821.P5.PhysicalSchurPairing

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem normalized_schur_pairing_le {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (X Q c Cabs : ℝ) (hX : 0 < X) (hQ : 0 < Q)
    (t : Finset A.State) (f : ℤ → ℂ) (g : A.State → ℂ)
    (h : NormBound A.stateMass (A.physicalKernel false) (Q ^ Cabs))
    (hf : A.normOn ((dyad X).product Finset.univ) (fun z => f z.1) ≤ Real.sqrt X * Q ^ c)
    (hg : A.normOn t g ≤ Real.sqrt X * Q ^ c) :
    ‖(X : ℂ)⁻¹ * A.pairing X t f g‖ ≤ Q ^ (Cabs + 2 * c) := by
  have hp := pairing_le_of_normBound A (Q ^ Cabs) X t f g h
  have hnorm : 0 ≤ A.normOn t g := Real.sqrt_nonneg _
  have hmain : ‖A.pairing X t f g‖ ≤ 1 * X * Q ^ (Cabs + 2 * c) := by
    calc
      _ ≤ Q ^ Cabs * A.normOn ((dyad X).product Finset.univ) (fun z => f z.1) *
          A.normOn t g := hp
      _ ≤ Q ^ Cabs * (Real.sqrt X * Q ^ c) * (Real.sqrt X * Q ^ c) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hQ.le _)) hg hnorm
          (mul_nonneg (Real.rpow_nonneg hQ.le _) (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hQ.le _)))
      _ = _ := by
        rw [show Cabs + 2 * c = (Cabs + c) + c by ring,
          Real.rpow_add hQ, Real.rpow_add hQ]
        calc
          _ = (Real.sqrt X) ^ 2 * (Q ^ Cabs * Q ^ c * Q ^ c) := by ring
          _ = _ := by rw [Real.sq_sqrt hX.le]; ring
  simpa only [one_mul] using norm_normalized_pairing_le X 1 (Q ^ (Cabs + 2 * c)) _ hX hmain

/-- The absolute dyadic pairing estimate is uniform over every Mellin
frequency; its cost is fixed after the probe count and before J. -/
theorem eventual_dyadic_mellin_absolute_bound (ha : AbsolutePhysicalBounds)
    (P : Geometry) (C τ η : ℝ) (hτ : 0 < τ) :
    ∃ c : ℝ, ∀ (m : ℕ) (C₁ : ℝ), ∃ Cabs : ℝ, ∀ J : ℕ,
      ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups) (B : Family P.graph G.graph J m)
        (E H : Endpoint) (k : ℤ) (Z a₁ a₂ ζ v : ℝ) (i : ℕ),
        Admissible P x G → EndpointBound x C τ η E → EndpointBound x C τ η H →
        (B.model 1 0).patternMass ≤ L x ^ C₁ → i ∈ retainedSourceDyads x τ →
        ‖dyadicMellinPairing B x Z a₁ a₂ E H k ζ i v‖ ≤ L x ^ (Cabs + 2 * c) := by
  obtain ⟨c, hc⟩ := eventual_dyadic_endpoint_bounds P C
  refine ⟨c, ?_⟩
  intro m C₁
  obtain ⟨Cabs, hCabs⟩ := ha P.graph m C₁
  refine ⟨Cabs, ?_⟩
  intro J
  filter_upwards [hCabs J, hc J m (τ / 2) (by linarith),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x habs hnorm hL
  change 1 ≤ L x at hL
  intro G B E H k Z a₁ a₂ ζ v i hG hE hH hmass hi
  have hV (g : Fin G.size) : 0 < G.graph.V g := by
    rw [graph_mass]
    exact P.positive.2.2.1.trans_le (hG.2.2.1 g).1
  have hscale := (mem_retainedSourceDyads x τ i).mp hi
  have hb := habs G.graph (B.model k (ζ - v)) (graph_admissible P x G hG) hmass
  have hschur := physical_normBound_of_neighbor_bounds (B.model k (ζ - v)) hV
    (L x ^ Cabs) (Real.rpow_nonneg (by linarith : 0 ≤ L x) _) hb.1 hb.2
  have hnorms := hnorm G (B.model k (ζ - v)) ((2 : ℝ) ^ i) Z τ η a₁ a₂ v E H
    (positiveRoots (x ^ (2 : ℕ))) (positiveRoots (x ^ (2 : ℕ))) hG hE hH hscale.2.1 hscale.2.2
  exact normalized_schur_pairing_le (B.model k (ζ - v)) ((2 : ℝ) ^ i) (L x) c Cabs
    (pow_pos (by norm_num) _) (by linarith)
    ((positiveRoots (x ^ (2 : ℕ)) ∩ comparableRoots ((2 : ℝ) ^ i)).product Finset.univ)
    (mellinPairingSource ((2 : ℝ) ^ i) Z
      (rootMask (positiveRoots (x ^ (2 : ℕ))) (liftedEndpoint (B.model k ζ) x E (-a₁))) v)
    (fun z => liftedEndpoint (B.model k ζ) x H a₂ z.1) hschur hnorms.2.1 hnorms.2.2

end Erdos821.P5Core
