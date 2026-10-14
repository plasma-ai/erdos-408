import Erdos821.P5.DyadicLiftPartition

noncomputable section
open scoped BigOperators Classical
open MeasureTheory Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

def dyadicMellinPairing {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Family P.graph G.graph J m) (x Z a₁ a₂ : ℝ) (E H : Endpoint)
    (k : ℤ) (ζ : ℝ) (i : ℕ) (v : ℝ) : ℂ :=
  (((2 : ℝ) ^ i : ℝ) : ℂ)⁻¹ *
    (B.model k (ζ - v)).pairing ((2 : ℝ) ^ i)
      ((positiveRoots (x ^ (2 : ℕ)) ∩ comparableRoots ((2 : ℝ) ^ i)).product Finset.univ)
      (mellinPairingSource ((2 : ℝ) ^ i) Z
        (rootMask (positiveRoots (x ^ (2 : ℕ))) (liftedEndpoint (B.model k ζ) x E (-a₁))) v)
      (fun z => liftedEndpoint (B.model k ζ) x H a₂ z.1)

/-- Exact finite dyadic inversion of the full lift. Both the original
source mask and the comparable target restriction survive inversion. -/
theorem fullResidualLift_dyadic_mellin_integral {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Family P.graph G.graph J m) (x Z a₁ a₂ C τ η : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hE : EndpointBound x C τ η E) (hsmall : 2 * x ^ (τ / 2) ≤ x ^ τ)
    (hV : ∀ g, G.graph.V g ≠ 0) (hZ : 0 < Z)
    (hD : ∀ i ∈ retainedSourceDyads x τ, ∀ v a u,
      |(k : ℝ)| * ((B.pattern v).D a u : ℝ) ≤ (2 : ℝ) ^ i / 2)
    (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    Integrable (fun ξ => α ξ * ∑ i ∈ retainedSourceDyads x τ,
      dyadicMellinPairing B x Z a₁ a₂ E H k ζ i (mellinFrequency ξ)) ∧
    fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused =
      ∫ ξ, α ξ * ∑ i ∈ retainedSourceDyads x τ,
        dyadicMellinPairing B x Z a₁ a₂ E H k ζ i (mellinFrequency ξ) := by
  let I := fun i ξ => α ξ * dyadicMellinPairing B x Z a₁ a₂ E H k ζ i (mellinFrequency ξ)
  have hdy (i : ℕ) (hi : i ∈ retainedSourceDyads x τ) :=
    dyadic_cutoff_eq_restricted_pairing_integral B k ζ ((2 : ℝ) ^ i) Z
      (positiveRoots (x ^ (2 : ℕ)))
      (rootMask (positiveRoots (x ^ (2 : ℕ))) (liftedEndpoint (B.model k ζ) x E (-a₁)))
      (liftedEndpoint (B.model k ζ) x H a₂) unused hV (pow_pos (by norm_num) _)
      hZ (hD i hi) Ψ α hα hrep
  have hI (i : ℕ) (hi : i ∈ retainedSourceDyads x τ) : Integrable (I i) := by
    simpa only [I, dyadicMellinPairing, mul_assoc] using (hdy i hi).1
  constructor
  · simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ hI
  · calc
      _ = ∑ i ∈ retainedSourceDyads x τ, ∫ ξ, I i ξ := by
        rw [fullResidualLift_eq_retained_dyadic B x Z a₁ a₂ C τ η E H Ψ k ζ unused hE hsmall]
        apply Finset.sum_congr rfl
        intro i hi
        simpa only [I, dyadicMellinPairing, mul_assoc] using (hdy i hi).2
      _ = ∫ ξ, ∑ i ∈ retainedSourceDyads x τ, I i ξ :=
        (integral_finsetSum _ hI).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ξ
        simp only [I, Finset.mul_sum]

theorem eventual_retainedSourceDyads_bounds (P : Geometry) (J : ℕ) (C τ : ℝ)
    (hτ : 0 < τ) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ x ∧ 2 * x ^ (τ / 2) ≤ x ^ τ ∧
      ((retainedSourceDyads x τ).card : ℝ) ≤ (2 / Real.log 2 + 1) * L x ∧
      ∀ (G : PrimeGroups) (m : ℕ) (B : Family P.graph G.graph J m) (k : ℤ),
        Admissible P x G → |(k : ℝ)| ≤ L x ^ C →
        ∀ i ∈ retainedSourceDyads x τ, ∀ v a u,
          |(k : ℝ)| * ((B.pattern v).D a u : ℝ) ≤ (2 : ℝ) ^ i / 2 := by
  filter_upwards [eventual_low_dyad_separation τ hτ,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventual_half_dyad_displacement P J C (τ / 2) (by linarith)]
    with x hlow hL hD
  refine ⟨hlow.1, hlow.2, ?_, ?_⟩
  · exact (by exact_mod_cast retainedSourceDyads_card_le x τ :
      ((retainedSourceDyads x τ).card : ℝ) ≤ sourceDyadicCount (x ^ (2 : ℕ))).trans
        (sourceDyadicCount_square_le x hlow.1 hL)
  · intro G m B k hG hk i hi
    exact hD G m (B.model k 0) _ hG hk ((mem_retainedSourceDyads x τ i).mp hi).2.1

end Erdos821.P5Core
