import Erdos821.P5.MellinPairingIntegral

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem fullResidualLift_eq_gatedFamilySum {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (x Y Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v)) :
    fullResidualLift B x Y Z a₁ a₂ E H Ψ k ζ unused =
      gatedFamilySum B k ζ (positiveRoots Y) (positiveRoots Y)
        (liftedEndpoint (B.model k ζ) x E (-a₁)) (liftedEndpoint (B.model k ζ) x H a₂)
        (harmonicCutoff Ψ Z) unused := rfl

/-- Exact inversion of the full lift on its original finite positive-root
sets. Dyadic partitioning may now be performed on this finite family. -/
theorem fullResidualLift_mellin_integral {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (x Y X Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hX : X ≠ 0) (hZ : 0 < Z) (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    Integrable (fun ξ => α ξ * (X : ℂ)⁻¹ *
      gatedFamilySum B k (ζ - mellinFrequency ξ) (positiveRoots Y) (positiveRoots Y)
        (mellinPairingSource X Z (liftedEndpoint (B.model k ζ) x E (-a₁)) (mellinFrequency ξ))
        (liftedEndpoint (B.model k ζ) x H a₂) (fun _ _ => 1) unused) ∧
    fullResidualLift B x Y Z a₁ a₂ E H Ψ k ζ unused =
      ∫ ξ, α ξ * (X : ℂ)⁻¹ *
        gatedFamilySum B k (ζ - mellinFrequency ξ) (positiveRoots Y) (positiveRoots Y)
          (mellinPairingSource X Z (liftedEndpoint (B.model k ζ) x E (-a₁)) (mellinFrequency ξ))
          (liftedEndpoint (B.model k ζ) x H a₂) (fun _ _ => 1) unused := by
  rw [fullResidualLift_eq_gatedFamilySum]
  exact gatedFamilySum_cutoff_integral B k ζ X Z (positiveRoots Y) (positiveRoots Y)
    (liftedEndpoint (B.model k ζ) x E (-a₁)) (liftedEndpoint (B.model k ζ) x H a₂) unused
    hX hZ (fun n hn => by exact_mod_cast ((mem_positiveRoots Y n).mp hn).1) Ψ α hα hrep

end Erdos821.P5Core
