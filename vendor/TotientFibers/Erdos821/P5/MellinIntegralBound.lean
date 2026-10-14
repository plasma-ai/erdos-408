import Erdos821.P5.DyadicAbsoluteBound
import Erdos821.P5.ResidualFamilyMainBound

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem mellin_main_tail_integral_bound (α F : (Fin 1 → ℝ) → ℂ)
    (hα : Integrable α) (hI : Integrable (fun ξ => α ξ * F ξ))
    (S : Set (Fin 1 → ℝ)) (hS : MeasurableSet S) (M R : ℝ) (hM : 0 ≤ M)
    (hmain : ∀ ξ ∈ S, ‖F ξ‖ ≤ M) (hall : ∀ ξ, ‖F ξ‖ ≤ R) :
    ‖∫ ξ, α ξ * F ξ‖ ≤ (∫ ξ, ‖α ξ‖) * M + (∫ ξ in Sᶜ, ‖α ξ‖) * R := by
  rw [← integral_add_compl hS hI]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · calc
      _ ≤ ∫ ξ in S, ‖α ξ‖ * M := norm_integral_le_of_norm_le
        (hα.norm.integrableOn.mul_const M) (by
          filter_upwards [ae_restrict_mem hS] with ξ hξ
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hmain ξ hξ) (norm_nonneg _))
      _ = (∫ ξ in S, ‖α ξ‖) * M := integral_mul_const M _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (setIntegral_le_integral hα.norm (Filter.Eventually.of_forall (fun ξ => norm_nonneg _))) hM
  · calc
      _ ≤ ∫ ξ in Sᶜ, ‖α ξ‖ * R := norm_integral_le_of_norm_le
        (hα.norm.integrableOn.mul_const R) (Filter.Eventually.of_forall (fun ξ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hall ξ) (norm_nonneg _)))
      _ = _ := integral_mul_const R _

/-- Main-frequency and absolute dyadic estimates pass to the actual full
lift, with exactly one factor equal to the number of retained dyads. -/
theorem fullResidualLift_norm_le_main_tail {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Family P.graph G.graph J m) (x Z a₁ a₂ C τ η : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hE : EndpointBound x C τ η E) (hsmall : 2 * x ^ (τ / 2) ≤ x ^ τ)
    (hV : ∀ g, G.graph.V g ≠ 0) (hZ : 0 < Z)
    (hD : ∀ i ∈ retainedSourceDyads x τ, ∀ v a u,
      |(k : ℝ)| * ((B.pattern v).D a u : ℝ) ≤ (2 : ℝ) ^ i / 2)
    (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ))
    (S : Set (Fin 1 → ℝ)) (hS : MeasurableSet S) (M R : ℝ) (hM : 0 ≤ M)
    (hmain : ∀ ξ ∈ S, ∀ i ∈ retainedSourceDyads x τ,
      ‖dyadicMellinPairing B x Z a₁ a₂ E H k ζ i (mellinFrequency ξ)‖ ≤ M)
    (hall : ∀ ξ, ∀ i ∈ retainedSourceDyads x τ,
      ‖dyadicMellinPairing B x Z a₁ a₂ E H k ζ i (mellinFrequency ξ)‖ ≤ R) :
    ‖fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused‖ ≤
      (retainedSourceDyads x τ).card *
        ((∫ ξ, ‖α ξ‖) * M + (∫ ξ in Sᶜ, ‖α ξ‖) * R) := by
  have hfull := fullResidualLift_dyadic_mellin_integral B x Z a₁ a₂ C τ η E H Ψ k ζ unused
    hE hsmall hV hZ hD α hα hrep
  let F := fun ξ => ∑ i ∈ retainedSourceDyads x τ,
    dyadicMellinPairing B x Z a₁ a₂ E H k ζ i (mellinFrequency ξ)
  have hmain' (ξ : Fin 1 → ℝ) (hξ : ξ ∈ S) :
      ‖F ξ‖ ≤ (retainedSourceDyads x τ).card * M := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ i ∈ retainedSourceDyads x τ, M := Finset.sum_le_sum (fun i hi => hmain ξ hξ i hi)
      _ = _ := by simp
  have hall' (ξ : Fin 1 → ℝ) : ‖F ξ‖ ≤ (retainedSourceDyads x τ).card * R := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ i ∈ retainedSourceDyads x τ, R := Finset.sum_le_sum (fun i hi => hall ξ i hi)
      _ = _ := by simp
  rw [hfull.2]
  have hb := mellin_main_tail_integral_bound α F hα hfull.1 S hS
    ((retainedSourceDyads x τ).card * M) ((retainedSourceDyads x τ).card * R)
    (mul_nonneg (Nat.cast_nonneg _) hM) hmain' hall'
  exact hb.trans_eq (by ring)

end Erdos821.P5Core
