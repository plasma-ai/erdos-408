import Erdos821.P5.MellinPairingAlgebra

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

def mellinFrequency (ξ : Fin 1 → ℝ) : ℝ := 2 * Real.pi * ξ 0

def mellinGatedTerm {F : FixedData} {G : Blueprint.Graph.PrimeGroups} {J m : ℕ}
    (B : Family F G J m) (k : ℤ) (ζ X Z : ℝ) (ν : Pattern G J F.ell m)
    (u : G.Aux J) (T : Finset ℤ) (f g : ℤ → ℂ) (v : ℝ)
    (n : ℤ) (a b : G.Labels (J + F.ell)) : ℂ :=
  (X : ℂ)⁻¹ * gatedPatternTerm (B.model k (ζ - v)) ν u T
    (mellinPairingSource X Z f v) g (fun _ _ => 1) n a b

theorem mellin_gated_integrable {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ X Z : ℝ)
    (ν : Pattern G J F.ell m) (u : G.Aux J) (T : Finset ℤ)
    (f g : ℤ → ℂ) (n : ℤ) (a b : G.Labels (J + F.ell))
    (hX : X ≠ 0) (hZ : 0 < Z) (hn : 0 < (n : ℝ))
    (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α) :
    Integrable (fun ξ => α ξ * mellinGatedTerm B k ζ X Z ν u T f g
      (mellinFrequency ξ) n a b) := by
  let y := (n : ℝ) / (Z * (ν.D a u : ℝ))
  have hc : Continuous (fun ξ : Fin 1 → ℝ => mellin y (mellinFrequency ξ)) := by
    exact (continuous_mellin y).comp (by unfold mellinFrequency; fun_prop)
  have hi : Integrable (fun ξ : Fin 1 → ℝ => α ξ * mellin y (mellinFrequency ξ)) :=
    hα.mul_bdd (c := 1) hc.aestronglyMeasurable (by filter_upwards with ξ; simp)
  have heq : (fun ξ => α ξ * mellinGatedTerm B k ζ X Z ν u T f g
      (mellinFrequency ξ) n a b) =
      (fun ξ => (α ξ * mellin y (mellinFrequency ξ)) *
        (gatedPatternTerm (B.model k ζ) ν u T f g (fun _ _ => 1) n a b / (n : ℂ))) := by
    funext ξ
    unfold mellinGatedTerm
    rw [normalized_mellin_gated_term B k ζ _ X Z ν u T f g n a b hX hZ hn]
    dsimp only [y]
    ring
  rw [heq]
  exact hi.mul_const _

/-- Fourier inversion inside one physical pattern, with its full product,
ban, physical lists and signed target gate retained. -/
theorem gated_cutoff_eq_mellin_integral {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ X Z : ℝ)
    (ν : Pattern G J F.ell m) (u : G.Aux J) (T : Finset ℤ)
    (f g : ℤ → ℂ) (n : ℤ) (a b : G.Labels (J + F.ell))
    (hX : X ≠ 0) (hZ : 0 < Z) (hn : 0 < (n : ℝ))
    (Ψ : ℝ → ℂ) (α : (Fin 1 → ℝ) → ℂ)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    gatedPatternTerm (B.model k ζ) ν u T f g (harmonicCutoff Ψ Z) n a b =
      ∫ ξ, α ξ * mellinGatedTerm B k ζ X Z ν u T f g (mellinFrequency ξ) n a b := by
  have hD : 0 < (ν.D a u : ℝ) := by
    rw [pattern_D_split]
    exact_mod_cast Nat.mul_pos (sharedProduct_pos ν a) (freeProduct_pos ν u)
  have hw : gatedPatternTerm (B.model k ζ) ν u T f g (harmonicCutoff Ψ Z) n a b =
      Ψ ((n : ℝ) / (Z * (ν.D a u : ℝ))) *
        (gatedPatternTerm (B.model k ζ) ν u T f g (fun _ _ => 1) n a b / (n : ℂ)) := by
    unfold gatedPatternTerm harmonicCutoff
    ring
  rw [hw, hrep _ (div_pos hn (mul_pos hZ hD)), ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold mellinGatedTerm
  rw [normalized_mellin_gated_term B k ζ _ X Z ν u T f g n a b hX hZ hn]
  ring

end Erdos821.P5Core
