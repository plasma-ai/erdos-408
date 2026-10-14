import Erdos821.P5.MellinFamilySum

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

/-- Exact finite-family inversion before any estimates or pattern stripping. -/
theorem gatedFamilySum_cutoff_integral {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ X Z : ℝ) (S T : Finset ℤ)
    (f g : ℤ → ℂ) (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hX : X ≠ 0) (hZ : 0 < Z) (hS : ∀ n ∈ S, 0 < (n : ℝ))
    (Ψ : ℝ → ℂ) (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    Integrable (fun ξ => α ξ * (X : ℂ)⁻¹ *
      gatedFamilySum B k (ζ - mellinFrequency ξ) S T
        (mellinPairingSource X Z f (mellinFrequency ξ)) g (fun _ _ => 1) unused) ∧
    gatedFamilySum B k ζ S T f g (harmonicCutoff Ψ Z) unused =
      ∫ ξ, α ξ * (X : ℂ)⁻¹ *
        gatedFamilySum B k (ζ - mellinFrequency ξ) S T
          (mellinPairingSource X Z f (mellinFrequency ξ)) g (fun _ _ => 1) unused := by
  let H := fun v u n a b ξ => α ξ * mellinGatedTerm B k ζ X Z (B.pattern v)
    (assembleAux (B.pattern v) u (unused v)) T f g (mellinFrequency ξ) n a b
  have hH v u n (hn : n ∈ S) a b : Integrable (H v u n a b) :=
    mellin_gated_integrable B k ζ X Z (B.pattern v)
      (assembleAux (B.pattern v) u (unused v)) T f g n a b hX hZ (hS n hn) α hα
  have heq : (fun ξ => α ξ * (X : ℂ)⁻¹ *
      gatedFamilySum B k (ζ - mellinFrequency ξ) S T
        (mellinPairingSource X Z f (mellinFrequency ξ)) g (fun _ _ => 1) unused) =
      (fun ξ => ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v),
        (freeDrawLaw (B.pattern v) u : ℂ) *
        ∑ n ∈ S, ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell), H v u n a b ξ) := by
    funext ξ
    unfold gatedFamilySum
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    dsimp only [H, mellinGatedTerm]
    ring
  constructor
  · rw [heq]
    exact integrable_family_sum B S H hH
  · rw [heq, integral_family_sum B S H hH]
    unfold gatedFamilySum
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact gated_cutoff_eq_mellin_integral B k ζ X Z (B.pattern v)
      (assembleAux (B.pattern v) u (unused v)) T f g n a b hX hZ (hS n hn) Ψ α hrep

/-- The cutoff-bearing physical lift on a dyad is an integral of actual P3
pairings, with every product dependence inside the shifted model. -/
theorem dyadic_cutoff_eq_pairing_integral {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ X Z : ℝ) (T : Finset ℤ)
    (f g : ℤ → ℂ) (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hV : ∀ g, G.V g ≠ 0) (hX : 0 < X) (hZ : 0 < Z)
    (Ψ : ℝ → ℂ) (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    Integrable (fun ξ => α ξ * (X : ℂ)⁻¹ *
      (B.model k (ζ - mellinFrequency ξ)).pairing X (T.product Finset.univ)
        (mellinPairingSource X Z f (mellinFrequency ξ)) (fun z => g z.1)) ∧
    gatedFamilySum B k ζ (dyad X) T f g (harmonicCutoff Ψ Z) unused =
      ∫ ξ, α ξ * (X : ℂ)⁻¹ *
        (B.model k (ζ - mellinFrequency ξ)).pairing X (T.product Finset.univ)
          (mellinPairingSource X Z f (mellinFrequency ξ)) (fun z => g z.1) := by
  have hS : ∀ n ∈ dyad X, 0 < (n : ℝ) := by
    intro n hn
    exact hX.trans_le ((Int.ceil_le.mp (Finset.mem_Ico.mp hn).1))
  have h := gatedFamilySum_cutoff_integral B k ζ X Z (dyad X) T f g unused
    hX.ne' hZ hS Ψ α hα hrep
  simp_rw [gatedFamilySum_eq_pairing B k _ X T _ g hV unused] at h
  exact h

end Erdos821.P5Core
