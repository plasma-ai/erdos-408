import Erdos821.P5.ComparisonMellinIntegral
import Erdos821.P5.ComparisonSupport

noncomputable section
open scoped BigOperators Classical
open Filter MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The coupled cutoff and its root interval are both separated on the
actual comparison cell. The remaining interval depends only on Y=Z*H'. -/
theorem comparison_cutoff_cell_eq_common_separated_integral
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
    (x Z a₁ a₂ lo hi : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hk : |(k : ℝ)| ≤ lo * Z / 8) (hs : Function.support Ψ ⊆ Set.Icc lo hi)
    (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    comparisonCellCorrelation ν block h j χA χB x Z a₁ a₂ E H Ψ k
      (fun u => cutoffRoots lo hi Z (freeDrawProduct ν u)) =
      ∫ ξ, α ξ * separatedComparisonCellCorrelation ν block h j χA χB
        x (Z * comparisonJointScale h j) a₁ a₂ (mellinFrequency ξ) E H k
        (fun _ => comparisonCommonRoots lo hi (Z * comparisonJointScale h j)) := by
  rw [comparisonCellCorrelation_eq_common_roots ν block h hh hwidth j χA χB z
    x Z a₁ a₂ lo hi E H Ψ k hlo hhi hZ hs]
  apply comparisonCellCorrelation_eq_separated_integral ν block h j χA χB
    x Z a₁ a₂ E H Ψ k _ z hZ _ α hα hrep
  intro u hu n hn
  exact comparison_common_root_positivity ν block h hh hwidth j u z hu
    lo hi Z k hlo hZ hk n hn

/-- The comparison separation has fixed Fourier mass and frequency costs
before the requested tail saving. It uses the proved P1 separation input. -/
theorem comparison_cutoff_separation (hsep : Blueprint.FourierSeparation)
    (C lo hi : ℝ) (bounds : ℕ → ℝ)
    (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Cf K : ℝ, 0 < Cf ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧
        ∀ᶠ x : ℝ in atTop, ∀ Ψ : ℝ → ℂ,
          CutoffBound x C lo hi Ψ bounds →
          ∃ α : (Fin 1 → ℝ) → ℂ,
            Integrable α ∧ (∫ ξ, ‖α ξ‖) ≤ L x ^ K ∧
            (∫ ξ in {ξ : Fin 1 → ℝ | L x ^ Cf < ‖ξ‖}, ‖α ξ‖) ≤ KA * L x ^ (-A) ∧
            ∀ (P : Geometry) (G : PrimeGroups) (J m Q : ℕ)
              (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
              (h : ℝ) (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
              (Z a₁ a₂ : ℝ) (E H : Endpoint) (k : ℤ),
              0 < h → Real.exp (2 * h) ≤ 2 → 0 < Z → |(k : ℝ)| ≤ lo * Z / 8 →
              comparisonCellCorrelation ν block h j χA χB x Z a₁ a₂ E H Ψ k
                (fun u => cutoffRoots lo hi Z (freeDrawProduct ν u)) =
                ∫ ξ, α ξ * separatedComparisonCellCorrelation ν block h j χA χB
                  x (Z * comparisonJointScale h j) a₁ a₂ (mellinFrequency ξ) E H k
                  (fun _ => comparisonCommonRoots lo hi (Z * comparisonJointScale h j)) := by
  obtain ⟨Cf, K, hCf, hK, hsepA⟩ := mellinCutoffTask_proof hsep C lo hi bounds hC hlo hhi hb
  refine ⟨Cf, K, hCf, hK, ?_⟩
  intro A hA
  obtain ⟨KA, hKA, hcut⟩ := hsepA A hA
  refine ⟨KA, hKA, ?_⟩
  filter_upwards [hcut] with x hx
  intro Ψ hΨ
  obtain ⟨α, hα, hmass, hrep, htail⟩ := hx Ψ hΨ
  refine ⟨α, hα, hmass, htail, ?_⟩
  intro P G J m Q ν block h j χA χB z Z a₁ a₂ E H k hh hwidth hZ hk
  exact comparison_cutoff_cell_eq_common_separated_integral ν block h hh hwidth
    j χA χB z x Z a₁ a₂ lo hi E H Ψ k hlo hhi hZ hk hΨ.2.1 α hα hrep

end Erdos821.P5Core
