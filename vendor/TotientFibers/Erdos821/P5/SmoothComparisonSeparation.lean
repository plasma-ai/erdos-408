import Erdos821.P5.SmoothComparisonIntegral
import Erdos821.P5.SmoothComparisonParameters

noncomputable section
open scoped BigOperators Classical
open Filter MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Quantitative smooth endpoint separation with all cell-width and signed
shift gates discharged eventually. Its fixed frequency/mass costs precede
the requested tail saving and the lift depth. -/
theorem comparison_smooth_cutoff_separation (hsep : Blueprint.FourierSeparation)
    (C lo hi hexp : ℝ) (bounds : ℕ → ℝ)
    (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) (hh : 0 < hexp)
    (hb : ∀ j, 0 ≤ bounds j) :
    ∃ Cf K : ℝ, 0 < Cf ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧
        ∀ᶠ x : ℝ in atTop, ∀ Ψ : ℝ → ℂ,
          CutoffBound x C lo hi Ψ bounds →
          ∃ α : (Fin 1 → ℝ) → ℂ,
            Integrable α ∧ (∫ ξ, ‖α ξ‖) ≤ L x ^ K ∧
            (∫ ξ in {ξ : Fin 1 → ℝ | L x ^ Cf < ‖ξ‖}, ‖α ξ‖) ≤ KA * L x ^ (-A) ∧
            ∀ (P : Geometry) (G : PrimeGroups) (J m Q : ℕ)
              (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
              (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
              (Z a₁ a₂ : ℝ) (E H : Endpoint) (k : ℤ),
              x * L x ^ (-C) ≤ Z → |(k : ℝ)| ≤ L x ^ C →
              comparisonCellCorrelation ν block (L x ^ (-hexp)) j χA χB x Z a₁ a₂ E H Ψ k
                (fun u => cutoffRoots lo hi Z (freeDrawProduct ν u)) =
                ∫ ξ, α ξ * smoothComparisonCellCorrelation ν block (L x ^ (-hexp)) j χA χB
                  x (Z * comparisonJointScale (L x ^ (-hexp)) j) a₁ a₂ (mellinFrequency ξ)
                  lo hi hlo hhi E H k := by
  obtain ⟨Cf, K, hCf, hK, hsepA⟩ := mellinCutoffTask_proof hsep C lo hi bounds hC hlo hhi hb
  refine ⟨Cf, K, hCf, hK, ?_⟩
  intro A hA
  obtain ⟨KA, hKA, hcut⟩ := hsepA A hA
  refine ⟨KA, hKA, ?_⟩
  filter_upwards [hcut, eventual_comparison_double_cell_width hexp hh,
    eventual_comparison_shift_margin C lo hlo] with x hx hwidth hmargin
  intro Ψ hΨ
  obtain ⟨α, hα, hmass, hrep, htail⟩ := hx Ψ hΨ
  refine ⟨α, hα, hmass, htail, ?_⟩
  intro P G J m Q ν block j χA χB z Z a₁ a₂ E H k hZ hk
  obtain ⟨hZpos, hk8⟩ := hmargin Z k hZ hk
  exact comparisonCellCorrelation_eq_smooth_integral ν block _ hwidth.1 hwidth.2 j χA χB z
    x Z a₁ a₂ lo hi E H Ψ k hlo hhi hZpos hk8 hΨ.2.1 α hα hrep

end Erdos821.P5Core
