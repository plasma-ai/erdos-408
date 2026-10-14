import Erdos821.P5.ComparisonArcScales
import Erdos821.P5.ComparisonFourierMultiplier

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- The adapter's avoidance of every rational is supplied by avoiding
the finite boundary-inclusive center set used by the Fourier arc bound. -/
theorem eventual_comparison_finite_minor_arcs
    (hadapter : ComparisonMinorArcAdapterTask) (hminor : MinorArcTask)
    (P : Geometry) (m : ℕ) (C A hexp : ℝ)
    (hC : 0 < C) (hA : 0 < A) (hh : 0 < hexp) :
    ∃ Carc K : ℝ, 0 < Carc ∧ 0 < K ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups) (J ell Q : ℕ) (ν : Pattern G.graph J ell m)
          (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ)
          (χA χB : CharacterIndex Q) (a₁ a₂ v : ℝ) (k : ℤ) (θ : ℝ),
          Admissible P x G →
          (∀ side : Bool, ∃ g : G.graph.BigGroup,
            block g = side ∧ (ν.changed g.val).Nonempty) →
          j ∈ comparisonCells ν block (L x ^ (-hexp)) →
          k ≠ 0 → |(k : ℝ)| ≤ L x ^ C → θ ∈ Set.Icc (0 : ℝ) 1 →
          (∀ c ∈ rationalArcCenters ⌊L x ^ Carc⌋₊,
            L x ^ Carc / comparisonJointScale (L x ^ (-hexp)) j < |θ - c|) →
          ‖comparisonMultiplier ν block (L x ^ (-hexp)) j
            (comparisonFourierTest χA (comparisonCellScale (L x ^ (-hexp)) j.1) a₁ a₂ v)
            (comparisonFourierTest χB (comparisonCellScale (L x ^ (-hexp)) j.2) a₁ a₂ v)
            k θ‖ ≤ K * L x ^ (-A) := by
  obtain ⟨Carc, K, hCarc, hK, hx⟩ := hadapter hminor P m C A hexp hC hA hh
  refine ⟨Carc, K, hCarc, hK, ?_⟩
  filter_upwards [hx, eventual_comparison_arc_scales P m hexp Carc hh hCarc]
    with x hx hscale
  intro G J ell Q ν block j χA χB a₁ a₂ v k θ hG hne hj hk hkb hθ haway
  have hwidth := (hscale.2.2 G J ell ν block j hG hne hj).2.1
  apply hx G J ell ν block j _ _ k θ hG hne hj
    (fun n => ⟨comparisonFourierTest_norm_le _ _ _ _ _ n,
      comparisonFourierTest_norm_le _ _ _ _ _ n⟩) hk hkb
  exact rationalArcCenters_avoid_real_bound (L x ^ Carc) θ
    (L x ^ Carc / comparisonJointScale (L x ^ (-hexp)) j) hθ hwidth haway

end Erdos821.P5Core
