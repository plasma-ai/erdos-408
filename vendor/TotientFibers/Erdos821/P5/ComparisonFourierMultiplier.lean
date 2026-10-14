import Erdos821.P5.ComparisonMinorArcAdapterTask
import Erdos821.P5.ComparisonMellinAlgebra

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem additivePhase_norm (θ : ℝ) : ‖e θ‖ = 1 := by
  simp [e, Complex.norm_exp]

theorem comparisonMultiplier_continuous {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (fA fB : ℕ → ℂ) (k : ℤ) :
    Continuous (comparisonMultiplier ν block h j fA fB k) := by
  unfold comparisonMultiplier e
  fun_prop

/-- Every occupied cell is a restriction of one probability law, so its
multiplier has norm at most one at every frequency. -/
theorem comparisonMultiplier_norm_le_one {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (block : G.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (fA fB : ℕ → ℂ) (k : ℤ) (θ : ℝ)
    (hV : ∀ g, 0 < G.V g) (hf : ∀ n, ‖fA n‖ ≤ 1 ∧ ‖fB n‖ ≤ 1) :
    ‖comparisonMultiplier ν block h j fA fB k θ‖ ≤ 1 := by
  unfold comparisonMultiplier
  calc
    _ ≤ ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j,
        ‖(freeDrawLaw ν u : ℂ) * fA (comparisonFreeProduct ν block false u) *
          fB (comparisonFreeProduct ν block true u) *
          e (-(k : ℝ) * θ * comparisonFreeProduct ν block false u *
            comparisonFreeProduct ν block true u)‖ := norm_sum_le _ _
    _ ≤ ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j, freeDrawLaw ν u := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul, norm_mul, norm_mul, additivePhase_norm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (freeDrawLaw_nonneg ν u (fun g => (hV g).le))]
      calc
        _ ≤ freeDrawLaw ν u * 1 * 1 := by
          have hw := freeDrawLaw_nonneg ν u (fun g => (hV g).le)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hf _).1 hw) (hf _).2
            (norm_nonneg _) (by simpa only [mul_one] using hw)
        _ = _ := by ring
    _ ≤ ∑ u : FreeDraw ν, freeDrawLaw ν u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun u hu hnot => freeDrawLaw_nonneg ν u (fun g => (hV g).le))
    _ = 1 := freeDrawLaw_sum ν (fun g => (hV g).ne')

def comparisonFourierTest {Q : ℕ} (χ : CharacterIndex Q) (U a₁ a₂ v : ℝ)
    (D : ℕ) : ℂ := star (charValue χ D) * comparisonMellinTest U a₁ a₂ v D

theorem comparisonFourierTest_norm_le {Q : ℕ} (χ : CharacterIndex Q)
    (U a₁ a₂ v : ℝ) (D : ℕ) : ‖comparisonFourierTest χ U a₁ a₂ v D‖ ≤ 1 := by
  simpa only [comparisonFourierTest, norm_mul, norm_star,
    comparisonMellinTest_norm, mul_one] using P4Char.norm_part Q χ D

end Erdos821.P5Core
