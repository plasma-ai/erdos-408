import Erdos821.P5.ComparisonCellCounts
import Erdos821.P5.ComparisonCellCostAdapter

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Positive harmonic mass supplies a label in every group. Full ideal
labels may repeat, so there is no condition on the number of slots. -/
theorem admissible_full_big_labels (P : Geometry) (G : PrimeGroups) (x : ℝ)
    (R : ℕ) (hG : Admissible P x G) : Nonempty (G.graph.BigLabels R) := by
  have hne (g : Fin G.size) : (G.primes g).Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm := P.positive.2.2.1.trans_le (hG.2.2.1 g).1
    have hzMass : mass G g = 0 := by simp [mass, hz]
    rw [hzMass] at hm
    exact lt_irrefl 0 hm
  choose p hp using hne
  exact ⟨fun g i => ⟨p g.val, hp g.val⟩⟩

theorem comparison_character_count_le_log_power (x qexp : ℝ) (hL : 0 < L x) :
    ((primitiveCharacters ⌊L x ^ qexp⌋₊).card : ℝ) ^ 2 ≤ L x ^ (4 * qexp) := by
  have hc : ((primitiveCharacters ⌊L x ^ qexp⌋₊).card : ℝ) ≤ (⌊L x ^ qexp⌋₊ : ℝ) ^ 2 := by
    exact_mod_cast P4Char.count_part ⌊L x ^ qexp⌋₊
  have hf : (⌊L x ^ qexp⌋₊ : ℝ) ≤ L x ^ qexp := Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hf0 : (0 : ℝ) ≤ (⌊L x ^ qexp⌋₊ : ℝ) := Nat.cast_nonneg _
  have hp0 := Real.rpow_nonneg hL.le qexp
  have hc' : ((primitiveCharacters ⌊L x ^ qexp⌋₊).card : ℝ) ≤ (L x ^ qexp) ^ 2 :=
    hc.trans (by nlinarith)
  have hn : (0 : ℝ) ≤ (primitiveCharacters ⌊L x ^ qexp⌋₊).card := Nat.cast_nonneg _
  calc
    _ ≤ ((L x ^ qexp) ^ 2) ^ 2 := by nlinarith [sq_nonneg (L x ^ qexp)]
    _ = _ := by
      simp only [pow_two]
      simp_rw [← Real.rpow_add hL]
      congr 1
      ring

/-- The complete cell/character count has a fixed logarithmic cost,
uniformly over all lift depths and actual occupied comparison cells. -/
theorem eventual_comparison_summation_count (P : Geometry) (m : ℕ) (qexp hexp : ℝ)
    (hh : 0 < hexp) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (J ell : ℕ) (ν : Pattern G.graph J ell m)
        (block : G.graph.BigGroup → Bool), Admissible P x G →
        ((comparisonCells ν block (L x ^ (-hexp))).card : ℝ) *
          ((primitiveCharacters ⌊L x ^ qexp⌋₊).card : ℝ) ^ 2 ≤
            L x ^ (2 * (P.d + hexp + 1) + 4 * qexp) := by
  filter_upwards [eventual_comparisonCells_count P m hexp hh,
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hc hL
  change 0 < L x at hL
  intro G J ell ν block hG
  calc
    _ ≤ L x ^ (2 * (P.d + hexp + 1)) * L x ^ (4 * qexp) :=
      mul_le_mul (hc G J ell ν block hG) (comparison_character_count_le_log_power x qexp hL)
        (sq_nonneg _) (Real.rpow_nonneg hL.le _)
    _ = _ := (Real.rpow_add hL _ _).symm

/-- The retained inverse-cell weights are charged to the actual pattern
cost before the bounded cell/character correlations are summed. -/
theorem comparison_cell_character_sum_norm_le_constant
    {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (Q : ℕ) (h ξ K : ℝ)
    (hQ : 1 ≤ Q) (hξ : 0 < ξ) (hc : HasComparisonCoefficient ν block Q h ξ)
    (a₀ : G.BigLabels (J + ell)) (z : SharedDraw ν)
    (f : (ℤ × ℤ) → CharacterIndex Q → CharacterIndex Q → ℂ)
    (hf : ∀ j ∈ comparisonCells ν block h, ∀ χA ∈ primitiveCharacters Q,
      ∀ χB ∈ primitiveCharacters Q, ‖f j χA χB‖ ≤ K) :
    ‖∑ j ∈ comparisonCells ν block h, ∑ χA ∈ primitiveCharacters Q,
      ∑ χB ∈ primitiveCharacters Q,
        (comparisonSign ν * comparisonCellInverse ν block false h ξ j.1 *
          comparisonCellInverse ν block true h ξ j.2) * f j χA χB‖ ≤
      patternCost ν * ((comparisonCells ν block h).card : ℝ) *
        ((primitiveCharacters Q).card : ℝ) ^ 2 * K := by
  apply (comparison_cell_character_sum_norm_le ν block Q h ξ hQ hξ hc a₀ z f).trans
  calc
    _ ≤ patternCost ν * ∑ j ∈ comparisonCells ν block h,
        ∑ χA ∈ primitiveCharacters Q, ∑ χB ∈ primitiveCharacters Q, K := by
      apply mul_le_mul_of_nonneg_left _ (patternCost_nonneg ν)
      exact Finset.sum_le_sum (fun j hj => Finset.sum_le_sum
        (fun χA hχA => Finset.sum_le_sum (fun χB hχB => hf j hj χA hχA χB hχB)))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos821.P5Core
