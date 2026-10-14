import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Every closed unit interval has a genuine maximizing point for the finite polynomial. -/
theorem dp_unit_interval_max (s : Finset ℕ) (c : ℕ → ℂ) (j : ℤ) :
    ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
      (⨆ u : Set.Icc (j : ℝ) ((j : ℝ) + 1), ‖dp s c u‖ ^ 2) = ‖dp s c t‖ ^ 2 := by
  have hcont : Continuous (fun t : ℝ => ‖dp s c t‖ ^ 2) := (continuous_dp s c).norm.pow 2
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)) hcont.continuousOn
  haveI : Nonempty (Set.Icc (j : ℝ) ((j : ℝ) + 1)) := ⟨⟨t, ht⟩⟩
  have hbounded : BddAbove (Set.range (fun u : Set.Icc (j : ℝ) ((j : ℝ) + 1) =>
      ‖dp s c u‖ ^ 2)) := ⟨‖dp s c t‖ ^ 2, by
    rintro _ ⟨u, rfl⟩
    exact hmax u.property⟩
  refine ⟨t, ht.1, ht.2, le_antisymm ?_ ?_⟩
  · exact ciSup_le (fun u => hmax u.property)
  · exact le_ciSup hbounded ⟨t, ht⟩

/-- The supremum sum is exactly a sum at points in the original closed cells. -/
theorem dp_maximizing_samples (s : Finset ℕ) (c : ℕ → ℂ) (E : Finset ℤ) :
    ∃ t : ℤ → ℝ,
      (∀ j : ℤ, (j : ℝ) ≤ t j ∧ t j ≤ (j : ℝ) + 1) ∧
      (∑ j ∈ E, ⨆ u : Set.Icc (j : ℝ) ((j : ℝ) + 1), ‖dp s c u‖ ^ 2) =
        ∑ j ∈ E, ‖dp s c (t j)‖ ^ 2 := by
  classical
  choose t ht using dp_unit_interval_max s c
  refine ⟨t, fun j => ⟨(ht j).1, (ht j).2.1⟩, ?_⟩
  exact Finset.sum_congr rfl (fun j _ => (ht j).2.2)

end Erdos821.P5Core
