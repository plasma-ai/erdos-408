import Erdos821.P5.ComparisonSmoothEndpoints
import Erdos821.P5.LongGrowth

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem eventual_comparison_double_cell_width (hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x : ℝ in atTop, 0 < L x ^ (-hexp) ∧ Real.exp (2 * L x ^ (-hexp)) ≤ 2 := by
  have ht := (tendsto_rpow_neg_atTop hh).comp Real.tendsto_log_atTop
  have hlim : 0 < Real.log 2 / 2 := by positivity
  filter_upwards [ht.eventually (eventually_lt_nhds hlim),
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hx hL
  change 0 < L x at hL
  change L x ^ (-hexp) < Real.log 2 / 2 at hx
  refine ⟨Real.rpow_pos_of_pos hL _, ?_⟩
  calc
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = 2 := Real.exp_log (by norm_num)

theorem eventual_comparison_shift_margin (C lo : ℝ) (hlo : 0 < lo) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : ℝ) (k : ℤ),
      x * L x ^ (-C) ≤ Z → |(k : ℝ)| ≤ L x ^ C →
      0 < Z ∧ |(k : ℝ)| ≤ lo * Z / 8 := by
  filter_upwards [eventual_constant_log_power_le_power 1 (2 * C) (8 / lo) (by norm_num)]
    with x hx
  have hL : 0 < L x := by linarith [hx.2.1]
  have hxpos : 0 < x := by linarith [hx.1]
  have hprod : L x ^ (2 * C) * L x ^ (-C) = L x ^ C := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hxbound : (8 / lo) * L x ^ (2 * C) ≤ x := by simpa using hx.2.2
  have hscaled := mul_le_mul_of_nonneg_right hxbound (Real.rpow_nonneg hL.le (-C))
  rw [mul_assoc, hprod] at hscaled
  have hscaled' := mul_le_mul_of_nonneg_left hscaled hlo.le
  have hleft : lo * ((8 / lo) * L x ^ C) = 8 * L x ^ C := by field_simp
  rw [hleft] at hscaled'
  intro Z k hZ hk
  refine ⟨(mul_pos hxpos (Real.rpow_pos_of_pos hL (-C))).trans_le hZ, ?_⟩
  have hZ' := mul_le_mul_of_nonneg_left hZ hlo.le
  nlinarith

theorem comparisonEnergyMark_slot_bound {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (ν : Pattern G.graph J P.ell m) (g : Fin G.size) : ν.t g ≤ P.ell + m := by
  dsimp [Pattern.t]
  exact Nat.add_le_add_left (ν.bound g) P.ell

/-- An actual comparison endpoint always has a designated small mark,
uniformly in the lift depth. Admissibility supplies a nonempty small group. -/
theorem eventual_comparison_small_mark (P : Geometry) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups) (J m : ℕ)
      (ν : Pattern G.graph J P.ell m),
      Admissible P x G → ∃ g ∈ G.small, 1 ≤ ν.t g := by
  filter_upwards [((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)).eventually_gt_atTop (0 : ℝ)]
    with x hx
  change 0 < T x at hx
  intro G J m ν hG
  have hcard : 0 < (G.small.card : ℝ) :=
    (mul_pos P.positive.1 hx).trans_le hG.1.1
  have hcardN : 0 < G.small.card := by exact_mod_cast hcard
  obtain ⟨g, hg⟩ := Finset.card_pos.mp hcardN
  refine ⟨g, hg, ?_⟩
  exact P.marks.trans (Nat.le_add_right _ _)

end Erdos821.P5Core
