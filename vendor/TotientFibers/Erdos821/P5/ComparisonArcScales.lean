import Erdos821.P5.RationalArcCenters
import Erdos821.P5.ComparisonScaleAsymptotics
import Erdos821.P5.LongGrowth

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem eventual_log_power_le_half_label_scale (c A : ℝ) (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ L x ∧ L x ^ A ≤ Real.exp (L x ^ c / 2) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventual_log_le_rpow_mul c (1 / (2 * A)) hc (by positivity))] with x hx
  change 1 ≤ L x ∧ Real.log (L x) ≤ 1 / (2 * A) * L x ^ c at hx
  have hL : 0 < L x := by linarith [hx.1]
  refine ⟨hx.1, ?_⟩
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right hx.2 hA.le
  have he : (1 / (2 * A)) * L x ^ c * A = L x ^ c / 2 := by field_simp
  rwa [he] at hm

/-- The rational arcs have the width and local-energy scale needed by §4.
All bounds are uniform over occupied comparison cells and lift depths. -/
theorem eventual_comparison_arc_scales (P : Geometry) (m : ℕ) (hexp Carc : ℝ)
    (hh : 0 < hexp) (hCarc : 0 < Carc) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧
      ∀ (G : PrimeGroups) (J ell : ℕ) (ν : Pattern G.graph J ell m)
        (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ),
        Admissible P x G →
        (∀ side : Bool, ∃ g : G.graph.BigGroup,
          block g = side ∧ (ν.changed g.val).Nonempty) →
        j ∈ comparisonCells ν block (L x ^ (-hexp)) →
        let H' := comparisonJointScale (L x ^ (-hexp)) j
        0 < L x ^ Carc / H' ∧ L x ^ Carc / H' < 1 ∧
          Real.exp (L x ^ P.c / 2) ≤ H' / L x ^ Carc ∧
          H' / L x ^ Carc ≤ x ^ (0.01 : ℝ) ∧
          ((rationalArcCenters ⌊L x ^ Carc⌋₊).card : ℝ) ≤ 4 * L x ^ (2 * Carc) := by
  have hc : 0 < P.c := by rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩; linarith
  filter_upwards [eventual_comparisonJointScale_bounds P m hexp (0.01 : ℝ) hh (by norm_num),
    eventual_log_power_le_half_label_scale P.c Carc hc hCarc] with x hscale hpow
  have hL : 0 < L x := by linarith [hpow.1]
  have hLp : 0 < L x ^ Carc := Real.rpow_pos_of_pos hL _
  have hLp1 : 1 ≤ L x ^ Carc := Real.one_le_rpow hpow.1 hCarc.le
  refine ⟨hscale.1, hpow.1, ?_⟩
  intro G J ell ν block j hG hne hj
  dsimp only
  let H' := comparisonJointScale (L x ^ (-hexp)) j
  have hHpos : 0 < H' := comparisonJointScale_pos _ _
  obtain ⟨hHlo, hHhi⟩ := hscale.2.2 G J ell ν block j hG hne hj
  have hH : L x ^ Carc < H' := hpow.2.trans_lt
    ((Real.exp_lt_exp.mpr (by linarith [Real.rpow_pos_of_pos hL P.c])).trans_le hHlo)
  refine ⟨div_pos hLp hHpos, (div_lt_one hHpos).mpr hH, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hLp).mpr
    calc
      _ ≤ Real.exp (L x ^ P.c / 2) * Real.exp (L x ^ P.c / 2) :=
        mul_le_mul_of_nonneg_left hpow.2 (Real.exp_pos _).le
      _ = Real.exp (L x ^ P.c) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hHlo
  · exact (div_le_self hHpos.le hLp1).trans hHhi
  · have h := rationalArcCenters_card_real_le (L x ^ Carc) hLp1
    apply h.trans
    rw [pow_two, ← Real.rpow_add hL]
    have he : Carc + Carc = 2 * Carc := by ring
    rw [he]

end Erdos821.P5Core
