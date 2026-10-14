import Erdos821.P5.ComparisonCellCounts
import Erdos821.S34.ComparisonGeometry

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem eventual_comparisonCellSupport (hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : Blueprint.Graph.PrimeGroups) (J ell m : ℕ) (ν : Pattern G J ell m)
        (block : G.BigGroup → Bool) (side : Bool) (u : FreeDraw ν),
        comparisonCellScale (L x ^ (-hexp))
          (cell (L x ^ (-hexp)) (comparisonFreeProduct ν block side u)) ≤
            (comparisonFreeProduct ν block side u : ℝ) ∧
        (comparisonFreeProduct ν block side u : ℝ) ≤ 2 *
          comparisonCellScale (L x ^ (-hexp))
            (cell (L x ^ (-hexp)) (comparisonFreeProduct ν block side u)) := by
  filter_upwards [S34Core.eventually_cell_width hexp hh] with x hx
  intro G J ell m ν block side u
  obtain ⟨hlo, hhi⟩ := comparisonCellScale_bounds _ hx.1 _
    (comparisonFreeProduct_pos ν block side u)
  have he : Real.exp (L x ^ (-hexp)) ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hx.2
  exact ⟨hlo, hhi.le.trans (mul_le_mul_of_nonneg_right he (comparisonCellScale_pos _ _).le)⟩

/-- Each nonempty free block has a cell scale exceeding every fixed log power. -/
theorem eventual_comparisonCellScale_large (P : Geometry) (A hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups) (J ell m : ℕ)
      (ν : Pattern G.graph J ell m) (block : G.graph.BigGroup → Bool)
      (side : Bool) (u : FreeDraw ν), Admissible P x G →
      (∃ g : G.graph.BigGroup, block g = side ∧ (ν.changed g.val).Nonempty) →
      L x ^ A ≤ comparisonCellScale (L x ^ (-hexp))
        (cell (L x ^ (-hexp)) (comparisonFreeProduct ν block side u)) := by
  have hc : 0 < P.c := by rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩; linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  filter_upwards [S34Core.eventually_cell_width hexp hh,
    S34Core.eventually_power_le_label_scale A P.c (Real.exp (-1)) hc (Real.exp_pos _)]
    with x hwidth hlarge
  intro G J ell m ν block side u hG hne
  have h := admissible_comparisonCellScale_lower P G x ν block side u _ hwidth.1 hG hne
  calc
    _ ≤ Real.exp (-1) * Real.exp (L x ^ P.c) := hlarge
    _ = Real.exp (L x ^ P.c - 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (L x ^ P.c - L x ^ (-hexp)) :=
      Real.exp_le_exp.mpr (by linarith [hwidth.2.trans hlog2])
    _ ≤ _ := h

/-- Exact §4 comparison scales, uniformly over every J and occupied cell.
The polynomial-in-log upper exponent depends on m only. -/
theorem eventual_comparisonJointScale_bounds (P : Geometry) (m : ℕ) (hexp γ : ℝ)
    (hh : 0 < hexp) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ L x ∧
      ∀ (G : PrimeGroups) (J ell : ℕ) (ν : Pattern G.graph J ell m)
        (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ), Admissible P x G →
        (∀ side : Bool, ∃ g : G.graph.BigGroup,
          block g = side ∧ (ν.changed g.val).Nonempty) →
        j ∈ comparisonCells ν block (L x ^ (-hexp)) →
        Real.exp (L x ^ P.c) ≤ comparisonJointScale (L x ^ (-hexp)) j ∧
          comparisonJointScale (L x ^ (-hexp)) j ≤ x ^ γ := by
  let β := 4 * (m : ℝ) * P.C₀
  have hC₀ := P.positive.2.1
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hβ1 : 0 < β + 1 := by linarith
  have hr : 0 < 1 - P.d := by linarith [P.ordered.2.2.2.2]
  have hc : 0 < P.c := by rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩; linarith
  have hLc := ((tendsto_rpow_atTop hc).comp Real.tendsto_log_atTop).eventually_ge_atTop (2 : ℝ)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he := Real.tendsto_log_atTop.eventually
    (eventual_log_le_rpow_mul (1 - P.d) (γ / (β + 1)) hr (div_pos hγ hβ1))
  filter_upwards [he, hLc, S34Core.eventually_cell_width hexp hh,
    eventually_ge_atTop (1 : ℝ)] with x hlog hLc hwidth hx
  change 2 ≤ L x ^ P.c at hLc
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hlog.1
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hβc : β * (γ / (β + 1)) ≤ γ := by
    calc
      _ ≤ (β + 1) * (γ / (β + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_pos hγ hβ1).le
      _ = γ := by field_simp
  have hpow : L x ^ (1 - P.d) * L x ^ P.d = L x := by
    rw [← Real.rpow_add hLpos]
    simp
  have hlinear : β * T x * L x ^ P.d ≤ γ * L x := by
    calc
      _ ≤ β * (γ / (β + 1) * L x ^ (1 - P.d)) * L x ^ P.d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog.2 hβ)
          (Real.rpow_nonneg hLpos.le _)
      _ = (β * (γ / (β + 1))) * (L x ^ (1 - P.d) * L x ^ P.d) := by ring
      _ = (β * (γ / (β + 1))) * L x := by rw [hpow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hβc hLpos.le
  refine ⟨hx, hlog.1, ?_⟩
  intro G J ell ν block j hG hne hj
  obtain ⟨hlo, hhi⟩ := admissible_comparisonJointScale_bounds P G x ν block _
    hwidth.1 hlog.1 hG hne j hj
  constructor
  · exact (Real.exp_le_exp.mpr (by linarith [hwidth.2.trans hlog2])).trans hlo
  · apply hhi.trans
    rw [Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    simpa only [β, L, mul_comm] using hlinear

/-- Multiplying by the allowed Z range gives Y=x^(1+o(1)), uniformly in J. -/
theorem eventual_comparisonY_range (P : Geometry) (m : ℕ) (hexp C γ : ℝ)
    (hh : 0 < hexp) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (J ell : ℕ) (ν : Pattern G.graph J ell m)
        (block : G.graph.BigGroup → Bool) (j : ℤ × ℤ) (Z : ℝ), Admissible P x G →
        (∀ side : Bool, ∃ g : G.graph.BigGroup,
          block g = side ∧ (ν.changed g.val).Nonempty) →
        j ∈ comparisonCells ν block (L x ^ (-hexp)) →
        x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
        x ^ (1 - γ) ≤ Z * comparisonJointScale (L x ^ (-hexp)) j ∧
          Z * comparisonJointScale (L x ^ (-hexp)) j ≤ x ^ (1 + γ) := by
  filter_upwards [eventual_comparisonJointScale_bounds P m hexp (γ / 2) hh (by positivity),
    eventual_log_power_le_power (γ / 2) C (by positivity),
    eventual_negative_power_le_log_power γ C hγ] with x hscale hlog hneg
  intro G J ell ν block j Z hG hne hj hZlo hZhi
  have hxpos : 0 < x := by linarith [hscale.1]
  have hLpos : 0 < L x := by linarith [hscale.2.1]
  obtain ⟨hHlo, hHhi⟩ := hscale.2.2 G J ell ν block j hG hne hj
  have hH1 : 1 ≤ comparisonJointScale (L x ^ (-hexp)) j :=
    (Real.one_le_exp_iff.mpr (Real.rpow_nonneg hLpos.le _)).trans hHlo
  have hZpos : 0 < Z := (mul_pos hxpos (Real.rpow_pos_of_pos hLpos (-C))).trans_le hZlo
  constructor
  · calc
      _ = x * x ^ (-γ) := by
        rw [show 1 - γ = 1 + (-γ) by ring, Real.rpow_add hxpos, Real.rpow_one]
      _ ≤ x * L x ^ (-C) := mul_le_mul_of_nonneg_left hneg.2.2 hxpos.le
      _ ≤ Z := hZlo
      _ ≤ _ := le_mul_of_one_le_right hZpos.le hH1
  · calc
      _ ≤ (x * L x ^ C) * x ^ (γ / 2) :=
        mul_le_mul hZhi hHhi (comparisonJointScale_pos _ _).le (by positivity)
      _ ≤ (x * x ^ (γ / 2)) * x ^ (γ / 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog.2.2 hxpos.le) (Real.rpow_nonneg hxpos.le _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hxpos,
          show γ / 2 + γ / 2 = γ by ring]
        rw [Real.rpow_add hxpos, Real.rpow_one]

end Erdos821.P5Core
