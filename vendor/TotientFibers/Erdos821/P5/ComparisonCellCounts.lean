import Erdos821.P5.ComparisonCellScales
import Erdos821.S34.CellCount
import Erdos821.S34.ScaleGrowth

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

def comparisonSideCells {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool) (h : ℝ) : Finset ℤ :=
  Finset.univ.image (fun u : FreeDraw ν => cell h (comparisonFreeProduct ν block side u))

theorem comparisonCells_subset_side_product {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (h : ℝ) :
    comparisonCells ν block h ⊆
      (comparisonSideCells ν block false h).product (comparisonSideCells ν block true h) := by
  intro j hj
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨u, hu, rfl⟩,
    Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

theorem comparisonCells_card_le {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (h R : ℝ)
    (hR : 0 ≤ R)
    (hc : ∀ side : Bool, ((comparisonSideCells ν block side h).card : ℝ) ≤ R) :
    ((comparisonCells ν block h).card : ℝ) ≤ R ^ 2 := by
  have hcard := Finset.card_le_card (comparisonCells_subset_side_product ν block h)
  have hcardR : ((comparisonCells ν block h).card : ℝ) ≤
      (comparisonSideCells ν block false h).card * (comparisonSideCells ν block true h).card := by
    simp only [Finset.product_eq_sprod, Finset.card_product] at hcard
    exact_mod_cast hcard
  exact hcardR.trans (by
    rw [pow_two]
    exact mul_le_mul (hc false) (hc true) (Nat.cast_nonneg _) hR)

theorem admissible_comparisonSideCells_count (P : Geometry) (G : PrimeGroups) (x : ℝ)
    {J ell m : ℕ} (ν : Pattern G.graph J ell m) (block : G.graph.BigGroup → Bool)
    (side : Bool) (h : ℝ) (hh : 0 < h) (hL : 1 ≤ L x) (hG : Admissible P x G) :
    ((comparisonSideCells ν block side h).card : ℝ) ≤
      (2 * (m : ℝ) * P.C₀ * T x * L x ^ P.d) / h + 1 := by
  have hT : 0 ≤ T x := Real.log_nonneg hL
  have hC₀ := P.positive.2.1
  apply S34Core.occupied_cell_count (comparisonFreeProduct ν block side) h _ hh
  · positivity
  · exact fun u => admissible_comparisonFreeProduct_log_le P G x ν block side u hL hG

/-- The logarithmic cell count is uniform over all full lift depths J. -/
theorem eventual_comparisonSideCells_count (P : Geometry) (m : ℕ) (hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups) (J ell : ℕ) (ν : Pattern G.graph J ell m)
      (block : G.graph.BigGroup → Bool) (side : Bool),
      Admissible P x G →
      ((comparisonSideCells ν block side (L x ^ (-hexp))).card : ℝ) ≤
        L x ^ (P.d + hexp + 1) := by
  have hC₀ := P.positive.2.1
  have hd : 0 < P.d := by
    have ho := P.ordered
    linarith [ho.1, ho.2.1, ho.2.2.1, ho.2.2.2.1]
  filter_upwards [S34Core.eventually_log_count_bound (2 * (m : ℝ) * P.C₀) (by positivity),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hcount hL
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  have hpow : 1 ≤ L x ^ (P.d + hexp) := Real.one_le_rpow hL (by linarith)
  intro G J ell ν block side hG
  have hc := admissible_comparisonSideCells_count P G x ν block side
    (L x ^ (-hexp)) (Real.rpow_pos_of_pos hLpos _) hL hG
  apply hc.trans
  calc
    _ = (2 * (m : ℝ) * P.C₀ * T x) * L x ^ (P.d + hexp) + 1 := by
      rw [Real.rpow_neg hLpos.le, div_inv_eq_mul, Real.rpow_add hLpos]
      ring
    _ ≤ (2 * (m : ℝ) * P.C₀ * T x + 1) * L x ^ (P.d + hexp) := by nlinarith
    _ ≤ L x * L x ^ (P.d + hexp) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hLpos.le _)
    _ = _ := by
      calc
        _ = L x ^ (1 : ℝ) * L x ^ (P.d + hexp) := by rw [Real.rpow_one]
        _ = L x ^ (1 + (P.d + hexp)) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring

theorem eventual_comparisonCells_count (P : Geometry) (m : ℕ) (hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x : ℝ in atTop, ∀ (G : PrimeGroups) (J ell : ℕ) (ν : Pattern G.graph J ell m)
      (block : G.graph.BigGroup → Bool), Admissible P x G →
      ((comparisonCells ν block (L x ^ (-hexp))).card : ℝ) ≤
        L x ^ (2 * (P.d + hexp + 1)) := by
  filter_upwards [eventual_comparisonSideCells_count P m hexp hh,
    Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with x hc hL
  change 0 < L x at hL
  intro G J ell ν block hG
  calc
    _ ≤ (L x ^ (P.d + hexp + 1)) ^ 2 :=
      comparisonCells_card_le ν block _ _ (Real.rpow_nonneg hL.le _)
        (fun side => hc G J ell ν block side hG)
    _ = _ := by rw [pow_two, ← Real.rpow_add hL]; congr 1; ring

end Erdos821.P5Core
