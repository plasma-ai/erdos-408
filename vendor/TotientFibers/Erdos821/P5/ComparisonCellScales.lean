import Erdos821.P5.ComparisonProductBounds
import Erdos821.P5.ComparisonCellPartition

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

def comparisonCellScale (h : ℝ) (j : ℤ) : ℝ := Real.exp (h * j)
def comparisonJointScale (h : ℝ) (j : ℤ × ℤ) : ℝ :=
  comparisonCellScale h j.1 * comparisonCellScale h j.2

theorem comparisonCellScale_pos (h : ℝ) (j : ℤ) : 0 < comparisonCellScale h j :=
  Real.exp_pos _

theorem comparisonJointScale_pos (h : ℝ) (j : ℤ × ℤ) : 0 < comparisonJointScale h j :=
  mul_pos (comparisonCellScale_pos h j.1) (comparisonCellScale_pos h j.2)

theorem comparisonCell_log_bounds (h : ℝ) (hh : 0 < h) (n : ℕ) :
    h * (cell h n : ℝ) ≤ Real.log n ∧ Real.log n < h * (cell h n : ℝ) + h := by
  have hlo := (le_div_iff₀ hh).mp (Int.floor_le (Real.log n / h))
  have hhi := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (Real.log n / h))
  change h * (⌊Real.log n / h⌋ : ℝ) ≤ Real.log n ∧
    Real.log n < h * (⌊Real.log n / h⌋ : ℝ) + h
  constructor <;> nlinarith

/-- The lower endpoint of a logarithmic cell and its exact multiplicative width. -/
theorem comparisonCellScale_bounds (h : ℝ) (hh : 0 < h) (n : ℕ) (hn : 0 < n) :
    comparisonCellScale h (cell h n) ≤ n ∧
      (n : ℝ) < Real.exp h * comparisonCellScale h (cell h n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hlo, hhi⟩ := comparisonCell_log_bounds h hh n
  constructor
  · simpa only [comparisonCellScale, Real.exp_log hnR] using Real.exp_le_exp.mpr hlo
  · simpa only [Real.exp_add, Real.exp_log hnR, comparisonCellScale, mul_comm] using
      Real.exp_lt_exp.mpr hhi

theorem comparisonJointScale_product_bounds {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (h : ℝ) (hh : 0 < h)
    (u : FreeDraw ν) :
    comparisonJointScale h (comparisonCellPair ν block h u) ≤
        (comparisonFreeProduct ν block false u : ℝ) * comparisonFreeProduct ν block true u ∧
      (comparisonFreeProduct ν block false u : ℝ) * comparisonFreeProduct ν block true u <
        Real.exp (2 * h) * comparisonJointScale h (comparisonCellPair ν block h u) := by
  obtain ⟨hA, hA'⟩ := comparisonCellScale_bounds h hh _
    (comparisonFreeProduct_pos ν block false u)
  obtain ⟨hB, hB'⟩ := comparisonCellScale_bounds h hh _
    (comparisonFreeProduct_pos ν block true u)
  dsimp only [comparisonJointScale, comparisonCellPair]
  constructor
  · exact mul_le_mul hA hB (comparisonCellScale_pos _ _).le (Nat.cast_nonneg _)
  · calc
      _ < (Real.exp h * comparisonCellScale h (cell h (comparisonFreeProduct ν block false u))) *
          (comparisonFreeProduct ν block true u : ℝ) :=
        mul_lt_mul_of_pos_right hA' (by exact_mod_cast comparisonFreeProduct_pos ν block true u)
      _ < (Real.exp h * comparisonCellScale h (cell h (comparisonFreeProduct ν block false u))) *
          (Real.exp h * comparisonCellScale h (cell h (comparisonFreeProduct ν block true u))) :=
        mul_lt_mul_of_pos_left hB' (mul_pos (Real.exp_pos _) (comparisonCellScale_pos _ _))
      _ = _ := by rw [show 2 * h = h + h by ring, Real.exp_add]; ring

theorem admissible_comparisonCellScale_lower (P : Geometry) (G : PrimeGroups) (x : ℝ)
    {J ell m : ℕ} (ν : Pattern G.graph J ell m) (block : G.graph.BigGroup → Bool)
    (side : Bool) (u : FreeDraw ν) (h : ℝ) (hh : 0 < h) (hG : Admissible P x G)
    (hne : ∃ g : G.graph.BigGroup, block g = side ∧ (ν.changed g.val).Nonempty) :
    Real.exp (L x ^ P.c - h) ≤
      comparisonCellScale h (cell h (comparisonFreeProduct ν block side u)) := by
  have hp := admissible_comparisonFreeProduct_lower P G x ν block side u hG hne
  have hlog := Real.log_le_log (Real.exp_pos _) hp
  rw [Real.log_exp] at hlog
  have hcell := (comparisonCell_log_bounds h hh (comparisonFreeProduct ν block side u)).2
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- Both occupied cell endpoints have big-prime scale. The upper exponent
depends on m, never on the full lift depth J. -/
theorem admissible_comparisonJointScale_bounds (P : Geometry) (G : PrimeGroups) (x : ℝ)
    {J ell m : ℕ} (ν : Pattern G.graph J ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hL : 1 ≤ L x) (hG : Admissible P x G)
    (hne : ∀ side : Bool, ∃ g : G.graph.BigGroup,
      block g = side ∧ (ν.changed g.val).Nonempty)
    (j : ℤ × ℤ) (hj : j ∈ comparisonCells ν block h) :
    Real.exp (2 * L x ^ P.c - 2 * h) ≤ comparisonJointScale h j ∧
      comparisonJointScale h j ≤ Real.exp (4 * (m : ℝ) * P.C₀ * T x * L x ^ P.d) := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
  constructor
  · have hs := fun side => admissible_comparisonCellScale_lower P G x ν block side u h hh hG (hne side)
    dsimp only [comparisonJointScale, comparisonCellPair]
    calc
      _ = Real.exp (L x ^ P.c - h) * Real.exp (L x ^ P.c - h) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := mul_le_mul (hs false) (hs true) (Real.exp_pos _).le
        (comparisonCellScale_pos _ _).le
  · let K := 2 * (m : ℝ) * P.C₀ * T x * L x ^ P.d
    have hs (side : Bool) : comparisonCellScale h (cell h (comparisonFreeProduct ν block side u)) ≤
        Real.exp K := by
      apply (comparisonCellScale_bounds h hh _ (comparisonFreeProduct_pos ν block side u)).1.trans
      have he := Real.exp_le_exp.mpr
        (admissible_comparisonFreeProduct_log_le P G x ν block side u hL hG)
      simpa only [Real.exp_log (by exact_mod_cast comparisonFreeProduct_pos ν block side u :
        (0 : ℝ) < comparisonFreeProduct ν block side u)] using he
    dsimp only [comparisonJointScale, comparisonCellPair]
    calc
      _ ≤ Real.exp K * Real.exp K :=
        mul_le_mul (hs false) (hs true) (comparisonCellScale_pos _ _).le (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [K]; ring

end Erdos821.P5Core
