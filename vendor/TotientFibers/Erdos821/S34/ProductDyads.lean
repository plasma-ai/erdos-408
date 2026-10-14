import Erdos821.S34.ScaleGrowth
import Erdos821.S34.CellCount

set_option autoImplicit false
open scoped BigOperators Classical
open Filter

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def dyadIndex (n : ℕ) : ℤ := cell (Real.log 2) n
def dyadScale (j : ℤ) : ℝ := Real.exp (Real.log 2 * j)

theorem dyadScale_pos (j : ℤ) : 0 < dyadScale j := Real.exp_pos _

theorem product_in_dyad (n : ℕ) (hn : 0 < n) :
    dyadScale (dyadIndex n) ≤ n ∧ (n : ℝ) < 2 * dyadScale (dyadIndex n) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow := Int.floor_le (Real.log n / Real.log 2)
  have hhigh := Int.lt_floor_add_one (Real.log n / Real.log 2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : Real.log 2 * (dyadIndex n : ℝ) ≤ Real.log n := by
    change Real.log 2 * (⌊Real.log n / Real.log 2⌋ : ℝ) ≤ _
    have h := (le_div_iff₀ hlog2).mp hlow
    nlinarith
  have hhi : Real.log n < Real.log 2 * (dyadIndex n : ℝ) + Real.log 2 := by
    change Real.log n < Real.log 2 * (⌊Real.log n / Real.log 2⌋ : ℝ) + Real.log 2
    have h := (div_lt_iff₀ hlog2).mp hhigh
    nlinarith
  constructor
  · simpa only [dyadScale, Real.exp_log hnR] using Real.exp_le_exp.mpr hlo
  · have ht := Real.exp_lt_exp.mpr hhi
    simpa only [Real.exp_add, Real.exp_log hnR, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      dyadScale, mul_comm] using ht

theorem eventually_product_cell_count (P : Geometry) (m : ℕ) (hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G → ∀ k, bigSlots G k m →
      ((Finset.univ.image (fun z : Tuple G k => cell (L x ^ (-hexp)) (product G k z))).card : ℝ) ≤
        L x ^ (P.d + 1 + hexp) := by
  have hC₀ : 0 < P.C₀ := P.positive.2.1
  have hd : 0 < P.d := by have h := P.ordered; linarith [h.1, h.2.1, h.2.2.1, h.2.2.2.1]
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_log_count_bound ((m : ℝ) * P.C₀) (by positivity),
    hL.eventually_ge_atTop 1] with x hc hL1
  have hLpos : 0 < L x := by linarith
  have hT : 0 ≤ T x := Real.log_nonneg hL1
  have hp : 1 ≤ L x ^ (P.d + hexp) := Real.one_le_rpow hL1 (by linarith)
  intro G hG k hk
  have hcount := product_cell_count P x G hLpos.le hT hG k m hk
    (L x ^ (-hexp)) (Real.rpow_pos_of_pos hLpos _)
  apply hcount.trans
  calc
    _ = ((m : ℝ) * P.C₀ * T x) * L x ^ (P.d + hexp) + 1 := by
      rw [Real.rpow_neg hLpos.le, div_inv_eq_mul, Real.rpow_add hLpos]
      ring
    _ ≤ ((m : ℝ) * P.C₀ * T x + 1) * L x ^ (P.d + hexp) := by nlinarith
    _ ≤ L x * L x ^ (P.d + hexp) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hLpos.le _)
    _ = _ := by
      calc
        _ = L x ^ (1 : ℝ) * L x ^ (P.d + hexp) := by rw [Real.rpow_one]
        _ = L x ^ (1 + (P.d + hexp)) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring

theorem eventually_product_dyad_count (P : Geometry) (m : ℕ) :
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G → ∀ k, bigSlots G k m →
      ((Finset.univ.image (fun z : Tuple G k => dyadIndex (product G k z))).card : ℝ) ≤
        L x ^ (P.d + 1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC₀ : 0 < P.C₀ := P.positive.2.1
  have hd : 0 < P.d := by have h := P.ordered; linarith [h.1, h.2.1, h.2.2.1, h.2.2.2.1]
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_log_count_bound ((m : ℝ) * P.C₀ / Real.log 2) (by positivity),
    hL.eventually_ge_atTop 1] with x hc hL1
  have hLpos : 0 < L x := by linarith
  have hT : 0 ≤ T x := Real.log_nonneg hL1
  intro G hG k hk
  have hcount := product_cell_count P x G hLpos.le hT hG k m hk (Real.log 2) hlog2
  change ((Finset.univ.image (fun z : Tuple G k => dyadIndex (product G k z))).card : ℝ) ≤ _ at hcount
  apply hcount.trans
  have hp : 1 ≤ L x ^ P.d := Real.one_le_rpow hL1 hd.le
  calc
    _ = ((m : ℝ) * P.C₀ / Real.log 2 * T x) * L x ^ P.d + 1 := by ring
    _ ≤ ((m : ℝ) * P.C₀ / Real.log 2 * T x + 1) * L x ^ P.d := by nlinarith
    _ ≤ L x * L x ^ P.d := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hLpos.le _)
    _ = _ := by
      calc
        _ = L x ^ (1 : ℝ) * L x ^ P.d := by rw [Real.rpow_one]
        _ = L x ^ (1 + P.d) := (Real.rpow_add hLpos _ _).symm
        _ = _ := by congr 1; ring

theorem eventually_product_dyad_scale (P : Geometry) (m : ℕ) (A : ℝ) :
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G → ∀ k, bigSlots G k m →
      ∀ z : Tuple G k, L x ^ A ≤ dyadScale (dyadIndex (product G k z)) := by
  have hc : 0 < P.c := by have h := P.ordered; linarith [h.1, h.2.1, h.2.2.1]
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_power_le_label_scale A P.c (1 / 2) hc (by norm_num),
    hL.eventually_ge_atTop 0] with x hx hLx
  intro G hG k hk z
  have hn := tuple_product_pos G k z
  have hp := (log_product_bounds P x G hLx hG k m hk z).1
  have hpR : (0 : ℝ) < product G k z := by exact_mod_cast hn
  have he : Real.exp (L x ^ P.c) ≤ (product G k z : ℝ) := by
    simpa only [Real.exp_log hpR] using Real.exp_le_exp.mpr hp
  have hd := (product_in_dyad _ hn).2
  linarith

end
end Erdos821.S34Core
