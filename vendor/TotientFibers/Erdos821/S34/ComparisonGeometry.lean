import Erdos821.S34.ProductDyads

set_option autoImplicit false
open scoped BigOperators Classical
open Filter

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def atomExponent (P : Geometry) (m : ℕ) : ℝ :=
  P.C₀ * (Real.log (Nat.factorial m) + m * Real.log (max 1 P.vmin⁻¹))

theorem atomExponent_nonneg (P : Geometry) (m : ℕ) : 0 ≤ atomExponent P m := by
  have hfac : (1 : ℝ) ≤ Nat.factorial m := by exact_mod_cast Nat.factorial_pos m
  have hf := Real.log_nonneg hfac
  have hm := Real.log_nonneg (le_max_left (1 : ℝ) P.vmin⁻¹)
  exact mul_nonneg P.positive.2.1.le (add_nonneg hf (mul_nonneg (Nat.cast_nonneg m) hm))

theorem eventually_cell_width (hexp : ℝ) (hh : 0 < hexp) :
    ∀ᶠ x in atTop, 0 < L x ^ (-hexp) ∧ L x ^ (-hexp) ≤ Real.log 2 := by
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have ht := (tendsto_rpow_neg_atTop hh).comp hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [ht.eventually (eventually_lt_nhds hlog2), hL.eventually_gt_atTop 0] with x hx hLx
  exact ⟨Real.rpow_pos_of_pos hLx _, hx.le⟩

theorem eventually_big_prime_power (P : Geometry) (q : ℝ) :
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ g ∈ G.big, ∀ p ∈ G.primes g, L x ^ q < (p : ℝ) := by
  have hc : 0 < P.c := by rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩; linarith
  filter_upwards [eventually_power_le_label_scale q P.c (1 / 2) hc (by norm_num)] with x hx
  intro G hG g hg p hp
  have hs : g ∉ G.small := (Finset.mem_sdiff.mp hg).2
  have hbound := hG.2.2.2.1 g p hp
  rw [if_neg hs] at hbound
  have he := Real.exp_pos (L x ^ P.c)
  linarith [hbound.1]

theorem eventually_dyad_denominator_log (P : Geometry) (m : ℕ) :
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ a b, bigSlots G a m → bigSlots G b m →
      ∀ (X : Tuple G a) (Y : Tuple G b) (r : ℝ), 1 ≤ r →
        r ≤ dyadScale (dyadIndex (product G a X)) * dyadScale (dyadIndex (product G b Y)) →
        Real.log (2 * r) ≤ L x ^ (P.d + 1) := by
  have hC₀ : 0 < P.C₀ := P.positive.2.1
  have hd : 0 < P.d := by rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩; linarith
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [eventually_log_count_bound (2 * (m : ℝ) * P.C₀) (by positivity),
    hL.eventually_ge_atTop 1] with x hc hL1
  have hLp : 0 < L x := by linarith
  have hpow : 1 ≤ L x ^ P.d := Real.one_le_rpow hL1 hd.le
  intro G hG a b ha hb X Y r hr hrUV
  let U := dyadScale (dyadIndex (product G a X))
  let V := dyadScale (dyadIndex (product G b Y))
  have hU : 0 < U := dyadScale_pos _
  have hV : 0 < V := dyadScale_pos _
  have hlogU : Real.log U ≤ (m : ℝ) * P.C₀ * T x * L x ^ P.d := by
    exact (Real.log_le_log hU (product_in_dyad _ (tuple_product_pos G a X)).1).trans
      (log_product_bounds P x G hLp.le hG a m ha X).2
  have hlogV : Real.log V ≤ (m : ℝ) * P.C₀ * T x * L x ^ P.d := by
    exact (Real.log_le_log hV (product_in_dyad _ (tuple_product_pos G b Y)).1).trans
      (log_product_bounds P x G hLp.le hG b m hb Y).2
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hrp : 0 < r := by linarith
  have hlogr := Real.log_le_log hrp hrUV
  rw [Real.log_mul hU.ne' hV.ne'] at hlogr
  calc
    _ = Real.log 2 + Real.log r := Real.log_mul (by norm_num) hrp.ne'
    _ ≤ 1 + 2 * (m : ℝ) * P.C₀ * T x * L x ^ P.d := by linarith
    _ ≤ (2 * (m : ℝ) * P.C₀ * T x + 1) * L x ^ P.d := by nlinarith
    _ ≤ L x * L x ^ P.d := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hLp.le _)
    _ = _ := by
      calc
        _ = L x ^ (1 : ℝ) * L x ^ P.d := by rw [Real.rpow_one]
        _ = L x ^ (1 + P.d) := (Real.rpow_add hLp _ _).symm
        _ = _ := by congr 1; ring

end
end Erdos821.S34Core
