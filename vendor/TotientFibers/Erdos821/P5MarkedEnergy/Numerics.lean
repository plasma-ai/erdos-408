import Erdos821.Blueprint.Analytic

/-! Eventual inequalities in `x`, with `L x = log x`. -/

noncomputable section
open Filter Real

namespace Erdos821.P5Marked
open Blueprint.Analytic

theorem tendsto_L : Tendsto L atTop atTop := Real.tendsto_log_atTop

theorem ev_L_ge (M : ℝ) : ∀ᶠ x : ℝ in atTop, M ≤ L x := tendsto_L.eventually_ge_atTop M

theorem ev_x_ge (M : ℝ) : ∀ᶠ x : ℝ in atTop, M ≤ x := eventually_ge_atTop M

theorem rpow_x_eq {x : ℝ} (hx : 0 < x) (s : ℝ) : x ^ s = Real.exp (s * L x) := by
  rw [Real.rpow_def_of_pos hx, mul_comm]; rfl

/-- A positive power of `L` eventually dominates any constant. -/
theorem ev_const_le_rpow (c e : ℝ) (he : 0 < e) : ∀ᶠ x : ℝ in atTop, c ≤ L x ^ e :=
  ((tendsto_rpow_atTop he).comp tendsto_L).eventually_ge_atTop c

/-- For `b < 1`, `c + L^b ≤ ε L` eventually. -/
theorem ev_rpow_small (b ε c : ℝ) (hb : b < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, c + L x ^ b ≤ ε * L x := by
  have h1 := ev_const_le_rpow (2 / ε) (1 - b) (by linarith)
  have h2 := ev_L_ge (max 1 (2 * |c| / ε))
  filter_upwards [h1, h2] with x hx1 hx2
  have hL1 : 1 ≤ L x := (le_max_left _ _).trans hx2
  have hLpos : 0 < L x := by linarith
  have hsplit : L x ^ b * L x ^ (1 - b) = L x := by
    rw [← Real.rpow_add hLpos]; simp
  have hbpos : 0 < L x ^ b := Real.rpow_pos_of_pos hLpos b
  have hA : L x ^ b ≤ ε / 2 * L x := by
    have : L x ^ b * (2 / ε) ≤ L x ^ b * L x ^ (1 - b) := mul_le_mul_of_nonneg_left hx1 hbpos.le
    rw [hsplit] at this
    have e : L x ^ b = L x ^ b * (2 / ε) * (ε / 2) := by field_simp
    rw [e]
    calc L x ^ b * (2 / ε) * (ε / 2) ≤ L x * (ε / 2) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = ε / 2 * L x := by ring
  have hB : c ≤ ε / 2 * L x := by
    have h := (le_max_right _ _).trans hx2
    rw [div_le_iff₀ hε] at h
    have := le_abs_self c
    linarith
  linarith

/-- For `a > 0`, `L^(1-a) log L ≤ ε L` eventually. -/
theorem ev_rpow_log_small (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, L x ^ (1 - a) * Real.log (L x) ≤ ε * L x := by
  have hlo := (isLittleO_log_rpow_atTop (show 0 < a by linarith)).comp_tendsto tendsto_L
  have hev := hlo.def hε
  filter_upwards [hev, ev_L_ge 1] with x hx hL1
  have hLpos : 0 < L x := by linarith
  simp only [Function.comp, Real.norm_eq_abs] at hx
  have hlog0 : 0 ≤ Real.log (L x) := Real.log_nonneg hL1
  rw [abs_of_nonneg hlog0, abs_of_nonneg (Real.rpow_nonneg hLpos.le _)] at hx
  calc L x ^ (1 - a) * Real.log (L x) ≤ L x ^ (1 - a) * (ε * L x ^ a) :=
        mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hLpos.le _)
    _ = ε * (L x ^ (1 - a) * L x ^ a) := by ring
    _ = ε * L x := by rw [← Real.rpow_add hLpos]; simp

/-- Polylogarithms against negative powers of `x`. -/
theorem ev_poly_mul_exp_neg (c e s : ℝ) (hs : 0 < s) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, c * L x ^ e * Real.exp (-(s * L x)) ≤ L x ^ (-A) := by
  have ht : Tendsto (fun y : ℝ => y ^ (e + A) * Real.exp (-s * y)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ hs
  have ht2 := ht.comp tendsto_L
  have hev : ∀ᶠ x : ℝ in atTop, L x ^ (e + A) * Real.exp (-s * L x) ≤ 1 / (|c| + 1) :=
    ht2.eventually (ge_mem_nhds (by positivity))
  filter_upwards [hev, ev_L_ge 1] with x hx hL1
  have hLpos : 0 < L x := by linarith
  have hsplit : L x ^ e = L x ^ (e + A) * L x ^ (-A) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have hc : c ≤ |c| + 1 := by linarith [le_abs_self c]
  have hLA : 0 < L x ^ (-A) := Real.rpow_pos_of_pos hLpos _
  have hE : 0 ≤ L x ^ (e + A) * Real.exp (-s * L x) := by positivity
  calc c * L x ^ e * Real.exp (-(s * L x))
      = c * (L x ^ (e + A) * Real.exp (-s * L x)) * L x ^ (-A) := by
        rw [hsplit, neg_mul]; ring
    _ ≤ (|c| + 1) * (1 / (|c| + 1)) * L x ^ (-A) := by
        apply mul_le_mul_of_nonneg_right _ hLA.le
        exact mul_le_mul hc hx hE (by positivity)
    _ = L x ^ (-A) := by field_simp

/-- A monomial in `L` with exponent below `-A` is eventually below `L^(-A)/M`. -/
theorem ev_monomial_le (c e A M : ℝ) (he : e < -A) (hM : 0 < M) :
    ∀ᶠ x : ℝ in atTop, c * L x ^ e ≤ L x ^ (-A) / M := by
  filter_upwards [ev_const_le_rpow ((|c| + 1) * M) (-A - e) (by linarith), ev_L_ge 1] with x hx hL1
  have hLpos : 0 < L x := by linarith
  have hsplit : L x ^ (-A) = L x ^ e * L x ^ (-A - e) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have he0 : 0 < L x ^ e := Real.rpow_pos_of_pos hLpos e
  rw [hsplit, le_div_iff₀ hM]
  calc c * L x ^ e * M ≤ (|c| + 1) * M * L x ^ e := by
        have : c ≤ |c| + 1 := by linarith [le_abs_self c]
        have h2 := mul_le_mul_of_nonneg_right this (mul_nonneg he0.le hM.le)
        linarith
    _ ≤ L x ^ (-A - e) * L x ^ e := mul_le_mul_of_nonneg_right hx he0.le
    _ = L x ^ e * L x ^ (-A - e) := by ring

end Erdos821.P5Marked
