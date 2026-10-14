import Erdos408.Extraction.TypeII.Asymp

/-!
# Growth facts for the tuple part

The comparisons of scales used in S13–S18 of `blueprint/two_sided_correlation.md` §§6.3–6.6,
with `L = log x`, `T = log L` and the slot margin `x^ε = exp(c L / T²⁰)`:

* `eventually_mul_rpow_mul_exp_le_exp`: `D L^C exp(L^a) ≤ exp(L^b)` for `0 ≤ a < b`;
* `eventually_mul_exp_rpow_le_margin`: `D exp(L^a) ≤ x^ε` for `0 ≤ a < 1`;
* `eventually_mul_exp_div_le_margin`: `D exp(L/T²²) ≤ x^ε`.
-/

namespace Erdos408.TwoSided.TupleHigh

open Filter

/-- Eventually `D L^C exp(L^a) ≤ exp(L^b)`, for `0 ≤ a < b`. -/
theorem eventually_mul_rpow_mul_exp_le_exp {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (C D : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      D * Real.log x ^ C * Real.exp (Real.log x ^ a) ≤ Real.exp (Real.log x ^ b) := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  filter_upwards [Real.tendsto_log_atTop.eventually
      (TypeII.eventually_mul_log_rpow_le (4 * C) 1 _ hb),
    ((tendsto_rpow_atTop (sub_pos.2 hab)).comp Real.tendsto_log_atTop).eventually_ge_atTop 2,
    ((tendsto_rpow_atTop hb).comp Real.tendsto_log_atTop).eventually_ge_atTop
      (4 * |Real.log D|),
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x h₁ h₂ h₃ hL
  simp only [Function.comp_apply, Real.rpow_one] at h₁ h₂ h₃
  set L := Real.log x
  rcases le_or_gt D 0 with hD | hD
  · have : D * L ^ C * Real.exp (L ^ a) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hD (by positivity))
        (by positivity)
    linarith [Real.exp_pos (L ^ b)]
  -- `log D + C log L + L^a ≤ L^b`
  have hLa : L ^ a ≤ L ^ b / 2 := by
    have : L ^ b = L ^ a * L ^ (b - a) := by rw [← Real.rpow_add hL]; ring_nf
    have : 0 ≤ L ^ a := by positivity
    nlinarith
  have hlogD : Real.log D ≤ L ^ b / 4 := by
    have := le_abs_self (Real.log D)
    linarith
  calc D * L ^ C * Real.exp (L ^ a)
      = Real.exp (Real.log D + C * Real.log L + L ^ a) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hD, Real.rpow_def_of_pos hL]
        ring_nf
    _ ≤ Real.exp (L ^ b) := Real.exp_le_exp.2 (by linarith)

/-- Eventually `D exp(L^a) ≤ exp(c L / T²⁰)`, for `0 ≤ a < 1` and `c > 0`. -/
theorem eventually_mul_exp_rpow_le_margin {a : ℝ} (ha : 0 ≤ a) (ha₁ : a < 1) {c : ℝ}
    (hc : 0 < c) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      D * Real.exp (Real.log x ^ a) ≤
        Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (TypeII.eventually_mul_log_rpow_le
      ((|Real.log D| + 1) / c) 20 _ (sub_pos.2 ha₁)),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1)] with x h₁ hL
  have hL1 : 1 ≤ Real.log x := le_trans (Real.one_le_exp (by norm_num)) hL
  have hL0 : 0 < Real.log x := by linarith
  set L := Real.log x
  have hT1 : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  have hT20 : 0 < Real.log L ^ 20 := by positivity
  rcases le_or_gt D 0 with hD | hD
  · have : D * Real.exp (L ^ a) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD (by positivity)
    linarith [Real.exp_pos (c * L / Real.log L ^ 20)]
  have hLa : 1 ≤ L ^ a := Real.one_le_rpow hL1 ha
  -- `T²⁰ (|log D| + 1) L^a ≤ c L`
  have h₂ : (|Real.log D| + 1) * Real.log L ^ 20 ≤ c * L ^ (1 - a) := by
    have h₁' : (|Real.log D| + 1) / c * Real.log L ^ (20 : ℕ) ≤ L ^ (1 - a) := by
      rw [← Real.rpow_natCast]
      exact_mod_cast h₁
    calc (|Real.log D| + 1) * Real.log L ^ 20
        = c * ((|Real.log D| + 1) / c * Real.log L ^ (20 : ℕ)) := by field_simp
      _ ≤ c * L ^ (1 - a) := mul_le_mul_of_nonneg_left h₁' hc.le
  have hLL : L ^ (1 - a) * L ^ a = L := by rw [← Real.rpow_add hL0]; ring_nf; exact Real.rpow_one L
  have h₃ : Real.log D + L ^ a ≤ c * L / Real.log L ^ 20 := by
    rw [le_div_iff₀ hT20]
    have hlD : Real.log D ≤ |Real.log D| := le_abs_self _
    have : (Real.log D + L ^ a) * Real.log L ^ 20 ≤
        (|Real.log D| + 1) * L ^ a * Real.log L ^ 20 := by
      gcongr
      nlinarith [mul_nonneg (abs_nonneg (Real.log D)) (sub_nonneg.2 hLa)]
    calc (Real.log D + L ^ a) * Real.log L ^ 20
        ≤ (|Real.log D| + 1) * L ^ a * Real.log L ^ 20 := this
      _ = (|Real.log D| + 1) * Real.log L ^ 20 * L ^ a := by ring
      _ ≤ c * L ^ (1 - a) * L ^ a := by gcongr
      _ = c * L := by rw [mul_assoc, hLL]
  calc D * Real.exp (L ^ a) = Real.exp (Real.log D + L ^ a) := by
        rw [Real.exp_add, Real.exp_log hD]
    _ ≤ _ := Real.exp_le_exp.2 h₃

/-- Eventually `D exp(L / T²²) ≤ exp(c L / T²⁰)`, for `c > 0`. -/
theorem eventually_mul_exp_div_le_margin {c : ℝ} (hc : 0 < c) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      D * Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤
        Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (TypeII.eventually_mul_log_rpow_le
      |Real.log D| 22 _ one_pos),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (Real.sqrt (2 / c) + 1),
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x h₁ hT hL0
  simp only [Function.comp_apply, Real.rpow_one] at h₁ hT
  set L := Real.log x
  set T := Real.log L
  have hT1 : 1 ≤ T := le_trans (by linarith [Real.sqrt_nonneg (2 / c)]) hT
  have hT0 : 0 < T := by linarith
  rcases le_or_gt D 0 with hD | hD
  · have : D * Real.exp (L / T ^ 22) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD (by positivity)
    linarith [Real.exp_pos (c * L / T ^ 20)]
  -- `c T² ≥ 2`
  have hcT : 2 ≤ c * T ^ 2 := by
    have hs : Real.sqrt (2 / c) ≤ T := by linarith
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rw [Real.sq_sqrt (by positivity)] at h
    rw [div_le_iff₀ hc] at h
    linarith
  have h22 : (|Real.log D| : ℝ) * T ^ (22 : ℕ) ≤ L := by
    rw [← Real.rpow_natCast]
    exact_mod_cast h₁
  have h₃ : Real.log D + L / T ^ 22 ≤ c * L / T ^ 20 := by
    have hlD : Real.log D ≤ |Real.log D| := le_abs_self _
    have e₂ : c * L / T ^ 20 = (c * T ^ 2) * (L / T ^ 22) := by
      field_simp
    have hpos : 0 ≤ L / T ^ 22 := by positivity
    have hD' : Real.log D ≤ L / T ^ 22 := by
      rw [le_div_iff₀ (by positivity)]
      exact (mul_le_mul_of_nonneg_right hlD (by positivity)).trans h22
    rw [e₂]
    nlinarith
  calc D * Real.exp (L / T ^ 22) = Real.exp (Real.log D + L / T ^ 22) := by
        rw [Real.exp_add, Real.exp_log hD]
    _ ≤ _ := Real.exp_le_exp.2 h₃

end Erdos408.TwoSided.TupleHigh
