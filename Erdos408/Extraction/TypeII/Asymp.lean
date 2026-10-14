module

public import Erdos408.Extraction.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Growth comparisons for the extraction parameters

With `L = log x`, `T = log L` and `s = log T`, every loss in steps E4–E5 has
the shape `exp(A (s² + 1))`, which is `L^{o(1)}` because `s² = o(e^s) = o(T)`.
This file records that comparison, the size `T^{-21} ≤ γ ≤ 1` of the presieve
exponent, and the elementary limits used with them.
-/

@[expose] public section

namespace Erdos408.TypeII

open Filter Real

theorem tendsto_logLog : Tendsto logLog atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_atTop

theorem tendsto_logLogLog : Tendsto logLogLog atTop atTop :=
  tendsto_log_atTop.comp tendsto_logLog

/-- `exp s = T` once `T > 0`. -/
theorem exp_logLogLog {x : ℝ} (h : 0 < logLog x) : Real.exp (logLogLog x) = logLog x :=
  Real.exp_log h

/-- `exp T = L` once `L > 0`. -/
theorem exp_logLog {x : ℝ} (h : 0 < Real.log x) : Real.exp (logLog x) = Real.log x :=
  Real.exp_log h

/-- `L^ε = exp(ε T)`. -/
theorem log_rpow_eq_exp {x : ℝ} (h : 0 < Real.log x) (ε : ℝ) :
    Real.log x ^ ε = Real.exp (ε * logLog x) := by
  rw [rpow_def_of_pos h, logLog, mul_comm]

/-- Eventually `A ≤ s`. -/
theorem eventually_le_logLogLog (A : ℝ) : ∀ᶠ x : ℝ in atTop, A ≤ logLogLog x :=
  tendsto_logLogLog.eventually_ge_atTop A

/-- Eventually `A ≤ T`. -/
theorem eventually_le_logLog (A : ℝ) : ∀ᶠ x : ℝ in atTop, A ≤ logLog x :=
  tendsto_logLog.eventually_ge_atTop A

/-- Eventually `A ≤ L`. -/
theorem eventually_le_log (A : ℝ) : ∀ᶠ x : ℝ in atTop, A ≤ Real.log x :=
  tendsto_log_atTop.eventually_ge_atTop A

/-- The basic comparison: eventually `A (s² + 1) ≤ ε T`. -/
theorem eventually_sq_le_logLog (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, A * (logLogLog x ^ 2 + 1) ≤ ε * logLog x := by
  have hlim := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp tendsto_logLogLog
  have hA : 0 < |A| + 1 := by positivity
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * (|A| + 1)) by positivity))
  filter_upwards [hev, eventually_le_logLogLog 1, eventually_le_logLog 1,
    eventually_le_logLog (2 * (|A| + 1) / ε)] with x hx hs hT hT'
  simp only [Function.comp] at hx
  have hTpos : 0 < logLog x := by linarith
  rw [Real.exp_neg, exp_logLogLog hTpos, ← div_eq_mul_inv, div_lt_iff₀ hTpos] at hx
  have hs2 : 1 ≤ logLogLog x ^ 2 := by nlinarith
  have hAA : A * (logLogLog x ^ 2 + 1) ≤ (|A| + 1) * (2 * logLogLog x ^ 2) := by
    have := le_abs_self A
    nlinarith
  have h2 : (|A| + 1) * (2 * logLogLog x ^ 2) ≤ ε * logLog x := by
    have := mul_lt_mul_of_pos_left hx (show 0 < 2 * (|A| + 1) by positivity)
    have hε' : 2 * (|A| + 1) * (ε / (2 * (|A| + 1)) * logLog x) = ε * logLog x := by
      field_simp
    nlinarith
  linarith

/-- `exp(A (s² + 1)) ≤ L^ε` eventually. -/
theorem eventually_exp_le_log_rpow (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.exp (A * (logLogLog x ^ 2 + 1)) ≤ Real.log x ^ ε := by
  filter_upwards [eventually_sq_le_logLog A ε hε, eventually_le_log 1] with x hx hL
  rw [log_rpow_eq_exp (by linarith)]
  exact Real.exp_le_exp.2 hx

/-- `T^A = exp(A s) ≤ exp(|A| (s² + 1))` once `s ≥ 0`. -/
theorem logLog_rpow_le_exp {x : ℝ} (hT : 0 < logLog x) (hs : 0 ≤ logLogLog x) (A : ℝ) :
    logLog x ^ A ≤ Real.exp (|A| * (logLogLog x ^ 2 + 1)) := by
  rw [rpow_def_of_pos hT]
  apply Real.exp_le_exp.2
  rw [show Real.log (logLog x) = logLogLog x from rfl]
  have h1 : logLogLog x ≤ logLogLog x ^ 2 + 1 := by nlinarith
  calc logLogLog x * A ≤ logLogLog x * |A| :=
        mul_le_mul_of_nonneg_left (le_abs_self A) hs
    _ ≤ (logLogLog x ^ 2 + 1) * |A| := mul_le_mul_of_nonneg_right h1 (abs_nonneg A)
    _ = _ := mul_comm _ _

/-- `T^A ≤ L^ε` eventually. -/
theorem eventually_logLog_rpow_le (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, logLog x ^ A ≤ Real.log x ^ ε := by
  filter_upwards [eventually_exp_le_log_rpow |A| ε hε, eventually_le_logLog 1,
    eventually_le_logLogLog 0] with x hx hT hs
  exact (logLog_rpow_le_exp (by linarith) hs A).trans hx

/-- The sieve depth is at most `2 (|C_h| s + 1)`. -/
theorem sieveDepth_le {Ch x : ℝ} (hs : 0 ≤ logLogLog x) :
    (sieveDepth Ch x : ℝ) ≤ 2 * (|Ch| * logLogLog x + 1) := by
  unfold sieveDepth
  push_cast
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ |Ch| * logLogLog x by positivity)
  have h2 : ⌈Ch * logLogLog x⌉₊ ≤ ⌈|Ch| * logLogLog x⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_abs_self Ch) hs)
  have h3 : (⌈Ch * logLogLog x⌉₊ : ℝ) ≤ ⌈|Ch| * logLogLog x⌉₊ := by exact_mod_cast h2
  linarith

/-- The presieve exponent satisfies `T^{-21} ≤ γ ≤ 1` eventually. -/
theorem eventually_presieveExponent_bounds (c Ch : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, logLog x ^ (-21 : ℝ) ≤ presieveExponent c Ch x ∧
      presieveExponent c Ch x ≤ 1 := by
  filter_upwards [eventually_sq_le_logLog (4 * (8 * |Ch| + 11) / c) 1 one_pos,
    eventually_le_logLog c, eventually_le_logLog 1, eventually_le_logLogLog 0]
    with x hx hTc hT hs
  have hTpos : 0 < logLog x := by linarith
  have hd := sieveDepth_le (Ch := Ch) hs
  have hd0 : (0 : ℝ) ≤ sieveDepth Ch x := Nat.cast_nonneg _
  have hT20 : 0 < logLog x ^ 20 := by positivity
  have h1T20 : 1 ≤ logLog x ^ 20 := one_le_pow₀ hT
  unfold presieveExponent
  set h : ℝ := (sieveDepth Ch x : ℝ)
  have hden : 0 < 4 * h + 3 := by linarith
  constructor
  · -- `4h + 3 ≤ 8|C_h| s + 11 ≤ c T / 4`
    have hs1 : logLogLog x ≤ logLogLog x ^ 2 + 1 := by nlinarith
    have hh : 4 * h + 3 ≤ c * logLog x / 4 := by
      have : 4 * (8 * |Ch| + 11) / c * (logLogLog x ^ 2 + 1) ≤ logLog x := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ hc] at this
      have habs : 0 ≤ |Ch| := abs_nonneg _
      nlinarith
    rw [Real.rpow_neg hTpos.le, show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, rpow_natCast]
    rw [div_div, div_div, inv_le_comm₀ (by positivity) (by positivity), inv_div]
    have h4 : 4 * (4 * h + 3) ≤ c * logLog x := by linarith
    calc logLog x ^ 20 * (4 * (4 * h + 3)) / c ≤ logLog x ^ 20 * (c * logLog x) / c :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hT20.le) hc.le
      _ = logLog x ^ 21 := by field_simp
  · rw [div_div, div_div, div_le_one (by positivity)]
    have hT20' : logLog x ≤ logLog x ^ 20 := le_self_pow₀ hT (by norm_num)
    nlinarith

/-- `C L^r ≤ x^s` eventually, for `s > 0`. -/
theorem eventually_mul_log_rpow_le (C r s : ℝ) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ r ≤ x ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop r hs).bound (show (0 : ℝ) < 1 / (|C| + 1) by
    positivity)
  filter_upwards [h, eventually_ge_atTop 1, eventually_le_log 1] with x hx hx1 hL
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hx
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have hpos : 0 ≤ Real.log x ^ r := by positivity
  calc C * Real.log x ^ r ≤ (|C| + 1) * Real.log x ^ r := mul_le_mul_of_nonneg_right hC hpos
    _ ≤ (|C| + 1) * (1 / (|C| + 1) * x ^ s) := by gcongr
    _ = x ^ s := by field_simp

/-- `L^a ≤ ε L^b` eventually, for `a < b` and `ε > 0`. -/
theorem eventually_log_rpow_le_mul (a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ a ≤ ε * Real.log x ^ b := by
  have hlim : Tendsto (fun y : ℝ => y ^ (b - a)) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [tendsto_log_atTop.eventually (hlim.eventually_ge_atTop (1 / ε)),
    eventually_le_log 1] with x hx hL
  have hL0 : 0 < Real.log x := by linarith
  have : Real.log x ^ b = Real.log x ^ (b - a) * Real.log x ^ a := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  have hpos : 0 < Real.log x ^ a := by positivity
  have : 1 ≤ ε * Real.log x ^ (b - a) := by
    rw [div_le_iff₀ hε] at hx; linarith
  nlinarith

/-- The comparison with any fixed power of `s`: eventually `A (s^k + 1) ≤ ε T`. -/
theorem eventually_pow_le_logLog (k : ℕ) (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, A * (logLogLog x ^ k + 1) ≤ ε * logLog x := by
  have hlim := (tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp tendsto_logLogLog
  have hA : 0 < |A| + 1 := by positivity
  have hev := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * (|A| + 1)) by positivity))
  filter_upwards [hev, eventually_le_logLogLog 1, eventually_le_logLog 1,
    eventually_le_logLog (2 * (|A| + 1) / ε)] with x hx hs hT hT'
  simp only [Function.comp] at hx
  have hTpos : 0 < logLog x := by linarith
  rw [Real.exp_neg, exp_logLogLog hTpos, ← div_eq_mul_inv, div_lt_iff₀ hTpos] at hx
  have hsk : 1 ≤ logLogLog x ^ k := one_le_pow₀ hs
  have hAA : A * (logLogLog x ^ k + 1) ≤ (|A| + 1) * (2 * logLogLog x ^ k) := by
    have := le_abs_self A
    nlinarith
  have h2 : (|A| + 1) * (2 * logLogLog x ^ k) ≤ ε * logLog x := by
    have := mul_lt_mul_of_pos_left hx (show 0 < 2 * (|A| + 1) by positivity)
    have hε' : 2 * (|A| + 1) * (ε / (2 * (|A| + 1)) * logLog x) = ε * logLog x := by
      field_simp
    nlinarith
  linarith

/-- `exp(A (s^k + 1)) ≤ L^ε` eventually. -/
theorem eventually_exp_pow_le_log_rpow (k : ℕ) (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.exp (A * (logLogLog x ^ k + 1)) ≤ Real.log x ^ ε := by
  filter_upwards [eventually_pow_le_logLog k A ε hε, eventually_le_log 1] with x hx hL
  rw [log_rpow_eq_exp (by linarith)]
  exact Real.exp_le_exp.2 hx

end Erdos408.TypeII
