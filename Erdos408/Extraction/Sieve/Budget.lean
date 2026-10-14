import Erdos408.Extraction.Sieve.Tail
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The error budget (E11)

With `h = 2 ⌈200 s⌉`, `J_c = ⌈1001 s⌉` and `N = ⌈30000 s⌉` bands per cluster
(`C_N = 30000 K`), every error of the extraction is at most `T⁻³⁰⁰`:

* `e^{-h} ≤ T⁻⁴⁰⁰`, `2^{-J_c} ≤ T^{-1001 log 2} ≤ T⁻⁶⁰⁰`, and
  `exp(-N / (12 e)) ≤ T⁻⁶⁰⁰`;
* `1 / L`, `L / z` and `L^{-c'}` are at most `T⁻⁴⁰⁰`, and `J_c ≤ T`.

Each error term is a fixed constant times a power of `T` times one of these
savings (`le_inv_pow_of_le`).
-/

namespace Erdos408

open Filter Real Finset

namespace Sieve

noncomputable section

/-- A term `C T^a A` with saving `A ≤ T^{-b}` and `|C| ≤ T`, `a + 301 ≤ b`, is at
most `T⁻³⁰⁰`. -/
lemma le_inv_pow_of_le {T C A : ℝ} {a b : ℕ} (hT : 1 ≤ T) (hC : |C| ≤ T) (hA0 : 0 ≤ A)
    (hA : A ≤ (T ^ b)⁻¹) (hab : a + 301 ≤ b) : C * T ^ a * A ≤ (T ^ 300)⁻¹ := by
  have hT0 : 0 < T := by linarith
  have h1 : C * T ^ a * A ≤ T * T ^ a * (T ^ b)⁻¹ := by
    have : C * T ^ a ≤ T * T ^ a :=
      mul_le_mul_of_nonneg_right ((le_abs_self C).trans hC) (by positivity)
    calc C * T ^ a * A ≤ T * T ^ a * A := mul_le_mul_of_nonneg_right this hA0
      _ ≤ T * T ^ a * (T ^ b)⁻¹ := mul_le_mul_of_nonneg_left hA (by positivity)
  refine h1.trans ?_
  rw [← pow_succ', mul_inv_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity),
    ← pow_add]
  exact pow_le_pow_right₀ hT (by omega)

/-- `T^{-a} ≤ T^{-b}` as an inverse natural power, for `b ≤ a`. -/
lemma rpow_neg_le_inv_pow {T a : ℝ} {b : ℕ} (hT : 1 ≤ T) (hab : (b : ℝ) ≤ a) :
    T ^ (-a) ≤ (T ^ b)⁻¹ := by
  rw [rpow_neg (by linarith), ← rpow_natCast]
  exact inv_anti₀ (by positivity) (rpow_le_rpow_of_exponent_le hT hab)

/-- The savings of the extraction, for large `x`. -/
lemma eventually_savings {K : ℕ} (hK : 1 ≤ K) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    ∀ᶠ x : ℝ in atTop, 1 ≤ logLog x ∧
      exp (-(sieveDepth 200 x : ℝ)) ≤ (logLog x ^ 400)⁻¹ ∧
      ((2 : ℝ) ^ compositeCutoff 1001 x)⁻¹ ≤ (logLog x ^ 600)⁻¹ ∧
      exp (-(inertPerCluster K (30000 * K) x / (12 * exp 1))) ≤ (logLog x ^ 600)⁻¹ ∧
      1 / Real.log x ≤ (logLog x ^ 400)⁻¹ ∧
      Real.log x / x ^ presieveExponent c 200 x ≤ (logLog x ^ 400)⁻¹ ∧
      Real.log x ^ (-c') ≤ (logLog x ^ 400)⁻¹ ∧
      (compositeCutoff 1001 x : ℝ) ≤ logLog x := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  filter_upwards [tendsto_logLog.eventually_ge_atTop 1,
    eventually_sieveDepth (Ch := 200) (by norm_num) 0,
    eventually_presieveExponent hc (by norm_num : (0 : ℝ) < 200),
    eventually_mul_rpow_le_log_rpow 1 400 one_pos, eventually_mul_rpow_le_log_rpow 1 400 hc',
    eventually_mul_rpow_le_log_rpow 2 23 one_pos, eventually_mul_logLogLog_le 1002,
    eventually_gt_atTop 0, tendsto_log_atTop.eventually_gt_atTop 0]
    with x hT ⟨_, _, hh⟩ ⟨hγ0, _, hγinv, _⟩ hL400 hLc hL23 hJ hx0 hL
  set T := logLog x
  have hT0 : 0 < T := by linarith
  have hs0 : 0 ≤ logLogLog x := by
    rw [logLogLog]
    exact log_nonneg hT
  have hpow : ∀ n : ℕ, T ^ (n : ℝ) = T ^ n := fun n => rpow_natCast T n
  rw [one_mul, rpow_one, show (400 : ℝ) = ((400 : ℕ) : ℝ) by norm_num, hpow] at hL400
  rw [one_mul, show (400 : ℝ) = ((400 : ℕ) : ℝ) by norm_num, hpow] at hLc
  rw [rpow_one, show (23 : ℝ) = ((23 : ℕ) : ℝ) by norm_num, hpow] at hL23
  refine ⟨hT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hh.trans (rpow_neg_le_inv_pow hT (by norm_num))
  · refine (two_pow_neg_compositeCutoff_le hT0).trans (rpow_neg_le_inv_pow hT ?_)
    have := log_two_gt_d9
    push_cast
    linarith
  · -- `N ≥ 30000 s`, so `exp(-N/(12e)) ≤ exp(-600 s) = T⁻⁶⁰⁰`
    have hN : 30000 * logLogLog x ≤ inertPerCluster K (30000 * K) x := by
      have := Nat.le_ceil (30000 * K * logLogLog x / K)
      rw [inertPerCluster]
      have h' : 30000 * K * logLogLog x / K = 30000 * logLogLog x := by field_simp
      rw [h'] at this
      rw [h']
      exact this
    have he : exp 1 < 3 := exp_one_lt_three
    have h1 : 600 * logLogLog x ≤ inertPerCluster K (30000 * K) x / (12 * exp 1) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc exp (-(inertPerCluster K (30000 * K) x / (12 * exp 1))) ≤ exp (-(600 * logLogLog x)) :=
          exp_le_exp.2 (by linarith)
      _ = T ^ (-(600 : ℝ)) := by rw [logLog_rpow_eq hT0]; ring_nf
      _ ≤ (T ^ 600)⁻¹ := rpow_neg_le_inv_pow hT (by norm_num)
  · rw [one_div]
    exact inv_anti₀ (by positivity) hL400
  · -- `z = exp(γ L) ≥ exp(2T) = L²` and `L ≥ T⁴⁰⁰`
    have hγL : 2 * T ≤ presieveExponent c 200 x * Real.log x := by
      rw [one_div, inv_le_iff_one_le_mul₀ hγ0] at hγinv
      have h1 : 2 * T ^ 23 * presieveExponent c 200 x ≤
          Real.log x * presieveExponent c 200 x := mul_le_mul_of_nonneg_right hL23 hγ0.le
      have h2 : T ^ 23 = T * T ^ 22 := by ring
      nlinarith
    have hz : Real.log x ^ 2 ≤ x ^ presieveExponent c 200 x := by
      rw [rpow_def_of_pos hx0, show Real.log x ^ 2 = exp (2 * T) by
        rw [show (2 : ℝ) * T = (2 : ℕ) * T by norm_num, exp_nat_mul, exp_logLog hL]]
      exact exp_le_exp.2 (by linarith)
    rw [div_le_iff₀ (by positivity)]
    calc Real.log x = (T ^ 400)⁻¹ * (T ^ 400 * Real.log x) := by field_simp
      _ ≤ (T ^ 400)⁻¹ * (Real.log x * Real.log x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL400 hL.le) (by positivity)
      _ ≤ (T ^ 400)⁻¹ * x ^ presieveExponent c 200 x :=
          mul_le_mul_of_nonneg_left (by rw [← sq]; exact hz) (by positivity)
  · rw [rpow_neg hL.le]
    exact inv_anti₀ (by positivity) hLc
  · have := Nat.ceil_lt_add_one (show 0 ≤ 1001 * logLogLog x by positivity)
    rw [compositeCutoff]
    linarith


/-- E11: the seven error terms of the extraction add up to at most `7 T⁻³⁰⁰`. -/
lemma final_budget {T eh iL Lz j2 e1 Lc J C₂ C₃ C₁₂ C₁₀ : ℝ} (hT : 1 ≤ T)
    (heh0 : 0 ≤ eh) (heh : eh ≤ (T ^ 400)⁻¹) (hiL0 : 0 ≤ iL) (hiL : iL ≤ (T ^ 400)⁻¹)
    (hLz0 : 0 ≤ Lz) (hLz : Lz ≤ (T ^ 400)⁻¹) (hj20 : 0 ≤ j2) (hj2 : j2 ≤ (T ^ 600)⁻¹)
    (he10 : 0 ≤ e1) (he1 : e1 ≤ (T ^ 600)⁻¹) (hLc0 : 0 ≤ Lc) (hLc : Lc ≤ (T ^ 400)⁻¹)
    (hJ : J ≤ T) (hC₂ : |C₂| ≤ T) (hC₃ : |C₃| ≤ T) (hC₁₂ : |C₁₂| ≤ T)
    (hC₁₂0 : 0 ≤ C₁₂) (hC₁₀ : |C₁₀| ≤ T) :
    C₂ * (T ^ 4 * T ^ 22 * eh + T ^ 4 * iL) + C₃ * (T ^ 62 * Lz + T ^ 62 * T ^ 44 * j2) +
        J * (C₁₂ * Lc) + T ^ 62 * (C₁₀ * (T ^ 22 * e1 + iL)) ≤ 7 * (T ^ 300)⁻¹ := by
  have h1 := le_inv_pow_of_le (a := 26) hT hC₂ heh0 heh (by norm_num)
  have h2 := le_inv_pow_of_le (a := 4) hT hC₂ hiL0 hiL (by norm_num)
  have h3 := le_inv_pow_of_le (a := 62) hT hC₃ hLz0 hLz (by norm_num)
  have h4 := le_inv_pow_of_le (a := 106) hT hC₃ hj20 hj2 (by norm_num)
  have h5 := le_inv_pow_of_le (a := 1) hT hC₁₂ hLc0 hLc (by norm_num)
  have h6 := le_inv_pow_of_le (a := 84) hT hC₁₀ he10 he1 (by norm_num)
  have h7 := le_inv_pow_of_le (a := 62) hT hC₁₀ hiL0 hiL (by norm_num)
  have h5' : J * (C₁₂ * Lc) ≤ C₁₂ * T ^ 1 * Lc := by
    rw [pow_one, mul_comm C₁₂ T, mul_assoc]
    exact mul_le_mul_of_nonneg_right hJ (mul_nonneg hC₁₂0 hLc0)
  have e1' : C₂ * (T ^ 4 * T ^ 22 * eh + T ^ 4 * iL) = C₂ * T ^ 26 * eh + C₂ * T ^ 4 * iL := by
    ring
  have e2' : C₃ * (T ^ 62 * Lz + T ^ 62 * T ^ 44 * j2) =
      C₃ * T ^ 62 * Lz + C₃ * T ^ 106 * j2 := by ring
  have e3' : T ^ 62 * (C₁₀ * (T ^ 22 * e1 + iL)) = C₁₀ * T ^ 84 * e1 + C₁₀ * T ^ 62 * iL := by
    ring
  rw [e1', e2', e3']
  linarith

end

end Sieve

end Erdos408
