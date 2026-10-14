import Erdos408.Analytic.Core
import Erdos408.Hypotheses
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import PrimeNumberTheoremAnd.PerronFormula

/-!
# The integer kernel in progressions

AC3 of `blueprint/rectangle_input.md` §3: the premise `IntegerKernelBound` of
`TwoSidedCorrelation` and the integer-kernel premise of `OneSidedTypeII`.
For `u⁴ ≤ H³`, elementary summation gives the principal term
`O(H / (1 + |u|))` plus `O(|u|)`. For larger `|u|`, the sharp sum is a
trapezoid combination of four smoothed sums
`∑ χ(n) n^{iu} (1 - n / Y) = (2πi)⁻¹ ∫_{(2)} L(s - iu, χ) Y^s / (s (s + 1)) ds`
with ramps of width `M = H^{127/128}`. Away from the pole, `|im s - u| ≥ 3`,
the line is shifted to `re s = 63/64`, where `|L| ≤ exp(C √L)`; this saves
`H^{-1/128}`. A residue class `a mod k` is reduced by `g = (a, k)` to a unit
class modulo `k / g`, which is an average of character twists.
-/

namespace Erdos408

open Filter Classical

namespace IntegerKernel

open Complex DirichletCharacter MeasureTheory Set Topology LSeries

/-- The integrand `L(s - iu, χ) Y^s / (s (s + 1))` of the smoothed Perron formula for
`∑ χ(n) n^{iu} (1 - n / Y)`. -/
noncomputable def kernelIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u Y : ℝ)
    (s : ℂ) : ℂ :=
  LFunction χ (s - u * I) * Perron.f Y s

/-- On `re s = 2`, `‖L(s, χ)‖` is at most `∑ n⁻²`. -/
theorem norm_LFunction_le_of_re_eq_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s.re = 2) : ‖LFunction χ s‖ ≤ ∑' n, ‖term 1 2 n‖ := by
  have hle : ∀ n, ‖term (fun n ↦ χ n) s n‖ ≤ ‖term 1 2 n‖ := by
    intro n
    rw [norm_term_eq, norm_term_eq, hs, show (2 : ℂ).re = 2 by simp]
    split_ifs
    · rfl
    gcongr
    simpa using χ.norm_le_one n
  have h1 : Summable fun n ↦ ‖term 1 2 n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr (by norm_num))
  rw [LFunction_eq_LSeries χ (by rw [hs]; norm_num), LSeries]
  exact (norm_tsum_le_tsum_norm (h1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle)).trans
    (Summable.tsum_le_tsum hle (h1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle) h1)

/-- Each term of the L-series at `s - iu` times `Y^s / (s (s + 1))` is a Perron kernel at
`Y / n`. -/
theorem term_mul_perron_f_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) {Y : ℝ}
    (hY : 0 < Y) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    term (fun n ↦ χ n) (s - u * I) n * Perron.f Y s =
      χ n * (n : ℂ) ^ ((u : ℂ) * I) * Perron.f (Y / n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := Perron.f_mul_eq_f hY (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s
  rw [ofReal_natCast, cpow_neg] at h
  rw [term_of_ne_zero hn, ← h, cpow_sub _ _ hn0]
  field_simp

/-- The line integral of the Perron kernel at `y > 1` is `2π (1 - 1/y)`. -/
theorem integral_perron_f_of_one_lt {y : ℝ} (hy : 1 < y) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 2 * Real.pi * (1 - 1 / y) := by
  have h := Perron.formulaGtOne (σ := 2) hy (by norm_num)
  rw [VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul] at h
  change 1 / (2 * Real.pi * I) * (I * ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I)) = _ at h
  generalize ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = J at h ⊢
  rw [← h]
  field_simp

/-- The line integral of the Perron kernel at `0 < y < 1` vanishes. -/
theorem integral_perron_f_of_lt_one {y : ℝ} (hy0 : 0 < y) (hy : y < 1) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 0 := by
  have h := Perron.formulaLtOne (σ := 2) hy0 hy (by norm_num)
  rw [VerticalIntegral, smul_eq_mul] at h
  simpa using h

/-- The smoothed Perron formula: the vertical integral of `kernelIntegrand` on `re s = 2`
is `2πi ∑_{n ≤ Y} χ(n) n^{iu} (1 - n / Y)`. -/
theorem verticalIntegral_kernelIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (u : ℝ) {Y : ℝ} (hY : 1 < Y) (hYN : ∀ m : ℕ, (m : ℝ) ≠ Y) :
    VerticalIntegral (kernelIntegrand χ u Y) 2 =
      2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
        χ m * (m : ℂ) ^ ((u : ℂ) * I) * (1 - m / Y) := by
  have hY0 : 0 < Y := by linarith
  have hre : ∀ t : ℝ, 1 < ((2 : ℝ) + t * I - u * I).re := fun t ↦ by simp
  -- Expand the integrand as a Dirichlet series of Perron kernels.
  set g : ℕ → ℝ → ℂ := fun n t ↦
    term (fun n ↦ χ n) ((2 : ℝ) + t * I - u * I) n * Perron.f Y ((2 : ℝ) + t * I) with hg
  have hsum : ∀ t : ℝ, kernelIntegrand χ u Y ((2 : ℝ) + t * I) = ∑' n, g n t := by
    intro t
    rw [kernelIntegrand, LFunction_eq_LSeries χ (hre t), LSeries, ← tsum_mul_right]
  have hg_eq : ∀ n, n ≠ 0 → ∀ t,
      g n t = χ n * (n : ℂ) ^ ((u : ℂ) * I) * Perron.f (Y / n) ((2 : ℝ) + t * I) :=
    fun n hn t ↦ term_mul_perron_f_eq χ u hY0 hn _
  -- Each term is integrable, and the integrals of the norms are summable.
  have hg_int : ∀ n, Integrable (g n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    · rw [funext (hg_eq n hn)]
      have hYn : 0 < Y / n := div_pos hY0 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      exact (Perron.isIntegrable hYn (by norm_num) (by norm_num)).const_mul _
  have hg_norm : ∀ n, ∫ t, ‖g n t‖ =
      ‖term (fun n ↦ χ n) 2 n‖ * ∫ t : ℝ, ‖Perron.f Y ((2 : ℝ) + t * I)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1 with t
    rw [hg, norm_mul, norm_term_eq, norm_term_eq]
    simp
  have hg_sum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    simp_rw [hg_norm]
    exact (summable_norm_iff.mpr (LSeriesSummable_of_one_lt_re χ (by norm_num))).mul_right _
  -- Evaluate each term with the Perron formula.
  have hg_val : ∀ n, ∫ t, g n t = if n ∈ Finset.Icc 1 ⌊Y⌋₊ then
      2 * Real.pi * (χ n * (n : ℂ) ^ ((u : ℂ) * I) * (1 - n / Y)) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [funext (hg_eq n hn), integral_const_mul]
    split_ifs with hmem
    · have hnY : (n : ℝ) < Y :=
        lt_of_le_of_ne ((Nat.le_floor_iff hY0.le).mp (Finset.mem_Icc.mp hmem).2) (hYN n)
      rw [integral_perron_f_of_one_lt ((one_lt_div hn0).mpr hnY)]
      push_cast
      rw [one_div_div]
      ring
    · have hYn : Y < n := (Nat.floor_lt hY0.le).mp (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
        omega)
      rw [integral_perron_f_of_lt_one (div_pos hY0 hn0) ((div_lt_one hn0).mpr hYn), mul_zero]
  -- Interchange the sum and the integral.
  rw [VerticalIntegral, smul_eq_mul, funext hsum,
    ← integral_tsum_of_summable_integral_norm hg_int hg_sum, tsum_congr hg_val,
    tsum_eq_sum (s := Finset.Icc 1 ⌊Y⌋₊) (fun n hn ↦ ite_eq_right hn),
    Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn), ← Finset.mul_sum]
  ring

/-- Cauchy's theorem on the half-strip `σ ≤ re s ≤ σ'`, `im s ≥ T`: the integral up the
right side equals the integral up the left side minus the bottom side. -/
theorem integral_Ici_eq_of_holomorphicOn {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ T ≤ z.im})
    (htop : Tendsto (fun y : ℝ ↦ ∫ x : ℝ in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : IntegrableOn (fun y : ℝ ↦ f (σ + y * I)) (Ici T))
    (hright : IntegrableOn (fun y : ℝ ↦ f (σ' + y * I)) (Ici T)) :
    I * ∫ y in Ici T, f (σ' + y * I) =
      I * (∫ y in Ici T, f (σ + y * I)) - HIntegral f σ σ' T := by
  have hvert (s : ℝ) (hs : IntegrableOn (fun y : ℝ ↦ f (s + y * I)) (Ici T)) :
      Tendsto (fun U : ℝ ↦ I * ∫ y in T..U, f (s + y * I)) atTop
        (𝓝 (I * ∫ y in Ici T, f (s + y * I))) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact (intervalIntegral_tendsto_integral_Ioi T (hs.mono_set Ioi_subset_Ici_self)
      tendsto_id).const_mul I
  have hlim := ((tendsto_const_nhds (x := HIntegral f σ σ' T)).sub htop).add
    ((hvert σ' hright).sub (hvert σ hleft))
  have hzero : ∀ᶠ U : ℝ in atTop, 0 = HIntegral f σ σ' T - (∫ x : ℝ in σ..σ', f (x + U * I)) +
      (I * (∫ y in T..U, f (σ' + y * I)) - I * ∫ y in T..U, f (σ + y * I)) := by
    filter_upwards [eventually_ge_atTop T] with U hTU
    have h := hf.vanishesOnRectangle (z := σ + I * T) (w := σ' + I * U) fun z hz ↦ by
      rw [mem_Rect (by simp [hσ]) (by simp [hTU])] at hz
      simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, add_im, mul_im, one_mul, zero_add] at hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1⟩
    simp only [RectangleIntegral, HIntegral, VIntegral, add_re, ofReal_re, mul_re, I_re,
      zero_mul, I_im, ofReal_im, mul_zero, sub_self, add_zero, add_im, mul_im, one_mul,
      zero_add, smul_eq_mul] at h
    rw [HIntegral]
    linear_combination -h
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero)
  rw [sub_zero] at h0
  linear_combination h0

/-- Cauchy's theorem on the half-strip `σ ≤ re s ≤ σ'`, `im s ≤ T`: the integral down the
right side equals the integral down the left side plus the top side. -/
theorem integral_Iic_eq_of_holomorphicOn {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ z.im ≤ T})
    (hbot : Tendsto (fun y : ℝ ↦ ∫ x : ℝ in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : IntegrableOn (fun y : ℝ ↦ f (σ + y * I)) (Iic T))
    (hright : IntegrableOn (fun y : ℝ ↦ f (σ' + y * I)) (Iic T)) :
    I * ∫ y in Iic T, f (σ' + y * I) =
      I * (∫ y in Iic T, f (σ + y * I)) + HIntegral f σ σ' T := by
  have hvert (s : ℝ) (hs : IntegrableOn (fun y : ℝ ↦ f (s + y * I)) (Iic T)) :
      Tendsto (fun U : ℝ ↦ I * ∫ y in U..T, f (s + y * I)) atBot
        (𝓝 (I * ∫ y in Iic T, f (s + y * I))) := by
    have h := intervalIntegral_tendsto_integral_Iic (l := atBot) (a := id) T hs tendsto_id
    exact h.const_mul I
  have hlim := (hbot.sub (tendsto_const_nhds (x := HIntegral f σ σ' T))).add
    ((hvert σ' hright).sub (hvert σ hleft))
  have hzero : ∀ᶠ U : ℝ in atBot, 0 = (∫ x : ℝ in σ..σ', f (x + U * I)) - HIntegral f σ σ' T +
      (I * (∫ y in U..T, f (σ' + y * I)) - I * ∫ y in U..T, f (σ + y * I)) := by
    filter_upwards [eventually_le_atBot T] with U hUT
    have h := hf.vanishesOnRectangle (z := σ + I * U) (w := σ' + I * T) fun z hz ↦ by
      rw [mem_Rect (by simp [hσ]) (by simp [hUT])] at hz
      simp only [add_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, add_im, mul_im, one_mul, zero_add] at hz
      exact ⟨hz.1, hz.2.1, hz.2.2.2⟩
    simp only [RectangleIntegral, HIntegral, VIntegral, add_re, ofReal_re, mul_re, I_re,
      zero_mul, I_im, ofReal_im, mul_zero, sub_self, add_zero, add_im, mul_im, one_mul,
      zero_add, smul_eq_mul] at h
    rw [HIntegral]
    linear_combination -h
  have h0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero)
  rw [zero_sub] at h0
  linear_combination h0

/-- `C √(log (k (|t - u| + 3)))` splits off `C √(log (k (|u| + 3)))` at the cost of a factor
`exp(C²) (1 + |t|)^{1/4}`. -/
theorem exp_mul_sqrt_log_le {k C : ℝ} (hk : 1 ≤ k) (hC : 0 ≤ C) (t u : ℝ) :
    Real.exp (C * Real.sqrt (Real.log (k * (|t - u| + 3)))) ≤
      Real.exp (C ^ 2) * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) *
        (1 + |t|) ^ (1 / 4 : ℝ) := by
  set a := Real.log (k * (|u| + 3))
  set b := Real.log (1 + |t|)
  have ha : 0 ≤ a := Real.log_nonneg (by nlinarith [abs_nonneg u])
  have hb : 0 ≤ b := Real.log_nonneg (by linarith [abs_nonneg t])
  -- the logarithm splits
  have hlog : Real.log (k * (|t - u| + 3)) ≤ a + b := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log (by nlinarith [abs_nonneg (t - u)]) ?_
    have htu : |t - u| ≤ |t| + |u| := abs_sub _ _
    nlinarith [abs_nonneg t, abs_nonneg u, mul_nonneg (abs_nonneg t) (abs_nonneg u)]
  -- so does its square root
  have hsqrt : Real.sqrt (Real.log (k * (|t - u| + 3))) ≤ Real.sqrt a + Real.sqrt b := by
    refine (Real.sqrt_le_sqrt hlog).trans ?_
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  -- and `C √b ≤ C² + b / 4`
  have hCb : C * Real.sqrt b ≤ C ^ 2 + b / 4 := by
    nlinarith [Real.sq_sqrt hb, sq_nonneg (Real.sqrt b / 2 - C)]
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
  gcongr
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hC]

/-- On `re s ≥ 1/2`, the Perron kernel is at most `8 Y^{re s} / (1 + |im s|)²`. -/
theorem norm_perron_f_le_of_re {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖Perron.f Y s‖ ≤ 8 * Y ^ s.re / (1 + |s.im|) ^ 2 := by
  have h1 : max (1 / 2) |s.im| ≤ ‖s‖ :=
    max_le (hs.trans ((le_abs_self _).trans (abs_re_le_norm s))) (abs_im_le_norm s)
  have h2 : max 1 |s.im| ≤ ‖s + 1‖ := by
    refine max_le ?_ (by simpa using abs_im_le_norm (s + 1))
    have := (le_abs_self _).trans (abs_re_le_norm (s + 1))
    simp only [add_re, one_re] at this
    linarith
  have h3 : (1 + |s.im|) ^ 2 ≤ 8 * ‖s * (s + 1)‖ := by
    rw [norm_mul]
    have := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    have h4 : (1 + |s.im|) / 4 ≤ max (1 / 2) |s.im| := by
      rcases le_total |s.im| (1 / 2) with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h]; linarith
    have h5 : (1 + |s.im|) / 2 ≤ max 1 |s.im| := by
      rcases le_total |s.im| 1 with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h]; linarith
    nlinarith [mul_le_mul h4 h5 (by positivity) (by positivity), abs_nonneg s.im]
  have hpos : 0 < (1 + |s.im|) ^ 2 := by positivity
  rw [Perron.f, norm_div, norm_cpow_eq_rpow_re_of_pos hY,
    div_le_div_iff₀ (by nlinarith) hpos]
  nlinarith [Real.rpow_pos_of_pos hY s.re]

/-- Off the real axis, the Perron kernel is at most `Y^{re s} / (im s)²`. -/
theorem norm_perron_f_le_of_im {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : s.im ≠ 0) :
    ‖Perron.f Y s‖ ≤ Y ^ s.re / s.im ^ 2 := by
  have h1 : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h2 : |s.im| ≤ ‖s + 1‖ := by simpa using abs_im_le_norm (s + 1)
  have h3 : s.im ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, ← sq_abs]
    nlinarith [abs_nonneg s.im]
  rw [Perron.f, norm_div, norm_cpow_eq_rpow_re_of_pos hY]
  gcongr

/-- The Perron kernel is holomorphic off `0` and `-1`. -/
theorem differentiableAt_perron_f {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Perron.f Y) s := by
  have hopen : IsOpen ({0, -1}ᶜ : Set ℂ) := (Set.toFinite _).isClosed.isOpen_compl
  refine (Perron.isHolomorphicOn hY).differentiableAt (hopen.mem_nhds ?_)
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor <;> rintro rfl <;> norm_num at hs

/-- The kernel integrand is holomorphic on `re s > 0` away from `s = 1 + iu`. -/
theorem differentiableAt_kernelIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (u : ℝ) {Y : ℝ} (hY : 0 < Y) {s : ℂ} (hs : 0 < s.re) (hs1 : s - u * I ≠ 1) :
    DifferentiableAt ℂ (kernelIntegrand χ u Y) s :=
  ((differentiableAt_LFunction χ _ (Or.inl hs1)).comp s
    (differentiableAt_id.sub_const _)).mul (differentiableAt_perron_f hY hs)

/-- The kernel integrand is continuous on each vertical line `re s = σ` with
`0 < σ ≠ 1`. -/
theorem continuous_kernelIntegrand_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (u : ℝ) {Y : ℝ} (hY : 0 < Y) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) :
    Continuous fun t : ℝ ↦ kernelIntegrand χ u Y (σ + t * I) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  refine ((differentiableAt_kernelIntegrand χ u hY (by simpa using hσ) fun h ↦ hσ1 ?_)
    |>.continuousAt).comp (by fun_prop : Continuous fun t : ℝ ↦ (σ : ℂ) + t * I).continuousAt
  simpa using congrArg re h

/-- The integrable majorant `(1 + |t|)^{-7/4}`. -/
theorem integrable_one_add_abs_rpow : Integrable fun t : ℝ ↦ (1 + |t|) ^ (-(7 / 4 : ℝ)) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 7 / 4)
    (by rw [Module.finrank_self]; norm_num)
  simpa only [Real.norm_eq_abs] using h

/-- The smoothed sums `∑_{n ≤ Y} χ(n) n^{iu} (1 - n / Y)` at heights `|u| ≥ 6`: shifting
the line of integration to `re s = 63/64` away from `|im s - u| < 3` gives
`O(exp(C √(log (k (|u| + 3)))) (Y^{63/64} + Y² / u²))`. -/
theorem norm_perronSum_le : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (u Y : ℝ), 6 ≤ |u| → 1 < Y → (∀ m : ℕ, (m : ℝ) ≠ Y) →
    ‖∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, χ m * (m : ℂ) ^ ((u : ℂ) * I) * (1 - m / Y)‖ ≤
      K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) *
        (Y ^ (63 / 64 : ℝ) + Y ^ 2 / u ^ 2) := by
  obtain ⟨C₀, hC₀⟩ := norm_LFunction_le_exp_sqrt
  set C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  set Z : ℝ := ∑' n, ‖term 1 2 n‖
  have hZ : 0 ≤ Z := tsum_nonneg fun _ ↦ norm_nonneg _
  set K₁ : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-(7 / 4 : ℝ))
  have hK₁ : 0 ≤ K₁ := integral_nonneg fun t ↦ by positivity
  refine ⟨C, 16 * Real.exp (C ^ 2) * K₁ + 9 + 24 * Z, hC, by positivity,
    fun k _ χ u Y hu hY hYN ↦ ?_⟩
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hY0 : 0 < Y := by linarith
  set E := Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3))))
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hC (Real.sqrt_nonneg _))
  set F := kernelIntegrand χ u Y
  set σ₀ : ℝ := 63 / 64
  -- the L-factor in the strip, away from the pole
  have hL : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 → 3 ≤ |s.im - u| →
      ‖LFunction χ (s - u * I)‖ ≤
        Real.exp (C * Real.sqrt (Real.log (k * (|s.im - u| + 3)))) := by
    intro s hs1 hs2 hs3
    have h := hC₀ k χ (s - u * I) (by simpa using hs1) (by simpa using hs2) (by simpa using hs3)
    simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero] at h
    exact h.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)))
  -- the integrand in the strip, away from the pole
  have hF : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 2 → 3 ≤ |s.im - u| →
      ‖F s‖ ≤ 8 * Real.exp (C ^ 2) * E * Y ^ s.re * (1 + |s.im|) ^ (-(7 / 4 : ℝ)) := by
    intro s hs1 hs2 hs3
    have h1 := (hL s hs1 hs2 hs3).trans (exp_mul_sqrt_log_le hk hC s.im u)
    have h2 := norm_perron_f_le_of_re hY0 (s := s) (by norm_num at hs1 ⊢; linarith)
    have hpos : 0 < 1 + |s.im| := by positivity
    have hsplit : (1 + |s.im|) ^ (-(7 / 4 : ℝ)) =
        (1 + |s.im|) ^ (1 / 4 : ℝ) / (1 + |s.im|) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_sub hpos]
      norm_num
    rw [show F s = LFunction χ (s - u * I) * Perron.f Y s from rfl, norm_mul, hsplit]
    calc ‖LFunction χ (s - u * I)‖ * ‖Perron.f Y s‖
        ≤ (Real.exp (C ^ 2) * E * (1 + |s.im|) ^ (1 / 4 : ℝ)) *
            (8 * Y ^ s.re / (1 + |s.im|) ^ 2) := by gcongr
      _ = _ := by ring
  have hσ₀ : (0 : ℝ) < σ₀ := by norm_num
  have hσ₀1 : σ₀ ≠ 1 := by norm_num
  have hcont₀ := continuous_kernelIntegrand_line χ u hY0 hσ₀ hσ₀1
  have hcont₂ := continuous_kernelIntegrand_line χ u hY0 (σ := 2) (by norm_num) (by norm_num)
  have hg := integrable_one_add_abs_rpow
  set c : ℝ := 8 * Real.exp (C ^ 2) * E * Y ^ σ₀
  -- the integrand on the shifted line, away from the pole
  have hF₀ : ∀ t : ℝ, 3 ≤ |t - u| →
      ‖F (σ₀ + t * I)‖ ≤ c * (1 + |t|) ^ (-(7 / 4 : ℝ)) := by
    intro t ht
    simpa using hF (σ₀ + t * I) (by simp) (by norm_num) (by simpa using ht)
  have hint₀ : ∀ S : Set ℝ, MeasurableSet S → (∀ t ∈ S, 3 ≤ |t - u|) →
      IntegrableOn (fun t : ℝ ↦ F (σ₀ + t * I)) S := fun S hS hSu ↦
    (hg.integrableOn.const_mul c).mono' hcont₀.aestronglyMeasurable
      (ae_restrict_of_forall_mem hS fun t ht ↦ hF₀ t (hSu t ht))
  have hbound₀ : ∀ S : Set ℝ, MeasurableSet S → (∀ t ∈ S, 3 ≤ |t - u|) →
      ‖∫ t in S, F (σ₀ + t * I)‖ ≤ c * K₁ := by
    intro S hS hSu
    calc ‖∫ t in S, F (σ₀ + t * I)‖
        ≤ ∫ t in S, ‖F (σ₀ + t * I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in S, c * (1 + |t|) ^ (-(7 / 4 : ℝ)) :=
          setIntegral_mono_on (hint₀ S hS hSu).norm (hg.integrableOn.const_mul c) hS
            fun t ht ↦ hF₀ t (hSu t ht)
      _ ≤ ∫ t, c * (1 + |t|) ^ (-(7 / 4 : ℝ)) :=
          setIntegral_le_integral (hg.const_mul c) (ae_of_all _ fun t ↦ by positivity)
      _ = c * K₁ := integral_const_mul _ _
  -- the integrand on the line `re s = 2`
  have hF₂ : ∀ t : ℝ, ‖F ((2 : ℝ) + t * I)‖ ≤ Z * ‖Perron.f Y ((2 : ℝ) + t * I)‖ := by
    intro t
    rw [show F ((2 : ℝ) + t * I) = LFunction χ ((2 : ℝ) + t * I - u * I) *
      Perron.f Y ((2 : ℝ) + t * I) from rfl, norm_mul]
    gcongr
    exact norm_LFunction_le_of_re_eq_two χ (by simp)
  have hint₂ : Integrable fun t : ℝ ↦ F ((2 : ℝ) + t * I) :=
    ((Perron.isIntegrable hY0 (by norm_num) (by norm_num)).norm.const_mul Z).mono'
      hcont₂.aestronglyMeasurable (ae_of_all _ hF₂)
  -- the horizontal integrals vanish at `±∞`
  have hhoriz : ∀ y : ℝ, 3 ≤ |y - u| →
      ‖∫ x : ℝ in σ₀..2, F (x + y * I)‖ ≤
        8 * Real.exp (C ^ 2) * E * Y ^ (2 : ℝ) * (1 + |y|) ^ (-(7 / 4 : ℝ)) * |2 - σ₀| := by
    intro y hy
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ ?_
    rw [uIoc_of_le (by norm_num)] at hx
    refine (hF (x + y * I) (by simpa using hx.1.le) (by simpa using hx.2)
      (by simpa using hy)).trans ?_
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    gcongr
    · exact hY.le
    · exact hx.2
  have hdecay : Tendsto (fun y : ℝ ↦ (1 + |y|) ^ (-(7 / 4 : ℝ))) (atBot ⊔ atTop) (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp
      (tendsto_atTop_add_const_left _ 1 (tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop))
  have hlimit : Tendsto (fun y : ℝ ↦ ∫ x : ℝ in σ₀..2, F (x + y * I)) (atBot ⊔ atTop)
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa only [mul_zero, zero_mul] using (hdecay.const_mul
      (8 * Real.exp (C ^ 2) * E * Y ^ (2 : ℝ))).mul_const |2 - σ₀|)
    have hev : ∀ᶠ y : ℝ in atBot ⊔ atTop, 3 ≤ |y - u| := by
      refine eventually_sup.mpr ⟨?_, ?_⟩
      · filter_upwards [eventually_le_atBot (u - 3)] with y hy
        rw [abs_of_nonpos (by linarith)]
        linarith
      · filter_upwards [eventually_ge_atTop (u + 3)] with y hy
        rw [abs_of_nonneg (by linarith)]
        linarith
    filter_upwards [hev] with y hy
    exact hhoriz y hy
  -- Cauchy's theorem on the two half-strips
  have hhol : ∀ z : ℂ, σ₀ ≤ z.re → 3 ≤ |z.im - u| → DifferentiableWithinAt ℂ F
      {z : ℂ | σ₀ ≤ z.re ∧ z.re ≤ 2 ∧ u + 3 ≤ z.im} z ∧ DifferentiableWithinAt ℂ F
      {z : ℂ | σ₀ ≤ z.re ∧ z.re ≤ 2 ∧ z.im ≤ u - 3} z := by
    intro z hz hzu
    have h := differentiableAt_kernelIntegrand χ u hY0 (s := z) (by linarith) fun h ↦ by
      have := congrArg im h
      simp only [sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
        add_zero, one_im] at this
      rw [this] at hzu
      norm_num at hzu
    exact ⟨h.differentiableWithinAt, h.differentiableWithinAt⟩
  have hupper := integral_Ici_eq_of_holomorphicOn (f := F) (σ := σ₀) (σ' := 2) (T := u + 3)
    (by norm_num) (fun z hz ↦ (hhol z hz.1 (by
      rw [abs_of_nonneg (by linarith [hz.2.2])]; linarith [hz.2.2])).1)
    (hlimit.mono_left le_sup_right)
    (hint₀ _ measurableSet_Ici fun t ht ↦ by
      rw [abs_of_nonneg (by linarith [mem_Ici.mp ht])]; linarith [mem_Ici.mp ht])
    hint₂.integrableOn
  have hlower := integral_Iic_eq_of_holomorphicOn (f := F) (σ := σ₀) (σ' := 2) (T := u - 3)
    (by norm_num) (fun z hz ↦ (hhol z hz.1 (by
      rw [abs_of_nonpos (by linarith [hz.2.2])]; linarith [hz.2.2])).2)
    (hlimit.mono_left le_sup_left)
    (hint₀ _ measurableSet_Iic fun t ht ↦ by
      rw [abs_of_nonpos (by linarith [mem_Iic.mp ht])]; linarith [mem_Iic.mp ht])
    hint₂.integrableOn
  -- the horizontal sides at heights `u ± 3`
  have hu0 : 0 < u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  have hside : ∀ y : ℝ, |y - u| = 3 →
      ‖HIntegral F σ₀ 2 y‖ ≤ E * (4 * Y ^ 2 / u ^ 2) * |2 - σ₀| := by
    intro y hy
    have hyu : u ^ 2 ≤ 4 * y ^ 2 := by
      have : |u| - 3 ≤ |y| := by linarith [abs_sub_abs_le_abs_sub u y, abs_sub_comm u y]
      nlinarith [sq_abs u, sq_abs y, abs_nonneg y]
    have hy0 : y ≠ 0 := by intro h; rw [h] at hyu; nlinarith
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ ?_
    rw [uIoc_of_le (by norm_num)] at hx
    have hx1 : σ₀ ≤ x := hx.1.le
    rw [show F (x + y * I) = LFunction χ (x + y * I - u * I) * Perron.f Y (x + y * I) from rfl,
      norm_mul]
    have h1 : ‖LFunction χ (x + y * I - u * I)‖ ≤ E := by
      refine (hL _ (by simpa using hx1) (by simpa using hx.2) (by simp [hy])).trans ?_
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add, hy]
      show _ ≤ Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3))))
      gcongr
      linarith
    have h2 : ‖Perron.f Y (x + y * I)‖ ≤ 4 * Y ^ 2 / u ^ 2 := by
      refine (norm_perron_f_le_of_im hY0 (by simpa using hy0)).trans ?_
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, add_im, mul_im, zero_add]
      rw [div_le_div_iff₀ (by positivity) hu0]
      have hYx : Y ^ x ≤ Y ^ 2 := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num; exact hx.2)
      nlinarith [Real.rpow_pos_of_pos hY0 x]
    exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
  -- the part of the line `re s = 2` near the pole
  have hmid : ‖VIntegral F 2 (u - 3) (u + 3)‖ ≤ Z * (4 * Y ^ 2 / u ^ 2) * |u + 3 - (u - 3)| := by
    rw [VIntegral, norm_smul, norm_I, one_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [uIoc_of_le (by linarith)] at ht
    have htu : u ^ 2 ≤ 4 * t ^ 2 := by
      have : |u| - 3 ≤ |t| := by
        have := abs_sub_abs_le_abs_sub u t
        rw [abs_sub_comm] at this
        linarith [abs_le.mpr (⟨by linarith [ht.1], by linarith [ht.2]⟩ : -3 ≤ t - u ∧ t - u ≤ 3)]
      nlinarith [sq_abs u, sq_abs t, abs_nonneg t]
    have ht0 : t ≠ 0 := by intro h; rw [h] at htu; nlinarith
    refine (hF₂ t).trans (mul_le_mul_of_nonneg_left ?_ hZ)
    refine (norm_perron_f_le_of_im hY0 (by simpa using ht0)).trans ?_
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
    rw [div_le_div_iff₀ (by positivity) hu0, show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    nlinarith [sq_nonneg Y]
  -- assemble the contour
  have hVI := verticalIntegral_kernelIntegrand χ u hY hYN
  rw [verticalIntegral_split_three (u - 3) (u + 3) hint₂, smul_eq_mul, smul_eq_mul, hupper,
    hlower] at hVI
  have hnorm : ‖2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊,
      χ m * (m : ℂ) ^ ((u : ℂ) * I) * (1 - m / Y)‖ ≤
      2 * (c * K₁) + 2 * (E * (4 * Y ^ 2 / u ^ 2) * |2 - σ₀|) +
        Z * (4 * Y ^ 2 / u ^ 2) * |u + 3 - (u - 3)| := by
    rw [← hVI]
    have h1 := hbound₀ (Iic (u - 3)) measurableSet_Iic fun t ht ↦ by
      rw [abs_of_nonpos (by linarith [mem_Iic.mp ht])]; linarith [mem_Iic.mp ht]
    have h2 := hbound₀ (Ici (u + 3)) measurableSet_Ici fun t ht ↦ by
      rw [abs_of_nonneg (by linarith [mem_Ici.mp ht])]; linarith [mem_Ici.mp ht]
    have h3 := hside (u - 3) (by norm_num)
    have h4 := hside (u + 3) (by norm_num)
    calc _ ≤ ‖(I * ∫ y in Iic (u - 3), F (σ₀ + y * I)) + HIntegral F σ₀ 2 (u - 3) +
          VIntegral F 2 (u - 3) (u + 3)‖ +
          ‖(I * ∫ y in Ici (u + 3), F (σ₀ + y * I)) - HIntegral F σ₀ 2 (u + 3)‖ :=
          norm_add_le _ _
      _ ≤ ‖I * ∫ y in Iic (u - 3), F (σ₀ + y * I)‖ + ‖HIntegral F σ₀ 2 (u - 3)‖ +
          ‖VIntegral F 2 (u - 3) (u + 3)‖ +
          (‖I * ∫ y in Ici (u + 3), F (σ₀ + y * I)‖ + ‖HIntegral F σ₀ 2 (u + 3)‖) := by
          gcongr
          · exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
          · exact norm_sub_le _ _
      _ ≤ _ := by
          rw [norm_mul, norm_I, one_mul, norm_mul, norm_I, one_mul]
          linarith
  rw [norm_mul, show ‖2 * (Real.pi : ℂ) * I‖ = 2 * Real.pi by
    rw [norm_mul, norm_I, mul_one, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]] at hnorm
  have hσ₀abs : |2 - σ₀| = 65 / 64 := by
    have h : (2 : ℝ) - σ₀ = 65 / 64 := by simp only [σ₀]; norm_num
    rw [h, abs_of_pos (by norm_num)]
  have h6 : |u + 3 - (u - 3)| = 6 := by
    rw [show u + 3 - (u - 3) = 6 by ring, abs_of_pos (by norm_num)]
  rw [hσ₀abs, h6] at hnorm
  set p := Y ^ σ₀
  set q := Y ^ 2 / u ^ 2
  have hp : 0 ≤ p := Real.rpow_nonneg hY0.le _
  have hq : 0 ≤ q := by positivity
  have hA : 0 ≤ Real.exp (C ^ 2) * K₁ := mul_nonneg (Real.exp_pos _).le hK₁
  have hsum : ‖∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, χ m * (m : ℂ) ^ ((u : ℂ) * I) * (1 - m / Y)‖ ≤
      2 * (c * K₁) + 2 * (E * (4 * q) * (65 / 64)) + Z * (4 * q) * 6 := by
    have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have h0 := norm_nonneg (∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, χ m * (m : ℂ) ^ ((u : ℂ) * I) *
      (1 - m / Y))
    simp only [q, mul_div_assoc] at hnorm ⊢
    nlinarith
  refine hsum.trans ?_
  simp only [c]
  nlinarith [mul_nonneg (mul_nonneg hA (by linarith : (0 : ℝ) ≤ E)) hq,
    mul_nonneg (by linarith : (0 : ℝ) ≤ E) hp,
    mul_nonneg (mul_nonneg hZ hp) (by linarith : (0 : ℝ) ≤ E),
    mul_nonneg hZ hq, mul_nonneg (mul_nonneg hZ hq) (by linarith : (0 : ℝ) ≤ E - 1),
    mul_nonneg (by linarith : (0 : ℝ) ≤ E) hq]

/-- The smoothed sum `∑_{1 ≤ n ≤ Y} χ(n) n^{iu} (1 - n / Y)`. -/
noncomputable def perronSum {N : ℕ} (χ : DirichletCharacter ℂ N) (u Y : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 ⌊Y⌋₊, χ m * (m : ℂ) ^ ((u : ℂ) * I) * (1 - m / Y)

/-- `Y` times the smoothed sum is the sum against the hinge `max (Y - n) 0`, over any range
`[1, R]` covering `[1, Y]`. -/
theorem mul_perronSum_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) {Y : ℝ} (hY : 0 < Y)
    {R : ℕ} (hR : ⌊Y⌋₊ ≤ R) :
    (Y : ℂ) * perronSum χ u Y = ∑ m ∈ Finset.Icc 1 R,
      χ m * (m : ℂ) ^ ((u : ℂ) * I) * ((max (Y - m) 0 : ℝ) : ℂ) := by
  rw [perronSum, Finset.mul_sum]
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right hR) (fun m _ hm ↦ ?_) |>.symm.trans
    (Finset.sum_congr rfl fun m hm ↦ ?_)
  · have hYm : Y < m := (Nat.floor_lt hY.le).mp (by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hm
      rcases hm with hm | hm
      · exact absurd hm (by simp at *; omega)
      · exact hm)
    rw [max_eq_right (by linarith), ofReal_zero, mul_zero]
  · have hmY : (m : ℝ) ≤ Y := (Nat.le_floor_iff hY.le).mp (Finset.mem_Icc.mp hm).2
    rw [max_eq_left (by linarith)]
    have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hY.ne'
    push_cast
    field_simp

/-- `‖n^{iu}‖ ≤ 1`. -/
theorem norm_natCast_cpow_I_mul_le (u : ℝ) (n : ℕ) : ‖(n : ℂ) ^ ((u : ℂ) * I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases eq_or_ne u 0 with rfl | hu
    · simp
    · rw [Nat.cast_zero, zero_cpow (by simpa using hu), norm_zero]
      exact zero_le_one
  · rw [norm_natCast_cpow_of_pos hn]
    simp

/-- The trapezoid weight `M 1_{(A, B]} - (hinges)` is supported on the two ramps and has
size at most `M`. -/
theorem abs_trapezoid_le {A B M m : ℕ} (hMA : M ≤ A) (hAB : A ≤ B) :
    |(M : ℝ) * (if m ∈ Finset.Ioc A B then 1 else 0) -
        (max ((B + M + 1 / 2 : ℝ) - m) 0 - max ((B + 1 / 2 : ℝ) - m) 0 -
          max ((A + 1 / 2 : ℝ) - m) 0 + max ((A - M + 1 / 2 : ℝ) - m) 0)| ≤
      M * (if m ∈ Finset.Ioc (A - M) A ∪ Finset.Ioc B (B + M) then 1 else 0) := by
  simp only [Finset.mem_Ioc, Finset.mem_union]
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hMA' : (M : ℝ) ≤ A := by exact_mod_cast hMA
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  rcases (by omega : m + M ≤ A ∨ (A < m + M ∧ m ≤ A) ∨ (A < m ∧ m ≤ B) ∨
      (B < m ∧ m ≤ B + M) ∨ B + M < m) with h | h | h | h | h
  · have hm : (m : ℝ) + M ≤ A := by exact_mod_cast h
    rw [ite_eq_right (by omega), ite_eq_right (by omega), max_eq_left (by linarith),
      max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
    norm_num
    ring
  · have hm1 : (A : ℝ) + 1 ≤ m + M := by exact_mod_cast h.1
    have hm2 : (m : ℝ) ≤ A := by exact_mod_cast h.2
    rw [ite_eq_right (by omega), ite_eq_left (by omega), max_eq_left (by linarith),
      max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith),
      abs_le]
    constructor <;> linarith
  · have hm1 : (A : ℝ) + 1 ≤ m := by exact_mod_cast h.1
    have hm2 : (m : ℝ) ≤ B := by exact_mod_cast h.2
    rw [ite_eq_left (by omega), ite_eq_right (by omega), max_eq_left (by linarith),
      max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    norm_num
  · have hm1 : (B : ℝ) + 1 ≤ m := by exact_mod_cast h.1
    have hm2 : (m : ℝ) ≤ B + M := by exact_mod_cast h.2
    rw [ite_eq_right (by omega), ite_eq_left (by omega), max_eq_left (by linarith),
      max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith),
      abs_le]
    constructor <;> linarith
  · have hm : (B : ℝ) + M + 1 ≤ m := by exact_mod_cast h
    rw [ite_eq_right (by omega), ite_eq_right (by omega), max_eq_right (by linarith),
      max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    norm_num

/-- The sharp sum over `(A, B]` against the trapezoid combination of four smoothed sums with
nodes `A - M + 1/2, A + 1/2, B + 1/2, B + M + 1/2`: the error is at most the ramp mass. -/
theorem norm_mul_sum_Ioc_sub_le {N : ℕ} (χ : DirichletCharacter ℂ N) (u : ℝ) {A B M : ℕ}
    (hMA : 2 * M ≤ A) (hAB : A ≤ B) :
    ‖(M : ℂ) * ∑ n ∈ Finset.Ioc A B, χ n * (n : ℂ) ^ ((u : ℂ) * I) -
        ((((B + M + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + M + 1 / 2) -
          ((B + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + 1 / 2) -
          ((A + 1 / 2 : ℝ) : ℂ) * perronSum χ u (A + 1 / 2)) +
          ((A - M + 1 / 2 : ℝ) : ℂ) * perronSum χ u (A - M + 1 / 2))‖ ≤ M * (2 * M) := by
  have hMA' : (2 * M : ℝ) ≤ A := by exact_mod_cast hMA
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hfloor : ∀ Y : ℝ, Y ≤ B + M + 1 / 2 → ⌊Y⌋₊ ≤ B + M := fun Y hY ↦
    Nat.lt_succ_iff.mp ((Nat.floor_lt' (by omega)).mpr (by push_cast; linarith))
  set f : ℕ → ℂ := fun n ↦ χ n * (n : ℂ) ^ ((u : ℂ) * I)
  have hIoc : ∑ n ∈ Finset.Ioc A B, f n =
      ∑ n ∈ Finset.Icc 1 (B + M), if n ∈ Finset.Ioc A B then f n else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr fun n hn ↦ by
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega]
  set w : ℕ → ℝ := fun n ↦ (M : ℝ) * (if n ∈ Finset.Ioc A B then 1 else 0) -
    (max ((B + M + 1 / 2 : ℝ) - n) 0 - max ((B + 1 / 2 : ℝ) - n) 0 -
      max ((A + 1 / 2 : ℝ) - n) 0 + max ((A - M + 1 / 2 : ℝ) - n) 0)
  rw [mul_perronSum_eq χ u (by positivity) (hfloor _ le_rfl),
    mul_perronSum_eq χ u (by positivity) (hfloor _ (by linarith)),
    mul_perronSum_eq χ u (by positivity) (hfloor _ (by linarith)),
    mul_perronSum_eq χ u (by linarith) (hfloor _ (by linarith)), hIoc]
  have heq : ((M : ℂ) * ∑ n ∈ Finset.Icc 1 (B + M), if n ∈ Finset.Ioc A B then f n else 0) -
      (∑ n ∈ Finset.Icc 1 (B + M), f n * ((max ((B + M + 1 / 2 : ℝ) - n) 0 : ℝ) : ℂ) -
        ∑ n ∈ Finset.Icc 1 (B + M), f n * ((max ((B + 1 / 2 : ℝ) - n) 0 : ℝ) : ℂ) -
        ∑ n ∈ Finset.Icc 1 (B + M), f n * ((max ((A + 1 / 2 : ℝ) - n) 0 : ℝ) : ℂ) +
        ∑ n ∈ Finset.Icc 1 (B + M), f n * ((max ((A - M + 1 / 2 : ℝ) - n) 0 : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 (B + M), f n * (w n : ℂ) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp only [w]
    split_ifs <;> push_cast <;> ring
  rw [heq]
  calc ‖∑ n ∈ Finset.Icc 1 (B + M), f n * (w n : ℂ)‖
      ≤ ∑ n ∈ Finset.Icc 1 (B + M),
          (M : ℝ) * (if n ∈ Finset.Ioc (A - M) A ∪ Finset.Ioc B (B + M) then 1 else 0) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hf : ‖f n‖ ≤ 1 := by
          simp only [f, norm_mul]
          simpa using mul_le_mul (χ.norm_le_one n) (norm_natCast_cpow_I_mul_le u n)
            (norm_nonneg _) zero_le_one
        exact (mul_le_mul hf (abs_trapezoid_le (by omega) hAB) (abs_nonneg _) zero_le_one).trans
          (by rw [one_mul])
    _ ≤ M * (2 * M) := by
        rw [← Finset.mul_sum, Finset.sum_boole]
        gcongr
        calc (((Finset.Icc 1 (B + M)).filter
              (· ∈ Finset.Ioc (A - M) A ∪ Finset.Ioc B (B + M))).card : ℝ)
            ≤ ((Finset.Ioc (A - M) A ∪ Finset.Ioc B (B + M)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card fun n hn ↦ (Finset.mem_filter.mp hn).2
          _ ≤ 2 * M := by
              have := Finset.card_union_le (Finset.Ioc (A - M) A) (Finset.Ioc B (B + M))
              simp only [Nat.card_Ioc] at this
              exact_mod_cast (this.trans (by omega))

/-- No integer is a half-integer. -/
theorem natCast_ne_add_half (n m : ℕ) : (m : ℝ) ≠ n + 1 / 2 := by
  intro h
  have h2 : ((2 * m : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have := Nat.cast_injective h2
  omega

/-- Sharp twisted sums over `(A, B]` at heights `|u| ≥ 6`, through the trapezoid of ramp
width `M`: `O(M + (B / M) exp(C √(log (k (|u| + 3)))) (B^{63/64} + B² / u²))`. -/
theorem norm_sum_Ioc_le : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (u : ℝ) (A B M : ℕ), 6 ≤ |u| → 1 ≤ M → 2 * M ≤ A → A ≤ B →
    ‖∑ n ∈ Finset.Ioc A B, χ n * (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
      2 * M + 4 * ((B + M + 1) / M) *
        (K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) *
          ((B + M + 1) ^ (63 / 64 : ℝ) + (B + M + 1) ^ 2 / u ^ 2)) := by
  obtain ⟨C, K, hC, hK, hS⟩ := norm_perronSum_le
  refine ⟨C, K, hC, hK, fun k _ χ u A B M hu hM hMA hAB ↦ ?_⟩
  set E := Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3))))
  set Yt : ℝ := B + M + 1
  set G : ℝ → ℝ := fun Y ↦ K * E * (Y ^ (63 / 64 : ℝ) + Y ^ 2 / u ^ 2)
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMA' : (2 * M : ℝ) ≤ A := by exact_mod_cast hMA
  have hAB' : (A : ℝ) ≤ B := by exact_mod_cast hAB
  -- each node contributes at most `Yt G(Yt)`
  have hnode : ∀ Y : ℝ, 1 < Y → Y ≤ Yt → (∀ m : ℕ, (m : ℝ) ≠ Y) →
      ‖(Y : ℂ) * perronSum χ u Y‖ ≤ Yt * G Yt := by
    intro Y hY hYt hYN
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine mul_le_mul hYt ((hS k χ u Y hu hY hYN).trans ?_) (norm_nonneg _) (by positivity)
    have hE : 0 ≤ K * E := mul_nonneg hK (Real.exp_pos _).le
    simp only [G]
    gcongr
  have hhalf : ∀ n : ℕ, ∀ m : ℕ, (m : ℝ) ≠ n + 1 / 2 := natCast_ne_add_half
  have h₁ := hnode (B + M + 1 / 2) (by linarith) (by simp only [Yt]; linarith)
    (by exact_mod_cast hhalf (B + M))
  have h₂ := hnode (B + 1 / 2) (by linarith) (by simp only [Yt]; linarith) (hhalf B)
  have h₃ := hnode (A + 1 / 2) (by linarith) (by simp only [Yt]; linarith) (hhalf A)
  have h₄ := hnode (A - M + 1 / 2) (by linarith) (by simp only [Yt]; linarith)
    (by have := hhalf (A - M); rwa [Nat.cast_sub (by omega : M ≤ A)] at this)
  have htrap := norm_mul_sum_Ioc_sub_le χ u hMA hAB
  set T := ∑ n ∈ Finset.Ioc A B, χ n * (n : ℂ) ^ ((u : ℂ) * I)
  have hMT : (M : ℝ) * ‖T‖ ≤ M * (2 * M) + 4 * (Yt * G Yt) := by
    have := norm_sub_norm_le ((M : ℂ) * T) _ |>.trans htrap
    rw [norm_mul, Complex.norm_natCast] at this
    have h5 := norm_add_le (((B + M + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + M + 1 / 2) -
      ((B + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + 1 / 2) -
      ((A + 1 / 2 : ℝ) : ℂ) * perronSum χ u (A + 1 / 2))
      (((A - M + 1 / 2 : ℝ) : ℂ) * perronSum χ u (A - M + 1 / 2))
    have h6 := norm_sub_le (((B + M + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + M + 1 / 2) -
      ((B + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + 1 / 2))
      (((A + 1 / 2 : ℝ) : ℂ) * perronSum χ u (A + 1 / 2))
    have h7 := norm_sub_le (((B + M + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + M + 1 / 2))
      (((B + 1 / 2 : ℝ) : ℂ) * perronSum χ u (B + 1 / 2))
    linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hT : ‖T‖ ≤ 2 * M + 4 * (Yt * G Yt) / M := by
    calc ‖T‖ = (M * ‖T‖) / M := by field_simp
      _ ≤ (M * (2 * M) + 4 * (Yt * G Yt)) / M := by gcongr
      _ = _ := by field_simp
  refine hT.trans_eq ?_
  simp only [G, Yt, E]
  ring

/-- A sum over a unit residue class is an average of character twists, so it is bounded by
any bound uniform over the characters. -/
theorem norm_sum_filter_modEq_le_of_coprime {k a : ℕ} [NeZero k] (ha : a.Coprime k)
    (f : ℕ → ℂ) (s : Finset ℕ) {X : ℝ}
    (hX : ∀ χ : DirichletCharacter ℂ k, ‖∑ n ∈ s, χ n * f n‖ ≤ X) :
    ‖∑ n ∈ s.filter (· ≡ a [MOD k]), f n‖ ≤ X := by
  have hu : IsUnit (a : ZMod k) := (ZMod.isUnit_iff_coprime a k).mpr ha
  have hφ : (0 : ℝ) < k.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hcard : (Finset.univ : Finset (DirichletCharacter ℂ k)).card = k.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  -- orthogonality of characters
  have horth : ∑ χ : DirichletCharacter ℂ k, χ (a : ZMod k)⁻¹ * ∑ n ∈ s, χ n * f n =
      (k.totient : ℂ) * ∑ n ∈ s.filter (· ≡ a [MOD k]), f n := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp_rw [← mul_assoc, ← Finset.sum_mul,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod k),
      ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm (a := a)]
    split_ifs <;> simp
  have hle : ‖(k.totient : ℂ) * ∑ n ∈ s.filter (· ≡ a [MOD k]), f n‖ ≤ k.totient * X := by
    rw [← horth]
    calc _ ≤ ∑ χ : DirichletCharacter ℂ k, X := (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun χ _ ↦ by
            rw [norm_mul]
            exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans (hX χ))
      _ = k.totient * X := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  rw [norm_mul, Complex.norm_natCast] at hle
  exact le_of_mul_le_mul_left hle hφ

/-- A residue class `a mod k` lies in the multiples of `g = (a, k)`: substituting `n = g m`
turns it into the unit class `a / g mod k / g` on `(A / g, B / g]`. -/
theorem sum_filter_modEq_eq_gcd {k a : ℕ} (hk : 0 < k) (A B : ℕ) (u : ℝ) :
    ∑ n ∈ (Finset.Ioc A B).filter (· ≡ a [MOD k]), (n : ℂ) ^ ((u : ℂ) * I) =
      ((a.gcd k : ℕ) : ℂ) ^ ((u : ℂ) * I) *
        ∑ m ∈ (Finset.Ioc (A / a.gcd k) (B / a.gcd k)).filter
          (· ≡ a / a.gcd k [MOD k / a.gcd k]), (m : ℂ) ^ ((u : ℂ) * I) := by
  set g := a.gcd k
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hk
  have hga : g * (a / g) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a k)
  have hgk : g * (k / g) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_right a k)
  -- the class `a mod k` in terms of the cofactor
  have hmod : ∀ m : ℕ, g * m ≡ a [MOD k] ↔ m ≡ a / g [MOD k / g] := by
    intro m
    constructor
    · intro h
      rw [← hga, ← hgk] at h
      exact Nat.ModEq.mul_left_cancel' hg.ne' h
    · intro h
      have := Nat.ModEq.mul_left' g h
      rwa [hga, hgk] at this
  have hdvd : ∀ n : ℕ, n ≡ a [MOD k] → g ∣ n := fun n h ↦ by
    rw [show g = n.gcd k from h.gcd_eq.symm]
    exact Nat.gcd_dvd_left n k
  have hIoc : ∀ m : ℕ, g * m ∈ Finset.Ioc A B ↔ m ∈ Finset.Ioc (A / g) (B / g) := by
    intro m
    simp only [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hg, Nat.le_div_iff_mul_le hg, mul_comm m]
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (· / g) (g * ·) (fun n hn ↦ ?_) (fun m hm ↦ ?_) (fun n hn ↦ ?_)
    (fun m _ ↦ Nat.mul_div_cancel_left m hg) (fun n hn ↦ ?_)
  · rw [Finset.mem_filter] at hn ⊢
    obtain ⟨m, rfl⟩ := hdvd n hn.2
    rw [Nat.mul_div_cancel_left m hg]
    exact ⟨(hIoc m).mp hn.1, (hmod m).mp hn.2⟩
  · rw [Finset.mem_filter] at hm ⊢
    exact ⟨(hIoc m).mpr hm.1, (hmod m).mpr hm.2⟩
  · exact Nat.mul_div_cancel' (hdvd n (Finset.mem_filter.mp hn).2)
  · obtain ⟨m, rfl⟩ := hdvd n (Finset.mem_filter.mp hn).2
    rw [Nat.mul_div_cancel_left m hg, Nat.cast_mul, natCast_mul_natCast_cpow]

/-- `y ↦ y^{iu}` is `|u| / y`-Lipschitz to the right of `y`. -/
theorem norm_cpow_I_mul_sub_le (u : ℝ) {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    ‖(z : ℂ) ^ ((u : ℂ) * I) - (y : ℂ) ^ ((u : ℂ) * I)‖ ≤ |u| * (z - y) / y := by
  have hz : 0 < z := hy.trans_le hyz
  have hlog : 0 ≤ Real.log z - Real.log y := sub_nonneg.mpr (Real.log_le_log hy hyz)
  have hlog' : Real.log z - Real.log y ≤ (z - y) / y := by
    rw [← Real.log_div hz.ne' hy.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hz hy)).trans_eq ?_
    field_simp
  rw [Complex.cpow_eq_exp_log_ofReal z hz, Complex.cpow_eq_exp_log_ofReal y hy,
    show (Real.log z : ℂ) * (u * I) = (Real.log y : ℂ) * (u * I) +
      I * ((u * (Real.log z - Real.log y) : ℝ) : ℂ) by push_cast; ring,
    Complex.exp_add, ← mul_sub_one, norm_mul,
    show (Real.log y : ℂ) * (u * I) = ((Real.log y * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hlog' (abs_nonneg u)

/-- The antiderivative `G(y) = y^{1+iu} / (1 + iu)` of `y^{iu}` matches a step of length `h`
up to `h² |u| / y`. -/
theorem norm_step_sub_le (u : ℝ) {y h : ℝ} (hy : 0 < y) (hh : 0 ≤ h) :
    ‖(h : ℂ) * (y : ℂ) ^ ((u : ℂ) * I) -
        (((y + h : ℝ) : ℂ) ^ (1 + (u : ℂ) * I) / (1 + u * I) -
          (y : ℂ) ^ (1 + (u : ℂ) * I) / (1 + u * I))‖ ≤ h ^ 2 * |u| / y := by
  have h1 : (1 + (u : ℂ) * I) ≠ 0 := fun h ↦ by simpa using congrArg re h
  set φ : ℝ → ℂ := fun z ↦ (z : ℂ) ^ (1 + (u : ℂ) * I) / (1 + u * I) -
    (z : ℂ) * (y : ℂ) ^ ((u : ℂ) * I)
  have hderiv : ∀ z ∈ Icc y (y + h), HasDerivWithinAt φ
      ((z : ℂ) ^ ((u : ℂ) * I) - (y : ℂ) ^ ((u : ℂ) * I)) (Icc y (y + h)) z := by
    intro z hz
    have hz0 : z ≠ 0 := (hy.trans_le hz.1).ne'
    have h2 := (hasDerivAt_ofReal_cpow_const hz0 h1).div_const (1 + u * I)
    have h3 := (hasDerivAt_id z).ofReal_comp.mul_const ((y : ℂ) ^ ((u : ℂ) * I))
    refine (h2.sub h3).hasDerivWithinAt.congr_deriv ?_
    simp only [add_sub_cancel_left, ofReal_one, one_mul]
    field_simp
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (C := |u| * h / y) (fun z hz ↦ by
      refine (norm_cpow_I_mul_sub_le u hy hz.1).trans ?_
      rw [mul_div_assoc, mul_div_assoc]
      gcongr
      linarith [hz.2]) (y + h) ⟨by linarith, le_rfl⟩
  have heq : φ (y + h) - φ y = -((h : ℂ) * (y : ℂ) ^ ((u : ℂ) * I) -
      (((y + h : ℝ) : ℂ) ^ (1 + (u : ℂ) * I) / (1 + u * I) -
        (y : ℂ) ^ (1 + (u : ℂ) * I) / (1 + u * I))) := by
    simp only [φ]
    push_cast
    ring
  rw [heq, norm_neg] at hbound
  refine hbound.trans_eq ?_
  ring

/-- Elementary summation on a residue class: comparing each term with a step of the
antiderivative `y^{1+iu} / (1 + iu)` gives the principal term
`O((B + k) / (k |1 + iu|))` plus `O((B - A + k) |u| / A)`. -/
theorem norm_sum_filter_modEq_le_elementary {k a A B : ℕ} (hk : 1 ≤ k) (hkA : k ≤ A)
    (hAB : A ≤ B) (u : ℝ) :
    ‖∑ n ∈ (Finset.Ioc A B).filter (· ≡ a [MOD k]), (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
      2 * (B + k) / (k * ‖1 + (u : ℂ) * I‖) + (B + k - A) * |u| / A := by
  have hk0 : 0 < k := hk
  set r := a % k
  have hr : r < k := Nat.mod_lt a hk0
  set m₀ := (A - r) / k
  set m₁ := (B - r) / k
  -- the residue class is the image of `(m₀, m₁]` under `m ↦ k m + r`
  have hreindex : ∑ n ∈ (Finset.Ioc A B).filter (· ≡ a [MOD k]), (n : ℂ) ^ ((u : ℂ) * I) =
      ∑ m ∈ Finset.Ioc m₀ m₁, (((k * m + r : ℕ) : ℝ) : ℂ) ^ ((u : ℂ) * I) := by
    refine Finset.sum_nbij' (· / k) (k * · + r) (fun n hn ↦ ?_) (fun m hm ↦ ?_) (fun n hn ↦ ?_)
      (fun m _ ↦ ?_) (fun n hn ↦ ?_)
    · rw [Finset.mem_filter, Finset.mem_Ioc] at hn
      have hn' : k * (n / k) + r = n := by
        rw [show r = n % k from hn.2.symm]
        exact Nat.div_add_mod n k
      rw [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hk0, Nat.le_div_iff_mul_le hk0, mul_comm]
      generalize k * (n / k) = p at hn'
      omega
    · rw [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hk0, Nat.le_div_iff_mul_le hk0,
        mul_comm m] at hm
      rw [Finset.mem_filter, Finset.mem_Ioc, Nat.ModEq, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      generalize k * m = p at hm
      omega
    · rw [Finset.mem_filter] at hn
      rw [show r = n % k from hn.2.symm]
      exact Nat.div_add_mod n k
    · rw [Nat.mul_add_div hk0, Nat.div_eq_of_lt hr, add_zero]
    · rw [Finset.mem_filter] at hn
      rw [show r = n % k from hn.2.symm, Nat.div_add_mod n k]
      simp
  rw [hreindex]
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hk0.trans_le hkA
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (0 : ℝ) < ‖1 + (u : ℂ) * I‖ :=
    norm_pos_iff.mpr fun h ↦ by simpa using congrArg re h
  rcases lt_or_ge m₁ m₀ with hm | hm
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    have : (A : ℝ) ≤ B := by exact_mod_cast hAB
    exact add_nonneg (by positivity)
      (div_nonneg (mul_nonneg (by linarith) (abs_nonneg u)) hA0.le)
  set G : ℕ → ℂ := fun m ↦ (((k * m + r : ℕ) : ℝ) : ℂ) ^ (1 + (u : ℂ) * I) / (1 + u * I)
  -- the antiderivative telescopes
  have htel : ∀ m ≥ m₀, ∑ j ∈ Finset.Ioc m₀ m, (G (j + 1) - G j) = G (m + 1) - G (m₀ + 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ioc_succ_top hm, ih]
      ring
  -- each term is a step of the antiderivative, up to `k² |u| / A`
  have hstep : ∀ j ∈ Finset.Ioc m₀ m₁, ‖(k : ℂ) * (((k * j + r : ℕ) : ℝ) : ℂ) ^ ((u : ℂ) * I) -
      (G (j + 1) - G j)‖ ≤ k ^ 2 * |u| / A := by
    intro j hj
    have hjA : (A : ℝ) < k * j + r := by
      rw [Finset.mem_Ioc, Nat.div_lt_iff_lt_mul hk0] at hj
      have : A < k * j + r := by rw [mul_comm k]; omega
      exact_mod_cast this
    have h := norm_step_sub_le u (y := ((k * j + r : ℕ) : ℝ)) (h := k) (by push_cast; linarith)
      (by positivity)
    simp only [G]
    rw [show (((k * (j + 1) + r : ℕ) : ℝ) : ℂ) = ((((k * j + r : ℕ) : ℝ) + k : ℝ) : ℂ) by
      push_cast; ring]
    refine h.trans ?_
    push_cast
    gcongr
  -- the two ends of the antiderivative
  have hG : ∀ m : ℕ, ‖G m‖ = (k * m + r : ℕ) / ‖1 + (u : ℂ) * I‖ := by
    intro m
    simp only [G]
    rw [norm_div, norm_cpow_eq_rpow_re_of_nonneg (by positivity) (by simp)]
    simp
  have hm₁ : ((k * (m₁ + 1) + r : ℕ) : ℝ) ≤ B + k := by
    have : m₁ * k ≤ B - r := (Nat.le_div_iff_mul_le hk0).mp le_rfl
    have : k * (m₁ + 1) + r ≤ B + k := by rw [mul_add, mul_comm k]; omega
    exact_mod_cast this
  have hm₀ : ((k * (m₀ + 1) + r : ℕ) : ℝ) ≤ B + k := by
    have : m₀ * k ≤ A - r := (Nat.le_div_iff_mul_le hk0).mp le_rfl
    have : k * (m₀ + 1) + r ≤ B + k := by rw [mul_add, mul_comm k]; omega
    exact_mod_cast this
  have hcard : ((Finset.Ioc m₀ m₁).card : ℝ) * k ≤ B + k - A := by
    rw [Nat.card_Ioc]
    have h1 : m₁ * k ≤ B - r := (Nat.le_div_iff_mul_le hk0).mp le_rfl
    have h2 : A - r < (m₀ + 1) * k := (Nat.div_lt_iff_lt_mul hk0).mp (Nat.lt_succ_self _)
    have : (m₁ - m₀) * k + A ≤ B + k := by
      rw [Nat.sub_mul, add_mul, one_mul] at *
      generalize m₁ * k = p at *
      generalize m₀ * k = q at *
      omega
    have : (((m₁ - m₀) * k + A : ℕ) : ℝ) ≤ B + k := by exact_mod_cast this
    push_cast at this
    linarith
  -- assemble
  have hmain : ‖(k : ℂ) * ∑ j ∈ Finset.Ioc m₀ m₁, (((k * j + r : ℕ) : ℝ) : ℂ) ^ ((u : ℂ) * I)‖ ≤
      2 * (B + k) / ‖1 + (u : ℂ) * I‖ + (B + k - A) * k * |u| / A := by
    have hsplit : (k : ℂ) * ∑ j ∈ Finset.Ioc m₀ m₁, (((k * j + r : ℕ) : ℝ) : ℂ) ^ ((u : ℂ) * I) =
        (G (m₁ + 1) - G (m₀ + 1)) + ∑ j ∈ Finset.Ioc m₀ m₁,
          ((k : ℂ) * (((k * j + r : ℕ) : ℝ) : ℂ) ^ ((u : ℂ) * I) - (G (j + 1) - G j)) := by
      rw [Finset.sum_sub_distrib, htel m₁ hm, Finset.mul_sum]
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
    · rw [hG, hG, ← add_div, two_mul]
      gcongr
    · refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      calc ((Finset.Ioc m₀ m₁).card : ℝ) * (k ^ 2 * |u| / A)
          = ((Finset.Ioc m₀ m₁).card * k) * k * |u| / A := by ring
        _ ≤ (B + k - A) * k * |u| / A := by gcongr
  rw [norm_mul, Complex.norm_natCast] at hmain
  have hk0' : (0 : ℝ) < k := by linarith
  calc _ = (k * ‖∑ j ∈ Finset.Ioc m₀ m₁, (((k * j + r : ℕ) : ℝ) : ℂ) ^ ((u : ℂ) * I)‖) / k := by
        field_simp
    _ ≤ (2 * (B + k) / ‖1 + (u : ℂ) * I‖ + (B + k - A) * k * |u| / A) / k := by gcongr
    _ = _ := by field_simp

/-- `(A + 1) / g - 1 ≤ A / g` for natural division. -/
theorem add_one_div_sub_one_le_natCast_div (A : ℕ) {g : ℕ} (hg : 0 < g) :
    ((A : ℝ) + 1) / g - 1 ≤ (A / g : ℕ) := by
  have h1 := Nat.div_add_mod A g
  have h2 := Nat.mod_lt A hg
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have h3 : (A : ℝ) + 1 ≤ g * (A / g : ℕ) + g := by
    have : A + 1 ≤ g * (A / g) + g := by omega
    exact_mod_cast this
  rw [sub_le_iff_le_add, div_le_iff₀ hg']
  linarith

/-- `|1 + iu| ≥ (1 + |u|) / 2`. -/
theorem one_add_abs_le_two_mul_norm (u : ℝ) : 1 + |u| ≤ 2 * ‖1 + (u : ℂ) * I‖ := by
  have h1 : |(1 + (u : ℂ) * I).re| ≤ ‖1 + (u : ℂ) * I‖ := abs_re_le_norm _
  have h2 : |(1 + (u : ℂ) * I).im| ≤ ‖1 + (u : ℂ) * I‖ := abs_im_le_norm _
  simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, abs_one, add_im, one_im, mul_im, zero_add] at h1 h2
  linarith

/-- The high-height regime `u⁴ > H³` for a single residue class, after removing
`g = (a, k)`: at most `K exp(C √(log (k (|u| + 3)))) (H / k)^{-1/128}` after
normalization. -/
theorem norm_sum_filter_modEq_le_of_large : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
    ∀ (H : ℝ) (A B k a : ℕ) (u : ℝ), 3 ^ 128 ≤ H / k → H ≤ A + 1 → (B : ℝ) ≤ 2 * H →
      1 ≤ k → A ≤ B → H ^ 3 < u ^ 4 →
      H⁻¹ * ‖∑ n ∈ (Finset.Ioc A B).filter (· ≡ a [MOD k]), (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
        K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) * (H / k) ^ (-(1 / 128 : ℝ)) := by
  obtain ⟨C, K₀, hC, hK₀, hII⟩ := norm_sum_Ioc_le
  refine ⟨C, 2 + 288 * K₀, hC, by positivity, fun H A B k a u hHk hHA hBH hk hAB hu ↦ ?_⟩
  have hk0 : 0 < k := hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hHbig : (3 : ℝ) ^ 128 ≤ H := by
    have := (le_div_iff₀ (by linarith : (0 : ℝ) < k)).mp hHk
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 3) 128]
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hHbig
  -- remove `g = (a, k)`
  set g := a.gcd k
  have hg : 0 < g := Nat.gcd_pos_of_pos_right a hk0
  have hgk : g ≤ k := Nat.le_of_dvd hk0 (Nat.gcd_dvd_right a k)
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hgk' : (g : ℝ) ≤ k := by exact_mod_cast hgk
  set k' := k / g
  have hk'0 : 0 < k' := Nat.div_pos hgk hg
  have : NeZero k' := ⟨hk'0.ne'⟩
  have hcop : (a / g).Coprime k' := Nat.coprime_div_gcd_div_gcd hg
  rw [sum_filter_modEq_eq_gcd hk0 A B u, norm_mul]
  -- the scale `H' = H / g = h^{128}`
  set H' := H / g
  have hH'k : H / k ≤ H' := div_le_div_of_nonneg_left hH0.le (by linarith) hgk'
  have hH'H : H' ≤ H := div_le_self hH0.le hg'
  have hH'0 : 0 < H' := by positivity
  set h := H' ^ (1 / 128 : ℝ)
  have hh128 : h ^ 128 = H' := by
    simp only [h]
    rw [show (1 / 128 : ℝ) = ((128 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hH'0.le (by norm_num)
  have hh3 : 3 ≤ h := by
    have : (3 ^ 128 : ℝ) ^ (1 / 128 : ℝ) ≤ h :=
      Real.rpow_le_rpow (by positivity) (hHk.trans hH'k) (by norm_num)
    rwa [show (3 ^ 128 : ℝ) = 3 ^ (128 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      show (128 : ℝ) * (1 / 128) = 1 by norm_num, Real.rpow_one] at this
  have hh0 : 0 < h := by linarith
  -- the reduced endpoints
  set A' := A / g
  set B' := B / g
  have hA' : h ^ 128 - 1 ≤ (A' : ℝ) := by
    rw [hh128]
    exact (sub_le_sub_right (div_le_div_of_nonneg_right hHA (by linarith)) 1).trans
      (add_one_div_sub_one_le_natCast_div A hg)
  have hB' : (B' : ℝ) ≤ 2 * h ^ 128 := by
    rw [hh128]
    refine Nat.cast_div_le.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have : 2 * (H / g) * g = 2 * H := by field_simp
    linarith
  -- the ramp width `M = ⌊h^{127}⌋`
  set M := ⌊h ^ 127⌋₊
  have h127 : 3 ≤ h ^ 127 := le_self_pow₀ (by linarith) (by norm_num) |>.trans' hh3
  have hM1 : (M : ℝ) ≤ h ^ 127 := Nat.floor_le (by positivity)
  have hM2 : h ^ 127 / 2 ≤ M := by linarith [Nat.sub_one_lt_floor (h ^ 127)]
  have hM : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hpow : 3 * h ^ 127 ≤ h ^ 128 := by
    rw [show h ^ 128 = h * h ^ 127 by ring]
    exact mul_le_mul_of_nonneg_right hh3 (by positivity)
  have hMA : 2 * M ≤ A' := by
    have : (2 * M : ℝ) ≤ A' := by linarith
    exact_mod_cast this
  have hu6 : 6 ≤ |u| := by
    have hH11 : (11 : ℝ) ≤ H := le_trans (by norm_num) hHbig
    by_contra hlt
    have : u ^ 4 ≤ 6 ^ 4 := by
      calc u ^ 4 = |u| ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
        _ ≤ 6 ^ 4 := pow_le_pow_left₀ (abs_nonneg u) (not_le.mp hlt).le 4
    nlinarith [pow_le_pow_left₀ (by norm_num) hH11 3]
  -- the character bound on the reduced class
  set E := Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3))))
  set E' := Real.exp (C * Real.sqrt (Real.log (k' * (|u| + 3))))
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hC (Real.sqrt_nonneg _))
  have hE' : 0 ≤ E' := (Real.exp_pos _).le
  have hEE : E' ≤ E := by
    have hkk : (k' : ℝ) ≤ k := by exact_mod_cast Nat.div_le_self k g
    have hk'1 : (1 : ℝ) ≤ k' := by exact_mod_cast hk'0
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (Real.log_le_log (by positivity) (by nlinarith [abs_nonneg u]))) hC)
  set Yt : ℝ := B' + M + 1
  have hX : ∀ χ : DirichletCharacter ℂ k',
      ‖∑ m ∈ Finset.Ioc A' B', χ m * (fun m : ℕ ↦ (m : ℂ) ^ ((u : ℂ) * I)) m‖ ≤
        2 * M + 4 * (Yt / M) * (K₀ * E' * (Yt ^ (63 / 64 : ℝ) + Yt ^ 2 / u ^ 2)) :=
    fun χ ↦ hII k' χ u A' B' M hu6 hM hMA (Nat.div_le_div_right hAB)
  have hres := norm_sum_filter_modEq_le_of_coprime hcop _ _ hX
  -- the sizes in terms of `h`
  have hM0 : (0 : ℝ) < M := by linarith
  have hYt : Yt ≤ 3 * h ^ 128 := by
    simp only [Yt]
    linarith
  have hYt0 : 0 ≤ Yt := by positivity
  have hb2 : Yt / M ≤ 6 * h := by
    rw [div_le_iff₀ hM0]
    have : 6 * h * (h ^ 127 / 2) ≤ 6 * h * M := mul_le_mul_of_nonneg_left hM2 (by positivity)
    have h6 : 6 * h * (h ^ 127 / 2) = 3 * h ^ 128 := by ring
    linarith
  have hb3 : Yt ^ (63 / 64 : ℝ) ≤ 3 * h ^ 126 := by
    calc Yt ^ (63 / 64 : ℝ) ≤ (3 * h ^ 128) ^ (63 / 64 : ℝ) :=
          Real.rpow_le_rpow hYt0 hYt (by norm_num)
      _ = 3 ^ (63 / 64 : ℝ) * h ^ 126 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast h 128,
            ← Real.rpow_mul hh0.le, ← Real.rpow_natCast h 126]
          norm_num
      _ ≤ 3 * h ^ 126 := by
          gcongr
          calc (3 : ℝ) ^ (63 / 64 : ℝ) ≤ 3 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 3 := Real.rpow_one 3
  have hu192 : h ^ 192 < u ^ 2 := by
    have h1 : (h ^ 128) ^ 3 ≤ H ^ 3 := pow_le_pow_left₀ (by positivity) (hh128 ▸ hH'H) 3
    by_contra hle
    have h2 : u ^ 4 ≤ (h ^ 192) ^ 2 := by
      calc u ^ 4 = (u ^ 2) ^ 2 := by ring
        _ ≤ (h ^ 192) ^ 2 := pow_le_pow_left₀ (by positivity) (not_lt.mp hle) 2
    have : (h ^ 192) ^ 2 = (h ^ 128) ^ 3 := by ring
    linarith
  have hb4 : Yt ^ 2 / u ^ 2 ≤ 9 * h ^ 64 := by
    rw [div_le_iff₀ (lt_trans (by positivity) hu192)]
    calc Yt ^ 2 ≤ (3 * h ^ 128) ^ 2 := pow_le_pow_left₀ hYt0 hYt 2
      _ = 9 * h ^ 64 * h ^ 192 := by ring
      _ ≤ 9 * h ^ 64 * u ^ 2 := mul_le_mul_of_nonneg_left hu192.le (by positivity)
  have hh64 : h ^ 64 ≤ h ^ 126 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hKE : 0 ≤ K₀ * E' := mul_nonneg hK₀ hE'
  have hsum : 2 * (M : ℝ) + 4 * (Yt / M) * (K₀ * E' * (Yt ^ (63 / 64 : ℝ) + Yt ^ 2 / u ^ 2)) ≤
      (2 + 288 * K₀ * E) * h ^ 127 := by
    have h1 : K₀ * E' * (Yt ^ (63 / 64 : ℝ) + Yt ^ 2 / u ^ 2) ≤ K₀ * E' * (12 * h ^ 126) :=
      mul_le_mul_of_nonneg_left (by linarith) hKE
    have h2 : 4 * (Yt / M) * (K₀ * E' * (Yt ^ (63 / 64 : ℝ) + Yt ^ 2 / u ^ 2)) ≤
        4 * (6 * h) * (K₀ * E' * (12 * h ^ 126)) := by
      gcongr
    have h3 : K₀ * E' ≤ K₀ * E := mul_le_mul_of_nonneg_left hEE hK₀
    have h4 : 4 * (6 * h) * (K₀ * E' * (12 * h ^ 126)) = 288 * (K₀ * E') * h ^ 127 := by ring
    have h5 : 288 * (K₀ * E') * h ^ 127 ≤ 288 * (K₀ * E) * h ^ 127 := by gcongr
    have h6 : (2 + 288 * K₀ * E) * h ^ 127 = 2 * h ^ 127 + 288 * (K₀ * E) * h ^ 127 := by ring
    linarith
  -- normalize
  have hg1 := norm_natCast_cpow_I_mul_le u g
  have hinv : H⁻¹ * h ^ 127 ≤ (H / k) ^ (-(1 / 128 : ℝ)) := by
    calc H⁻¹ * h ^ 127 ≤ H'⁻¹ * h ^ 127 := by gcongr
      _ = h⁻¹ := by rw [← hh128]; field_simp
      _ = H' ^ (-(1 / 128 : ℝ)) := by rw [Real.rpow_neg hH'0.le]
      _ ≤ (H / k) ^ (-(1 / 128 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hH'k (by norm_num)
  calc H⁻¹ * (‖((g : ℕ) : ℂ) ^ ((u : ℂ) * I)‖ * ‖∑ m ∈ (Finset.Ioc A' B').filter
        (· ≡ a / g [MOD k']), (m : ℂ) ^ ((u : ℂ) * I)‖)
      ≤ H⁻¹ * (1 * ((2 + 288 * K₀ * E) * h ^ 127)) := by
        gcongr
        exact hres.trans hsum
    _ = (2 + 288 * K₀ * E) * (H⁻¹ * h ^ 127) := by ring
    _ ≤ (2 + 288 * K₀ * E) * (H / k) ^ (-(1 / 128 : ℝ)) := by gcongr
    _ ≤ (2 + 288 * K₀) * E * (H / k) ^ (-(1 / 128 : ℝ)) := by
        gcongr
        linarith [mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 288 * K₀)]

/-- The integer kernel on one residue class, explicitly: elementary summation for
`u⁴ ≤ H³` and the contour shift above, giving
`H⁻¹ |∑| ≤ 12 / (1 + |u|) + K exp(C √(log (k (|u| + 3)))) (H / k)^{-1/128}`. -/
theorem norm_sum_filter_modEq_le : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧
    ∀ (H : ℝ) (A B k a : ℕ) (u : ℝ), 3 ^ 128 ≤ H / k → H ≤ A + 1 → (B : ℝ) ≤ 2 * H →
      1 ≤ k → 1 ≤ |u| →
      H⁻¹ * ‖∑ n ∈ (Finset.Ioc A B).filter (· ≡ a [MOD k]), (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
        12 / (1 + |u|) + K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) *
          (H / k) ^ (-(1 / 128 : ℝ)) := by
  obtain ⟨C, K₀, hC, hK₀, hlarge⟩ := norm_sum_filter_modEq_le_of_large
  refine ⟨C, K₀ + 4, hC, by positivity, fun H A B k a u hHk hHA hBH hk hu ↦ ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hHbig : (3 : ℝ) ^ 128 * k ≤ H := (le_div_iff₀ (by linarith)).mp hHk
  have h3k : (3 : ℝ) * k ≤ 3 ^ 128 * k := by gcongr; norm_num
  have hH0 : 0 < H := by linarith
  set E := Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3))))
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg hC (Real.sqrt_nonneg _))
  have hR : 0 ≤ (H / k) ^ (-(1 / 128 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hRHS : 0 ≤ 12 / (1 + |u|) := by positivity
  rcases lt_or_ge B A with hBA | hAB
  · rw [Finset.Ioc_eq_empty (by omega), Finset.filter_empty, Finset.sum_empty, norm_zero,
      mul_zero]
    positivity
  rcases lt_or_ge (H ^ 3) (u ^ 4) with hbig | hsmall
  · refine (hlarge H A B k a u hHk hHA hBH hk hAB hbig).trans ?_
    have : K₀ * E * (H / k) ^ (-(1 / 128 : ℝ)) ≤ (K₀ + 4) * E * (H / k) ^ (-(1 / 128 : ℝ)) := by
      gcongr
      linarith
    linarith
  -- elementary summation
  have hkA : k ≤ A := by
    have : (k : ℝ) ≤ A := by linarith
    exact_mod_cast this
  have hA0 : (0 : ℝ) < A := by linarith
  have helem := norm_sum_filter_modEq_le_elementary (a := a) hk hkA hAB u
  have hz := one_add_abs_le_two_mul_norm u
  have hz0 : 0 < ‖1 + (u : ℂ) * I‖ := by linarith [abs_nonneg u]
  have ht1 : H⁻¹ * (2 * (B + k) / (k * ‖1 + (u : ℂ) * I‖)) ≤ 12 / (1 + |u|) := by
    rw [inv_mul_eq_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (B : ℝ) + k ≤ 3 * H := by linarith
    have h1 : 2 * (B + k) * (1 + |u|) ≤ 2 * (3 * H) * (2 * ‖1 + (u : ℂ) * I‖) :=
      mul_le_mul (by linarith) hz (by positivity) (by positivity)
    have h2 : H * ‖1 + (u : ℂ) * I‖ ≤ H * (k * ‖1 + (u : ℂ) * I‖) := by
      have := mul_le_mul_of_nonneg_left hk' hz0.le
      nlinarith
    nlinarith
  -- `|u| / H ≤ H^{-1/128}` from `u⁴ ≤ H³`
  set y := H ^ (1 / 128 : ℝ)
  have hy128 : y ^ 128 = H := by
    simp only [y]
    rw [show (1 / 128 : ℝ) = ((128 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hH0.le (by norm_num)
  have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) (by norm_num)
  have huy : |u| * y ≤ y ^ 128 := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
    calc (|u| * y) ^ 4 = u ^ 4 * y ^ 4 := by rw [mul_pow, pow_abs, abs_of_nonneg (by positivity)]
      _ ≤ (y ^ 128) ^ 3 * y ^ 4 := by rw [hy128]; gcongr
      _ = y ^ 388 := by ring
      _ ≤ y ^ 512 := pow_le_pow_right₀ hy1 (by norm_num)
      _ = (y ^ 128) ^ 4 := by ring
  have ht2 : H⁻¹ * ((B + k - A) * |u| / A) ≤ 4 * (H / k) ^ (-(1 / 128 : ℝ)) := by
    have h1 : (B : ℝ) + k - A ≤ 2 * H := by linarith
    have h2 : H / 2 ≤ A := by linarith
    have h3 : (B + k - A) * |u| / A ≤ 4 * |u| := by
      rw [div_le_iff₀ hA0]
      nlinarith [abs_nonneg u]
    have h4 : H⁻¹ * |u| ≤ H ^ (-(1 / 128 : ℝ)) := by
      rw [Real.rpow_neg hH0.le]
      change H⁻¹ * |u| ≤ y⁻¹
      rw [← hy128, inv_mul_eq_div, div_le_iff₀ (by positivity)]
      calc |u| = |u| * y * y⁻¹ := by field_simp
        _ ≤ y ^ 128 * y⁻¹ := by gcongr
        _ = y⁻¹ * y ^ 128 := by ring
    have h5 : H ^ (-(1 / 128 : ℝ)) ≤ (H / k) ^ (-(1 / 128 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (div_le_self hH0.le hk') (by norm_num)
    calc H⁻¹ * ((B + k - A) * |u| / A) ≤ H⁻¹ * (4 * |u|) := by gcongr
      _ = 4 * (H⁻¹ * |u|) := by ring
      _ ≤ 4 * (H / k) ^ (-(1 / 128 : ℝ)) := by gcongr; exact h4.trans h5
  have hfin : 4 * (H / k) ^ (-(1 / 128 : ℝ)) ≤ (K₀ + 4) * E * (H / k) ^ (-(1 / 128 : ℝ)) := by
    gcongr
    nlinarith
  calc _ ≤ H⁻¹ * (2 * (B + k) / (k * ‖1 + (u : ℂ) * I‖) + (B + k - A) * |u| / A) := by
        gcongr
    _ ≤ _ := by rw [mul_add]; linarith

/-- A smaller power is eventually at most `ε` times a larger one. -/
theorem eventually_rpow_le_mul_rpow {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, X ^ a ≤ ε * X ^ b := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).eventually (gt_mem_nhds hε)
  filter_upwards [h, eventually_gt_atTop 0] with X hL hL0
  rw [show a = -(b - a) + b by ring, Real.rpow_add hL0]
  exact mul_le_mul_of_nonneg_right hL.le (Real.rpow_nonneg hL0.le _)

/-- The logarithm is eventually at most `ε` times any positive power. -/
theorem eventually_log_le_mul_rpow {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, Real.log X ≤ ε * X ^ b := by
  filter_upwards [(isLittleO_log_rpow_atTop hb).bound hε, eventually_gt_atTop 0] with X hL hL0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at hL
  exact (le_abs_self _).trans hL

/-- A constant is eventually at most `ε` times any positive power. -/
theorem eventually_const_le_mul_rpow (c : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, c ≤ ε * X ^ b := by
  filter_upwards [(tendsto_rpow_atTop hb).eventually_ge_atTop (c / ε)] with X hL
  rwa [div_le_iff₀' hε] at hL

/-- The growth conditions on `X`, used at `X = L = log x` to absorb the losses of the
contour shift into `exp(-L^{0.95})`. -/
theorem eventually_growth (Cm C K : ℝ) : ∀ᶠ X : ℝ in atTop,
    1 ≤ X ∧ Cm * Real.log X + Real.log 2 ≤ X ∧
    128 * Real.log 3 ≤ X ^ (0.98 : ℝ) - |Cm| * Real.log X ∧
    Real.log (|K| + 1) + |C| * (2 * Real.sqrt X) + X ^ (0.95 : ℝ) ≤
      (X ^ (0.98 : ℝ) - |Cm| * Real.log X) / 128 ∧
    X ^ (0.98 : ℝ) + 1 ≤ X ^ (0.99 : ℝ) ∧ Real.log X ^ 22 ≤ X ^ (0.02 : ℝ) := by
  set a := |Cm|
  have ha : 0 ≤ a := abs_nonneg _
  have hC : 0 ≤ |C| := abs_nonneg _
  have hK : 0 ≤ Real.log (|K| + 1) := Real.log_nonneg (by linarith [abs_nonneg K])
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  filter_upwards [eventually_ge_atTop 1,
    eventually_log_le_mul_rpow (b := 1) one_pos (ε := 1 / (2 * (a + 1))) (by positivity),
    eventually_const_le_mul_rpow (Real.log 2) (b := 1) one_pos (ε := 1 / 2) (by norm_num),
    eventually_const_le_mul_rpow (Real.log (|K| + 1) + 2 * Real.log 3) (b := 0.98)
      (by norm_num) (ε := 1 / 512) (by norm_num),
    eventually_rpow_le_mul_rpow (a := 1 / 2) (b := 0.98) (by norm_num)
      (ε := 1 / (1024 * (|C| + 1))) (by positivity),
    eventually_rpow_le_mul_rpow (a := 0.95) (b := 0.98) (by norm_num) (ε := 1 / 512)
      (by norm_num),
    eventually_log_le_mul_rpow (b := 0.98) (by norm_num) (ε := 1 / (4 * (a + 1)))
      (by positivity),
    eventually_rpow_le_mul_rpow (a := 0.98) (b := 0.99) (by norm_num) (ε := 1 / 2)
      (by norm_num),
    eventually_const_le_mul_rpow 1 (b := 0.99) (by norm_num) (ε := 1 / 2) (by norm_num),
    eventually_log_le_mul_rpow (b := 1 / 1100) (by norm_num) (ε := 1) one_pos]
    with X hL1 hlogL h2 hc hsqrt h95 hlog98 h98 h99 hlog1100
  have hL0 : 0 < X := by linarith
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hL1
  have hp : 0 ≤ X ^ (0.98 : ℝ) := Real.rpow_nonneg hL0.le _
  rw [Real.rpow_one] at hlogL h2
  have hsq : Real.sqrt X = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
  -- `a log X ≤ X^{0.98} / 4` and `|C| √X ≤ X^{0.98} / 1024`
  have hloga : a * Real.log X ≤ X ^ (0.98 : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_left hlog98 ha
    have h4 : a * (1 / (4 * (a + 1)) * X ^ (0.98 : ℝ)) ≤ X ^ (0.98 : ℝ) / 4 := by
      rw [show a * (1 / (4 * (a + 1)) * X ^ (0.98 : ℝ)) =
        a / (a + 1) * (X ^ (0.98 : ℝ) / 4) by field_simp]
      exact mul_le_of_le_one_left (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
    linarith
  have hCsq : |C| * Real.sqrt X ≤ X ^ (0.98 : ℝ) / 1024 := by
    rw [hsq]
    have := mul_le_mul_of_nonneg_left hsqrt hC
    have h4 : |C| * (1 / (1024 * (|C| + 1)) * X ^ (0.98 : ℝ)) ≤ X ^ (0.98 : ℝ) / 1024 := by
      rw [show |C| * (1 / (1024 * (|C| + 1)) * X ^ (0.98 : ℝ)) =
        |C| / (|C| + 1) * (X ^ (0.98 : ℝ) / 1024) by field_simp]
      exact mul_le_of_le_one_left (by positivity) ((div_le_one (by linarith)).mpr (by linarith))
    linarith
  refine ⟨hL1, ?_, ?_, ?_, by linarith, ?_⟩
  · have : Cm * Real.log X ≤ a * Real.log X := mul_le_mul_of_nonneg_right (le_abs_self _) hlog0
    have h5 : a * Real.log X ≤ X / 2 := by
      have := mul_le_mul_of_nonneg_left hlogL ha
      have h6 : a * (1 / (2 * (a + 1)) * X) ≤ X / 2 := by
        rw [show a * (1 / (2 * (a + 1)) * X) = a / (a + 1) * (X / 2) by field_simp]
        exact mul_le_of_le_one_left (by linarith) ((div_le_one (by linarith)).mpr (by linarith))
      linarith
    linarith
  · nlinarith
  · nlinarith
  · have h1 : Real.log X ≤ X ^ (1 / 1100 : ℝ) := by linarith
    calc Real.log X ^ 22 ≤ (X ^ (1 / 1100 : ℝ)) ^ 22 := pow_le_pow_left₀ hlog0 h1 22
      _ = X ^ (0.02 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
          norm_num

/-- The integer kernel on residue classes for large `x`: at scales `H ≥ exp(L^{0.98})`, for
moduli `k ≤ L^{C_m}` and `1 ≤ |u| ≤ x³`,
`H⁻¹ |∑_{n ∈ (A, B], n ≡ a} n^{iu}| ≤ 12 ((1 + |u|)⁻¹ + exp(-L^{0.95}))`. -/
theorem eventually_norm_sum_filter_modEq_le (Cm : ℝ) : ∀ᶠ x : ℝ in atTop,
    ∀ (H : ℝ) (A B k a : ℕ) (u : ℝ), Real.exp (Real.log x ^ (0.98 : ℝ)) ≤ H → H ≤ A + 1 →
      (B : ℝ) ≤ 2 * H → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm → 1 ≤ |u| → |u| ≤ x ^ 3 →
      H⁻¹ * ‖∑ n ∈ (Finset.Ioc A B).filter (· ≡ a [MOD k]), (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
        12 * ((1 + |u|)⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ))) := by
  obtain ⟨C, K, hC, hK, hbound⟩ := norm_sum_filter_modEq_le
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_growth Cm C K),
    eventually_ge_atTop 2] with x hx hx2
  obtain ⟨hl1, hl2, hl3, hl4, -, -⟩ := hx
  intro H A B k a u hH hHA hBH hk hkl hu1 hux
  set l := Real.log x
  have hl0 : 0 < l := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hH0 : 0 < H := (Real.exp_pos _).trans_le hH
  have hloglog : 0 ≤ Real.log l := Real.log_nonneg hl1
  -- `log k ≤ C_m log L` and `log H ≥ L^{0.98}`
  have hlogk : Real.log k ≤ |Cm| * Real.log l := by
    have := Real.log_le_log (by linarith) hkl
    rw [Real.log_rpow hl0] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hloglog)
  have hlogH : l ^ (0.98 : ℝ) ≤ Real.log H := by
    have := Real.log_le_log (Real.exp_pos _) hH
    rwa [Real.log_exp] at this
  set ℓ := Real.log (H / k)
  have hℓ : l ^ (0.98 : ℝ) - |Cm| * Real.log l ≤ ℓ := by
    simp only [ℓ]
    rw [Real.log_div hH0.ne' (by linarith)]
    linarith
  -- the scale condition `H / k ≥ 3^{128}`
  have hK1 : 0 ≤ Real.log (|K| + 1) := Real.log_nonneg (by linarith [abs_nonneg K])
  have hCl : 0 ≤ |C| * (2 * Real.sqrt l) := by positivity
  have h95 : 0 ≤ l ^ (0.95 : ℝ) := Real.rpow_nonneg hl0.le _
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hHk : (3 : ℝ) ^ 128 ≤ H / k := by
    have h3 : (3 : ℝ) ^ 128 = Real.exp (128 * Real.log 3) := by
      rw [show (128 : ℝ) * Real.log 3 = Real.log (3 ^ 128) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [h3, ← Real.exp_log (by positivity : 0 < H / k)]
    exact Real.exp_le_exp.mpr (by linarith)
  refine (hbound H A B k a u hHk hHA hBH hk hu1).trans ?_
  -- the exponential factor
  have hlogku : Real.log (k * (|u| + 3)) ≤ 4 * l := by
    have hx3 : |u| + 3 ≤ 2 * x ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx2 3]
    calc Real.log (k * (|u| + 3)) ≤ Real.log (l ^ Cm * (2 * x ^ 3)) :=
          Real.log_le_log (by positivity) (mul_le_mul hkl hx3 (by positivity) (by positivity))
      _ = Cm * Real.log l + Real.log 2 + 3 * l := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hl0,
            Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast
          ring
      _ ≤ 4 * l := by linarith
  have hE : C * Real.sqrt (Real.log (k * (|u| + 3))) ≤ |C| * (2 * Real.sqrt l) := by
    have : Real.sqrt (Real.log (k * (|u| + 3))) ≤ 2 * Real.sqrt l := by
      calc Real.sqrt (Real.log (k * (|u| + 3))) ≤ Real.sqrt (4 * l) := Real.sqrt_le_sqrt hlogku
        _ = 2 * Real.sqrt l := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
              Real.sqrt_sq (by norm_num)]
    exact (mul_le_mul_of_nonneg_left this hC).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hR : (H / k) ^ (-(1 / 128 : ℝ)) = Real.exp (-(ℓ / 128)) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    simp only [ℓ]
    ring
  have hKexp : K ≤ Real.exp (Real.log (|K| + 1)) := by
    rw [Real.exp_log (by positivity)]
    linarith [le_abs_self K]
  have hsmall : K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) *
      (H / k) ^ (-(1 / 128 : ℝ)) ≤ Real.exp (-l ^ (0.95 : ℝ)) := by
    rw [hR]
    calc K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) * Real.exp (-(ℓ / 128))
        ≤ Real.exp (Real.log (|K| + 1)) * Real.exp (|C| * (2 * Real.sqrt l)) *
            Real.exp (-(ℓ / 128)) := by
          gcongr
      _ = Real.exp (Real.log (|K| + 1) + |C| * (2 * Real.sqrt l) - ℓ / 128) := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf
      _ ≤ Real.exp (-l ^ (0.95 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have h12 : 12 / (1 + |u|) = 12 * (1 + |u|)⁻¹ := by rw [div_eq_mul_inv]
  have hexp := Real.exp_pos (-l ^ (0.95 : ℝ))
  linarith

end IntegerKernel

open IntegerKernel

/-- The integer kernel in progressions (AC3), the premise
`IntegerKernelBound` of `TwoSidedCorrelation`. -/
theorem eventually_integerKernelBound (Cm : ℝ) :
    ∃ κ : ℝ, ∀ᶠ x : ℝ in atTop, IntegerKernelBound x Cm κ := by
  refine ⟨12, ?_⟩
  filter_upwards [eventually_norm_sum_filter_modEq_le Cm,
    Real.tendsto_log_atTop.eventually (eventually_growth Cm 0 0),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop 1)] with x hx hgrowth hl1
  obtain ⟨-, -, -, -, -, hlog22⟩ := hgrowth
  intro H lo hi hH _ hlo hhi k a hk hkl u hu1 hux
  set l := Real.log x
  have hl0 : 0 < l := by linarith
  have hloglog : 0 < Real.log l ^ 22 := pow_pos (Real.log_pos hl1) 22
  -- `exp(L^{0.98}) ≤ exp(L / T²²)`
  have hscale : Real.exp (l ^ (0.98 : ℝ)) ≤ H := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hH
    calc l ^ (0.98 : ℝ) = l / l ^ (0.02 : ℝ) := by
          rw [show (0.98 : ℝ) = 1 - 0.02 by norm_num, Real.rpow_sub hl0, Real.rpow_one]
      _ ≤ l / Real.log l ^ 22 := div_le_div_of_nonneg_left hl0.le hloglog hlog22
  have hH0 : 0 < H := (Real.exp_pos _).trans_le hscale
  refine hx H ⌊lo⌋₊ ⌊hi⌋₊ k a u hscale (hlo.trans (Nat.lt_floor_add_one lo).le) ?_ hk hkl hu1
    hux
  calc (⌊hi⌋₊ : ℝ) ≤ ⌊2 * H⌋₊ := by exact_mod_cast Nat.floor_mono hhi
    _ ≤ 2 * H := Nat.floor_le (by positivity)

/-- The integer-kernel premise of `OneSidedTypeII`: on `[H_n, 2H_n]` with
`H_n ≥ x^γ`, `γ ≥ L^{-1/100}` and `H_m H_n ≤ C_X x`,
`H_n⁻¹ |∑ n^{iΔ}| ≪ |Δ|⁻¹ + exp(-L^{0.95})` for `1 ≤ |Δ| ≤ 4 H_m H_n L^B + 2`. -/
theorem eventually_kernel_premise (CX B : ℝ) : ∃ cG : ℝ, ∀ᶠ x : ℝ in atTop,
    ∀ γ Hm Hn : ℝ, Real.log x ^ (-(1 / 100 : ℝ)) ≤ γ → x ^ γ ≤ Hm → x ^ γ ≤ Hn →
      Hm * Hn ≤ CX * x → ∀ Δ : ℝ, 1 ≤ |Δ| → |Δ| ≤ 4 * (Hm * Hn) * Real.log x ^ B + 2 →
        Hn⁻¹ * ‖∑ n ∈ Finset.Icc ⌈Hn⌉₊ ⌊2 * Hn⌋₊, (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ ≤
          cG * (|Δ|⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ))) := by
  refine ⟨24, ?_⟩
  filter_upwards [eventually_norm_sum_filter_modEq_le 0,
    Real.tendsto_log_atTop.eventually (eventually_growth 0 0 0),
    ((isLittleO_log_rpow_rpow_atTop B one_pos).bound one_pos),
    eventually_ge_atTop (4 * |CX| + 2)] with x hx hgrowth hlogB hxCX
  obtain ⟨hl1, -, -, -, hl99, -⟩ := hgrowth
  intro γ Hm Hn hγ hHm hHn hmn Δ hΔ1 hΔ2
  set l := Real.log x
  have hl0 : 0 < l := by linarith
  have hx1 : 1 < x := by linarith [abs_nonneg CX]
  have hx0 : 0 < x := by linarith
  -- `x^γ ≥ exp(L^{0.99})`
  have hxγ : Real.exp (l ^ (0.99 : ℝ)) ≤ x ^ γ := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    calc l ^ (0.99 : ℝ) = l * l ^ (-(1 / 100 : ℝ)) := by
          rw [← Real.rpow_one_add' hl0.le (by norm_num)]
          norm_num
      _ ≤ l * γ := mul_le_mul_of_nonneg_left hγ hl0.le
  have he : (4 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hscale : Real.exp (l ^ (0.98 : ℝ)) ≤ 3 * Hn / 4 := by
    have : Real.exp (l ^ (0.98 : ℝ)) * Real.exp 1 ≤ Real.exp (l ^ (0.99 : ℝ)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hl99
    nlinarith [Real.exp_pos (l ^ (0.98 : ℝ))]
  have hHn0 : 0 < Hn := by linarith [Real.exp_pos (l ^ (0.98 : ℝ))]
  have hHm0 : 0 < Hm := (Real.exp_pos _).trans_le (hxγ.trans hHm)
  -- `|Δ| ≤ x³`
  have hΔx : |Δ| ≤ x ^ 3 := by
    have hlB : l ^ B ≤ x := by
      simpa [Real.norm_eq_abs, abs_of_pos hx0, abs_of_nonneg (Real.rpow_nonneg hl0.le B)]
        using hlogB
    have hCX : Hm * Hn ≤ |CX| * x := hmn.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      hx0.le)
    calc |Δ| ≤ 4 * (Hm * Hn) * l ^ B + 2 := hΔ2
      _ ≤ 4 * (|CX| * x) * x + 2 := by gcongr
      _ ≤ x ^ 3 := by
          have := mul_le_mul_of_nonneg_right hxCX (sq_nonneg x)
          nlinarith [abs_nonneg CX]
  have hk0 : ((1 : ℕ) : ℝ) ≤ l ^ (0 : ℝ) := by simp
  -- split `[⌈H_n⌉, 2H_n]` at `3H_n / 2`
  set N := ⌊3 * Hn / 2⌋₊
  have hc1 : 1 ≤ ⌈Hn⌉₊ := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcN : ⌈Hn⌉₊ - 1 ≤ N := by
    refine Nat.le_floor ?_
    rw [Nat.cast_sub hc1, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hHn0.le]
  have hN2 : N ≤ ⌊2 * Hn⌋₊ := Nat.floor_mono (by linarith)
  have hIcc : Finset.Icc ⌈Hn⌉₊ ⌊2 * Hn⌋₊ = Finset.Ioc (⌈Hn⌉₊ - 1) N ∪ Finset.Ioc N ⌊2 * Hn⌋₊ := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc hcN hN2]
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hfilter : ∀ p q : ℕ, (Finset.Ioc p q).filter (· ≡ 0 [MOD 1]) = Finset.Ioc p q :=
    fun p q ↦ Finset.filter_true_of_mem fun n _ ↦ Nat.modEq_one
  have h₁ := hx (3 * Hn / 4) (⌈Hn⌉₊ - 1) N 1 0 Δ hscale (by
      rw [Nat.cast_sub hc1, Nat.cast_one, sub_add_cancel]
      linarith [Nat.le_ceil Hn]) (by linarith [Nat.floor_le (by positivity : 0 ≤ 3 * Hn / 2)])
    le_rfl hk0 hΔ1 hΔx
  have h₂ := hx Hn N ⌊2 * Hn⌋₊ 1 0 Δ (hscale.trans (by linarith))
    (by linarith [Nat.lt_floor_add_one (3 * Hn / 2)]) (Nat.floor_le (by positivity)) le_rfl hk0
    hΔ1 hΔx
  rw [hfilter] at h₁ h₂
  set R := (1 + |Δ|)⁻¹ + Real.exp (-l ^ (0.95 : ℝ))
  have hR : 0 ≤ R := by positivity
  rw [inv_mul_le_iff₀ (by positivity)] at h₁ h₂
  rw [hIcc, Finset.sum_union (Finset.disjoint_left.mpr fun n h1 h2 ↦ by
    simp only [Finset.mem_Ioc] at h1 h2; omega), inv_mul_le_iff₀ hHn0]
  have hRΔ : R ≤ |Δ|⁻¹ + Real.exp (-l ^ (0.95 : ℝ)) := by
    have : (1 + |Δ|)⁻¹ ≤ |Δ|⁻¹ := inv_anti₀ (by linarith) (by linarith)
    simp only [R]
    linarith
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 3 * Hn / 4 * (12 * R) + Hn * (12 * R) := add_le_add h₁ h₂
    _ ≤ Hn * (24 * R) := by nlinarith
    _ ≤ Hn * (24 * (|Δ|⁻¹ + Real.exp (-l ^ (0.95 : ℝ)))) := by gcongr

end Erdos408
