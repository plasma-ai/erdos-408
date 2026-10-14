import Erdos408.Analytic.Core
import Erdos408.Hypotheses
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import PrimeNumberTheoremAnd.PerronFormula

/-!
# Twisted prime sums at large heights

AC2 of `blueprint/rectangle_input.md` §3, the premise `PrimeTwistBound` of
`TwoSidedCorrelation`: for `L^E ≤ |u| ≤ x³` and scales `H ≥ exp(L / T²²)`,
`∑_{p ∈ I} χ(p) p^{-1+iu} = O(L^{-A})`. Shift `-L'/L` to `re s = 1 - d` with
`d` fixed inside the zero-free half-plane, saving `H^{-d}`.

* The Perron formula writes the Cesàro sum `∑_{n ≤ y} χ(n) Λ(n) n^{iu} (1 - n/y)` as the
  vertical integral on `re w = 2` of `-(L'/L)(w - iu, χ) y^w / (w (w + 1))`.
* Truncate at height `T ≈ y²` and shift to `re w = 15/16`, keeping a notch on
  `re w = 1 + 1/log y` around the pole `w = 1 + iu`. On the notch `|L'/L| ≪ log² y` from the
  Dirichlet series; elsewhere `|L'/L| ≪ log(k (|t| + 3))` by
  `Erdos408.norm_logDeriv_LFunction_le`. The Cesàro sum is
  `O(y (log x) (y^{-1/16} + log² y / u²))`.
* Differencing the Cesàro sums at `j + 1/2` and `j + 1/2 + m`, `m ≈ H L^{-A}`, gives the sharp
  sums, prime powers cost `ψ - θ ≪ √H log H`, and Abel summation with the weights
  `1 / (p log p)` gives the twisted prime sum.
-/

namespace Erdos408

namespace PrimeTwist

open Complex ArithmeticFunction DirichletCharacter MeasureTheory Set LSeries
open scoped LSeries.notation

/-- The twisted von Mangoldt coefficients `χ(n) Λ(n) n^{iu}`. -/
noncomputable def twistCoeff {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ) (n : ℕ) : ℂ :=
  χ n * Λ n * (n : ℂ) ^ ((u : ℂ) * I)

/-- The Perron integrand `-(L'/L)(w - iu, χ) y^w / (w (w + 1))` of the twisted sum. -/
noncomputable def twistIntegrand {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (u y : ℝ)
    (w : ℂ) : ℂ :=
  -(deriv (LFunction χ) (w - u * I) / LFunction χ (w - u * I)) * Perron.f y w

/-- The terms of the L-series of `twistCoeff` are those of `χ Λ`, shifted by `iu`. -/
theorem term_twistCoeff {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ) (w : ℂ) (n : ℕ) :
    term (twistCoeff χ u) w n = term (↗χ * ↗Λ) (w - u * I) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hu : (n : ℂ) ^ ((u : ℂ) * I) ≠ 0 := fun h ↦ hn' ((cpow_eq_zero_iff _ _).mp h).1
  have hw : (n : ℂ) ^ w ≠ 0 := fun h ↦ hn' ((cpow_eq_zero_iff _ _).mp h).1
  rw [term_of_ne_zero hn, term_of_ne_zero hn, cpow_sub _ _ hn', twistCoeff, Pi.mul_apply]
  field_simp

/-- On `re w > 1`, `-(L'/L)(w - iu, χ)` is the L-series of `twistCoeff`. -/
theorem neg_logDeriv_LFunction_sub_eq {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    (u : ℝ) {w : ℂ} (hw : 1 < w.re) :
    -(deriv (LFunction χ) (w - u * I) / LFunction χ (w - u * I)) =
      LSeries (twistCoeff χ u) w := by
  have hs : 1 < (w - u * I).re := by simpa using hw
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
    ← neg_div, ← LSeries_twist_vonMangoldt_eq χ hs, LSeries, LSeries]
  exact tsum_congr fun n ↦ (term_twistCoeff χ u w n).symm

/-- To the right of `1`, the terms of the L-series of `χ Λ` are dominated by those of `Λ`. -/
theorem norm_term_twist_vonMangoldt_le {k : ℕ} (χ : DirichletCharacter ℂ k) (s : ℂ)
    (n : ℕ) : ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
  rw [norm_term_eq, norm_term_eq, ofReal_re]
  split_ifs
  · rfl
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  gcongr
  simpa [norm_mul] using mul_le_of_le_one_left (abs_nonneg (Λ n)) hχ

/-- To the right of `1`, `‖(L'/L)(s, χ)‖ ≤ ∑ Λ(n) / n^{re s}`. -/
theorem norm_logDeriv_LFunction_le_tsum {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ ∑' n, ‖term ↗Λ (s.re : ℂ) n‖ := by
  have hle := norm_term_twist_vonMangoldt_le χ s
  have hΛ : Summable fun n ↦ ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by simpa using hs))
  have hsum : Summable fun n ↦ ‖term (↗χ * ↗Λ) s n‖ :=
    hΛ.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [← norm_neg, ← neg_div, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
    ← LSeries_twist_vonMangoldt_eq χ hs, LSeries]
  exact (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_le_tsum hle hsum hΛ)

/-- The terms `Λ(n) / n²` are absolutely summable. -/
theorem summable_norm_term_vonMangoldt : Summable fun n ↦ ‖term ↗Λ 2 n‖ :=
  summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by norm_num))

/-- On `re s = 2`, `‖x^s / (s (s + 1))‖ ≤ x² / t²` with `t = im s`. -/
theorem norm_perron_f_le {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : t ≠ 0) :
    ‖Perron.f x ((2 : ℝ) + t * I)‖ ≤ x ^ 2 / t ^ 2 := by
  set s : ℂ := (2 : ℝ) + t * I
  have hs : ‖s‖ * ‖s + 1‖ = ‖s * (s + 1)‖ := (norm_mul _ _).symm
  have h1 : |t| ≤ ‖s‖ := by simpa [s] using abs_im_le_norm s
  have h2 : |t| ≤ ‖s + 1‖ := by simpa [s] using abs_im_le_norm (s + 1)
  have h3 : t ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [← hs, ← sq_abs]
    nlinarith [abs_nonneg t]
  rw [Perron.f, norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [s, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    add_zero, Real.rpow_two]
  gcongr

/-- On `re w = 2`, the twisted integrand is dominated by `x^w / (w (w + 1))`. -/
theorem norm_twistIntegrand_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (u y t : ℝ) :
    ‖twistIntegrand χ u y ((2 : ℝ) + t * I)‖ ≤
      (∑' n, ‖term ↗Λ 2 n‖) * ‖Perron.f y ((2 : ℝ) + t * I)‖ := by
  rw [twistIntegrand, norm_mul, norm_neg]
  gcongr
  have h := norm_logDeriv_LFunction_le_tsum χ (s := (2 : ℝ) + t * I - u * I) (by simp)
  simpa using h

/-- The twisted integrand is integrable on the line `re w = 2`. -/
theorem integrable_twistIntegrand {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (u : ℝ)
    {y : ℝ} (hy : 0 < y) : Integrable fun t : ℝ ↦ twistIntegrand χ u y ((2 : ℝ) + t * I) := by
  have hf : Integrable fun t : ℝ ↦ Perron.f y ((2 : ℝ) + t * I) :=
    Perron.isIntegrable hy (by norm_num) (by norm_num)
  have hline : Continuous fun t : ℝ ↦ ((2 : ℝ) : ℂ) + t * I - u * I := by fun_prop
  have hL : Continuous fun t : ℝ ↦ LFunction χ ((2 : ℝ) + t * I - u * I) := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    refine ((differentiableAt_LFunction χ _ (Or.inl fun h ↦ ?_)).continuousAt).comp
      hline.continuousAt
    simpa using congrArg re h
  have hmeas : AEStronglyMeasurable fun t : ℝ ↦ twistIntegrand χ u y ((2 : ℝ) + t * I) :=
    ((((measurable_deriv (LFunction χ)).comp hline.measurable).div
      hL.measurable).neg.aestronglyMeasurable).mul hf.aestronglyMeasurable
  exact (hf.norm.const_mul _).mono' hmeas
    (Filter.Eventually.of_forall fun t ↦ norm_twistIntegrand_le χ u y t)

/-- Each term of an L-series times `x^s / (s (s + 1))` is a Perron kernel at `x / n`. -/
theorem term_mul_perron_f_eq (f : ℕ → ℂ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    term f s n * Perron.f x s = f n * Perron.f (x / n) s := by
  have h := Perron.f_mul_eq_f hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s
  rw [ofReal_natCast, cpow_neg] at h
  rw [term_of_ne_zero hn, ← h]
  ring

/-- The line integral of the Perron kernel at `y > 1` is `2π (1 - 1/y)`. -/
theorem integral_perron_f_of_one_lt {y : ℝ} (hy : 1 < y) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 2 * Real.pi * (1 - 1 / y) := by
  have h := Perron.formulaGtOne (σ := 2) hy (by norm_num)
  rw [VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul] at h
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
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

/-- The twisted Perron formula: the vertical integral of `twistIntegrand` on `re w = 2` is
`2πi` times the Cesàro-weighted twisted sum. -/
theorem verticalIntegral_twistIntegrand {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    (u : ℝ) {y : ℝ} (hy : 1 < y) (hyN : ∀ m : ℕ, (m : ℝ) ≠ y) :
    VerticalIntegral (twistIntegrand χ u y) 2 =
      2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, twistCoeff χ u m * (1 - m / y) := by
  have hy0 : 0 < y := by linarith
  -- Expand the integrand as a Dirichlet series of Perron kernels.
  set g : ℕ → ℝ → ℂ := fun n t ↦
    term (twistCoeff χ u) ((2 : ℝ) + t * I) n * Perron.f y ((2 : ℝ) + t * I) with hg
  have hsum : ∀ t : ℝ, twistIntegrand χ u y ((2 : ℝ) + t * I) = ∑' n, g n t := by
    intro t
    rw [twistIntegrand, neg_logDeriv_LFunction_sub_eq χ u (by simp), LSeries,
      ← tsum_mul_right]
  have hg_eq : ∀ n, n ≠ 0 → ∀ t,
      g n t = twistCoeff χ u n * Perron.f (y / n) ((2 : ℝ) + t * I) :=
    fun n hn t ↦ term_mul_perron_f_eq _ hy0 hn _
  -- Each term is integrable, and the integrals of the norms are summable.
  have hg_int : ∀ n, Integrable (g n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    · rw [funext (hg_eq n hn)]
      have hyn : 0 < y / n := div_pos hy0 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      exact (Perron.isIntegrable hyn (by norm_num) (by norm_num)).const_mul _
  have hg_norm : ∀ n, ∫ t, ‖g n t‖ =
      ‖term (↗χ * ↗Λ) 2 n‖ * ∫ t : ℝ, ‖Perron.f y ((2 : ℝ) + t * I)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1 with t
    rw [hg, norm_mul, term_twistCoeff, norm_term_eq, norm_term_eq]
    simp
  have hg_sum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    simp_rw [hg_norm]
    have hχΛ : LSeriesSummable (↗χ * ↗Λ) 2 :=
      LSeriesSummable_twist_vonMangoldt χ (by norm_num)
    exact (summable_norm_iff.mpr hχΛ).mul_right _
  -- Evaluate each term with the Perron formula.
  have hg_val : ∀ n, ∫ t, g n t = if n ∈ Finset.Icc 1 ⌊y⌋₊ then
      2 * Real.pi * (twistCoeff χ u n * (1 - n / y)) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [funext (hg_eq n hn), integral_const_mul]
    split_ifs with hmem
    · have hny : (n : ℝ) < y :=
        lt_of_le_of_ne ((Nat.le_floor_iff hy0.le).mp (Finset.mem_Icc.mp hmem).2) (hyN n)
      rw [integral_perron_f_of_one_lt ((one_lt_div hn0).mpr hny)]
      push_cast
      rw [one_div_div]
      ring
    · have hyn : y < n := (Nat.floor_lt hy0.le).mp (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
        omega)
      rw [integral_perron_f_of_lt_one (div_pos hy0 hn0) ((div_lt_one hn0).mpr hyn), mul_zero]
  -- Interchange the sum and the integral.
  rw [VerticalIntegral, smul_eq_mul, funext hsum,
    ← integral_tsum_of_summable_integral_norm hg_int hg_sum, tsum_congr hg_val,
    tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊) (fun n hn ↦ ite_eq_right hn),
    Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn), ← Finset.mul_sum]
  ring

/-- A function bounded by `B / t²` on `(T, ∞)` has integral there of norm at most `B / T`. -/
theorem norm_setIntegral_Ioi_le {g : ℝ → ℂ} {B T : ℝ} (hT : 0 < T)
    (hg : IntegrableOn g (Ioi T)) (hgB : ∀ t, T < t → ‖g t‖ ≤ B / t ^ 2) :
    ‖∫ t in Ioi T, g t‖ ≤ B / T := by
  have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have hle : ∀ t ∈ Ioi T, ‖g t‖ ≤ B * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, Real.rpow_two, ← div_eq_mul_inv]
    exact hgB t ht
  calc ‖∫ t in Ioi T, g t‖
      ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, B * t ^ (-2 : ℝ) :=
        setIntegral_mono_on hg.norm (hrpow.const_mul B) measurableSet_Ioi hle
    _ = B / T := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
        norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- Truncating the twisted vertical integral at height `T` costs `O(y² / T)`. -/
theorem exists_norm_verticalIntegral_twist_sub_le :
    ∃ C : ℝ, ∀ {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (u : ℝ) {y T : ℝ}, 1 ≤ y →
      1 ≤ T → ‖VerticalIntegral (twistIntegrand χ u y) 2 -
          VIntegral (twistIntegrand χ u y) 2 (-T) T‖ ≤ C * y ^ 2 / T := by
  refine ⟨2 * ∑' n, ‖term ↗Λ 2 n‖, fun χ u y T hy hT ↦ ?_⟩
  set A := ∑' n, ‖term ↗Λ 2 n‖
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  set F : ℝ → ℂ := fun t ↦ twistIntegrand χ u y ((2 : ℝ) + t * I)
  have hF_int : Integrable F := integrable_twistIntegrand χ u hy0
  have hA : 0 ≤ A := tsum_nonneg fun _ ↦ norm_nonneg _
  -- Pointwise, `‖F t‖ ≤ A y² / t²`.
  have hF_le : ∀ t : ℝ, t ≠ 0 → ‖F t‖ ≤ A * y ^ 2 / t ^ 2 := by
    intro t ht
    rw [mul_div_assoc]
    exact (norm_twistIntegrand_le χ u y t).trans
      (mul_le_mul_of_nonneg_left (norm_perron_f_le hy0 ht) hA)
  -- Bound the two tails.
  have hupper : ‖∫ t in Ici T, F t‖ ≤ A * y ^ 2 / T := by
    rw [integral_Ici_eq_integral_Ioi]
    exact norm_setIntegral_Ioi_le hT0 hF_int.integrableOn
      fun t ht ↦ hF_le t (hT0.trans ht).ne'
  have hlower : ‖∫ t in Iic (-T), F t‖ ≤ A * y ^ 2 / T := by
    rw [← integral_comp_neg_Ioi]
    refine norm_setIntegral_Ioi_le hT0 hF_int.comp_neg.integrableOn fun t ht ↦ ?_
    rw [← neg_sq t]
    exact hF_le (-t) (neg_ne_zero.mpr (hT0.trans ht).ne')
  rw [verticalIntegral_split_three (-T) T hF_int, add_right_comm, add_sub_cancel_right]
  calc ‖I • (∫ t in Iic (-T), F t) + I • ∫ t in Ici T, F t‖
      ≤ ‖∫ t in Iic (-T), F t‖ + ‖∫ t in Ici T, F t‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        simp
    _ ≤ A * y ^ 2 / T + A * y ^ 2 / T := add_le_add hlower hupper
    _ = 2 * A * y ^ 2 / T := by ring

/-- The twisted integrand is holomorphic at `w` when `re w > 7/8` and `w - iu ≠ 1`. -/
theorem differentiableAt_twistIntegrand {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    (u : ℝ) {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : 7 / 8 < w.re) (hw1 : w - u * I ≠ 1) :
    DifferentiableAt ℂ (twistIntegrand χ u y) w := by
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hL : DifferentiableOn ℂ (LFunction χ) {s : ℂ | s ≠ 1} :=
    fun s hs ↦ (differentiableAt_LFunction χ s (Or.inl hs)).differentiableWithinAt
  have hshift : DifferentiableAt ℂ (fun w : ℂ ↦ w - u * I) w := by fun_prop
  have hD' : DifferentiableAt ℂ (deriv (LFunction χ)) (w - u * I) :=
    (hL.deriv hopen).differentiableAt (hopen.mem_nhds hw1)
  have hD : DifferentiableAt ℂ (deriv (LFunction χ) ∘ fun w ↦ w - u * I) w :=
    hD'.comp w hshift
  have hLw : DifferentiableAt ℂ (LFunction χ ∘ fun w ↦ w - u * I) w :=
    (differentiableAt_LFunction χ _ (Or.inl hw1)).comp w hshift
  have hne : LFunction χ (w - u * I) ≠ 0 :=
    LFunction_ne_zero_of_seven_eighths_lt_re χ (by simpa using hw) fun h ↦ hw1 h.2
  have hw0 : w ≠ 0 := fun h ↦ by
    rw [h, zero_re] at hw
    linarith
  have hw1' : w + 1 ≠ 0 := fun h ↦ by
    have := congrArg re h
    rw [add_re, one_re, zero_re] at this
    linarith
  have hK : DifferentiableAt ℂ (Perron.f y) w := by
    have h₁ : DifferentiableAt ℂ (fun s : ℂ ↦ (y : ℂ) ^ s) w :=
      DifferentiableAt.const_cpow differentiableAt_id (Or.inl (ofReal_ne_zero.mpr hy.ne'))
    have h₂ : DifferentiableAt ℂ (fun s : ℂ ↦ s * (s + 1)) w := by fun_prop
    exact h₁.div h₂ (mul_ne_zero hw0 hw1')
  exact ((hD.div hLw hne).neg).mul hK

/-- Membership in a rectangle with ordered corners. -/
theorem mem_rectangle_iff {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {p : ℂ} :
    p ∈ Rectangle (a + c * I) (b + d * I) ↔ p.re ∈ Icc a b ∧ p.im ∈ Icc c d := by
  simp [Rectangle, mem_reProdIm, uIcc_of_le hab, uIcc_of_le hcd]

/-- The rectangle integral in terms of its four edges. -/
theorem rectangleIntegral_eq (f : ℂ → ℂ) (a b c d : ℝ) :
    RectangleIntegral f (a + c * I) (b + d * I) =
      HIntegral f a b c - HIntegral f a b d + VIntegral f b c d - VIntegral f a c d := by
  simp [RectangleIntegral]

/-- The twisted integrand integrates to zero around a rectangle with ordered corners in
`re w > 7/8` avoiding the pole `w = 1 + iu`. -/
theorem rectangleIntegral_twistIntegrand_eq_zero {k : ℕ} [NeZero k]
    (χ : DirichletCharacter ℂ k) (u : ℝ) {y : ℝ} (hy : 0 < y) {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (ha : 7 / 8 < a)
    (hpole : ∀ p : ℂ, a ≤ p.re → p.re ≤ b → c ≤ p.im → p.im ≤ d → p - u * I ≠ 1) :
    RectangleIntegral (twistIntegrand χ u y) (a + c * I) (b + d * I) = 0 := by
  refine HolomorphicOn.vanishesOnRectangle (U := Rectangle (a + c * I) (b + d * I))
    (fun p hp ↦ ?_) subset_rfl
  rw [mem_rectangle_iff hab hcd] at hp
  exact (differentiableAt_twistIntegrand χ u hy (by linarith [hp.1.1])
    (hpole p hp.1.1 hp.1.2 hp.2.1 hp.2.2)).differentiableWithinAt

/-- To the right of the imaginary axis, `‖y^w / (w (w + 1))‖ ≤ y^{re w} / ‖w‖²`. -/
theorem norm_perron_f_le_div_sq {y : ℝ} (hy : 0 < y) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖Perron.f y w‖ ≤ y ^ w.re / ‖w‖ ^ 2 := by
  rw [Perron.f, norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have hsq : ‖w‖ ^ 2 ≤ ‖w + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp only [add_re, one_re, add_im, one_im, add_zero]
    nlinarith
  have hle : ‖w‖ ≤ ‖w + 1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  refine div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (by positivity) ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)

/-- `‖w‖² = (re w)² + (im w)²`. -/
theorem norm_sq_eq_re_sq_add_im_sq (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]
  ring

/-- The twisted integrand is at most a bound on `L'/L` times `y^{re w} / ‖w‖²`. -/
theorem norm_twistIntegrand_le_mul {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {u y : ℝ} (hy : 0 < y) {w : ℂ} (hw : 0 ≤ w.re) {B : ℝ}
    (hB : ‖deriv (LFunction χ) (w - u * I) / LFunction χ (w - u * I)‖ ≤ B) :
    ‖twistIntegrand χ u y w‖ ≤ B * (y ^ w.re / ‖w‖ ^ 2) := by
  rw [twistIntegrand, norm_mul, norm_neg]
  exact mul_le_mul hB (norm_perron_f_le_div_sq hy hw) (norm_nonneg _)
    ((norm_nonneg _).trans hB)

/-- `Λ(n) / n^{1+η} ≤ (2/η) / n^{1+η/2}`. -/
theorem norm_term_vonMangoldt_succ_le {η : ℝ} (hη : 0 < η) (n : ℕ) :
    ‖term ↗Λ ((1 + η : ℝ) : ℂ) (n + 1)‖ ≤ 2 / η * (1 / ((n : ℝ) + 1) ^ (1 + η / 2)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [norm_term_eq]
  simp only [Nat.add_one_ne_zero, ↓reduceIte, ofReal_re, Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg]
  push_cast
  have hlog : Λ (n + 1) ≤ ((n : ℝ) + 1) ^ (η / 2) / (η / 2) := by
    refine vonMangoldt_le_log.trans ?_
    exact_mod_cast Real.log_le_rpow_div hn.le (by linarith)
  have hsplit : ((n : ℝ) + 1) ^ (1 + η) =
      ((n : ℝ) + 1) ^ (η / 2) * ((n : ℝ) + 1) ^ (1 + η / 2) := by
    rw [← Real.rpow_add hn]
    ring_nf
  rw [hsplit, div_le_iff₀ (by positivity)]
  calc Λ (n + 1) ≤ ((n : ℝ) + 1) ^ (η / 2) / (η / 2) := hlog
    _ = 2 / η * (1 / ((n : ℝ) + 1) ^ (1 + η / 2)) *
        (((n : ℝ) + 1) ^ (η / 2) * ((n : ℝ) + 1) ^ (1 + η / 2)) := by
      field_simp

/-- Near `re s = 1`, `∑ Λ(n) / n^{1+η} ≤ 6 / η²`. -/
theorem tsum_norm_term_vonMangoldt_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∑' n, ‖term ↗Λ ((1 + η : ℝ) : ℂ) n‖ ≤ 6 / η ^ 2 := by
  have hsum : Summable fun n ↦ ‖term ↗Λ ((1 + η : ℝ) : ℂ) n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by simp; linarith))
  have hs : 1 < 1 + η / 2 := by linarith
  have hζ : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ (1 + η / 2) := by
    exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  have hterm := norm_term_vonMangoldt_succ_le hη
  have hζle : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (1 + η / 2) ≤ 2 / η + 1 := by
    have h := ZetaAsymptotics.zeta_limit_aux1 hs
    have h0 : 0 ≤ ZetaAsymptotics.termTSum (1 + η / 2) :=
      tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) _
    have h2 : 1 / (1 + η / 2 - 1) = 2 / η := by
      rw [show 1 + η / 2 - 1 = η / 2 by ring, one_div_div]
    have h3 : 0 ≤ (1 + η / 2) * ZetaAsymptotics.termTSum (1 + η / 2) :=
      mul_nonneg (by linarith) h0
    rw [h2] at h
    linarith
  rw [hsum.tsum_eq_zero_add]
  simp only [term_zero, norm_zero, zero_add]
  calc ∑' n : ℕ, ‖term ↗Λ ((1 + η : ℝ) : ℂ) (n + 1)‖
      ≤ ∑' n : ℕ, 2 / η * (1 / ((n : ℝ) + 1) ^ (1 + η / 2)) :=
        Summable.tsum_le_tsum hterm
          (hsum.comp_injective (add_left_injective 1)) (hζ.mul_left _)
    _ = 2 / η * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ (1 + η / 2) := tsum_mul_left
    _ ≤ 2 / η * (2 / η + 1) := by gcongr
    _ = 4 / η ^ 2 + 2 / η := by ring
    _ ≤ 4 / η ^ 2 + 2 / η ^ 2 := by
        gcongr
        exact pow_le_of_le_one hη.le hη1 two_ne_zero
    _ = 6 / η ^ 2 := by ring

/-- A horizontal segment integral is at most the length times a pointwise bound. -/
theorem norm_hIntegral_le {F : ℂ → ℂ} {a b τ B : ℝ} (hab : a ≤ b)
    (hF : ∀ σ ∈ Icc a b, ‖F (σ + τ * I)‖ ≤ B) : ‖HIntegral F a b τ‖ ≤ B * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := B)
    (f := fun σ : ℝ ↦ F (σ + τ * I)) fun σ hσ ↦ by
      rw [uIoc_of_le hab] at hσ
      exact hF σ (Ioc_subset_Icc_self hσ)
  rwa [abs_of_nonneg (by linarith)] at h

/-- A vertical segment integral is at most the length times a pointwise bound. -/
theorem norm_vIntegral_le {F : ℂ → ℂ} {σ a b B : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ‖F (σ + t * I)‖ ≤ B) : ‖VIntegral F σ a b‖ ≤ B * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := B)
    (f := fun t : ℝ ↦ F (σ + t * I)) fun t ht ↦ by
      rw [uIoc_of_le hab] at ht
      exact hF t (Ioc_subset_Icc_self ht)
  rw [VIntegral, norm_smul, norm_I, one_mul]
  rwa [abs_of_nonneg (by linarith)] at h

/-- A vertical segment integral dominated by `B / (1 + t²)` is at most `π B`. -/
theorem norm_vIntegral_le_mul_pi {F : ℂ → ℂ} {σ a b B : ℝ} (hab : a ≤ b)
    (hF : ∀ t ∈ Icc a b, ‖F (σ + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹) :
    ‖VIntegral F σ a b‖ ≤ B * Real.pi := by
  have hB : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hF a ⟨le_rfl, hab⟩)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  have hint : IntervalIntegrable (fun t : ℝ ↦ B * (1 + t ^ 2)⁻¹) volume a b :=
    (Continuous.intervalIntegrable (by
      exact continuous_const.mul ((continuous_const.add (continuous_pow 2)).inv₀
        fun t ↦ (add_pos_of_pos_of_nonneg one_pos (sq_nonneg t)).ne')) _ _)
  rw [VIntegral, norm_smul, norm_I, one_mul]
  calc ‖∫ t in a..b, F (σ + t * I)‖
      ≤ ∫ t in a..b, B * (1 + t ^ 2)⁻¹ :=
        intervalIntegral.norm_integral_le_of_norm_le hab
          (Filter.Eventually.of_forall fun t ht ↦ hF t (Ioc_subset_Icc_self ht)) hint
    _ = B * (Real.arctan b - Real.arctan a) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_one_add_sq]
    _ ≤ B * Real.pi := by
        gcongr
        linarith [Real.arctan_lt_pi_div_two b, Real.neg_pi_div_two_lt_arctan a]

/-- Away from `u`, `u² / 4 ≤ t²` when `|t - u| ≤ 2 ≤ |u| / 2`. -/
theorem sq_div_four_le_sq {u t : ℝ} (hu : 4 ≤ |u|) (ht : |t - u| ≤ 2) : u ^ 2 / 4 ≤ t ^ 2 := by
  have h₁ : |u| ≤ |t| + |t - u| := by
    have := abs_sub_abs_le_abs_sub u t
    rw [abs_sub_comm] at this
    linarith [abs_sub_comm u t]
  have h₂ : |u| / 2 ≤ |t| := by linarith
  have h₃ := pow_le_pow_left₀ (by positivity) h₂ 2
  rw [div_pow, sq_abs, sq_abs] at h₃
  linarith

/-- The right edge `re w = 2` of the truncated contour equals the notched contour through
`re w = 15/16` and, near the pole `w = 1 + iu`, `re w = 1 + η`: the differences are three
rectangles on which the twisted integrand is holomorphic. -/
theorem vIntegral_two_twistIntegrand_eq {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {u y T η : ℝ} (hy0 : 0 < y) (hη : 0 < η) (hη1 : η ≤ 1) (hT₁ : u + 2 ≤ T)
    (hT₂ : -T ≤ u - 2) :
    VIntegral (twistIntegrand χ u y) 2 (-T) T =
      VIntegral (twistIntegrand χ u y) (15 / 16) (-T) (u - 2) -
        HIntegral (twistIntegrand χ u y) (15 / 16) (1 + η) (-T) +
        HIntegral (twistIntegrand χ u y) (15 / 16) (1 + η) (u - 2) +
        VIntegral (twistIntegrand χ u y) (1 + η) (u - 2) (u + 2) +
        VIntegral (twistIntegrand χ u y) (15 / 16) (u + 2) T -
        HIntegral (twistIntegrand χ u y) (15 / 16) (1 + η) (u + 2) +
        HIntegral (twistIntegrand χ u y) (15 / 16) (1 + η) T -
        HIntegral (twistIntegrand χ u y) (1 + η) 2 (-T) +
        HIntegral (twistIntegrand χ u y) (1 + η) 2 T := by
  set G := twistIntegrand χ u y with hG
  set σ₁ := 1 + η with hσ₁
  -- the three rectangles
  have hσ₁2 : σ₁ ≤ 2 := by linarith
  have hσ₁1 : 1 < σ₁ := by linarith
  have hRA := rectangleIntegral_twistIntegrand_eq_zero χ u hy0 (a := σ₁) (b := 2) (c := -T)
    (d := T) hσ₁2 (by linarith) (by linarith) fun p hp _ _ _ h ↦ by
      have := congrArg re h
      simp at this
      linarith
  have hRB := rectangleIntegral_twistIntegrand_eq_zero χ u hy0 (a := 15 / 16) (b := σ₁)
    (c := u + 2) (d := T) (by linarith) (by linarith) (by norm_num)
    fun p _ _ hp _ h ↦ by
      have := congrArg im h
      simp at this
      linarith
  have hRC := rectangleIntegral_twistIntegrand_eq_zero χ u hy0 (a := 15 / 16) (b := σ₁)
    (c := -T) (d := u - 2) (by linarith) (by linarith) (by norm_num)
    fun p _ _ _ hp h ↦ by
      have := congrArg im h
      simp at this
      linarith
  rw [rectangleIntegral_eq] at hRA hRB hRC
  -- split the notch line at `u ± 2`
  have hcont : Continuous fun t : ℝ ↦ G (σ₁ + t * I) := by
    have hline : Continuous fun t : ℝ ↦ (σ₁ : ℂ) + t * I := by fun_prop
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    refine ((differentiableAt_twistIntegrand χ u hy0 (by simp; linarith)
      fun h ↦ ?_).continuousAt).comp hline.continuousAt
    have := congrArg re h
    simp at this
    linarith
  have hsplit : VIntegral G σ₁ (-T) T = VIntegral G σ₁ (-T) (u - 2) +
      VIntegral G σ₁ (u - 2) (u + 2) + VIntegral G σ₁ (u + 2) T := by
    simp only [VIntegral, ← smul_add]
    rw [intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hid : VIntegral G 2 (-T) T =
      VIntegral G (15 / 16) (-T) (u - 2) - HIntegral G (15 / 16) σ₁ (-T) +
        HIntegral G (15 / 16) σ₁ (u - 2) + VIntegral G σ₁ (u - 2) (u + 2) +
        VIntegral G (15 / 16) (u + 2) T - HIntegral G (15 / 16) σ₁ (u + 2) +
        HIntegral G (15 / 16) σ₁ T - HIntegral G σ₁ 2 (-T) + HIntegral G σ₁ 2 T := by
    linear_combination hRA + hsplit + hRB + hRC
  exact hid

/-- The bound on the right edge `re w = 2` of the truncated contour, given
`|L'/L(s, χ)| ≤ C log(k (|t| + 3))` on `15/16 ≤ re s ≤ 2`, `|s - 1| ≥ 1`. -/
theorem norm_vIntegral_two_twistIntegrand_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {C : ℝ} (hC0 : 0 ≤ C) (hLog : ∀ s : ℂ, 15 / 16 ≤ s.re → s.re ≤ 2 → 1 ≤ ‖s - 1‖ →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C * Real.log (k * (|s.im| + 3)))
    {u y T η : ℝ} (hu : 4 ≤ |u|) (hT : |u| + 3 ≤ T) (hy : 2 ≤ y) (hη : 0 < η) (hη1 : η ≤ 1) :
    ‖VIntegral (twistIntegrand χ u y) 2 (-T) T‖ ≤
      10 * (C * Real.log (k * (T + |u| + 3)) * y ^ (15 / 16 : ℝ)) +
        6 * (C * Real.log (k * (T + |u| + 3)) * (y ^ 2 / T ^ 2)) +
        16 * (C * Real.log (k * (T + |u| + 3)) * (y ^ (1 + η) / u ^ 2)) +
        96 * (y ^ (1 + η) / (η ^ 2 * u ^ 2)) := by
  set G := twistIntegrand χ u y with hG
  set σ₁ := 1 + η with hσ₁
  set M := Real.log (k * (T + |u| + 3)) with hM
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hM0 : 0 ≤ M := Real.log_nonneg (by nlinarith [abs_nonneg u])
  have hT0 : 0 < T := by linarith [abs_nonneg u]
  have hu2 : 0 < u ^ 2 := by
    have : 0 < |u| := by linarith
    rw [← sq_abs]
    positivity
  have hCM : 0 ≤ C * M := mul_nonneg hC0 hM0
  have hσ₁2 : σ₁ ≤ 2 := by linarith
  -- the bound on `L'/L` away from the pole
  have hLL : ∀ w : ℂ, 15 / 16 ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im - u| → |w.im - u| ≤ T + |u| →
      ‖deriv (LFunction χ) (w - u * I) / LFunction χ (w - u * I)‖ ≤ C * M := by
    intro w h₁ h₂ h₃ h₄
    have hre : (w - u * I).re = w.re := by simp
    have him : (w - u * I).im = w.im - u := by simp
    have hs1 : 1 ≤ ‖w - u * I - 1‖ := by
      refine h₃.trans ?_
      have := abs_im_le_norm (w - u * I - 1)
      simpa using this
    refine (hLog _ (by rw [hre]; exact h₁) (by rw [hre]; exact h₂) hs1).trans ?_
    rw [him]
    refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hC0
    gcongr
  have hpt : ∀ w : ℂ, 15 / 16 ≤ w.re → w.re ≤ 2 → 1 ≤ |w.im - u| → |w.im - u| ≤ T + |u| →
      ‖G w‖ ≤ C * M * (y ^ w.re / ‖w‖ ^ 2) := fun w h₁ h₂ h₃ h₄ ↦
    norm_twistIntegrand_le_mul χ hy0 (by linarith) (hLL w h₁ h₂ h₃ h₄)
  -- the horizontal edges at height `±T`
  have hedgeT : ∀ τ : ℝ, |τ| = T → ∀ σ ∈ Icc (15 / 16 : ℝ) 2,
      ‖G (σ + τ * I)‖ ≤ C * M * (y ^ 2 / T ^ 2) := by
    intro τ hτ σ hσ
    have hre : ((σ : ℂ) + τ * I).re = σ := by simp
    have him : ((σ : ℂ) + τ * I).im = τ := by simp
    have h₁ : 1 ≤ |τ - u| := by linarith [abs_sub_abs_le_abs_sub τ u]
    have h₂ : |τ - u| ≤ T + |u| := by linarith [abs_sub τ u]
    refine (hpt _ (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2) (by rw [him]; exact h₁)
      (by rw [him]; exact h₂)).trans ?_
    rw [hre]
    gcongr
    · rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hy1 hσ.2
    · have := abs_im_le_norm ((σ : ℂ) + τ * I)
      rwa [him, hτ] at this
  -- the horizontal edges at height `u ± 2`
  have hedgeU : ∀ τ : ℝ, |τ - u| = 2 → ∀ σ ∈ Icc (15 / 16 : ℝ) σ₁,
      ‖G (σ + τ * I)‖ ≤ C * M * (4 * (y ^ σ₁ / u ^ 2)) := by
    intro τ hτ σ hσ
    have hre : ((σ : ℂ) + τ * I).re = σ := by simp
    have him : ((σ : ℂ) + τ * I).im = τ := by simp
    have h₂ : |τ - u| ≤ T + |u| := by linarith [abs_nonneg u]
    refine (hpt _ (by rw [hre]; exact hσ.1) (by rw [hre]; linarith [hσ.2])
      (by rw [him, hτ]; norm_num) (by rw [him]; exact h₂)).trans ?_
    rw [hre]
    have hτu := sq_div_four_le_sq hu hτ.le
    have hw : u ^ 2 / 4 ≤ ‖(σ : ℂ) + τ * I‖ ^ 2 := by
      rw [norm_sq_eq_re_sq_add_im_sq, him]
      nlinarith
    have hyσ : y ^ σ ≤ y ^ σ₁ := Real.rpow_le_rpow_of_exponent_le hy1 hσ.2
    gcongr
    calc y ^ σ / ‖(σ : ℂ) + τ * I‖ ^ 2 ≤ y ^ σ₁ / (u ^ 2 / 4) :=
          div_le_div₀ (by positivity) hyσ (by positivity) hw
      _ = 4 * (y ^ σ₁ / u ^ 2) := by ring
  -- the notch `re w = 1 + η`, `|im w - u| ≤ 2`
  have hnotch : ∀ t ∈ Icc (u - 2) (u + 2),
      ‖G (σ₁ + t * I)‖ ≤ 6 / η ^ 2 * (4 * (y ^ σ₁ / u ^ 2)) := by
    intro t ht
    have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
    have him : ((σ₁ : ℂ) + t * I).im = t := by simp
    have hsre : ((σ₁ : ℂ) + t * I - u * I).re = 1 + η := by simp [hσ₁]
    have hL := norm_logDeriv_LFunction_le_tsum χ (s := (σ₁ : ℂ) + t * I - u * I)
      (by rw [hsre]; linarith)
    rw [hsre] at hL
    refine (norm_twistIntegrand_le_mul χ hy0 (by rw [hre]; linarith)
      (hL.trans (tsum_norm_term_vonMangoldt_le hη hη1))).trans ?_
    rw [hre]
    have htu : |t - u| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hτu := sq_div_four_le_sq hu htu
    have hw : u ^ 2 / 4 ≤ ‖(σ₁ : ℂ) + t * I‖ ^ 2 := by
      rw [norm_sq_eq_re_sq_add_im_sq, him]
      nlinarith
    gcongr
    calc y ^ σ₁ / ‖(σ₁ : ℂ) + t * I‖ ^ 2 ≤ y ^ σ₁ / (u ^ 2 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hw
      _ = 4 * (y ^ σ₁ / u ^ 2) := by ring
  -- the left edge `re w = 15/16`, `|im w - u| ≥ 2`
  have hleft : ∀ t : ℝ, |t| ≤ T → 2 ≤ |t - u| →
      ‖G ((15 / 16 : ℝ) + t * I)‖ ≤ C * M * y ^ (15 / 16 : ℝ) * (256 / 225) * (1 + t ^ 2)⁻¹ := by
    intro t ht htu
    have hre : (((15 / 16 : ℝ) : ℂ) + t * I).re = 15 / 16 := by simp
    have him : (((15 / 16 : ℝ) : ℂ) + t * I).im = t := by simp
    refine (hpt _ (by rw [hre]) (by rw [hre]; norm_num) (by rw [him]; linarith)
      (by rw [him]; linarith [abs_sub t u])).trans ?_
    rw [hre, norm_sq_eq_re_sq_add_im_sq, hre, him]
    have h₁ : 0 < (15 / 16 : ℝ) ^ 2 + t ^ 2 := by positivity
    rw [mul_assoc (C * M * _), mul_assoc (C * M)]
    gcongr
    rw [div_eq_mul_inv]
    gcongr
    rw [← one_div, ← one_div, div_mul_div_comm, div_le_div_iff₀ h₁ (by positivity)]
    nlinarith
  rw [vIntegral_two_twistIntegrand_eq χ hy0 hη hη1 (by linarith [le_abs_self u])
    (by linarith [neg_abs_le u])]
  -- bound the nine pieces
  have hb₁ : ‖VIntegral G (15 / 16) (-T) (u - 2)‖ ≤
      C * M * y ^ (15 / 16 : ℝ) * (256 / 225) * Real.pi :=
    norm_vIntegral_le_mul_pi (by linarith [neg_abs_le u]) fun t ht ↦
      hleft t (abs_le.mpr ⟨ht.1, by linarith [ht.2, le_abs_self u]⟩)
        (le_abs.mpr (Or.inr (by linarith [ht.2])))
  have hb₂ : ‖VIntegral G (15 / 16) (u + 2) T‖ ≤
      C * M * y ^ (15 / 16 : ℝ) * (256 / 225) * Real.pi :=
    norm_vIntegral_le_mul_pi (by linarith [le_abs_self u]) fun t ht ↦
      hleft t (abs_le.mpr ⟨by linarith [ht.1, neg_abs_le u], ht.2⟩)
        (le_abs.mpr (Or.inl (by linarith [ht.1])))
  have hTabs : |T| = T := abs_of_pos hT0
  have hTabs' : |-T| = T := by rw [abs_neg, hTabs]
  have hh₁ : ‖HIntegral G (15 / 16) σ₁ (-T)‖ ≤ C * M * (y ^ 2 / T ^ 2) * (σ₁ - 15 / 16) :=
    norm_hIntegral_le (by linarith) fun σ hσ ↦ hedgeT (-T) hTabs' σ ⟨hσ.1, by linarith [hσ.2]⟩
  have hh₂ : ‖HIntegral G (15 / 16) σ₁ T‖ ≤ C * M * (y ^ 2 / T ^ 2) * (σ₁ - 15 / 16) :=
    norm_hIntegral_le (by linarith) fun σ hσ ↦ hedgeT T hTabs σ ⟨hσ.1, by linarith [hσ.2]⟩
  have hh₃ : ‖HIntegral G σ₁ 2 (-T)‖ ≤ C * M * (y ^ 2 / T ^ 2) * (2 - σ₁) :=
    norm_hIntegral_le hσ₁2 fun σ hσ ↦ hedgeT (-T) hTabs' σ ⟨by linarith [hσ.1], hσ.2⟩
  have hh₄ : ‖HIntegral G σ₁ 2 T‖ ≤ C * M * (y ^ 2 / T ^ 2) * (2 - σ₁) :=
    norm_hIntegral_le hσ₁2 fun σ hσ ↦ hedgeT T hTabs σ ⟨by linarith [hσ.1], hσ.2⟩
  have hh₅ : ‖HIntegral G (15 / 16) σ₁ (u - 2)‖ ≤
      C * M * (4 * (y ^ σ₁ / u ^ 2)) * (σ₁ - 15 / 16) :=
    norm_hIntegral_le (by linarith) (hedgeU (u - 2) (by norm_num [show u - 2 - u = -2 by ring]))
  have hh₆ : ‖HIntegral G (15 / 16) σ₁ (u + 2)‖ ≤
      C * M * (4 * (y ^ σ₁ / u ^ 2)) * (σ₁ - 15 / 16) :=
    norm_hIntegral_le (by linarith) (hedgeU (u + 2) (by norm_num))
  have hn : ‖VIntegral G σ₁ (u - 2) (u + 2)‖ ≤
      6 / η ^ 2 * (4 * (y ^ σ₁ / u ^ 2)) * (u + 2 - (u - 2)) :=
    norm_vIntegral_le (by linarith) hnotch
  set b := y ^ 2 / T ^ 2
  set c := y ^ σ₁ / u ^ 2
  set d := y ^ (15 / 16 : ℝ)
  set e := y ^ σ₁ / (η ^ 2 * u ^ 2)
  have hn' : 6 / η ^ 2 * (4 * c) * (u + 2 - (u - 2)) = 96 * e := by
    simp only [c, e]
    field_simp
    ring
  have hπ : C * M * d * (256 / 225) * Real.pi ≤ 5 * (C * M * d) := by
    have := Real.pi_le_four
    have h0 : 0 ≤ C * M * d := by positivity
    nlinarith
  have hCMb : 0 ≤ C * M * b := by positivity
  have hb₃ : C * M * b * (σ₁ - 15 / 16) ≤ C * M * b * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) hCMb
  have hb₄ : C * M * b * (2 - σ₁) ≤ C * M * b * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) hCMb
  have hb₅ : C * M * (4 * c) * (σ₁ - 15 / 16) ≤ C * M * (4 * c) * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  rw [hn'] at hn
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
  have h₁ := norm_sub_le (VIntegral G (15 / 16) (-T) (u - 2) - HIntegral G (15 / 16) σ₁ (-T) +
    HIntegral G (15 / 16) σ₁ (u - 2) + VIntegral G σ₁ (u - 2) (u + 2) +
    VIntegral G (15 / 16) (u + 2) T) (HIntegral G (15 / 16) σ₁ (u + 2))
  have h₂ := norm_add_le (VIntegral G (15 / 16) (-T) (u - 2) - HIntegral G (15 / 16) σ₁ (-T) +
    HIntegral G (15 / 16) σ₁ (u - 2) + VIntegral G σ₁ (u - 2) (u + 2))
    (VIntegral G (15 / 16) (u + 2) T)
  have h₃ := norm_add_le (VIntegral G (15 / 16) (-T) (u - 2) - HIntegral G (15 / 16) σ₁ (-T) +
    HIntegral G (15 / 16) σ₁ (u - 2)) (VIntegral G σ₁ (u - 2) (u + 2))
  have h₄ := norm_add_le (VIntegral G (15 / 16) (-T) (u - 2) - HIntegral G (15 / 16) σ₁ (-T))
    (HIntegral G (15 / 16) σ₁ (u - 2))
  have h₅ := norm_sub_le (VIntegral G (15 / 16) (-T) (u - 2)) (HIntegral G (15 / 16) σ₁ (-T))
  linarith

/-- The Cesàro-weighted twisted sum, by the contour shift to `re w = 15/16`, with a notch on
`re w = 1 + η` around the pole `w = 1 + iu`. -/
theorem exists_norm_twistCesaro_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {k : ℕ} [NeZero k]
    (χ : DirichletCharacter ℂ k) {u y T η : ℝ}, 4 ≤ |u| → |u| + 3 ≤ T → 2 ≤ y →
    (∀ m : ℕ, (m : ℝ) ≠ y) → 0 < η → η ≤ 1 →
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, twistCoeff χ u m * (1 - m / y)‖ ≤
      K * (y ^ 2 / T + Real.log (k * (T + |u| + 3)) *
        (y ^ 2 / T ^ 2 + y ^ (1 + η) / u ^ 2 + y ^ (15 / 16 : ℝ)) +
        y ^ (1 + η) / (η ^ 2 * u ^ 2)) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_verticalIntegral_twist_sub_le
  obtain ⟨C₂, hC₂⟩ := norm_logDeriv_LFunction_le
  set C := max C₂ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  refine ⟨|C₁| + 16 * C + 96, by positivity, ?_⟩
  intro k _ χ u y T η hu hT hy hyN hη hη1
  have hLog : ∀ s : ℂ, 15 / 16 ≤ s.re → s.re ≤ 2 → 1 ≤ ‖s - 1‖ →
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ C * Real.log (k * (|s.im| + 3)) := by
    intro s h₁ h₂ h₃
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
    refine (hC₂ k χ s h₁ h₂ h₃).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact Real.log_nonneg (by nlinarith [abs_nonneg s.im])
  have hV := norm_vIntegral_two_twistIntegrand_le χ hC0 hLog hu hT hy hη hη1
  set G := twistIntegrand χ u y with hG
  set M := Real.log (k * (T + |u| + 3)) with hM
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hM0 : 0 ≤ M := Real.log_nonneg (by nlinarith [abs_nonneg u])
  have hT0 : 0 < T := by linarith [abs_nonneg u]
  have htr := hC₁ χ u (y := y) (T := T) hy1 (by linarith [abs_nonneg u])
  have hVI : ‖VerticalIntegral G 2‖ ≤
      ‖VerticalIntegral G 2 - VIntegral G 2 (-T) T‖ + ‖VIntegral G 2 (-T) T‖ := by
    have := norm_sub_norm_le (VerticalIntegral G 2) (VIntegral G 2 (-T) T)
    linarith
  have hS : ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, twistCoeff χ u m * (1 - m / y)‖ ≤
      ‖VerticalIntegral G 2‖ := by
    rw [hG, verticalIntegral_twistIntegrand χ u (by linarith) hyN, norm_mul]
    have : (1 : ℝ) ≤ ‖2 * (Real.pi : ℂ) * I‖ := by
      simp [abs_of_pos Real.pi_pos]
      linarith [Real.pi_gt_three]
    exact le_mul_of_one_le_left (norm_nonneg _) this
  set a := y ^ 2 / T
  set b := y ^ 2 / T ^ 2
  set c := y ^ (1 + η) / u ^ 2
  set d := y ^ (15 / 16 : ℝ)
  set e := y ^ (1 + η) / (η ^ 2 * u ^ 2)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have hd : 0 ≤ d := by positivity
  have he : 0 ≤ e := by positivity
  have htr' : C₁ * y ^ 2 / T ≤ |C₁| * a := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) ha
  have h₁ : 0 ≤ (16 * C + 96) * a := by positivity
  have h₂ : 0 ≤ (|C₁| + 96) * (M * (b + c + d)) := by positivity
  have h₃ : 0 ≤ (|C₁| + 16 * C) * e := by positivity
  have h₄ : 0 ≤ C * M * d := by positivity
  have h₅ : 0 ≤ C * M * b := by positivity
  have key : (|C₁| + 16 * C + 96) * (a + M * (b + c + d) + e) -
      (|C₁| * a + (10 * (C * M * d) + 6 * (C * M * b) + 16 * (C * M * c) + 96 * e)) =
      (16 * C + 96) * a + (|C₁| + 96) * (M * (b + c + d)) + 6 * (C * M * d) +
        10 * (C * M * b) + (|C₁| + 16 * C) * e := by ring
  linarith

/-- `log 3 > 1`. -/
theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- The algebra of `exists_mul_norm_twistCesaro_le`, with `T = y² + |u| + 3`, `η = 1 / log y`,
`y^{1+η} = e y` and `y^{15/16} = y z`. -/
theorem cesaro_algebra {K y z M u T η ℓ S : ℝ} (hK0 : 0 ≤ K) (hy : 3 ≤ y) (hz0 : 0 < z)
    (hyz : 1 ≤ y * z) (hM0 : 0 ≤ M) (hu : 4 ≤ |u|) (hT : T = y ^ 2 + |u| + 3) (hlog : 1 < ℓ)
    (hη : η = 1 / ℓ)
    (h : S ≤ K * (y ^ 2 / T + M * (y ^ 2 / T ^ 2 + y * Real.exp 1 / u ^ 2 + y * z) +
      y * Real.exp 1 / (η ^ 2 * u ^ 2))) :
    y * S ≤ 3 * K * y ^ 2 * ((M + 1) * (z + (1 + ℓ ^ 2) / u ^ 2)) := by
  have hy0 : 0 < y := by linarith
  have hexp : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hu2 : 0 < u ^ 2 := by
    have : 0 < |u| := by linarith
    rw [← sq_abs]
    positivity
  have hyT : y ^ 2 ≤ T := by rw [hT]; linarith [abs_nonneg u]
  have hT0 : 0 < T := by rw [hT]; positivity
  have hq₁ : y ^ 2 / T ≤ 1 := div_le_one_of_le₀ hyT hT0.le
  have hy1 : 1 ≤ y := by linarith
  have hq₂ : y ^ 2 / T ^ 2 ≤ 1 / y := by
    rw [div_le_div_iff₀ (by positivity) hy0]
    have h₁ : y ^ 3 ≤ (y ^ 2) ^ 2 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hy1 (by norm_num)
    have h₂ : (y ^ 2) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hyT 2
    calc y ^ 2 * y = y ^ 3 := by ring
      _ ≤ 1 * T ^ 2 := by linarith
  have hy2z : y ≤ y ^ 2 * z := by
    calc y = y * 1 := (mul_one y).symm
      _ ≤ y * (y * z) := mul_le_mul_of_nonneg_left hyz hy0.le
      _ = y ^ 2 * z := by ring
  have hq₃ : y * (y ^ 2 / T) ≤ y ^ 2 * z :=
    (mul_le_of_le_one_right hy0.le hq₁).trans hy2z
  have hq₄ : y * (M * (y ^ 2 / T ^ 2)) ≤ M * (y ^ 2 * z) := by
    have h₁ : y * (y ^ 2 / T ^ 2) ≤ 1 := by
      calc y * (y ^ 2 / T ^ 2) ≤ y * (1 / y) := by gcongr
        _ = 1 := by field_simp
    calc y * (M * (y ^ 2 / T ^ 2)) = M * (y * (y ^ 2 / T ^ 2)) := by ring
      _ ≤ M * (y ^ 2 * z) := mul_le_mul_of_nonneg_left (h₁.trans (hy1.trans hy2z)) hM0
  have hq₅ : y * (M * (y * Real.exp 1 / u ^ 2)) ≤ 3 * M * (y ^ 2 / u ^ 2) := by
    rw [show y * (M * (y * Real.exp 1 / u ^ 2)) = Real.exp 1 * (M * (y ^ 2 / u ^ 2)) by ring]
    have : 0 ≤ M * (y ^ 2 / u ^ 2) := by positivity
    nlinarith
  have hq₆ : y * (y * Real.exp 1 / (η ^ 2 * u ^ 2)) ≤ 3 * (ℓ ^ 2 * (y ^ 2 / u ^ 2)) := by
    have hη2 : η ^ 2 * u ^ 2 = u ^ 2 / ℓ ^ 2 := by rw [hη]; field_simp
    rw [hη2, show y * (y * Real.exp 1 / (u ^ 2 / ℓ ^ 2)) =
      Real.exp 1 * (ℓ ^ 2 * (y ^ 2 / u ^ 2)) by field_simp]
    have : 0 ≤ ℓ ^ 2 * (y ^ 2 / u ^ 2) := by positivity
    nlinarith
  have hmain : y * S ≤
      K * (y ^ 2 * z + M * (y ^ 2 * z) + 3 * M * (y ^ 2 / u ^ 2) + M * (y ^ 2 * z) +
        3 * (ℓ ^ 2 * (y ^ 2 / u ^ 2))) := by
    refine (mul_le_mul_of_nonneg_left h hy0.le).trans ?_
    rw [show y * (K * (y ^ 2 / T + M * (y ^ 2 / T ^ 2 + y * Real.exp 1 / u ^ 2 + y * z) +
        y * Real.exp 1 / (η ^ 2 * u ^ 2))) = K * (y * (y ^ 2 / T) + y * (M * (y ^ 2 / T ^ 2)) +
        y * (M * (y * Real.exp 1 / u ^ 2)) + M * (y ^ 2 * z) +
        y * (y * Real.exp 1 / (η ^ 2 * u ^ 2))) by ring]
    gcongr
  have hw : 0 ≤ y ^ 2 / u ^ 2 := by positivity
  have hyz2 : 0 ≤ y ^ 2 * z := by positivity
  have key : 3 * (y ^ 2 * ((M + 1) * (z + (1 + ℓ ^ 2) / u ^ 2))) -
      (y ^ 2 * z + M * (y ^ 2 * z) + 3 * M * (y ^ 2 / u ^ 2) + M * (y ^ 2 * z) +
        3 * (ℓ ^ 2 * (y ^ 2 / u ^ 2))) =
      2 * (y ^ 2 * z) + M * (y ^ 2 * z) + 3 * (y ^ 2 / u ^ 2) +
        3 * (M * ℓ ^ 2 * (y ^ 2 / u ^ 2)) := by ring
  have h₁ : 0 ≤ M * ℓ ^ 2 * (y ^ 2 / u ^ 2) := by positivity
  have h₂ : 0 ≤ M * (y ^ 2 * z) := mul_nonneg hM0 hyz2
  calc y * S
      ≤ K * (3 * (y ^ 2 * ((M + 1) * (z + (1 + ℓ ^ 2) / u ^ 2)))) :=
        hmain.trans (mul_le_mul_of_nonneg_left (by linarith) hK0)
    _ = 3 * K * y ^ 2 * ((M + 1) * (z + (1 + ℓ ^ 2) / u ^ 2)) := by ring

/-- The Cesàro-weighted twisted sum, normalized: with `M = log(k (y² + 2|u| + 6))`,
`y |S(y)| ≪ y² (M + 1) (y^{-1/16} + (1 + log² y) / u²)`. -/
theorem exists_mul_norm_twistCesaro_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {k : ℕ} [NeZero k]
    (χ : DirichletCharacter ℂ k) {u y : ℝ}, 4 ≤ |u| → 3 ≤ y → (∀ m : ℕ, (m : ℝ) ≠ y) →
    y * ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, twistCoeff χ u m * (1 - m / y)‖ ≤
      K * y ^ 2 * ((Real.log (k * (y ^ 2 + 2 * |u| + 6)) + 1) *
        (y ^ (-(1 / 16) : ℝ) + (1 + Real.log y ^ 2) / u ^ 2)) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_twistCesaro_le
  refine ⟨3 * K, by positivity, ?_⟩
  intro k _ χ u y hu hy hyN
  have hy0 : 0 < y := by linarith
  have hlog : 1 < Real.log y :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hy)
  set ℓ := Real.log y with hℓ
  set η := 1 / ℓ with hη
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by rw [hη, div_le_one (by linarith)]; linarith
  set T := y ^ 2 + |u| + 3 with hT
  have h := hK χ (T := T) (η := η) hu (by nlinarith [abs_nonneg u]) (by linarith) hyN hη0 hη1
  have hTu : T + |u| + 3 = y ^ 2 + 2 * |u| + 6 := by ring
  rw [hTu] at h
  set M := Real.log (k * (y ^ 2 + 2 * |u| + 6)) with hM
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hM0 : 0 ≤ M := Real.log_nonneg (by nlinarith [abs_nonneg u])
  -- `y^{1+η} = e y` and `y^{15/16} = y · y^{-1/16}`
  have he : y ^ (1 + η) = y * Real.exp 1 := by
    rw [Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0, ← hℓ, hη,
      mul_one_div_cancel (by linarith)]
  have h1516 : y ^ (15 / 16 : ℝ) = y * y ^ (-(1 / 16) : ℝ) := by
    rw [← Real.rpow_one_add' hy0.le (by norm_num)]
    norm_num
  rw [he, h1516] at h
  set z := y ^ (-(1 / 16) : ℝ) with hz
  have hz0 : 0 < z := by positivity
  have hyz : 1 ≤ y * z := by
    rw [hz, ← Real.rpow_one_add' hy0.le (by norm_num)]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  exact cesaro_algebra hK0 hy hz0 hyz hM0 hu hT hlog hη h

/-- `‖χ(n) Λ(n) n^{iu}‖ ≤ Λ(n)`. -/
theorem norm_twistCoeff_le {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ) (n : ℕ) :
    ‖twistCoeff χ u n‖ ≤ Λ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [twistCoeff]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [twistCoeff, norm_mul, norm_mul, norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    Real.rpow_zero, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  calc ‖χ n‖ * Λ n ≤ 1 * Λ n := by
        gcongr
        exact DirichletCharacter.norm_le_one χ n
    _ = Λ n := one_mul _

/-- `Icc 1 N = Ioc 0 N` in `ℕ`. -/
theorem Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- Sharp sums from Cesàro sums: differencing `y S(y)` at `N + 1/2` and `N + 1/2 + m`. -/
theorem norm_sum_twistCoeff_le {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ) (N m : ℕ)
    (hm : 1 ≤ m) :
    ‖∑ n ∈ Finset.Icc 1 N, twistCoeff χ u n‖ ≤
      (((N : ℝ) + 1 / 2 + m) * ‖∑ n ∈ Finset.Icc 1 ⌊(N : ℝ) + 1 / 2 + m⌋₊,
          twistCoeff χ u n * (1 - n / (((N : ℝ) + 1 / 2 + m : ℝ) : ℂ))‖ +
        ((N : ℝ) + 1 / 2) * ‖∑ n ∈ Finset.Icc 1 ⌊(N : ℝ) + 1 / 2⌋₊,
          twistCoeff χ u n * (1 - n / (((N : ℝ) + 1 / 2 : ℝ) : ℂ))‖) / m +
        m * Real.log (N + m) := by
  set a := twistCoeff χ u
  set y₀ : ℝ := N + 1 / 2 with hy₀
  set y₁ : ℝ := N + 1 / 2 + m with hy₁
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hy₀0 : 0 < y₀ := by positivity
  have hy₁0 : 0 < y₁ := by positivity
  have hfl₀ : ⌊y₀⌋₊ = N := by
    rw [Nat.floor_eq_iff hy₀0.le]
    constructor <;> linarith
  have hfl₁ : ⌊y₁⌋₊ = N + m := by
    rw [Nat.floor_eq_iff hy₁0.le, hy₁]
    push_cast
    constructor <;> linarith
  -- `y S(y) = ∑ a(n) (y - n)`
  have hΦ : ∀ y : ℝ, 0 < y → (y : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * (1 - n / y) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, a n * ((y : ℂ) - n) := by
    intro y hy
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
    field_simp
  set R := ∑ n ∈ Finset.Ioc N (N + m), a n * ((y₁ : ℂ) - n) with hR
  have hid : (m : ℂ) * ∑ n ∈ Finset.Icc 1 N, a n =
      (y₁ : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y₁⌋₊, a n * (1 - n / y₁) -
        (y₀ : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y₀⌋₊, a n * (1 - n / y₀) - R := by
    rw [hΦ y₁ hy₁0, hΦ y₀ hy₀0, hfl₀, hfl₁, Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le N) (Nat.le_add_right N m), hR,
      show ∀ X Y Z : ℂ, X + Y - Z - Y = X - Z from fun X Y Z ↦ by ring,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [hy₁, hy₀]
    push_cast
    ring
  -- the remainder over `(N, N + m]`
  have hRle : ‖R‖ ≤ m * (m * Real.log (N + m)) := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    have hlog : 0 ≤ Real.log (N + m) := Real.log_nonneg (by linarith)
    calc ‖R‖ ≤ ∑ n ∈ Finset.Ioc N (N + m), ‖a n * ((y₁ : ℂ) - n)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Ioc N (N + m), m * Real.log (N + m) := by
          refine Finset.sum_le_sum fun n hn ↦ ?_
          rw [Finset.mem_Ioc] at hn
          have hn₁ : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
          have hn₂ : (n : ℝ) ≤ N + m := by exact_mod_cast hn.2
          have hyn : ‖(y₁ : ℂ) - n‖ ≤ m := by
            rw [show (y₁ : ℂ) - n = ((y₁ - n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            linarith
          have han : ‖a n‖ ≤ Real.log (N + m) :=
            (norm_twistCoeff_le χ u n).trans (vonMangoldt_le_log.trans
              (Real.log_le_log (by linarith) hn₂))
          rw [norm_mul, mul_comm (m : ℝ)]
          exact mul_le_mul han hyn (norm_nonneg _) hlog
      _ = m * (m * Real.log (N + m)) := by
          rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
  have hnorm := congrArg norm hid
  rw [norm_mul, Complex.norm_natCast] at hnorm
  have h₁ := norm_sub_le ((y₁ : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y₁⌋₊, a n * (1 - n / y₁) -
    (y₀ : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y₀⌋₊, a n * (1 - n / y₀)) R
  have h₂ := norm_sub_le ((y₁ : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y₁⌋₊, a n * (1 - n / y₁))
    ((y₀ : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y₀⌋₊, a n * (1 - n / y₀))
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hy₁0.le,
    Real.norm_of_nonneg hy₀0.le] at h₂
  rw [div_add' _ _ _ hm0.ne', le_div_iff₀ hm0]
  linarith

/-- The prime part `χ(p) p^{iu} log p` of `twistCoeff`. -/
noncomputable def primeCoeff {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ) (n : ℕ) : ℂ :=
  if n.Prime then χ n * (n : ℂ) ^ ((u : ℂ) * I) * Real.log n else 0

/-- Prime powers `p^a`, `a ≥ 2`, contribute at most `ψ(N) - θ(N) ≤ 2 √N log N`. -/
theorem norm_sum_twistCoeff_sub_primeCoeff_le {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, twistCoeff χ u n - ∑ n ∈ Finset.Icc 1 N, primeCoeff χ u n‖ ≤
      2 * √N * Real.log N := by
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n, ‖twistCoeff χ u n - primeCoeff χ u n‖ ≤ if n.Prime then 0 else Λ n := by
    intro n
    by_cases hn : n.Prime
    · simp only [hn, primeCoeff, twistCoeff, vonMangoldt_apply_prime hn, ↓reduceIte,
        norm_le_zero_iff]
      push_cast
      ring
    · simp only [hn, primeCoeff, ↓reduceIte, sub_zero]
      exact norm_twistCoeff_le χ u n
  refine (Finset.sum_le_sum fun n _ ↦ hterm n).trans ?_
  have hψθ := Chebyshev.psi_sub_theta_eq_sum_not_prime (N : ℝ)
  rw [Nat.floor_natCast, Finset.sum_filter] at hψθ
  rw [Icc_one_eq_Ioc_zero]
  calc ∑ n ∈ Finset.Ioc 0 N, (if n.Prime then 0 else Λ n)
      = ∑ n ∈ Finset.Ioc 0 N, (if ¬n.Prime then Λ n else 0) :=
        Finset.sum_congr rfl fun n _ ↦ by split_ifs <;> rfl
    _ = Chebyshev.psi N - Chebyshev.theta N := hψθ.symm
    _ ≤ 2 * √N * Real.log N := Chebyshev.psi_sub_theta_le (by exact_mod_cast hN)

/-- Abel's inequality: for weights `w` nonincreasing and nonnegative on `(m, n + 1]`, a
weighted sum is at most `w(m + 1)` times a bound on the partial sums. -/
theorem norm_sum_mul_le_of_antitone {w : ℕ → ℝ} {c : ℕ → ℂ} {m n : ℕ} {B : ℝ} (hB0 : 0 ≤ B)
    (hw : ∀ i, m < i → w (i + 1) ≤ w i) (hw0 : ∀ i, 0 ≤ w i)
    (hB : ∀ j, m ≤ j → j ≤ n → ‖∑ i ∈ Finset.Ioc m j, c i‖ ≤ B) :
    ‖∑ i ∈ Finset.Ioc m n, (w i : ℂ) * c i‖ ≤ B * w (m + 1) := by
  rcases lt_or_ge n m with hnm | hmn
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    exact mul_nonneg hB0 (hw0 _)
  -- the Abel identity with tail weight `w(j + 1)`
  have key : ∀ j, m ≤ j → j ≤ n → ‖∑ i ∈ Finset.Ioc m j, (w i : ℂ) * c i -
      (w (j + 1) : ℂ) * ∑ i ∈ Finset.Ioc m j, c i‖ ≤ B * (w (m + 1) - w (j + 1)) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      intro hjn
      have ih := ih (by omega)
      rw [Finset.sum_Ioc_succ_top hj, Finset.sum_Ioc_succ_top hj]
      have hrw : ∑ i ∈ Finset.Ioc m j, (w i : ℂ) * c i + (w (j + 1) : ℂ) * c (j + 1) -
          (w (j + 1 + 1) : ℂ) * (∑ i ∈ Finset.Ioc m j, c i + c (j + 1)) =
          (∑ i ∈ Finset.Ioc m j, (w i : ℂ) * c i - (w (j + 1) : ℂ) * ∑ i ∈ Finset.Ioc m j, c i) +
            ((w (j + 1) - w (j + 1 + 1) : ℝ) : ℂ) * (∑ i ∈ Finset.Ioc m j, c i + c (j + 1)) := by
        push_cast
        ring
      rw [hrw]
      refine (norm_add_le _ _).trans ?_
      have hwj : 0 ≤ w (j + 1) - w (j + 1 + 1) := sub_nonneg.mpr (hw _ (by omega))
      have hC : ‖∑ i ∈ Finset.Ioc m j, c i + c (j + 1)‖ ≤ B := by
        rw [← Finset.sum_Ioc_succ_top hj]
        exact hB _ (by omega) hjn
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hwj]
      nlinarith
  have h := key n hmn le_rfl
  have hn := hB n hmn le_rfl
  have h₁ := norm_sub_norm_le (∑ i ∈ Finset.Ioc m n, (w i : ℂ) * c i)
    ((w (n + 1) : ℂ) * ∑ i ∈ Finset.Ioc m n, c i)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 _)] at h₁
  nlinarith [hw0 (n + 1)]

/-- The twisted prime sum as a weighted sum of `primeCoeff` with weights `1 / (n log n)`. -/
theorem sum_prime_eq_sum_primeCoeff {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ) (a b : ℕ) :
    ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, χ p * (p : ℂ) ^ ((-1 : ℂ) + (u : ℂ) * I) =
      ∑ n ∈ Finset.Ioc a b, (((n : ℝ) * Real.log n)⁻¹ : ℝ) * primeCoeff χ u n := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [primeCoeff]
  split_ifs with hn
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
    have hlog : (Real.log n : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
    have hlog' : Complex.log n ≠ 0 := by
      rwa [← ofReal_natCast, ← ofReal_log (Nat.cast_nonneg n)]
    rw [cpow_add _ _ hn0, cpow_neg_one]
    push_cast
    field_simp
  · rw [mul_zero]

/-- `j + 1/2` is not an integer. -/
theorem natCast_ne_add_half (j n : ℕ) : (n : ℝ) ≠ j + 1 / 2 := by
  intro h
  have h₂ : ((2 * n : ℕ) : ℝ) = ((2 * j + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have := Nat.cast_injective h₂
  omega

/-- Partial sums of `primeCoeff`, given a bound `D` for the normalized Cesàro error on
`[j, j + m + 1]`. -/
theorem exists_norm_sum_primeCoeff_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {k : ℕ} [NeZero k]
    (χ : DirichletCharacter ℂ k) {u : ℝ} {j m : ℕ} {D : ℝ}, 4 ≤ |u| → 3 ≤ j → 1 ≤ m →
    (∀ y : ℝ, (j : ℝ) ≤ y → y ≤ j + m + 1 →
      (Real.log (k * (y ^ 2 + 2 * |u| + 6)) + 1) *
        (y ^ (-(1 / 16) : ℝ) + (1 + Real.log y ^ 2) / u ^ 2) ≤ D) →
    ‖∑ n ∈ Finset.Icc 1 j, primeCoeff χ u n‖ ≤
      2 * K * ((j : ℝ) + m + 1) ^ 2 * D / m + m * Real.log (j + m) +
        2 * √j * Real.log j := by
  obtain ⟨K, hK0, hK⟩ := exists_mul_norm_twistCesaro_le
  refine ⟨K, hK0, ?_⟩
  intro k _ χ u j m D hu hj hm hD
  have hj3 : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  -- each Cesàro term is at most `K (j + m + 1)² D`
  have hS : ∀ y : ℝ, (j : ℝ) ≤ y → y ≤ j + m + 1 → (∀ n : ℕ, (n : ℝ) ≠ y) →
      y * ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, twistCoeff χ u n * (1 - n / (y : ℂ))‖ ≤
        K * ((j : ℝ) + m + 1) ^ 2 * D := by
    intro y hy₁ hy₂ hyN
    refine (hK χ hu (by linarith) hyN).trans ?_
    have hΔ := hD y hy₁ hy₂
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
    have hΔ0 : 0 ≤ (Real.log (k * (y ^ 2 + 2 * |u| + 6)) + 1) *
        (y ^ (-(1 / 16) : ℝ) + (1 + Real.log y ^ 2) / u ^ 2) := by
      have : 0 ≤ Real.log (k * (y ^ 2 + 2 * |u| + 6)) :=
        Real.log_nonneg (by nlinarith [abs_nonneg u, sq_nonneg y])
      have : 0 < y := by linarith
      positivity
    rw [mul_assoc, mul_assoc]
    gcongr
    linarith
  have h₀ := hS ((j : ℝ) + 1 / 2) (by linarith) (by linarith) (fun n ↦ natCast_ne_add_half j n)
  have h₁ := hS ((j : ℝ) + 1 / 2 + m) (by linarith) (by linarith) (fun n ↦ by
    have := natCast_ne_add_half (j + m) n
    push_cast at this
    rwa [add_right_comm] at this)
  have hdiff := norm_sum_twistCoeff_le χ u j m hm
  have hpp := norm_sum_twistCoeff_sub_primeCoeff_le χ u (N := j) (by omega)
  have hsum := norm_sub_le (∑ n ∈ Finset.Icc 1 j, twistCoeff χ u n)
    (∑ n ∈ Finset.Icc 1 j, twistCoeff χ u n - ∑ n ∈ Finset.Icc 1 j, primeCoeff χ u n)
  rw [sub_sub_cancel] at hsum
  have hdiv : (((j : ℝ) + 1 / 2 + m) * ‖∑ n ∈ Finset.Icc 1 ⌊(j : ℝ) + 1 / 2 + m⌋₊,
        twistCoeff χ u n * (1 - n / (((j : ℝ) + 1 / 2 + m : ℝ) : ℂ))‖ +
      ((j : ℝ) + 1 / 2) * ‖∑ n ∈ Finset.Icc 1 ⌊(j : ℝ) + 1 / 2⌋₊,
        twistCoeff χ u n * (1 - n / (((j : ℝ) + 1 / 2 : ℝ) : ℂ))‖) / m ≤
      2 * K * ((j : ℝ) + m + 1) ^ 2 * D / m := by
    gcongr
    linarith
  linarith

/-- The twisted prime sum over `(a, b]` is at most `2 B / ((a + 1) log (a + 1))`, given the
bound `B` on the partial sums of `primeCoeff` up to `j ∈ [a, b]`. -/
theorem norm_sum_prime_le {k : ℕ} (χ : DirichletCharacter ℂ k) (u : ℝ) {a b : ℕ} {B : ℝ}
    (ha : 1 ≤ a) (hB0 : 0 ≤ B)
    (hB : ∀ j, a ≤ j → j ≤ b → ‖∑ n ∈ Finset.Icc 1 j, primeCoeff χ u n‖ ≤ B) :
    ‖∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, χ p * (p : ℂ) ^ ((-1 : ℂ) + (u : ℂ) * I)‖ ≤
      2 * B * (((a + 1 : ℕ) : ℝ) * Real.log ((a + 1 : ℕ) : ℝ))⁻¹ := by
  rw [sum_prime_eq_sum_primeCoeff]
  refine norm_sum_mul_le_of_antitone (by positivity) (fun i hi ↦ ?_) (fun i ↦ ?_)
    (fun j hj hjb ↦ ?_)
  · have hi1 : (2 : ℝ) ≤ i := by exact_mod_cast (show 2 ≤ i by omega)
    have hpos : 0 < (i : ℝ) * Real.log i :=
      mul_pos (by linarith) (Real.log_pos (by linarith))
    refine inv_anti₀ hpos ?_
    push_cast
    exact mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
      (Real.log_nonneg (by linarith)) (by linarith)
  · exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
  · have hsplit : ∑ n ∈ Finset.Ioc a j, primeCoeff χ u n =
        ∑ n ∈ Finset.Icc 1 j, primeCoeff χ u n - ∑ n ∈ Finset.Icc 1 a, primeCoeff χ u n := by
      rw [Icc_one_eq_Ioc_zero, Icc_one_eq_Ioc_zero,
        ← Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hj, add_sub_cancel_left]
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    linarith [hB j hj hjb, hB a le_rfl (hj.trans hjb)]

/-- The normalized Cesàro error at heights `y ≍ H` with `H^{1/32} ≥ L^{2A + 2}`,
`|u| ≥ L^{A + 2}` and `k ≤ x`, where `L = log x`: it is at most `36 L^{-2A}`. -/
theorem cesaroError_le {A l x H y u : ℝ} {k : ℕ} (hA : 1 ≤ A) (hL : 3 ≤ l) (hx : 20 ≤ x)
    (hLx : l = Real.log x) (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ x)
    (hHQ : l ^ (2 * A + 2) ≤ H ^ (1 / 32 : ℝ)) (hH : 16 ≤ H) (hHx : H ≤ x) (hy₁ : H - 1 ≤ y)
    (hy₂ : y ≤ 4 * H) (hu : l ^ (A + 2) ≤ |u|) (hux : |u| ≤ x ^ 3) :
    (Real.log (k * (y ^ 2 + 2 * |u| + 6)) + 1) *
      (y ^ (-(1 / 16) : ℝ) + (1 + Real.log y ^ 2) / u ^ 2) ≤ 36 * (l ^ (-A)) ^ 2 := by
  have hL0 : 0 < l := by linarith
  have hy0 : 0 < y := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set P := l ^ A with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) (by linarith)
  have hPA : l ^ (2 * A + 2) = l ^ 2 * P ^ 2 := by
    rw [show 2 * A + 2 = A + A + 2 by ring, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_two]
    ring
  have hPE : l ^ (A + 2) = l ^ 2 * P := by
    rw [Real.rpow_add hL0, Real.rpow_two]
    ring
  rw [Real.rpow_neg hL0.le, ← hP]
  -- `log(k (y² + 2|u| + 6)) + 1 ≤ 6 l`
  have hM : Real.log (k * (y ^ 2 + 2 * |u| + 6)) + 1 ≤ 6 * l := by
    have hy4 : y ^ 2 ≤ 16 * x ^ 2 := by
      have := pow_le_pow_left₀ hy0.le (show y ≤ 4 * x by linarith) 2
      linarith [show (4 * x) ^ 2 = 16 * x ^ 2 by ring]
    have hpoly : k * (y ^ 2 + 2 * |u| + 6) ≤ x ^ 5 := by
      calc k * (y ^ 2 + 2 * |u| + 6) ≤ x * (16 * x ^ 2 + 2 * x ^ 3 + 6) := by
            gcongr
          _ = 2 * x ^ 4 + 16 * x ^ 3 + 6 * x := by ring
          _ ≤ x ^ 5 := by
            have hx0 : 0 < x := by linarith
            have h3 := pow_pos hx0 3
            have h4 := pow_pos hx0 4
            have e1 : 16 * x ^ 3 ≤ x ^ 4 := by nlinarith
            have e2 : 6 * x ≤ x ^ 4 := by nlinarith
            have e3 : 4 * x ^ 4 ≤ x ^ 5 := by nlinarith
            linarith
    have hlog : Real.log (k * (y ^ 2 + 2 * |u| + 6)) ≤ 5 * l := by
      have h5 : Real.log (x ^ 5) = 5 * Real.log x := by
        rw [Real.log_pow]
        norm_num
      rw [hLx, ← h5]
      exact Real.log_le_log (mul_pos (by linarith) (by positivity)) (by exact_mod_cast hpoly)
    linarith
  -- `y^{-1/16} ≤ l^{-(2A+2)}`
  have hz : y ^ (-(1 / 16) : ℝ) ≤ (l ^ 2 * P ^ 2)⁻¹ := by
    have hsq : H ^ (1 / 2 : ℝ) ≤ y := by
      rw [← Real.sqrt_eq_rpow]
      have h4 : 4 ≤ √H := by
        rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
        exact Real.sqrt_le_sqrt hH
      have := Real.sq_sqrt (show 0 ≤ H by linarith)
      have h₂ : 4 * √H ≤ √H * √H := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg H)
      nlinarith
    have h1 : H ^ (1 / 32 : ℝ) ≤ y ^ (1 / 16 : ℝ) := by
      calc H ^ (1 / 32 : ℝ) = (H ^ (1 / 2 : ℝ)) ^ (1 / 16 : ℝ) := by
            rw [← Real.rpow_mul (by linarith)]
            norm_num
        _ ≤ y ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by positivity) hsq (by norm_num)
    rw [Real.rpow_neg hy0.le, ← hPA]
    exact inv_anti₀ (by positivity) (hHQ.trans h1)
  -- `(1 + log² y) / u² ≤ 5 l² / l^{2A+4}`
  have hlogy : 1 + Real.log y ^ 2 ≤ 5 * l ^ 2 := by
    have h₁ : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have h₂ : Real.log y ≤ 2 * l := by
      have h4 : Real.log 4 ≤ l := by
        rw [hLx]
        exact Real.log_le_log (by norm_num) (by linarith)
      calc Real.log y ≤ Real.log (4 * x) := Real.log_le_log hy0 (by linarith)
        _ = Real.log 4 + l := by rw [Real.log_mul (by norm_num) (by linarith), hLx]
        _ ≤ 2 * l := by linarith
    nlinarith
  have hu2 : (l ^ 2 * P) ^ 2 ≤ u ^ 2 := by
    rw [← hPE, ← sq_abs u]
    exact pow_le_pow_left₀ (by positivity) hu 2
  have hw : (1 + Real.log y ^ 2) / u ^ 2 ≤ 5 * l ^ 2 / (l ^ 2 * P) ^ 2 :=
    div_le_div₀ (by positivity) hlogy (by positivity) hu2
  have hM0 : 0 ≤ Real.log (k * (y ^ 2 + 2 * |u| + 6)) + 1 := by
    have : 0 ≤ Real.log (k * (y ^ 2 + 2 * |u| + 6)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 (by nlinarith [abs_nonneg u]))
    linarith
  calc (Real.log (k * (y ^ 2 + 2 * |u| + 6)) + 1) *
        (y ^ (-(1 / 16) : ℝ) + (1 + Real.log y ^ 2) / u ^ 2)
      ≤ 6 * l * ((l ^ 2 * P ^ 2)⁻¹ + 5 * l ^ 2 / (l ^ 2 * P) ^ 2) :=
        mul_le_mul hM (add_le_add hz hw) (by positivity) (by positivity)
    _ = 36 * (P⁻¹) ^ 2 / l := by
        field_simp
        ring
    _ ≤ 36 * (P⁻¹) ^ 2 := div_le_self (by positivity) (by linarith)

/-- `log (c H) ≤ 2 log H` for `c ≤ H`. -/
theorem log_mul_le_two_mul_log {c H : ℝ} (hc : 0 < c) (hcH : c ≤ H) :
    Real.log (c * H) ≤ 2 * Real.log H := by
  have hH : 0 < H := hc.trans_le hcH
  rw [Real.log_mul hc.ne' hH.ne', two_mul]
  linarith [Real.log_le_log hc hcH]

/-- The three error terms of `exists_norm_sum_primeCoeff_le` at `m ≈ H ε`, `j ≍ H`. -/
theorem partial_bound_aux {K H ε j m : ℝ} (hK0 : 0 ≤ K) (hH16 : 16 ≤ H) (hε0 : 0 < ε)
    (hHε : 1 ≤ H * ε) (hsqrtHε : √H ≤ H * ε) (hj₁' : H - 1 ≤ j) (hj₂' : j ≤ 2 * H)
    (hmlo : H * ε ≤ m) (hm2 : m ≤ 2 * (H * ε)) (hmH : m ≤ H) (hlogH : 1 ≤ Real.log H) :
    2 * K * (j + m + 1) ^ 2 * (36 * ε ^ 2) / m + m * Real.log (j + m) +
        2 * √j * Real.log j ≤ (1152 * K + 12) * (H * ε * Real.log H) := by
  have hH0 : 0 < H := by linarith
  have hm0 : 0 < m := by linarith
  -- the Cesàro part
  have hT₁ : 2 * K * ((j : ℝ) + m + 1) ^ 2 * (36 * ε ^ 2) / m ≤
      1152 * K * (H * ε * Real.log H) := by
    have hjm : ((j : ℝ) + m + 1) ^ 2 ≤ (4 * H) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc 2 * K * ((j : ℝ) + m + 1) ^ 2 * (36 * ε ^ 2) / m
        ≤ 2 * K * (4 * H) ^ 2 * (36 * ε ^ 2) / (H * ε) := by
          gcongr
      _ = 1152 * K * (H * ε) := by
          field_simp
          ring
      _ ≤ 1152 * K * (H * ε * Real.log H) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hlogH)
            (by positivity)
  -- the remainder of the differencing
  have hT₂ : (m : ℝ) * Real.log (j + m) ≤ 4 * (H * ε * Real.log H) := by
    have hlog : Real.log (j + m) ≤ 2 * Real.log H :=
      (Real.log_le_log (by linarith) (by linarith : (j : ℝ) + m ≤ 3 * H)).trans
        (log_mul_le_two_mul_log (by norm_num) (by linarith))
    calc (m : ℝ) * Real.log (j + m) ≤ (2 * (H * ε)) * (2 * Real.log H) :=
          mul_le_mul hm2 hlog (Real.log_nonneg (by linarith)) (by positivity)
      _ = 4 * (H * ε * Real.log H) := by ring
  -- the prime powers
  have hT₃ : 2 * √j * Real.log j ≤ 8 * (H * ε * Real.log H) := by
    have hsj : √(j : ℝ) ≤ 2 * √H := by
      calc √(j : ℝ) ≤ √(2 * H) := Real.sqrt_le_sqrt hj₂'
        _ = √2 * √H := Real.sqrt_mul (by norm_num) H
        _ ≤ 2 * √H := by
            gcongr
            rw [Real.sqrt_le_left (by norm_num)]
            norm_num
    have hlj : Real.log j ≤ 2 * Real.log H :=
      (Real.log_le_log (by linarith) hj₂').trans
        (log_mul_le_two_mul_log (by norm_num) (by linarith))
    calc 2 * √j * Real.log j ≤ 2 * (2 * √H) * (2 * Real.log H) := by
          gcongr
          exact Real.log_nonneg (by linarith)
      _ = 8 * (√H * Real.log H) := by ring
      _ ≤ 8 * (H * ε * Real.log H) := by gcongr
  linarith

/-- The twisted prime sum at heights `H` with `H^{1/32} ≥ L^{2A + 2}`, for `k ≤ x` and
`L^{A + 2} ≤ |u| ≤ x³`, where `L = log x`: it is `O(L^{-A})`. -/
theorem exists_norm_sum_prime_le_of_large : ∃ κ : ℝ, ∀ {A l x H lo hi u : ℝ} {k : ℕ}
    [NeZero k] (χ : DirichletCharacter ℂ k), 1 ≤ A → 3 ≤ l → 20 ≤ x → l = Real.log x →
    (k : ℝ) ≤ x → l ^ (2 * A + 2) ≤ H ^ (1 / 32 : ℝ) → 1 ≤ H → H ≤ x → H ≤ lo →
    hi ≤ 2 * H → l ^ (A + 2) ≤ |u| → |u| ≤ x ^ 3 →
    ‖∑ p ∈ (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime,
        χ p * (p : ℂ) ^ ((-1 : ℂ) + (u : ℂ) * I)‖ ≤ κ * l ^ (-A) := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sum_primeCoeff_le
  refine ⟨2304 * K + 24, ?_⟩
  intro A l x H lo hi u k _ χ hA hl hx hlx hkx hHQ hH1 hHx hlo hhi hu hux
  have hl0 : 0 < l := by linarith
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  set P := l ^ A with hP
  have hlP : l ≤ P := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ l) hA
    rwa [Real.rpow_one] at this
  have hPA : l ^ (2 * A + 2) = l ^ 2 * P ^ 2 := by
    rw [show 2 * A + 2 = A + A + 2 by ring, Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_two]
    ring
  have hPE : l ^ (A + 2) = l ^ 2 * P := by
    rw [Real.rpow_add hl0, Real.rpow_two]
    ring
  set ε := l ^ (-A) with hε
  have hεP : ε = P⁻¹ := by rw [hε, Real.rpow_neg hl0.le]
  have hP0 : 0 < P := by linarith
  have hε0 : 0 < ε := by rw [hεP]; positivity
  -- sizes of `H`
  have hQH : H ^ (1 / 32 : ℝ) ≤ √H := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num)
  have hsqrtH : √H ≤ H := by
    rw [Real.sqrt_le_left (by linarith)]
    exact le_self_pow₀ hH1 two_ne_zero
  have hbig : l ^ 2 * P ^ 2 ≤ √H := hPA ▸ (hHQ.trans hQH)
  have hl9 : 9 ≤ l ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hl 2
    norm_num at this
    exact this
  have hP9 : 9 ≤ P ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) (hl.trans hlP) 2
    norm_num at this
    exact this
  have hP2 : P ≤ l ^ 2 * P ^ 2 := by
    have h₁ : P ≤ P ^ 2 := le_self_pow₀ (by linarith) two_ne_zero
    have h₂ : P ^ 2 ≤ l ^ 2 * P ^ 2 := le_mul_of_one_le_left (sq_nonneg _) (by linarith)
    linarith
  have hPsq : P ≤ √H := hP2.trans hbig
  have h81 : 81 ≤ l ^ 2 * P ^ 2 := by
    have := mul_le_mul hl9 hP9 (by norm_num) (by linarith)
    linarith
  have hH16 : 16 ≤ H := by linarith
  have hH0 : 0 < H := by linarith
  have hHε : 1 ≤ H * ε := by
    rw [hεP, ← div_eq_mul_inv, le_div_iff₀ hP0]
    linarith
  have hsqrtHε : √H ≤ H * ε := by
    rw [hεP, ← div_eq_mul_inv, le_div_iff₀ hP0]
    calc √H * P ≤ √H * √H := mul_le_mul_of_nonneg_left hPsq (Real.sqrt_nonneg H)
      _ = H := Real.mul_self_sqrt hH0.le
  have hε3 : ε ≤ 1 / 3 := by
    rw [hεP]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hlogH : 1 ≤ Real.log H := by
    have := one_lt_log_three.trans_le (Real.log_le_log (by norm_num) (by linarith : (3 : ℝ) ≤ H))
    linarith
  -- the differencing step `m = ⌈H ε⌉`
  set m := ⌈H * ε⌉₊ with hm
  have hmlo : H * ε ≤ m := Nat.le_ceil _
  have hmhi : (m : ℝ) < H * ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm1 : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hm2 : (m : ℝ) ≤ 2 * (H * ε) := by linarith
  have hmH : (m : ℝ) ≤ H := by
    have := mul_le_mul_of_nonneg_left hε3 hH0.le
    linarith
  -- the endpoints
  have hlo0 : 0 ≤ lo := by linarith
  have hN₁ : H < (⌊lo⌋₊ : ℝ) + 1 := hlo.trans_lt (Nat.lt_floor_add_one lo)
  have hN₁15 : 15 ≤ ⌊lo⌋₊ := by
    have : (14 : ℝ) < ⌊lo⌋₊ := by linarith
    exact_mod_cast this
  have hN₂ : ∀ j : ℕ, j ≤ ⌊hi⌋₊ → (j : ℝ) ≤ 2 * H := fun j hj ↦ by
    have : (j : ℝ) ≤ ⌊hi⌋₊ := by exact_mod_cast hj
    rcases le_or_gt 0 hi with h | h
    · linarith [Nat.floor_le h]
    · rw [Nat.floor_of_nonpos h.le, Nat.cast_zero] at this
      linarith
  -- the partial sums of `primeCoeff`
  set B₀ := (1152 * K + 12) * (H * ε * Real.log H) with hB₀
  have hB : ∀ j, ⌊lo⌋₊ ≤ j → j ≤ ⌊hi⌋₊ → ‖∑ n ∈ Finset.Icc 1 j, primeCoeff χ u n‖ ≤ B₀ := by
    intro j hj₁ hj₂
    have hj₁' : H - 1 ≤ (j : ℝ) := by
      have : (⌊lo⌋₊ : ℝ) ≤ j := by exact_mod_cast hj₁
      linarith
    have hj₂' := hN₂ j hj₂
    have hj3 : 3 ≤ j := by
      have : (2 : ℝ) < j := by linarith
      exact_mod_cast this
    have hu4 : 4 ≤ |u| := by
      rw [hPE] at hu
      have := mul_le_mul hl9 (hl.trans hlP) (by norm_num) (by linarith)
      linarith
    have h := hK χ (u := u) (j := j) (m := m) (D := 36 * ε ^ 2) hu4 hj3 hm1 fun y hy₁ hy₂ ↦
      cesaroError_le hA hl hx hlx hk hkx hHQ hH16 hHx (by linarith) (by linarith) hu hux
    refine h.trans ?_
    exact partial_bound_aux hK0 hH16 hε0 hHε hsqrtHε hj₁' hj₂' hmlo hm2 hmH hlogH
  have hB0 : 0 ≤ B₀ := by positivity
  refine (norm_sum_prime_le χ u (by omega) hB0 hB).trans ?_
  -- `(⌊lo⌋ + 1) log (⌊lo⌋ + 1) ≥ H log H`
  have hw : (((⌊lo⌋₊ + 1 : ℕ) : ℝ) * Real.log ((⌊lo⌋₊ + 1 : ℕ) : ℝ))⁻¹ ≤ (H * Real.log H)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    push_cast
    exact mul_le_mul hN₁.le (Real.log_le_log hH0 hN₁.le) (by linarith) (by linarith)
  calc 2 * B₀ * (((⌊lo⌋₊ + 1 : ℕ) : ℝ) * Real.log ((⌊lo⌋₊ + 1 : ℕ) : ℝ))⁻¹
      ≤ 2 * B₀ * (H * Real.log H)⁻¹ := by gcongr
    _ = (2304 * K + 24) * ε := by
        rw [hB₀]
        field_simp
        ring

open Filter in
/-- For large `x`, with `L = log x` and `T = log L`: `L ≥ 3`, `L^{C_m} ≤ x` and
`L^B ≤ exp(L / T²² / 32)`. -/
theorem eventually_log_bounds (Cm B : ℝ) (hB : 0 < B) : ∀ᶠ x : ℝ in atTop,
    3 ≤ Real.log x ∧ Real.log x ^ Cm ≤ x ∧
      Real.log x ^ B ≤ Real.exp (Real.log x / Real.log (Real.log x) ^ 22 / 32) := by
  have hlog := Real.tendsto_log_atTop
  have h₁ := (Real.isLittleO_log_id_atTop.comp_tendsto hlog).bound
    (c := 1 / (|Cm| + 1)) (by positivity)
  have h₂ := ((Real.isLittleO_pow_log_id_atTop (n := 23)).comp_tendsto hlog).bound
    (c := 1 / (32 * B + 1)) (by positivity)
  filter_upwards [hlog.eventually_ge_atTop 3, eventually_ge_atTop 1, h₁, h₂]
    with x hL hx hx₁ hx₂
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hx₁ hx₂
  have hL0 : 0 < Real.log x := by linarith
  have hT : 1 < Real.log (Real.log x) :=
    one_lt_log_three.trans_le (Real.log_le_log (by norm_num) hL)
  rw [abs_of_pos hL0, abs_of_pos (by linarith : (0 : ℝ) < Real.log (Real.log x))] at hx₁
  rw [abs_of_pos hL0, abs_of_pos (pow_pos (by linarith) 23)] at hx₂
  set l := Real.log x with hLdef
  set T := Real.log l with hTdef
  refine ⟨hL, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hL0, ← hTdef]
    calc Real.exp (T * Cm) ≤ Real.exp l := by
          refine Real.exp_le_exp.mpr ?_
          have h₃ : T * Cm ≤ T * |Cm| := mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
          have h₄ : T * |Cm| ≤ l := by
            have := mul_le_mul_of_nonneg_left hx₁ (abs_nonneg Cm)
            rw [show |Cm| * (1 / (|Cm| + 1) * l) = |Cm| / (|Cm| + 1) * l by ring] at this
            have h₅ : |Cm| / (|Cm| + 1) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith
            rw [mul_comm]
            exact this.trans (mul_le_of_le_one_left hL0.le h₅)
          linarith
      _ = x := Real.exp_log (by linarith)
  · rw [Real.rpow_def_of_pos hL0, ← hTdef]
    refine Real.exp_le_exp.mpr ?_
    rw [div_div, le_div_iff₀ (by positivity)]
    have h₃ : 32 * B * T ^ 23 ≤ l := by
      have := mul_le_mul_of_nonneg_left hx₂ (by positivity : (0 : ℝ) ≤ 32 * B)
      rw [show 32 * B * (1 / (32 * B + 1) * l) = 32 * B / (32 * B + 1) * l by ring] at this
      have h₅ : 32 * B / (32 * B + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      exact this.trans (mul_le_of_le_one_left hL0.le h₅)
    calc T * B * (T ^ 22 * 32) = 32 * B * T ^ 23 := by ring
      _ ≤ l := h₃

end PrimeTwist

open PrimeTwist

open Filter in
/-- Twisted prime sums at large heights (AC2), the premise `PrimeTwistBound`
of `TwoSidedCorrelation`. -/
theorem eventually_primeTwistBound (A Cm : ℝ) :
    ∃ E κ : ℝ, ∀ᶠ x : ℝ in atTop, PrimeTwistBound x A E Cm κ := by
  obtain ⟨κ, hκ⟩ := exists_norm_sum_prime_le_of_large
  set A' := max A 1 with hA'
  have hA'1 : 1 ≤ A' := le_max_right _ _
  refine ⟨A' + 2, max κ 0, ?_⟩
  filter_upwards [eventually_log_bounds Cm (2 * A' + 2) (by positivity),
    eventually_ge_atTop 20] with x hx hx20
  obtain ⟨hL3, hLCm, hLB⟩ := hx
  intro H lo hi hH hHx hlo hhi k hk1 hkL χ u huL hux
  have : NeZero k := ⟨by omega⟩
  set l := Real.log x with hLdef
  have hL0 : 0 < l := by linarith
  set T := Real.log l with hTdef
  have hT : 0 < T := Real.log_pos (by linarith)
  -- `H^{1/32} ≥ exp(l / T²² / 32) ≥ l^{2A' + 2}`
  have hH0 : 0 ≤ l / T ^ 22 := by positivity
  have hH1 : 1 ≤ H := (Real.one_le_exp hH0).trans hH
  have hHQ : l ^ (2 * A' + 2) ≤ H ^ (1 / 32 : ℝ) := by
    refine hLB.trans ?_
    calc Real.exp (l / T ^ 22 / 32) = Real.exp (l / T ^ 22) ^ (1 / 32 : ℝ) := by
          rw [← Real.exp_mul]
          ring_nf
      _ ≤ H ^ (1 / 32 : ℝ) := Real.rpow_le_rpow (Real.exp_pos _).le hH (by norm_num)
  have h := hκ χ hA'1 hL3 hx20 hLdef (hkL.trans hLCm) hHQ hH1 hHx hlo hhi huL hux
  refine h.trans ?_
  have hLA : l ^ (-A') ≤ l ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg (le_max_left _ _))
  calc κ * l ^ (-A') ≤ max κ 0 * l ^ (-A') :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max κ 0 * l ^ (-A) := mul_le_mul_of_nonneg_left hLA (le_max_right _ _)

end Erdos408
