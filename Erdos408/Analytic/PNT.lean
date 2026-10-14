module

public import Erdos408.Analytic.Core
public import Erdos408.Hypotheses
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import PrimeNumberTheoremAnd.PerronFormula

/-!
# The prime number theorem in progressions with a power saving

AC0 of `blueprint/rectangle_input.md` §3:
`ψ(y, χ) = [χ = 1] y + O(k^C y^{1-c})` for every Dirichlet character `χ` of
modulus `k`, from a smoothed Perron formula shifted into the zero-free
half-plane `re s > 7/8`.

* The smoothed sum `∑_{m ≤ x} Λ(m) χ(m) (1 - m / x)` is the vertical integral on
  `re s = 2` of `-(L'/L)(s, χ) x^s / (s (s + 1))`; truncating at height `x²`
  costs `O(1)`. The Perron part is adapted from `Erdos770.Analytic.Perron`.
* Shift to `re s = 15/16` across the rectangle `[15/16, 2] × [-x², x²]`. No zero
  lies inside, so only the pole of the principal character at `s = 1`
  contributes, with residue `x / 2`.
* On the left edge, `L'/L ≪ log (k (|t| + 3))` away from `s = 1`, by
  `Erdos408.Analytic.Core`. Near `s = 1`, Borel–Carathéodory on discs centred at
  `2 + it` bounds `L'/L` for `χ ≠ 1`, and `L'/L + 1/(s - 1)` for the principal
  character through the entire function `(s - 1) L(s, χ₀)`, by `O(k)`.
* So the smoothed sum is `[χ = 1] x / 2 + O(k x^{15/16})`. Differencing the
  weighted sums `∑_{n ≤ z} Λ(n) χ(n) (z - n)` at `z = ⌊y⌋ + 1/2` and `z + h`,
  with `h ≈ y^{31/32}`, gives the theorem with `c = 1/64` and `C = O(1)`.
-/

@[expose] public section

namespace Erdos408

open Filter Classical

namespace PNT

/-! ### The smoothed Perron formula -/

section Perron

open Complex ArithmeticFunction DirichletCharacter

/-- The integrand `-(L'/L)(s, χ) x^s / (s (s + 1))` of the smoothed explicit
formula. -/
noncomputable def perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ)
    (s : ℂ) : ℂ :=
  -(deriv (LFunction χ) s / LFunction χ s) * ((x : ℂ) ^ s / (s * (s + 1)))

open MeasureTheory Set LSeries
open scoped LSeries.notation

/-- On `re s > 1`, `-(L'/L)(s, χ)` is the L-series of `χ Λ`. -/
theorem neg_logDeriv_LFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -(deriv (LFunction χ) s / LFunction χ s) = LSeries (↗χ * ↗Λ) s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
    LSeries_twist_vonMangoldt_eq χ hs, neg_div]

/-- On `re s = 2`, the terms of the L-series of `χ Λ` are dominated by those of `Λ`
at `2`. -/
theorem norm_term_twist_vonMangoldt_le {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.re = 2) (n : ℕ) : ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ 2 n‖ := by
  rw [norm_term_eq, norm_term_eq, hs, show (2 : ℂ).re = 2 by simp]
  split_ifs
  · rfl
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  gcongr
  simpa [norm_mul] using mul_le_of_le_one_left (abs_nonneg (Λ n)) hχ

/-- The terms `Λ(n) / n²` are absolutely summable. -/
theorem summable_norm_term_vonMangoldt : Summable fun n ↦ ‖term ↗Λ 2 n‖ :=
  summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by norm_num))

/-- On `re s = 2`, `‖(L'/L)(s, χ)‖ ≤ ∑ Λ(n) / n²`. -/
theorem norm_neg_logDeriv_LFunction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : s.re = 2) :
    ‖-(deriv (LFunction χ) s / LFunction χ s)‖ ≤ ∑' n, ‖term ↗Λ 2 n‖ := by
  have hle := norm_term_twist_vonMangoldt_le χ hs
  have hsum : Summable fun n ↦ ‖term (↗χ * ↗Λ) s n‖ :=
    summable_norm_term_vonMangoldt.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [neg_logDeriv_LFunction_eq χ (by rw [hs]; norm_num), LSeries]
  exact (norm_tsum_le_tsum_norm hsum).trans
    (Summable.tsum_le_tsum hle hsum summable_norm_term_vonMangoldt)

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

/-- On `re s = 2`, the Perron integrand is dominated by `x^s / (s (s + 1))`. -/
theorem norm_perronIntegrand_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x t : ℝ) :
    ‖perronIntegrand χ x ((2 : ℝ) + t * I)‖ ≤
      (∑' n, ‖term ↗Λ 2 n‖) * ‖Perron.f x ((2 : ℝ) + t * I)‖ := by
  rw [perronIntegrand, norm_mul]
  gcongr
  exact norm_neg_logDeriv_LFunction_le χ (by simp)

/-- The Perron integrand is integrable on the line `re s = 2`. -/
theorem integrable_perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 0 < x) : Integrable fun t : ℝ ↦ perronIntegrand χ x ((2 : ℝ) + t * I) := by
  have hf : Integrable fun t : ℝ ↦ Perron.f x ((2 : ℝ) + t * I) :=
    Perron.isIntegrable hx (by norm_num) (by norm_num)
  have hline : Continuous fun t : ℝ ↦ ((2 : ℝ) : ℂ) + t * I := by fun_prop
  have hL : Continuous fun t : ℝ ↦ LFunction χ ((2 : ℝ) + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    refine ((differentiableAt_LFunction χ _ (Or.inl fun h ↦ ?_)).continuousAt).comp
      hline.continuousAt
    simpa using congrArg re h
  have hmeas : AEStronglyMeasurable fun t : ℝ ↦ perronIntegrand χ x ((2 : ℝ) + t * I) :=
    ((((measurable_deriv (LFunction χ)).comp hline.measurable).div
      hL.measurable).neg.aestronglyMeasurable).mul hf.aestronglyMeasurable
  exact (hf.norm.const_mul _).mono' hmeas
    (Filter.Eventually.of_forall fun t ↦ norm_perronIntegrand_le χ x t)

/-- Each term of the L-series times `x^s / (s (s + 1))` is a Perron kernel at `x / n`. -/
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

/-- The smoothed Perron formula: the vertical integral of `perronIntegrand` on
`re s = 2` is `2πi` times the weighted sum. -/
theorem verticalIntegral_perronIntegrand {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 1 < x) (hxN : ∀ m : ℕ, (m : ℝ) ≠ x) :
    VerticalIntegral (perronIntegrand χ x) 2 =
      2 * Real.pi * I * ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x) := by
  have hx0 : 0 < x := by linarith
  -- Expand the integrand as a Dirichlet series of Perron kernels.
  set g : ℕ → ℝ → ℂ := fun n t ↦
    term (↗χ * ↗Λ) ((2 : ℝ) + t * I) n * Perron.f x ((2 : ℝ) + t * I) with hg
  have hsum : ∀ t : ℝ, perronIntegrand χ x ((2 : ℝ) + t * I) = ∑' n, g n t := by
    intro t
    rw [perronIntegrand, neg_logDeriv_LFunction_eq χ (by simp), LSeries, ← tsum_mul_right]
  have hg_eq : ∀ n, n ≠ 0 → ∀ t,
      g n t = (↗χ * ↗Λ) n * Perron.f (x / n) ((2 : ℝ) + t * I) :=
    fun n hn t ↦ term_mul_perron_f_eq _ hx0 hn _
  -- Each term is integrable, and the integrals of the norms are summable.
  have hg_int : ∀ n, Integrable (g n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    · rw [funext (hg_eq n hn)]
      have hxn : 0 < x / n := div_pos hx0 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      exact (Perron.isIntegrable hxn (by norm_num) (by norm_num)).const_mul _
  have hg_norm : ∀ n, ∫ t, ‖g n t‖ =
      ‖term (↗χ * ↗Λ) 2 n‖ * ∫ t : ℝ, ‖Perron.f x ((2 : ℝ) + t * I)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1 with t
    rw [hg, norm_mul, norm_term_eq, norm_term_eq]
    simp
  have hg_sum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    simp_rw [hg_norm]
    have hχΛ : LSeriesSummable (↗χ * ↗Λ) 2 :=
      LSeriesSummable_twist_vonMangoldt χ (by norm_num)
    exact (summable_norm_iff.mpr hχΛ).mul_right _
  -- Evaluate each term with the Perron formula.
  have hg_val : ∀ n, ∫ t, g n t = if n ∈ Finset.Icc 1 ⌊x⌋₊ then
      2 * Real.pi * ((Λ n : ℂ) * χ n * (1 - n / x)) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [funext (hg_eq n hn), integral_const_mul]
    split_ifs with hmem
    · have hnx : (n : ℝ) < x :=
        lt_of_le_of_ne ((Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hmem).2) (hxN n)
      rw [integral_perron_f_of_one_lt ((one_lt_div hn0).mpr hnx)]
      push_cast
      rw [one_div_div]
      simp only [Pi.mul_apply]
      ring
    · have hxn : x < n := (Nat.floor_lt hx0.le).mp (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
        omega)
      rw [integral_perron_f_of_lt_one (div_pos hx0 hn0) ((div_lt_one hn0).mpr hxn), mul_zero]
  -- Interchange the sum and the integral.
  rw [VerticalIntegral, smul_eq_mul, funext hsum,
    ← integral_tsum_of_summable_integral_norm hg_int hg_sum, tsum_congr hg_val,
    tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn ↦ ite_eq_right hn),
    Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn), ← Finset.mul_sum]
  ring

/-- Truncating the vertical integral at height `T` costs `O(x² / T)`. -/
theorem exists_norm_verticalIntegral_sub_le :
    ∃ C : ℝ, ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {x T : ℝ}, 1 ≤ x → 1 ≤ T →
      ‖VerticalIntegral (perronIntegrand χ x) 2 -
          VIntegral (perronIntegrand χ x) 2 (-T) T‖ ≤ C * x ^ 2 / T := by
  refine ⟨2 * ∑' n, ‖term ↗Λ 2 n‖, fun χ x T hx hT ↦ ?_⟩
  set A := ∑' n, ‖term ↗Λ 2 n‖
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set F : ℝ → ℂ := fun t ↦ perronIntegrand χ x ((2 : ℝ) + t * I)
  have hF_int : Integrable F := integrable_perronIntegrand χ hx0
  have hA : 0 ≤ A := tsum_nonneg fun _ ↦ norm_nonneg _
  -- Pointwise, `‖F t‖ ≤ A x² / t²`.
  have hF_le : ∀ t : ℝ, t ≠ 0 → ‖F t‖ ≤ A * x ^ 2 / t ^ 2 := by
    intro t ht
    rw [mul_div_assoc]
    exact (norm_perronIntegrand_le χ x t).trans
      (mul_le_mul_of_nonneg_left (norm_perron_f_le hx0 ht) hA)
  -- Bound the two tails.
  have hupper : ‖∫ t in Ici T, F t‖ ≤ A * x ^ 2 / T := by
    rw [integral_Ici_eq_integral_Ioi]
    exact norm_setIntegral_Ioi_le hT0 hF_int.integrableOn
      fun t ht ↦ hF_le t (hT0.trans ht).ne'
  have hlower : ‖∫ t in Iic (-T), F t‖ ≤ A * x ^ 2 / T := by
    rw [← integral_comp_neg_Ioi]
    refine norm_setIntegral_Ioi_le hT0 hF_int.comp_neg.integrableOn fun t ht ↦ ?_
    rw [← neg_sq t]
    exact hF_le (-t) (neg_ne_zero.mpr (hT0.trans ht).ne')
  rw [verticalIntegral_split_three (-T) T hF_int, add_right_comm, add_sub_cancel_right]
  calc ‖I • (∫ t in Iic (-T), F t) + I • ∫ t in Ici T, F t‖
      ≤ ‖∫ t in Iic (-T), F t‖ + ‖∫ t in Ici T, F t‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        simp
    _ ≤ A * x ^ 2 / T + A * x ^ 2 / T := add_le_add hlower hupper
    _ = 2 * A * x ^ 2 / T := by ring

end Perron

/-! ### Bounds on the kernel and on the edges -/

section Edges

open Complex

/-- To the right of `1/16`, `‖s (s + 1)‖` is at least `(1 + |im s|)² / 64`. -/
lemma one_add_abs_im_sq_le_norm_mul {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    (1 + |s.im|) ^ 2 ≤ 64 * ‖s * (s + 1)‖ := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₂ : s.re ≤ ‖s‖ := re_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  have h₄ : (s + 1).re ≤ ‖s + 1‖ := re_le_norm _
  simp only [add_im, one_im, add_zero, add_re, one_re] at h₃ h₄
  have h₅ : 1 + |s.im| ≤ 32 * ‖s‖ := by linarith
  have h₆ : 1 + |s.im| ≤ 2 * ‖s + 1‖ := by linarith
  calc (1 + |s.im|) ^ 2 ≤ (32 * ‖s‖) * (2 * ‖s + 1‖) := by
        rw [sq]; exact mul_le_mul h₅ h₆ (by positivity) (by positivity)
    _ = 64 * ‖s * (s + 1)‖ := by rw [norm_mul]; ring

/-- To the right of `1/16`, `‖x^s / (s (s + 1))‖ ≤ 64 x^{re s} / (1 + |im s|)²`. -/
lemma norm_cpow_div_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 16 ≤ s.re) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ 64 * x ^ s.re / (1 + |s.im|) ^ 2 := by
  have h := one_add_abs_im_sq_le_norm_mul hs
  have hpos : 0 < ‖s * (s + 1)‖ := by
    have : 0 < (1 + |s.im|) ^ 2 := by positivity
    linarith
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx, div_le_div_iff₀ hpos (by positivity)]
  have := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le s.re)
  linarith

/-- Off the real axis, `‖x^s / (s (s + 1))‖ ≤ x^{re s} / (im s)²`. -/
lemma norm_cpow_div_le_of_im_ne_zero {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0) :
    ‖(x : ℂ) ^ s / (s * (s + 1))‖ ≤ x ^ s.re / s.im ^ 2 := by
  have h₁ : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h₃ : |(s + 1).im| ≤ ‖s + 1‖ := abs_im_le_norm _
  simp only [add_im, one_im, add_zero] at h₃
  have h : s.im ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, ← sq_abs, sq]
    exact mul_le_mul h₁ h₃ (abs_nonneg _) (norm_nonneg _)
  have hpos : 0 < s.im ^ 2 := by positivity
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hpos h

/-- `1 + log (|t| + 3) ≤ 5 (1 + |t|)^{1/2}`. -/
lemma one_add_log_le_rpow (t : ℝ) :
    1 + Real.log (|t| + 3) ≤ 5 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hu : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h₁ : Real.log (|t| + 3) ≤ Real.log 3 + Real.log (1 + |t|) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  have h₂ : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have h₃ : Real.log (1 + |t|) ≤ (1 + |t|) ^ (1 / 2 : ℝ) / (1 / 2) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h₄ : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow hu (by norm_num)
  linarith

/-- A horizontal segment integral is at most the length times a pointwise bound. -/
lemma norm_hIntegral_le {F : ℂ → ℂ} {a b y C : ℝ} (hab : a ≤ b)
    (hF : ∀ σ ∈ Set.Icc a b, ‖F (σ + y * I)‖ ≤ C) : ‖HIntegral F a b y‖ ≤ C * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
    (f := fun σ : ℝ ↦ F (σ + y * I)) fun σ hσ ↦ by
      rw [Set.uIoc_of_le hab] at hσ
      exact hF σ (Set.Ioc_subset_Icc_self hσ)
  rwa [abs_of_nonneg (by linarith)] at h

/-- A vertical segment integral is at most `c ∫ (1 + |t|)^{-3/2} dt` when the integrand is
dominated by `c (1 + |t|)^{-3/2}`. -/
lemma norm_vIntegral_le {F : ℂ → ℂ} {σ T c : ℝ} (hT : 0 ≤ T)
    (hF : ∀ t : ℝ, ‖F (σ + t * I)‖ ≤ c * (1 + |t|) ^ (-(3 / 2) : ℝ)) :
    ‖VIntegral F σ (-T) T‖ ≤ c * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  have hint : MeasureTheory.Integrable fun t : ℝ ↦ c * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
    have h := integrable_one_add_norm (E := ℝ) (μ := MeasureTheory.volume) (r := 3 / 2)
      (by simp; norm_num)
    simpa [Real.norm_eq_abs] using h.const_mul c
  have hc : 0 ≤ c := by simpa using (norm_nonneg _).trans (hF 0)
  rw [VIntegral, norm_smul, norm_I, one_mul, ← MeasureTheory.integral_const_mul]
  calc ‖∫ t in -T..T, F (σ + t * I)‖
      ≤ ∫ t in -T..T, c * (1 + |t|) ^ (-(3 / 2) : ℝ) :=
        intervalIntegral.norm_integral_le_of_norm_le (by linarith)
          (Filter.Eventually.of_forall fun t _ ↦ hF t) hint.intervalIntegrable
    _ ≤ ∫ t, c * (1 + |t|) ^ (-(3 / 2) : ℝ) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun t ↦ by positivity)

end Edges

/-! ### Logarithmic derivatives near `s = 1` -/

section NearOne

open Complex DirichletCharacter Metric

open scoped LSeries.notation

/-- **Borel–Carathéodory near `s = 1`.** If `g` is entire and zero-free on `re s > 7/8`,
at most `M` on `29/32 < re s < 4`, `|im s| < 3`, and at least `1/2` on `re s = 2`,
`|im s| ≤ 1`, then `‖g'/g‖ ≤ 8832 log (2M)` on `15/16 ≤ re s ≤ 2`, `|im s| ≤ 1`. -/
lemma norm_logDeriv_le_of_near_one {g : ℂ → ℂ} {M : ℝ} (hg : Differentiable ℂ g)
    (hg₀ : ∀ w : ℂ, 7 / 8 < w.re → g w ≠ 0)
    (hM : ∀ w : ℂ, 29 / 32 < w.re → w.re < 4 → |w.im| < 3 → ‖g w‖ ≤ M)
    (hm : ∀ t : ℝ, |t| ≤ 1 → 1 / 2 ≤ ‖g (2 + t * I)‖) {z : ℂ} (hz₁ : 15 / 16 ≤ z.re)
    (hz₂ : z.re ≤ 2) (hz : |z.im| ≤ 1) :
    ‖deriv g z / g z‖ ≤ 8832 * Real.log (2 * M) := by
  set c : ℂ := 2 + z.im * I
  -- the ball `ball c (35/32)` lies where `g` is bounded and zero-free
  have hball : ∀ w ∈ ball c (35 / 32), 29 / 32 < w.re ∧ w.re < 4 ∧ |w.im| < 3 := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h₁ := (abs_re_le_norm (w - c)).trans_lt hw
    have h₂ := (abs_im_le_norm (w - c)).trans_lt hw
    simp only [c, sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, sub_im, add_im,
      mul_im] at h₁ h₂
    norm_num at h₁ h₂
    obtain ⟨h₁, h₁'⟩ := abs_lt.mp h₁
    obtain ⟨h₂, h₂'⟩ := abs_lt.mp h₂
    obtain ⟨h₃, h₃'⟩ := abs_le.mp hz
    exact ⟨by linarith, by linarith, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  have hcb : c ∈ ball c (35 / 32) := mem_ball_self (by norm_num)
  have hgc : 1 / 2 ≤ ‖g c‖ := hm z.im hz
  have hgc₀ : g c ≠ 0 := norm_pos_iff.mp (by linarith)
  have hMc : ‖g c‖ ≤ M := by
    obtain ⟨h₁, h₂, h₃⟩ := hball c hcb
    exact hM c h₁ h₂ h₃
  -- a holomorphic logarithm of `g / g c` on the ball
  obtain ⟨h, hh, he, hh₀⟩ := exists_holomorphic_log (c := c) (R := 35 / 32) (by norm_num)
    (hg.differentiableOn.div_const (g c))
    (fun w hw ↦ div_ne_zero (hg₀ w (by linarith [(hball w hw).1])) hgc₀) (div_self hgc₀)
  set B := Real.log M - Real.log ‖g c‖ with hB
  have hB₀ : 0 ≤ B := sub_nonneg.mpr (Real.log_le_log (by linarith) hMc)
  have hre : ∀ w ∈ ball c (35 / 32), (h w).re ≤ B := by
    intro w hw
    obtain ⟨h₁, h₂, h₃⟩ := hball w hw
    have hgw : g w ≠ 0 := hg₀ w (by linarith)
    have hew : Complex.exp (h w) = g w / g c := he hw
    have hlog : (h w).re = Real.log ‖g w‖ - Real.log ‖g c‖ := by
      rw [← Real.log_exp (h w).re, ← Complex.norm_exp, hew, norm_div,
        Real.log_div (norm_ne_zero_iff.mpr hgw) (norm_ne_zero_iff.mpr hgc₀)]
    rw [hlog, hB]
    gcongr
    exact hM w h₁ h₂ h₃
  -- `z` lies in `closedBall c (17/16)`
  have hzc : z ∈ closedBall c (17 / 16) := by
    rw [mem_closedBall, dist_eq_norm]
    have hzc' : z - c = ((z.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [hzc', norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hzb : z ∈ ball c (35 / 32) := closedBall_subset_ball (by norm_num) hzc
  -- the derivative of the logarithm is `g' / g`
  have hderiv : deriv h z = deriv g z / g z := by
    have hhz : DifferentiableAt ℂ h z := hh.differentiableAt (isOpen_ball.mem_nhds hzb)
    have hev : (fun w ↦ Complex.exp (h w)) =ᶠ[nhds z] fun w ↦ g w / g c :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hzb) fun w hw ↦ he hw
    have h₁ := hev.deriv_eq
    have hez : Complex.exp (h z) = g z / g c := he hzb
    rw [deriv_cexp hhz, deriv_div_const, hez] at h₁
    have hgz : g z ≠ 0 := hg₀ z (by linarith)
    field_simp at h₁ ⊢
    linear_combination h₁
  rw [← hderiv]
  refine (norm_deriv_le_of_re_le (by norm_num) (by norm_num) hB₀ hh hh₀ hre hzc).trans ?_
  have hM₀ : 0 < M := by linarith
  have hlog2 : B ≤ Real.log (2 * M) := by
    rw [Real.log_mul (by norm_num) hM₀.ne', hB]
    have : Real.log (1 / 2) ≤ Real.log ‖g c‖ := Real.log_le_log (by norm_num) hgc
    rw [one_div, Real.log_inv] at this
    linarith
  norm_num
  linarith

/-- The entire function `(s - 1) ζ(s)`, with its value `1` at `s = 1`. -/
noncomputable def zetaReg : ℂ → ℂ :=
  Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1

/-- `(s - 1) ζ(s)` is entire. -/
lemma differentiable_zetaReg : Differentiable ℂ zetaReg := by
  have hne : ∀ w : ℂ, w ≠ 1 → DifferentiableAt ℂ zetaReg w := by
    intro w hw
    have hev : zetaReg =ᶠ[nhds w] fun s ↦ (s - 1) * riemannZeta s := by
      filter_upwards [eventually_ne_nhds hw] with v hv
      simp [zetaReg, Function.update_of_ne hv]
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hw)).congr_of_eventuallyEq hev
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact hne s hs
  refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
  · filter_upwards [self_mem_nhdsWithin] with w hw using hne w hw
  · simpa only [zetaReg, continuousAt_update_same] using riemannZeta_residue_one

/-- The entire function `(s - 1) L(s, χ₀)` for the principal character `χ₀` mod `k`. -/
noncomputable def trivReg (k : ℕ) : ℂ → ℂ :=
  fun s ↦ (∏ p ∈ k.primeFactors, (1 - (p : ℂ) ^ (-s))) * zetaReg s

/-- Away from `s = 1`, `trivReg k s = (s - 1) L(s, χ₀)`. -/
lemma trivReg_eq {k : ℕ} [NeZero k] {s : ℂ} (hs : s ≠ 1) :
    trivReg k s = (s - 1) * LFunction (1 : DirichletCharacter ℂ k) s := by
  have h := LFunctionTrivChar_eq_mul_riemannZeta (N := k) hs
  simp only [LFunctionTrivChar] at h
  rw [trivReg, zetaReg, Function.update_of_ne hs, h]
  ring

/-- `(s - 1) L(s, χ₀)` is entire. -/
lemma differentiable_trivReg (k : ℕ) : Differentiable ℂ (trivReg k) := by
  intro s
  refine DifferentiableAt.mul (DifferentiableAt.fun_finsetProd fun p hp ↦ ?_)
    (differentiable_zetaReg s)
  have hp₀ : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hp₀)
    |>.const_sub 1

/-- On `re s ≥ 0`, the Euler factors at the primes dividing `k` have product at most `k`. -/
lemma norm_prod_one_sub_le {k : ℕ} [NeZero k] {s : ℂ} (hs : 0 ≤ s.re) :
    ‖∏ p ∈ k.primeFactors, (1 - (p : ℂ) ^ (-s))‖ ≤ k := by
  rw [norm_prod]
  calc ∏ p ∈ k.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖
      ≤ ∏ p ∈ k.primeFactors, (p : ℝ) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun p hp ↦ ?_
        have hp := Nat.prime_of_mem_primeFactors hp
        have hp₂ : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_natCast_cpow_of_pos hp.pos]
        have : (p : ℝ) ^ (-s).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simpa using hs)
        linarith
    _ ≤ k := by
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd (NeZero.pos k) (Nat.prod_primeFactors_dvd k)

/-- `(s - 1) L(s, χ₀)` has no zeros on `re s > 7/8`. -/
lemma trivReg_ne_zero {k : ℕ} [NeZero k] {s : ℂ} (hs : 7 / 8 < s.re) : trivReg k s ≠ 0 := by
  rcases ne_or_eq s 1 with h | rfl
  · rw [trivReg_eq h]
    exact mul_ne_zero (sub_ne_zero.mpr h)
      (LFunction_ne_zero_of_seven_eighths_lt_re 1 hs fun h' ↦ h h'.2)
  · rw [trivReg, zetaReg, Function.update_self, mul_one]
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
    have hp := Nat.prime_of_mem_primeFactors hp
    rw [cpow_neg_one, sub_ne_zero]
    intro h
    have : (1 : ℂ) = p := by simpa using congrArg (·⁻¹) h
    exact hp.one_lt.ne (by exact_mod_cast this)

/-- Away from `s = 1`, `L'/L(s, χ₀) = g'/g(s) - 1/(s - 1)` for `g = trivReg k`. -/
lemma logDeriv_LFunction_one_eq {k : ℕ} [NeZero k] {s : ℂ} (hs : s ≠ 1)
    (hL : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0) :
    deriv (LFunction (1 : DirichletCharacter ℂ k)) s / LFunction (1 : DirichletCharacter ℂ k) s =
      deriv (trivReg k) s / trivReg k s - 1 / (s - 1) := by
  have hev : trivReg k =ᶠ[nhds s] fun w ↦ (w - 1) * LFunction (1 : DirichletCharacter ℂ k) w := by
    filter_upwards [eventually_ne_nhds hs] with w hw using trivReg_eq hw
  have hd : HasDerivAt (fun w ↦ (w - 1) * LFunction (1 : DirichletCharacter ℂ k) w)
      (1 * LFunction (1 : DirichletCharacter ℂ k) s +
        (s - 1) * deriv (LFunction (1 : DirichletCharacter ℂ k)) s) s :=
    ((hasDerivAt_id s).sub_const 1).mul
      (differentiableAt_LFunction 1 s (Or.inl hs)).hasDerivAt
  rw [hev.deriv_eq, hd.deriv, trivReg_eq hs]
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-- `log (k (|t| + 3)) ≤ 6 k (1 + |t|)^{1/2}`. -/
lemma log_mul_le_mul_rpow {k : ℝ} (hk : 1 ≤ k) (t : ℝ) :
    Real.log (k * (|t| + 3)) ≤ 6 * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have h₁ := one_add_log_le_rpow t
  have h₂ : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h₃ : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg t])
    (by norm_num)
  rw [Real.log_mul (by linarith) (by linarith [abs_nonneg t])]
  nlinarith

/-- On the line `re s = 15/16`, `‖L'/L(s, χ)‖ ≤ A k (1 + |t|)^{1/2}`. -/
theorem exists_norm_logDeriv_le_left : ∃ A : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (t : ℝ),
    ‖deriv (LFunction χ) (15 / 16 + t * I) / LFunction χ (15 / 16 + t * I)‖ ≤
      A * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := norm_logDeriv_LFunction_le
  obtain ⟨C₂, hC₂⟩ := norm_LFunction_le_poly
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_zetaReg.continuous.continuousOn
  set A₁ := 8832 * 2 * (36 * |C₂| + |M₀| + 1) + 16
  refine ⟨6 * |C₁| + 8832 * 16 + A₁, fun k _ χ t ↦ ?_⟩
  set s : ℂ := 15 / 16 + t * I
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hr : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg t])
    (by norm_num)
  have hre : s.re = 15 / 16 := by simp [s]
  have him : s.im = t := by simp [s]
  have hA₁ : 0 ≤ A₁ := by positivity
  by_cases hfar : 1 ≤ ‖s - 1‖
  · -- away from `s = 1`, use the logarithmic bound
    have h := hC₁ k χ s (by rw [hre]) (by rw [hre]; norm_num) hfar
    rw [him] at h
    have hlog := log_mul_le_mul_rpow hk t
    have hlog₀ : 0 ≤ Real.log (k * (|t| + 3)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t])
    calc _ ≤ C₁ * Real.log (k * (|t| + 3)) := h
      _ ≤ |C₁| * (6 * k * (1 + |t|) ^ (1 / 2 : ℝ)) :=
          mul_le_mul (le_abs_self _) hlog hlog₀ (abs_nonneg _)
      _ ≤ (6 * |C₁| + 8832 * 16 + A₁) * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
          have : 0 ≤ (8832 * 16 + A₁) * k * (1 + |t|) ^ (1 / 2 : ℝ) := by positivity
          nlinarith
  -- near `s = 1`, use Borel–Carathéodory
  have ht : |t| ≤ 1 := by
    have := abs_im_le_norm (s - 1)
    rw [sub_im, him, one_im, sub_zero] at this
    linarith
  have hs₁ : s ≠ 1 := fun h ↦ by rw [h, one_re] at hre; norm_num at hre
  have hz₁ : 15 / 16 ≤ s.re := hre.ge
  have hz₂ : s.re ≤ 2 := by rw [hre]; norm_num
  have hz : |s.im| ≤ 1 := by rwa [him]
  suffices hnear : ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ (8832 * 16 + A₁) * k by
    calc _ ≤ (8832 * 16 + A₁) * k := hnear
      _ ≤ (6 * |C₁| + 8832 * 16 + A₁) * k * (1 + |t|) ^ (1 / 2 : ℝ) := by
          have : 0 ≤ (8832 * 16 + A₁) * k := by positivity
          have : 0 ≤ 6 * |C₁| * k := by positivity
          nlinarith
  by_cases hχ : χ = 1
  · subst hχ
    -- `g = (s - 1) L(s, χ₀)`
    have hM : ∀ w : ℂ, 29 / 32 < w.re → w.re < 4 → |w.im| < 3 →
        ‖trivReg k w‖ ≤ (36 * |C₂| + |M₀| + 1) * k := by
      intro w h₁ h₂ h₃
      by_cases hw : ‖w - 1‖ ≤ 1
      · rw [trivReg, norm_mul]
        have hP := norm_prod_one_sub_le (k := k) (s := w) (by linarith)
        have hZ := (hM₀ w (by rwa [mem_closedBall, dist_eq_norm])).trans (le_abs_self M₀)
        calc _ ≤ (k : ℝ) * |M₀| := mul_le_mul hP hZ (norm_nonneg _) (by positivity)
          _ ≤ (36 * |C₂| + |M₀| + 1) * k := by nlinarith [abs_nonneg C₂]
      · have hw₁ : w ≠ 1 := fun h ↦ hw (by simp [h])
        rw [trivReg_eq hw₁, norm_mul]
        have hL := hC₂ k 1 w (by linarith) (by linarith)
        have hn : ‖w - 1‖ ≤ 6 := by
          refine (norm_le_abs_re_add_abs_im _).trans ?_
          rw [sub_re, one_re, sub_im, one_im, sub_zero]
          have := abs_lt.mpr (⟨by linarith, by linarith⟩ : -3 < w.re - 1 ∧ w.re - 1 < 3)
          linarith
        have hL' : ‖LFunction (1 : DirichletCharacter ℂ k) w‖ ≤ |C₂| * k * 6 := by
          refine hL.trans ?_
          have : C₂ * k ≤ |C₂| * k := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          have : 0 ≤ |C₂| * k := by positivity
          nlinarith [abs_nonneg w.im]
        calc _ ≤ 6 * (|C₂| * k * 6) := mul_le_mul hn hL' (norm_nonneg _) (by norm_num)
          _ ≤ (36 * |C₂| + |M₀| + 1) * k := by nlinarith [abs_nonneg M₀, abs_nonneg C₂]
    have hm : ∀ t : ℝ, |t| ≤ 1 → 1 / 2 ≤ ‖trivReg k (2 + t * I)‖ := by
      intro t _
      have hne : (2 + t * I : ℂ) ≠ 1 := fun h ↦ by simpa using congrArg re h
      rw [trivReg_eq hne, norm_mul]
      have h₁ : 1 ≤ ‖(2 + t * I : ℂ) - 1‖ := by
        have := re_le_norm ((2 + t * I : ℂ) - 1)
        simp only [sub_re, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, one_re] at this
        norm_num at this
        linarith
      have h₂ := le_norm_LFunction (1 : DirichletCharacter ℂ k) (s := 2 + t * I) (by simp)
      have hre₂ : (2 + t * I : ℂ).re = 2 := by simp
      rw [hre₂] at h₂
      norm_num at h₂
      nlinarith
    have hB := norm_logDeriv_le_of_near_one (differentiable_trivReg k)
      (fun w hw ↦ trivReg_ne_zero hw) hM hm hz₁ hz₂ hz
    have hL₀ : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0 :=
      LFunction_ne_zero_of_seven_eighths_lt_re 1 (by rw [hre]; norm_num) fun h ↦ hs₁ h.2
    rw [logDeriv_LFunction_one_eq hs₁ hL₀]
    have hinv : ‖1 / (s - 1)‖ ≤ 16 := by
      have h₁ : 1 / 16 ≤ ‖s - 1‖ := by
        have := abs_re_le_norm (s - 1)
        rw [sub_re, hre, one_re] at this
        norm_num at this
        linarith
      rw [norm_div, norm_one]
      exact (div_le_iff₀ (by linarith)).mpr (by linarith)
    have hlog : Real.log (2 * ((36 * |C₂| + |M₀| + 1) * k)) ≤ 2 * ((36 * |C₂| + |M₀| + 1) * k) :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    calc _ ≤ ‖deriv (trivReg k) s / trivReg k s‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
      _ ≤ 8832 * (2 * ((36 * |C₂| + |M₀| + 1) * k)) + 16 := by linarith
      _ ≤ (8832 * 16 + A₁) * k := by
          have : (16 : ℝ) ≤ 16 * k := by linarith
          simp only [A₁]
          nlinarith
  · -- `g = L(s, χ)` is entire
    have hM : ∀ w : ℂ, 29 / 32 < w.re → w.re < 4 → |w.im| < 3 →
        ‖LFunction χ w‖ ≤ 8 * k := by
      intro w h₁ h₂ h₃
      refine (norm_LFunction_le_of_ne_one hχ (by linarith)).trans ?_
      rw [div_le_iff₀ (by linarith)]
      have hn : ‖w‖ ≤ 7 := by
        refine (norm_le_abs_re_add_abs_im _).trans ?_
        rw [abs_of_pos (by linarith)]
        linarith
      nlinarith
    have hm : ∀ t : ℝ, |t| ≤ 1 → 1 / 2 ≤ ‖LFunction χ (2 + t * I)‖ := by
      intro t _
      have h₂ := le_norm_LFunction χ (s := 2 + t * I) (by simp)
      have hre₂ : (2 + t * I : ℂ).re = 2 := by simp
      rw [hre₂] at h₂
      norm_num at h₂
      linarith
    have hB := norm_logDeriv_le_of_near_one (differentiable_LFunction hχ)
      (fun w hw ↦ LFunction_ne_zero_of_seven_eighths_lt_re χ hw fun h ↦ hχ h.1) hM hm hz₁ hz₂ hz
    have hlog : Real.log (2 * (8 * k)) ≤ 2 * (8 * k) :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    calc _ ≤ 8832 * Real.log (2 * (8 * k)) := hB
      _ ≤ 8832 * (2 * (8 * k)) := by linarith
      _ ≤ (8832 * 16 + A₁) * k := by nlinarith

end NearOne

/-! ### The smoothed sum -/

section Smoothed

open Complex ArithmeticFunction DirichletCharacter

/-- The rectangle integral recovers the right edge from the other three. -/
lemma vIntegral_eq_rectangleIntegral (F : ℂ → ℂ) (U : ℝ) :
    VIntegral F 2 (-U) U = RectangleIntegral F (15 / 16 - U * I) (2 + U * I) -
      HIntegral F (15 / 16) 2 (-U) + HIntegral F (15 / 16) 2 U +
        VIntegral F (15 / 16) (-U) U := by
  simp only [RectangleIntegral, sub_re, add_re, sub_im, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im]
  norm_num
  abel

/-- The kernel `x^s / (s (s + 1))` is holomorphic on `re s > 0`. -/
lemma differentiableOn_kernel {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (fun s : ℂ ↦ (x : ℂ) ^ s / (s * (s + 1))) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs₀ : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hs₁ : s + 1 ≠ 0 := fun h ↦ by
    have := congrArg re h
    simp at this hs
    linarith
  have h₁ : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) s :=
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl (ofReal_ne_zero.mpr hx.ne'))
  have h₂ : DifferentiableAt ℂ (fun s : ℂ ↦ s * (s + 1)) s := by fun_prop
  exact (h₁.div h₂ (mul_ne_zero hs₀ hs₁)).differentiableWithinAt

/-- The rectangle `[15/16, 2] × [-U, U]` lies in the zero-free half-plane `re s > 7/8`. -/
lemma rectangle_subset_re_gt (U : ℝ) :
    Rectangle (15 / 16 - U * I) (2 + U * I) ⊆ {s : ℂ | 7 / 8 < s.re} := by
  intro s hs
  rw [Rectangle, mem_reProdIm] at hs
  have h := hs.1
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h
  norm_num [Set.uIcc_of_le] at h
  exact lt_of_lt_of_le (by norm_num) h.1

/-- Across the rectangle `[15/16, 2] × [-U, U]`, the Perron integrand picks up only the
residue `x / 2` of the principal character at `s = 1`. -/
theorem rectangleIntegral_perronIntegrand {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {x : ℝ} (hx : 0 < x) {U : ℝ} (hU : 0 < U) :
    RectangleIntegral (perronIntegrand χ x) (15 / 16 - U * I) (2 + U * I) =
      if χ = 1 then 2 * Real.pi * I * (x / 2) else 0 := by
  set K : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  have hKd := differentiableOn_kernel hx
  have hKΩ : ∀ s : ℂ, 7 / 8 < s.re → DifferentiableAt ℂ K s := fun s hs ↦
    hKd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
      (show (0 : ℝ) < s.re by linarith))
  split_ifs with hχ
  · subst hχ
    set g := trivReg k
    have hg := differentiable_trivReg k
    set H : ℂ → ℂ := fun s ↦ -(deriv g s / g s) * K s + dslope K 1 s
    have hre : (15 / 16 - U * I : ℂ).re ≤ (2 + U * I : ℂ).re := by simp; norm_num
    have him : (15 / 16 - U * I : ℂ).im ≤ (2 + U * I : ℂ).im := by simp; linarith
    have hnhds : Rectangle (15 / 16 - U * I) (2 + U * I) ∈ nhds (1 : ℂ) := by
      rw [rectangle_mem_nhds_iff, mem_reProdIm, Set.uIoo_of_le hre, Set.uIoo_of_le him]
      simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, sub_im, add_im,
        mul_im, one_re, one_im]
      norm_num
      exact hU
    have hH : HolomorphicOn H (Rectangle (15 / 16 - U * I) (2 + U * I)) := by
      intro s hs
      have hs' : 7 / 8 < s.re := rectangle_subset_re_gt U hs
      have hdg : DifferentiableAt ℂ (deriv g) s := ((hg.analyticAt s).deriv).differentiableAt
      have hslope : DifferentiableAt ℂ (dslope K 1) s := by
        have h₁ : {s : ℂ | 0 < s.re} ∈ nhds (1 : ℂ) :=
          (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
        exact ((differentiableOn_dslope h₁).mpr hKd).differentiableAt
          ((isOpen_lt continuous_const continuous_re).mem_nhds
            (show (0 : ℝ) < s.re by linarith))
      exact (((hdg.div (hg s) (trivReg_ne_zero hs')).neg.mul (hKΩ s hs')).add
        hslope).differentiableWithinAt
    have hpart : Set.EqOn (perronIntegrand (1 : DirichletCharacter ℂ k) x - fun s ↦ K 1 / (s - 1)) H
        (Rectangle (15 / 16 - U * I) (2 + U * I) \ {1}) := by
      intro s ⟨hs, hs₁⟩
      have hs' : 7 / 8 < s.re := rectangle_subset_re_gt U hs
      have hs₁' : s ≠ 1 := hs₁
      have hL : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0 :=
        LFunction_ne_zero_of_seven_eighths_lt_re 1 hs' fun h ↦ hs₁' h.2
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁'
      simp only [Pi.sub_apply, perronIntegrand, H, logDeriv_LFunction_one_eq hs₁' hL,
        dslope_of_ne _ hs₁', slope_def_field]
      change -(deriv g s / g s - 1 / (s - 1)) * K s - K 1 / (s - 1) = _
      field_simp
      ring
    have h := ResidueTheoremOnRectangleWithSimplePole hre him hnhds hH hpart
    rw [RectangleIntegral', smul_eq_mul] at h
    have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hK1 : K 1 = x / 2 := by simp [K]; ring
    rw [← hK1, ← h]
    field_simp
  · have hF : HolomorphicOn (perronIntegrand χ x) {s : ℂ | 7 / 8 < s.re} := by
      intro s hs
      have hs' : 7 / 8 < s.re := hs
      have hLd := differentiable_LFunction hχ
      have hdL : DifferentiableAt ℂ (deriv (LFunction χ)) s :=
        ((hLd.analyticAt s).deriv).differentiableAt
      have hL : LFunction χ s ≠ 0 :=
        LFunction_ne_zero_of_seven_eighths_lt_re χ hs' fun h ↦ hχ h.1
      exact ((hdL.div (hLd s) hL).neg.mul (hKΩ s hs')).differentiableWithinAt
    exact hF.vanishesOnRectangle (rectangle_subset_re_gt U)

/-- The smoothed twisted prime sum:
`∑_{m ≤ x} Λ(m) χ(m) (1 - m / x) = [χ = 1] x / 2 + O(k x^{15/16})`. -/
theorem exists_norm_smoothed_sub_le : ∃ B : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (x : ℝ), 2 ≤ x → (∀ m : ℕ, (m : ℝ) ≠ x) →
      ‖∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x) -
          (if χ = 1 then (x : ℂ) / 2 else 0)‖ ≤ B * k * x ^ (15 / 16 : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_verticalIntegral_sub_le
  obtain ⟨C₂, hC₂⟩ := norm_logDeriv_LFunction_le
  obtain ⟨A, hA⟩ := exists_norm_logDeriv_le_left
  set I₀ := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)
  have hI₀ : 0 ≤ I₀ := MeasureTheory.integral_nonneg fun t ↦ by positivity
  refine ⟨|C₁| + 12 * |C₂| + 64 * |A| * I₀, ?_⟩
  intro k _ χ x hx hxN
  set U := x ^ 2 with hUdef
  set L := LFunction χ
  set F := perronIntegrand χ x
  set Kx : ℂ → ℂ := fun s ↦ (x : ℂ) ^ s / (s * (s + 1))
  set S := ∑ m ∈ Finset.Icc 1 ⌊x⌋₊, (Λ m : ℂ) * χ m * (1 - m / x)
  set P : ℂ := if χ = 1 then (x : ℂ) / 2 else 0
  have hx₀ : 0 < x := by linarith
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hU : 4 ≤ U := by nlinarith
  have hnormF : ∀ s, ‖F s‖ = ‖deriv L s / L s‖ * ‖Kx s‖ := fun s ↦ by
    simp only [F, perronIntegrand, norm_mul, norm_neg, L, Kx]
  -- the rectangle picks up the residue
  have hR : RectangleIntegral F (15 / 16 - U * I) (2 + U * I) = 2 * Real.pi * I * P := by
    rw [rectangleIntegral_perronIntegrand χ hx₀ (by linarith)]
    split_ifs <;> simp [P, *]
  -- the horizontal edges at height `±U`
  have hH : ∀ τ ∈ ({U, -U} : Set ℝ), ‖HIntegral F (15 / 16) 2 τ‖ ≤ 6 * |C₂| * k := by
    intro τ hτ
    have hτ₂ : |τ| = U := by
      rcases hτ with rfl | rfl
      · exact abs_of_pos (by linarith)
      · rw [abs_neg]; exact abs_of_pos (by linarith)
    have hlog : Real.log (k * (U + 3)) ≤ 3 * k * U := by
      rw [Real.log_mul (by linarith) (by linarith)]
      have h₁ : Real.log k ≤ k := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      have h₂ : Real.log (U + 3) ≤ U + 2 :=
        (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      nlinarith
    have hpt : ∀ σ ∈ Set.Icc (15 / 16 : ℝ) 2, ‖F (σ + τ * I)‖ ≤ 3 * |C₂| * k := by
      intro σ hσ
      have hre : (σ + τ * I : ℂ).re = σ := by simp
      have him : (σ + τ * I : ℂ).im = τ := by simp
      have hfar : 1 ≤ ‖(σ + τ * I : ℂ) - 1‖ := by
        have := abs_im_le_norm ((σ + τ * I : ℂ) - 1)
        rw [sub_im, him, one_im, sub_zero, hτ₂] at this
        linarith
      have h₁ := hC₂ k χ (σ + τ * I) (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2) hfar
      rw [him, hτ₂] at h₁
      have h₂ : ‖Kx (σ + τ * I)‖ ≤ 1 / U := by
        have h := norm_cpow_div_le_of_im_ne_zero hx₀ (s := σ + τ * I)
          (by rw [him]; intro h; rw [h, abs_zero] at hτ₂; linarith)
        rw [hre, him] at h
        have hxσ : x ^ σ ≤ x ^ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hσ.2
          rwa [Real.rpow_two] at this
        refine h.trans ?_
        rw [← sq_abs τ, hτ₂, hUdef, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hlog₀ : 0 ≤ Real.log (k * (U + 3)) := Real.log_nonneg (by nlinarith)
      rw [hnormF]
      calc ‖deriv L (σ + τ * I) / L (σ + τ * I)‖ * ‖Kx (σ + τ * I)‖
          ≤ (|C₂| * (3 * k * U)) * (1 / U) := by
            refine mul_le_mul (h₁.trans ?_) h₂ (norm_nonneg _) (by positivity)
            exact mul_le_mul (le_abs_self _) hlog hlog₀ (abs_nonneg _)
        _ = 3 * |C₂| * k := by field_simp
    refine (norm_hIntegral_le (by norm_num) hpt).trans ?_
    have : 0 ≤ |C₂| * k := by positivity
    nlinarith
  -- the left edge `re s = 15/16`
  have hV : ‖VIntegral F (15 / 16) (-U) U‖ ≤ 64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀ := by
    refine norm_vIntegral_le (by linarith) fun t ↦ ?_
    have hs : (((15 / 16 : ℝ) : ℂ) + t * I) = 15 / 16 + t * I := by push_cast; ring
    have h₁ := (hA k χ t).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)) (by positivity))
    have hre : (15 / 16 + t * I : ℂ).re = 15 / 16 := by simp
    have him : (15 / 16 + t * I : ℂ).im = t := by simp
    have h₂ := norm_cpow_div_le hx₀ (s := 15 / 16 + t * I) (by rw [hre]; norm_num)
    rw [hre, him] at h₂
    have hu : 0 < 1 + |t| := by positivity
    have h₃ : (1 + |t|) ^ (-(3 / 2) : ℝ) = (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2 := by
      rw [show (-(3 / 2) : ℝ) = 1 / 2 - (2 : ℕ) by norm_num, Real.rpow_sub hu,
        Real.rpow_natCast]
    rw [hs, hnormF, h₃]
    calc ‖deriv L (15 / 16 + t * I) / L (15 / 16 + t * I)‖ * ‖Kx (15 / 16 + t * I)‖
        ≤ (|A| * k * (1 + |t|) ^ (1 / 2 : ℝ)) * (64 * x ^ (15 / 16 : ℝ) / (1 + |t|) ^ 2) :=
          mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)
      _ = 64 * |A| * k * x ^ (15 / 16 : ℝ) * ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ 2) := by
          ring
  -- truncating the vertical integral at height `U`
  have hC : ‖VerticalIntegral F 2 - VIntegral F 2 (-U) U‖ ≤ |C₁| := by
    refine (hC₁ χ (by linarith) (by linarith)).trans ?_
    rw [← hUdef, mul_div_assoc, div_self (by positivity), mul_one]
    exact le_abs_self _
  -- assembling the pieces
  have hS : VerticalIntegral F 2 = 2 * Real.pi * I * S :=
    verticalIntegral_perronIntegrand χ (by linarith) hxN
  have hsplit : 2 * Real.pi * I * (S - P) = (VerticalIntegral F 2 - VIntegral F 2 (-U) U) +
      (-HIntegral F (15 / 16) 2 (-U) + HIntegral F (15 / 16) 2 U +
        VIntegral F (15 / 16) (-U) U) := by
    rw [vIntegral_eq_rectangleIntegral, hR, hS]
    ring
  have hnorm : ‖2 * Real.pi * I * (S - P)‖ = 2 * Real.pi * ‖S - P‖ := by
    simp [abs_of_pos Real.pi_pos]
  have hle : ‖2 * Real.pi * I * (S - P)‖ ≤
      |C₁| + (6 * |C₂| * k + 6 * |C₂| * k + 64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add hC ?_)
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ?_ (hH U (by simp)))) hV)
    rw [norm_neg]
    exact hH (-U) (by simp)
  have hxr : 1 ≤ x ^ (15 / 16 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have h₄ : ‖S - P‖ ≤ 2 * Real.pi * ‖S - P‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (by linarith [Real.two_le_pi])
  have h₅ : |C₁| ≤ |C₁| * k * x ^ (15 / 16 : ℝ) := by
    have : 1 ≤ k * x ^ (15 / 16 : ℝ) := one_le_mul_of_one_le_of_one_le hk hxr
    nlinarith [abs_nonneg C₁]
  have h₆ : 12 * |C₂| * k ≤ 12 * |C₂| * k * x ^ (15 / 16 : ℝ) := by
    have : 0 ≤ 12 * |C₂| * k := by positivity
    nlinarith
  have h₇ : (|C₁| + 12 * |C₂| + 64 * |A| * I₀) * k * x ^ (15 / 16 : ℝ) =
      |C₁| * k * x ^ (15 / 16 : ℝ) + 12 * |C₂| * k * x ^ (15 / 16 : ℝ) +
        64 * |A| * k * x ^ (15 / 16 : ℝ) * I₀ := by ring
  rw [h₇]
  linarith

end Smoothed

/-! ### Removing the smoothing -/

section Unsmoothing

open Complex

/-- Differencing the weighted sums `W(z) = ∑_{n ≤ z} a(n) (z - n)` over a step `h` recovers
`h ∑_{n ≤ x} a(n)` up to `h² log (x + h)`, when `‖a(n)‖ ≤ log n`. -/
lemma norm_sum_sub_sum_sub_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Real.log n) {x : ℝ}
    (hx : 0 ≤ x) (h : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n) -
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n) -
          h * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ h ^ 2 * Real.log (x + h) := by
  have hI : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := fun n ↦ by ext; simp; omega
  have hmx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hxm : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  rw [Nat.floor_add_natCast hx, hI, hI]
  generalize ⌊x⌋₊ = m at hmx hxm ⊢
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) (Nat.le_add_right m h)]
  -- the sums over `n ≤ x` cancel
  have hcancel : ∑ n ∈ Finset.Ioc 0 m, a n * (((x + h : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Ioc 0 m, a n * ((x : ℂ) - n) - h * ∑ n ∈ Finset.Ioc 0 m, a n = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    push_cast
    ring
  rw [show ∀ A B C D : ℂ, A + B - C - D = (A - C - D) + B by intros; ring, hcancel, zero_add]
  -- each new term is at most `h log (x + h)`
  have hterm : ∀ n ∈ Finset.Ioc m (m + h),
      ‖a n * (((x + h : ℝ) : ℂ) - n)‖ ≤ h * Real.log (x + h) := by
    intro n hn
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Ioc.mp hn
    have hn₁' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hn₁
    have hn₂' : (n : ℝ) ≤ m + h := by exact_mod_cast hn₂
    have hn₀ : (0 : ℝ) < n := by linarith
    rw [norm_mul, mul_comm]
    have h₁ : ‖((x + h : ℝ) : ℂ) - n‖ ≤ h := by
      rw [show ((x + h : ℝ) : ℂ) - n = ((x + h - n : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have h₂ : ‖a n‖ ≤ Real.log (x + h) :=
      (ha n).trans (Real.log_le_log hn₀ (by linarith))
    exact mul_le_mul h₁ h₂ (norm_nonneg _) (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, Nat.card_Ioc, Nat.add_sub_cancel_left, nsmul_eq_mul]
  exact le_of_eq (by ring)

end Unsmoothing

end PNT

open Complex PNT

/-- The prime number theorem in progressions with a power saving (AC0):
`∑_{n ≤ y} Λ(n) χ(n) = [χ = 1] y + O(k^C y^{1-c})`. -/
theorem sum_vonMangoldt_mul_char_sub_le : ∃ c > (0 : ℝ), ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
    ‖∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
        (if χ = 1 then (y : ℂ) else 0)‖ ≤ C * (k : ℝ) ^ C * y ^ (1 - c) := by
  obtain ⟨B, hB⟩ := exists_norm_smoothed_sub_le
  set C₀ := 32 * |B| + 520
  refine ⟨1 / 64, by norm_num, C₀, fun k _ χ y hy ↦ ?_⟩
  set a : ℕ → ℂ := fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
  have ha : ∀ n, ‖a n‖ ≤ Real.log n := fun n ↦ by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one χ n)).trans ArithmeticFunction.vonMangoldt_le_log
  set I₁ : ℂ := if χ = 1 then 1 else 0
  have hI₁ : ‖I₁‖ ≤ 1 := by simp only [I₁]; split_ifs <;> simp
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hy₀ : 0 < y := by linarith
  -- powers of `r = y^{1/64}`
  set r := y ^ (1 / 64 : ℝ) with hr
  have hr₀ : 0 < r := Real.rpow_pos_of_pos hy₀ _
  have hr₁ : 1 ≤ r := Real.one_le_rpow (by linarith) (by norm_num)
  have hpow : ∀ n : ℕ, y ^ ((n : ℝ) / 64) = r ^ n := fun n ↦ by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hy₀.le]
    congr 1
    ring
  have hy64 : y = r ^ 64 := by rw [← hpow 64]; norm_num
  have hy60 : y ^ (15 / 16 : ℝ) = r ^ 60 := by rw [← hpow 60]; norm_num
  have hy62 : y ^ (31 / 32 : ℝ) = r ^ 62 := by rw [← hpow 62]; norm_num
  have hy63 : y ^ (1 - 1 / 64 : ℝ) = r ^ 63 := by rw [← hpow 63]; norm_num
  have hr62 : r ^ 62 ≤ r ^ 63 := pow_le_pow_right₀ hr₁ (by norm_num)
  have hr63 : r ^ 63 ≤ r ^ 64 := pow_le_pow_right₀ hr₁ (by norm_num)
  have hr1 : 1 ≤ r ^ 62 := one_le_pow₀ hr₁
  -- the evaluation points `x = ⌊y⌋ + 1/2` and `x + h`, with `h = ⌈y^{31/32}⌉`
  set m := ⌊y⌋₊
  set x : ℝ := m + 1 / 2
  have hmy : (m : ℝ) ≤ y := Nat.floor_le hy₀.le
  have hym : y < m + 1 := Nat.lt_floor_add_one y
  have hx : 2 ≤ x := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast Nat.le_floor (by exact_mod_cast hy)
    simp only [x]
    linarith
  have hxfloor : ⌊x⌋₊ = m := by
    rw [Nat.floor_eq_iff (by linarith)]
    constructor <;> simp only [x] <;> linarith
  set h := ⌈y ^ (31 / 32 : ℝ)⌉₊
  have hh₁ : r ^ 62 ≤ h := hy62 ▸ Nat.le_ceil _
  have hh₂ : (h : ℝ) ≤ 2 * r ^ 62 := by
    have h₁ : (h : ℝ) < y ^ (31 / 32 : ℝ) + 1 :=
      Nat.ceil_lt_add_one (show 0 ≤ y ^ (31 / 32 : ℝ) by positivity)
    rw [hy62] at h₁
    linarith
  have hh₀ : (0 : ℝ) < h := by linarith
  have hhalf : ∀ n : ℕ, ∀ j : ℕ, (n : ℝ) ≠ j + 1 / 2 := by
    intro n j hn
    have : ((2 * n : ℕ) : ℝ) = ((2 * j + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_injective this
    omega
  have hxN : ∀ n : ℕ, (n : ℝ) ≠ x := fun n ↦ hhalf n m
  have hxhN : ∀ n : ℕ, (n : ℝ) ≠ x + h := fun n hn ↦ hhalf n (m + h) (by rw [hn]; push_cast; ring)
  have hxh : x + h ≤ 4 * r ^ 64 := by
    simp only [x]
    nlinarith
  -- the weighted sums `W(z) = ∑_{n ≤ z} a(n) (z - n)` are `I₁ z²/2 + O(k z^{31/16})`
  have hW : ∀ z : ℝ, 2 ≤ z → (∀ n : ℕ, (n : ℝ) ≠ z) → z ≤ 4 * r ^ 64 →
      ‖∑ n ∈ Finset.Icc 1 ⌊z⌋₊, a n * ((z : ℂ) - n) - I₁ * ((z : ℂ) ^ 2 / 2)‖ ≤
        16 * |B| * k * r ^ 124 := by
    intro z hz hzN hz₄
    have hz₀ : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
    have h₁ := hB k χ z hz hzN
    have heq : ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, a n * ((z : ℂ) - n) - I₁ * ((z : ℂ) ^ 2 / 2) =
        (z : ℂ) * (∑ m ∈ Finset.Icc 1 ⌊z⌋₊,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ m * (1 - m / z) -
            (if χ = 1 then (z : ℂ) / 2 else 0)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun n _ ↦ ?_
        simp only [a]
        field_simp
      · simp only [I₁]
        split_ifs <;> ring
    rw [heq, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hz15 : z ^ (15 / 16 : ℝ) ≤ 4 * r ^ 60 := by
      calc z ^ (15 / 16 : ℝ) ≤ (4 * y) ^ (15 / 16 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by rw [hy64]; exact hz₄) (by norm_num)
        _ = 4 ^ (15 / 16 : ℝ) * r ^ 60 := by
            rw [Real.mul_rpow (by norm_num) hy₀.le, hy60]
        _ ≤ 4 * r ^ 60 := by
            gcongr
            calc (4 : ℝ) ^ (15 / 16 : ℝ) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := Real.rpow_one 4
    have h₂ : ‖_‖ ≤ |B| * k * (4 * r ^ 60) :=
      h₁.trans (by gcongr; exact le_abs_self B)
    calc z * ‖_‖ ≤ (4 * r ^ 64) * (|B| * k * (4 * r ^ 60)) :=
          mul_le_mul hz₄ h₂ (norm_nonneg _) (by positivity)
      _ = 16 * |B| * k * r ^ 124 := by ring
  have hWx := hW x hx hxN (by linarith)
  have hWxh := hW (x + h) (by linarith) hxhN hxh
  -- the differencing error
  have hR := norm_sum_sub_sum_sub_le ha (by linarith : (0 : ℝ) ≤ x) h
  have hlog : Real.log (x + h) ≤ 256 * r := by
    have h₁ := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ x + h) (by norm_num : (0 : ℝ) < 1 / 64)
    have h₂ : (x + h) ^ (1 / 64 : ℝ) ≤ 4 * r := by
      calc (x + h) ^ (1 / 64 : ℝ) ≤ (4 * y) ^ (1 / 64 : ℝ) :=
            Real.rpow_le_rpow (by linarith) (by rw [hy64]; exact hxh) (by norm_num)
        _ = 4 ^ (1 / 64 : ℝ) * r := by rw [Real.mul_rpow (by norm_num) hy₀.le]
        _ ≤ 4 * r := by
            gcongr
            calc (4 : ℝ) ^ (1 / 64 : ℝ) ≤ 4 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 4 := Real.rpow_one 4
    calc Real.log (x + h) ≤ (x + h) ^ (1 / 64 : ℝ) / (1 / 64) := h₁
      _ ≤ 4 * r / (1 / 64) := by gcongr
      _ = 256 * r := by ring
  -- the identity behind the differencing
  set S := ∑ n ∈ Finset.Icc 1 m, a n
  set Wx := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n)
  set Wxh := ∑ n ∈ Finset.Icc 1 ⌊x + h⌋₊, a n * (((x + h : ℝ) : ℂ) - n)
  have hid : (h : ℂ) * (S - I₁ * y) = (Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2)) - (Wxh - Wx - h * S) +
        I₁ * (h * ((x : ℂ) - y + h / 2)) := by
    push_cast
    ring
  have hxy : ‖(x : ℂ) - y + h / 2‖ ≤ 1 / 2 + h / 2 := by
    rw [show (x : ℂ) - y + h / 2 = ((x - y + h / 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_le]
    simp only [x]
    constructor <;> linarith
  have hmain : (h : ℝ) * ‖S - I₁ * y‖ ≤ 32 * |B| * k * r ^ 124 +
      h ^ 2 * (256 * r) + h * (1 / 2 + h / 2) := by
    have h₁ : ‖(h : ℂ) * (S - I₁ * y)‖ = h * ‖S - I₁ * y‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← h₁, hid]
    have h₂ : ‖I₁ * (h * ((x : ℂ) - y + h / 2))‖ ≤ h * (1 / 2 + h / 2) := by
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc ‖I₁‖ * (h * ‖(x : ℂ) - y + h / 2‖) ≤ 1 * (h * (1 / 2 + h / 2)) := by
            gcongr
        _ = h * (1 / 2 + h / 2) := one_mul _
    have h₃ : ‖Wxh - Wx - h * S‖ ≤ h ^ 2 * (256 * r) := by
      rw [hxfloor] at hR
      refine hR.trans ?_
      gcongr
    have h₄ := norm_add_le ((Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2)) - (Wxh - Wx - h * S)) (I₁ * (h * ((x : ℂ) - y + h / 2)))
    have h₅ := norm_sub_le ((Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) -
      (Wx - I₁ * ((x : ℂ) ^ 2 / 2))) (Wxh - Wx - h * S)
    have h₆ := norm_sub_le (Wxh - I₁ * (((x + h : ℝ) : ℂ) ^ 2 / 2)) (Wx - I₁ * ((x : ℂ) ^ 2 / 2))
    linarith
  -- dividing by `h ≥ r^62`
  have hfinal : ‖S - I₁ * y‖ ≤ C₀ * k * r ^ 63 := by
    refine le_of_mul_le_mul_left (hmain.trans ?_) hh₀
    have hB₀ : 0 ≤ |B| * k := by positivity
    have e₁ : 32 * |B| * k * r ^ 124 ≤ h * (32 * |B| * k * r ^ 63) := by
      have : r ^ 124 ≤ r ^ 62 * r ^ 63 := by
        rw [← pow_add]; exact pow_le_pow_right₀ hr₁ (by norm_num)
      calc 32 * |B| * k * r ^ 124 ≤ 32 * |B| * k * (r ^ 62 * r ^ 63) := by gcongr
        _ ≤ 32 * |B| * k * (h * r ^ 63) := by gcongr
        _ = h * (32 * |B| * k * r ^ 63) := by ring
    have e₂ : (h : ℝ) ^ 2 * (256 * r) ≤ h * (512 * r ^ 63) := by
      have : (h : ℝ) * r ≤ 2 * r ^ 63 := by
        calc (h : ℝ) * r ≤ 2 * r ^ 62 * r := by gcongr
          _ = 2 * r ^ 63 := by ring
      nlinarith
    have e₃ : (h : ℝ) * (1 / 2 + h / 2) ≤ h * (2 * r ^ 63) := by
      gcongr
      linarith
    have e₄ : 32 * |B| * k * r ^ 63 + 512 * r ^ 63 + 2 * r ^ 63 ≤ C₀ * k * r ^ 63 := by
      have h₁ : (514 : ℝ) * r ^ 63 ≤ 520 * k * r ^ 63 := by
        have : 0 ≤ r ^ 63 := by positivity
        nlinarith
      have h₂ : C₀ * k * r ^ 63 = 32 * |B| * k * r ^ 63 + 520 * k * r ^ 63 := by
        simp only [C₀]; ring
      linarith
    calc 32 * |B| * k * r ^ 124 + (h : ℝ) ^ 2 * (256 * r) + h * (1 / 2 + h / 2)
        ≤ h * (32 * |B| * k * r ^ 63) + h * (512 * r ^ 63) + h * (2 * r ^ 63) := by
          linarith
      _ = h * (32 * |B| * k * r ^ 63 + 512 * r ^ 63 + 2 * r ^ 63) := by ring
      _ ≤ h * (C₀ * k * r ^ 63) := mul_le_mul_of_nonneg_left e₄ hh₀.le
  -- conclude
  have hS : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
      (if χ = 1 then (y : ℂ) else 0) = S - I₁ * y := by
    simp only [S, I₁, a, m]
    split_ifs <;> ring
  have hC₀ : 1 ≤ C₀ := by simp only [C₀]; linarith [abs_nonneg B]
  have hkC : (k : ℝ) ≤ (k : ℝ) ^ C₀ := by
    calc (k : ℝ) = (k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (k : ℝ) ^ C₀ := Real.rpow_le_rpow_of_exponent_le hk hC₀
  rw [hS, hy63]
  calc ‖S - I₁ * y‖ ≤ C₀ * k * r ^ 63 := hfinal
    _ ≤ C₀ * (k : ℝ) ^ C₀ * r ^ 63 := by gcongr

end Erdos408
