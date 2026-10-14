import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The energy of an average

`blueprint/one_sided_type_ii.md` §6.3 step 6. After Mellin inversion, the polynomial of one
dyad is bounded by an average `c ∫ w(ξ) h(ξ, τ) dξ` of isolated polynomials `h(ξ, ·)`, with
`w = |g|` the Mellin transform. PD passes to the energy by Minkowski's integral inequality.
Here Cauchy–Schwarz in `ξ` with the weight `w` gives `(∫ w h)² ≤ (∫ w) ∫ w h²`, and Fubini
gives `∫_a^b F² ≤ c² (∫ w)² sup_ξ ∫_a^b h(ξ, ·)²`.
-/

namespace Erdos408.OneSided

open MeasureTheory

/-- Cauchy–Schwarz with a weight: `(∫ w h)² ≤ (∫ w) ∫ w h²` for `w ≥ 0` integrable and `h`
bounded. The quadratic `s ↦ ∫ w (h - s)²` is nonnegative, so its discriminant is not
positive. -/
theorem sq_integral_mul_le {w h : ℝ → ℝ} (hw : Integrable w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hh : AEStronglyMeasurable h) {M : ℝ} (hM : ∀ ξ, |h ξ| ≤ M) :
    (∫ ξ, w ξ * h ξ) ^ 2 ≤ (∫ ξ, w ξ) * ∫ ξ, w ξ * h ξ ^ 2 := by
  have h₁ : Integrable fun ξ => w ξ * h ξ :=
    hw.mul_bdd hh (Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hM ξ)
  have h₂ : Integrable fun ξ => w ξ * h ξ ^ 2 :=
    hw.mul_bdd (hh.pow 2) (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM ξ) 2)
  -- `s ↦ ∫ w (h - s)²` is a nonnegative quadratic
  have hq : ∀ s : ℝ, 0 ≤ (∫ ξ, w ξ) * (s * s) + (-2 * ∫ ξ, w ξ * h ξ) * s +
      ∫ ξ, w ξ * h ξ ^ 2 := by
    intro s
    have e : ∀ ξ, w ξ * (h ξ - s) ^ 2 =
        (w ξ * h ξ ^ 2 - (2 * s) * (w ξ * h ξ)) + (s * s) * w ξ := fun ξ => by ring
    have hint : ∫ ξ, w ξ * (h ξ - s) ^ 2 = (∫ ξ, w ξ) * (s * s) +
        (-2 * ∫ ξ, w ξ * h ξ) * s + ∫ ξ, w ξ * h ξ ^ 2 := by
      simp_rw [e]
      rw [integral_add (f := fun ξ => w ξ * h ξ ^ 2 - (2 * s) * (w ξ * h ξ))
          (h₂.sub (h₁.const_mul _)) (hw.const_mul _),
        integral_sub (f := fun ξ => w ξ * h ξ ^ 2) h₂ (h₁.const_mul _), integral_const_mul,
        integral_const_mul]
      ring
    rw [← hint]
    exact integral_nonneg fun ξ => mul_nonneg (hw0 ξ) (sq_nonneg _)
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  have e : (-2 * ∫ ξ, w ξ * h ξ) ^ 2 = 4 * (∫ ξ, w ξ * h ξ) ^ 2 := by ring
  linarith

/-- The energy of an average: if `0 ≤ F(τ) ≤ c ∫ w(ξ) h(ξ, τ) dξ` with `w ≥ 0` integrable and
`0 ≤ h ≤ M` continuous, and `∫_a^b h(ξ, ·)² ≤ E` for every `ξ`, then
`∫_a^b F² ≤ c² (∫ w)² E`. -/
theorem integral_sq_le_of_le_integral {a b c M E : ℝ} (hab : a ≤ b) {w : ℝ → ℝ}
    (hw : Integrable w) (hw0 : ∀ ξ, 0 ≤ w ξ) {h : ℝ → ℝ → ℝ}
    (hh : Continuous (Function.uncurry h)) (hh0 : ∀ ξ τ, 0 ≤ h ξ τ)
    (hhM : ∀ ξ τ, h ξ τ ≤ M) (hE : ∀ ξ, ∫ τ in a..b, h ξ τ ^ 2 ≤ E) {F : ℝ → ℝ}
    (hF0 : ∀ τ, 0 ≤ F τ) (hF : ∀ τ, F τ ≤ c * ∫ ξ, w ξ * h ξ τ) :
    ∫ τ in a..b, F τ ^ 2 ≤ c ^ 2 * (∫ ξ, w ξ) ^ 2 * E := by
  set μ := volume.restrict (Set.Ioc a b)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set W := ∫ ξ, w ξ
  have hW : 0 ≤ W := integral_nonneg hw0
  -- the integrand `w(ξ) h(ξ, τ)²` is integrable on `(a, b] × ℝ`
  set f : ℝ → ℝ → ℝ := fun τ ξ => w ξ * h ξ τ ^ 2
  have hf : Integrable (Function.uncurry f) (μ.prod volume) := by
    refine Integrable.mono' ((integrable_const (M ^ 2)).mul_prod hw) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact hw.aestronglyMeasurable.comp_snd.mul
        ((hh.comp continuous_swap).pow 2).aestronglyMeasurable
    · simp only [Function.uncurry, f, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (hw0 _) (sq_nonneg _)), mul_comm (M ^ 2)]
      gcongr
      · exact hw0 _
      · exact hh0 _ _
      · exact hhM _ _
  -- pointwise Cauchy–Schwarz in `ξ`
  have hCS : ∀ τ, F τ ^ 2 ≤ c ^ 2 * W * ∫ ξ, f τ ξ := by
    intro τ
    have hM : ∀ ξ, |h ξ τ| ≤ M := fun ξ => by
      rw [abs_of_nonneg (hh0 ξ τ)]
      exact hhM ξ τ
    have h₁ := sq_integral_mul_le hw hw0
      (hh.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable hM
    calc F τ ^ 2 ≤ (c * ∫ ξ, w ξ * h ξ τ) ^ 2 := pow_le_pow_left₀ (hF0 τ) (hF τ) 2
      _ = c ^ 2 * (∫ ξ, w ξ * h ξ τ) ^ 2 := by ring
      _ ≤ c ^ 2 * (W * ∫ ξ, w ξ * h ξ τ ^ 2) := by gcongr; exact h₁
      _ = c ^ 2 * W * ∫ ξ, f τ ξ := by ring
  -- the inner energies are at most `w(ξ) E`
  have hin : ∀ ξ, ∫ τ in Set.Ioc a b, f τ ξ ≤ w ξ * E := by
    intro ξ
    simp only [f]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hab]
    exact mul_le_mul_of_nonneg_left (hE ξ) (hw0 ξ)
  rw [intervalIntegral.integral_of_le hab]
  calc ∫ τ in Set.Ioc a b, F τ ^ 2 ≤ ∫ τ in Set.Ioc a b, c ^ 2 * W * ∫ ξ, f τ ξ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => sq_nonneg _)
          (hf.integral_prod_left.const_mul _) (Filter.Eventually.of_forall hCS)
    _ = c ^ 2 * W * ∫ ξ, ∫ τ in Set.Ioc a b, f τ ξ := by
        rw [integral_const_mul, integral_integral_swap hf]
    _ ≤ c ^ 2 * W * ∫ ξ, w ξ * E :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ =>
          integral_nonneg fun τ => mul_nonneg (hw0 ξ) (sq_nonneg _)) (hw.mul_const E)
          (Filter.Eventually.of_forall hin)) (by positivity)
    _ = c ^ 2 * W ^ 2 * E := by
        rw [integral_mul_const]
        ring

end Erdos408.OneSided
