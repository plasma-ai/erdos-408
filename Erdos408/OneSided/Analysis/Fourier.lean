import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fourier transforms of smooth cutoffs

Decay and inversion for compactly supported smooth functions on `ℝ`, with constants explicit
in the support radius and the derivative bounds. These are the transforms used in
`mem:cutoff-fourier` and in the Mellin steps of PD §5. There the cutoffs depend on `x`, so
the constants must be explicit.

The transform is `ft f ξ = ∫ e(-x ξ) f(x) dx`, with `e(t) = exp(2πi t)`, which is Mathlib's
`Real.fourierIntegral` written out.

* `norm_ft_mul_le`: if `f` is `C^k`, supported in `[-R, R]`, and `|f^{(k)}| ≤ M`, then
  `(2π|ξ|)^k |ft f ξ| ≤ 2 R M`.
* `integral_norm_ft_le`: for `C²` such `f`, `ft f` is integrable with
  `∫ |ft f| ≤ 4 R (M₀ + M₂)`.
* `ft_inversion`: `f(x) = ∫ e(x ξ) ft f ξ dξ`.
-/

namespace Erdos408.OneSided

open MeasureTheory

/-- The Fourier transform `ft f ξ = ∫ e(-x ξ) f(x) dx`. -/
noncomputable def ft (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (ξ : ℂ))) * f x

/-! ### Auxiliary lemmas -/

/-- `ft` is Mathlib's Fourier transform `𝓕` on `ℝ`. -/
theorem ft_eq_fourier (f : ℝ → ℂ) : ft f = FourierTransform.fourier f := by
  funext ξ
  rw [Real.fourier_real_eq_integral_exp_smul, ft]
  congr 1 with x
  rw [smul_eq_mul]
  push_cast
  ring_nf

/-- Mathlib's inverse Fourier transform `𝓕⁻` on `ℝ`, written out as `∫ e(x ξ) g(ξ) dξ`. -/
theorem fourierInv_eq_integral (g : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv g x =
      ∫ ξ : ℝ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (ξ : ℂ)) * g ξ := by
  rw [Real.fourierInv_eq']
  congr 1 with ξ
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  push_cast
  ring_nf

/-- A function vanishing outside `[-R, R]` has compact support. -/
theorem hasCompactSupport_of_lt_abs {f : ℝ → ℂ} {R : ℝ} (hsupp : ∀ x, R < |x| → f x = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => hsupp x ?_
  simpa [Real.norm_eq_abs] using hx

/-- The derivatives of a function vanishing outside `[-R, R]` also vanish outside `[-R, R]`. -/
theorem iteratedDeriv_eq_zero_of_lt_abs {f : ℝ → ℂ} {R : ℝ}
    (hsupp : ∀ x, R < |x| → f x = 0) (k : ℕ) : ∀ x, R < |x| → iteratedDeriv k f x = 0 := by
  intro x hx
  -- the closed support lies in `[-R, R]`
  have hts : tsupport f ⊆ Metric.closedBall 0 R := by
    refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
    by_contra h
    exact hy (hsupp y (by simpa [Real.norm_eq_abs] using h))
  have hx' : x ∉ tsupport f := fun h => by
    have := hts h
    simp [Real.norm_eq_abs] at this
    linarith
  -- derivatives vanish off the closed support
  have := Function.notMem_support.1 fun h => hx' (support_iteratedFDeriv_subset (𝕜 := ℝ) k h)
  rw [iteratedDeriv_eq_iteratedFDeriv, this]
  rfl

/-- The trivial bound `|ft g ξ| ≤ 2 R M` for `g` supported in `[-R, R]` with `|g| ≤ M`. -/
theorem norm_ft_le {g : ℝ → ℂ} {R M : ℝ} (hR : 0 ≤ R) (hsupp : ∀ x, R < |x| → g x = 0)
    (hM : ∀ x, ‖g x‖ ≤ M) (ξ : ℝ) : ‖ft g ξ‖ ≤ 2 * R * M := by
  -- restrict the integral to `[-R, R]`
  have hI : ft g ξ = ∫ x in Set.Icc (-R) R,
      Complex.exp (-(2 * Real.pi * Complex.I * (x : ℂ) * (ξ : ℂ))) * g x := by
    rw [ft, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
    rw [hsupp x ?_, mul_zero]
    by_contra h
    exact hx (abs_le.1 (not_lt.1 h))
  rw [hI]
  refine (norm_setIntegral_le_of_norm_le_const (C := M) (by simp) fun x _ => ?_).trans
    (le_of_eq ?_)
  · rw [norm_mul, Complex.norm_exp]
    simpa using hM x
  · rw [Real.volume_real_Icc_of_le (by linarith)]
    ring

/-! ### Decay and inversion -/

/-- Decay of the transform: `(2π|ξ|)^k |ft f ξ| ≤ 2 R M` for `f` of class `C^k`, supported in
`[-R, R]`, with `|f^{(k)}| ≤ M`. -/
theorem norm_ft_mul_le {f : ℝ → ℂ} {k : ℕ} (hf : ContDiff ℝ k f) {R M : ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ x, R < |x| → f x = 0) (hM : ∀ x, ‖iteratedDeriv k f x‖ ≤ M) (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ k * ‖ft f ξ‖ ≤ 2 * R * M := by
  -- the derivatives are continuous with compact support, hence integrable
  have hint : ∀ n : ℕ, n ≤ (k : ℕ∞) → Integrable (iteratedDeriv n f) := fun n hn =>
    (hf.continuous_iteratedDeriv n (by exact_mod_cast hn)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_lt_abs (iteratedDeriv_eq_zero_of_lt_abs hsupp n))
  -- differentiating `k` times multiplies the transform by `(2πiξ)^k`
  have hk := congrFun (Real.fourier_iteratedDeriv (N := k) hf hint le_rfl) ξ
  calc (2 * Real.pi * |ξ|) ^ k * ‖ft f ξ‖ = ‖ft (iteratedDeriv k f) ξ‖ := by
        rw [ft_eq_fourier, ft_eq_fourier, hk, norm_smul, norm_pow]
        simp [abs_of_pos Real.pi_pos]
    _ ≤ 2 * R * M := norm_ft_le hR (iteratedDeriv_eq_zero_of_lt_abs hsupp k) hM ξ

/-- For `f` of class `C²` supported in `[-R, R]` with `|f| ≤ M₀` and `|f''| ≤ M₂`, the
transform is integrable and `∫ |ft f| ≤ 4 R (M₀ + M₂)`. -/
theorem integral_norm_ft_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {R M₀ M₂ : ℝ} (hR : 0 ≤ R)
    (hsupp : ∀ x, R < |x| → f x = 0) (hM₀ : ∀ x, ‖f x‖ ≤ M₀)
    (hM₂ : ∀ x, ‖iteratedDeriv 2 f x‖ ≤ M₂) :
    Integrable (ft f) ∧ ∫ ξ : ℝ, ‖ft f ξ‖ ≤ 4 * R * (M₀ + M₂) := by
  have hfi : Integrable f :=
    hf.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_lt_abs hsupp)
  have hM : 0 ≤ M₀ + M₂ :=
    add_nonneg ((norm_nonneg _).trans (hM₀ 0)) ((norm_nonneg _).trans (hM₂ 0))
  -- the comparison function `(1 + (2πξ)²)⁻¹`, whose integral is `1 / 2`
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have hg : Integrable fun ξ : ℝ => (1 + (2 * Real.pi * ξ) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' hpi
  have hgI : ∫ ξ : ℝ, (1 + (2 * Real.pi * ξ) ^ 2)⁻¹ = 1 / 2 := by
    rw [Measure.integral_comp_mul_left (fun y => (1 + y ^ 2)⁻¹), integral_univ_inv_one_add_sq,
      smul_eq_mul, abs_of_pos (by positivity)]
    field_simp
  -- combine `|ft f| ≤ 2 R M₀` with `(2πξ)² |ft f| ≤ 2 R M₂`
  have hb : ∀ ξ, ‖ft f ξ‖ ≤ 2 * R * (M₀ + M₂) * (1 + (2 * Real.pi * ξ) ^ 2)⁻¹ := by
    intro ξ
    have h0 := norm_ft_le hR hsupp hM₀ ξ
    have h2 := norm_ft_mul_le hf hR hsupp hM₂ ξ
    rw [mul_pow, sq_abs, ← mul_pow] at h2
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  -- the transform is continuous, so integrable by comparison
  have hc : Continuous (ft f) := ft_eq_fourier f ▸
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hfi
  have hi : Integrable (ft f) :=
    (hg.const_mul _).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hi, (integral_mono hi.norm (hg.const_mul _) hb).trans ?_⟩
  rw [integral_const_mul, hgI]
  nlinarith

/-- Fourier inversion for compactly supported `C²` functions: `f(x) = ∫ e(x ξ) ft f ξ dξ`. -/
theorem ft_inversion {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {R : ℝ}
    (hsupp : ∀ x, R < |x| → f x = 0) (x : ℝ) :
    ∫ ξ : ℝ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ) * (ξ : ℂ)) * ft f ξ = f x := by
  -- enlarge the support radius to make it nonnegative
  have hsupp' : ∀ x, max R 0 < |x| → f x = 0 := fun x hx =>
    hsupp x ((le_max_left R 0).trans_lt hx)
  have hfc : Continuous f := hf.continuous
  have hfi : Integrable f :=
    hfc.integrable_of_hasCompactSupport (hasCompactSupport_of_lt_abs hsupp)
  -- `f` and `f''` are bounded, being continuous with compact support
  obtain ⟨M₀, hM₀⟩ := hfc.bounded_above_of_compact_support (hasCompactSupport_of_lt_abs hsupp)
  obtain ⟨M₂, hM₂⟩ := (hf.continuous_iteratedDeriv 2 le_rfl).bounded_above_of_compact_support
    (hasCompactSupport_of_lt_abs (iteratedDeriv_eq_zero_of_lt_abs hsupp 2))
  -- so the transform is integrable, and Mathlib's inversion theorem applies
  have hFi := (integral_norm_ft_le hf (le_max_right R 0) hsupp' hM₀ hM₂).1
  rw [ft_eq_fourier] at hFi
  rw [← fourierInv_eq_integral, ft_eq_fourier, hfc.fourierInv_fourier_eq hfi hFi]

end Erdos408.OneSided
