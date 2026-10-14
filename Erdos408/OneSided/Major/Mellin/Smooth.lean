import Erdos408.OneSided.Analysis.Fourier
import Erdos408.OneSided.Setup

/-!
# Derivative bounds for the Mellin kernels

Tools for bounding iterated derivatives of the smooth kernels in
`Erdos408.OneSided.Major.Mellin`.

* `norm_iteratedFDeriv_fderiv_apply_le`: `‖D^k ∂_d f‖ ≤ ‖d‖ ‖D^{k + 1} f‖`.
* `iteratedDeriv_two_comp_line`: the second derivative along `t ↦ a + t d` is `∂_d ∂_d f`.
* `exists_norm_iteratedFDeriv_le`: a smooth function with compact support has bounded derivatives.
* `norm_iteratedFDeriv_twist_le`: `‖D^i [φ(y) e(c y)]‖ ≤ 2^i P (2π(1 + |c|))^i` when the first
  `i` derivatives of `φ` are bounded by `P`.
* `contDiff_plateau`: the plateau `ψ` is smooth.
-/

namespace Erdos408.OneSided.Mellin

open ContDiff Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A directional derivative of a smooth function is smooth. -/
theorem contDiff_fderiv_apply {f : E → F} (hf : ContDiff ℝ ∞ f) (d : E) :
    ContDiff ℝ ∞ fun x => fderiv ℝ f x d :=
  (hf.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const

/-- `‖D^k ∂_d f‖ ≤ ‖d‖ ‖D^{k + 1} f‖`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {f : E → F} (hf : ContDiff ℝ ∞ f) (d : E) (k : ℕ)
    (x : E) :
    ‖iteratedFDeriv ℝ k (fun x => fderiv ℝ f x d) x‖ ≤ ‖d‖ * ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
  have h := (ContinuousLinearMap.apply ℝ F d).norm_iteratedFDeriv_comp_left (n := k)
    ((hf.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).contDiffAt (x := x))
    (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun L => by
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact L.le_opNorm d

/-- The derivative along the line `t ↦ a + t d` is the directional derivative. -/
theorem deriv_comp_line {f : E → F} (hf : Differentiable ℝ f) (a d : E) (t : ℝ) :
    deriv (fun t => f (a + t • d)) t = fderiv ℝ f (a + t • d) d := by
  have h := ((hasDerivAt_id t).smul_const d).const_add a
  rw [one_smul] at h
  exact ((hf _).hasFDerivAt.comp_hasDerivAt t h).deriv

/-- The second derivative along the line `t ↦ a + t d` is `∂_d ∂_d f`. -/
theorem iteratedDeriv_two_comp_line {f : E → F} (hf : ContDiff ℝ ∞ f) (a d : E) (t : ℝ) :
    iteratedDeriv 2 (fun t => f (a + t • d)) t =
      fderiv ℝ (fun x => fderiv ℝ f x d) (a + t • d) d := by
  have hd : ∀ {g : E → F}, ContDiff ℝ ∞ g → Differentiable ℝ g := fun hg =>
    hg.differentiable (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h : deriv (fun t => f (a + t • d)) = fun t => fderiv ℝ f (a + t • d) d :=
    funext (deriv_comp_line (hd hf) a d)
  rw [h]
  exact deriv_comp_line (f := fun x => fderiv ℝ f x d) (hd (contDiff_fderiv_apply hf d)) a d t

/-- A smooth function with compact support has bounded derivatives up to any order. -/
theorem exists_norm_iteratedFDeriv_le {f : E → F} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (n : ℕ) : ∃ P : ℝ, ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ P := by
  have hb : ∀ j : ℕ, ∃ P : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ P := fun j =>
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv j)
  induction n with
  | zero =>
    obtain ⟨P, hP⟩ := hb 0
    exact ⟨P, fun j hj x => by rw [Nat.le_zero.1 hj]; exact hP x⟩
  | succ n ih =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨Q, hQ⟩ := hb (n + 1)
    refine ⟨max P Q, fun j hj x => ?_⟩
    rcases Nat.le_succ_iff.1 hj with hj | rfl
    · exact (hP j hj x).trans (le_max_left _ _)
    · exact (hQ x).trans (le_max_right _ _)

/-- The derivatives of the twist `e(c y)`. -/
theorem iteratedDeriv_twist (c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun y : ℝ => Complex.exp (2 * π * Complex.I * ((c * y : ℝ) : ℂ))) =
      fun y => (2 * π * Complex.I * c) ^ k *
        Complex.exp (2 * π * Complex.I * ((c * y : ℝ) : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h : HasDerivAt (fun y : ℝ => 2 * π * Complex.I * ((c * y : ℝ) : ℂ))
        (2 * π * Complex.I * c) y := by
      have := ((hasDerivAt_id y).const_mul c).ofReal_comp.const_mul (2 * π * Complex.I)
      simpa using this
    rw [(h.cexp.const_mul _).deriv]
    ring

/-- `‖D^i [φ(y) e(c y)]‖ ≤ 2^i P (2π(1 + |c|))^i` when `‖D^j φ‖ ≤ P` for `j ≤ i`. -/
theorem norm_iteratedFDeriv_twist_le {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) {P : ℝ} {i : ℕ}
    (hP : ∀ j ≤ i, ∀ y, ‖iteratedFDeriv ℝ j φ y‖ ≤ P) (c y : ℝ) :
    ‖iteratedFDeriv ℝ i
        (fun y => φ y * Complex.exp (2 * π * Complex.I * ((c * y : ℝ) : ℂ))) y‖ ≤
      2 ^ i * P * (2 * π * (1 + |c|)) ^ i := by
  have he : ContDiff ℝ ∞ fun y : ℝ => Complex.exp (2 * π * Complex.I * ((c * y : ℝ) : ℂ)) :=
    Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)))
  have hb : 1 ≤ 2 * π * (1 + |c|) := by
    nlinarith [two_le_pi, abs_nonneg c]
  refine (norm_iteratedFDeriv_mul_le hφ he y (by exact_mod_cast le_top)).trans ?_
  -- each term is at most `C(i, j) P (2π(1 + |c|))^i`
  have hterm : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j φ y‖ *
      ‖iteratedFDeriv ℝ (i - j) (fun y : ℝ =>
        Complex.exp (2 * π * Complex.I * ((c * y : ℝ) : ℂ))) y‖ ≤
      (i.choose j : ℝ) * (P * (2 * π * (1 + |c|)) ^ i) := by
    intro j hj
    have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have he' : ‖iteratedFDeriv ℝ (i - j) (fun y : ℝ =>
        Complex.exp (2 * π * Complex.I * ((c * y : ℝ) : ℂ))) y‖ = (2 * π * |c|) ^ (i - j) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_twist, norm_mul, norm_pow,
        Complex.norm_exp]
      simp [abs_of_pos pi_pos]
    rw [he', mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul (hP j hj' y) ?_ (by positivity)
      ((norm_nonneg _).trans (hP 0 (Nat.zero_le _) y))) (Nat.cast_nonneg _)
    calc (2 * π * |c|) ^ (i - j) ≤ (2 * π * (1 + |c|)) ^ (i - j) := by
          gcongr
          linarith
      _ ≤ (2 * π * (1 + |c|)) ^ i := pow_le_pow_right₀ hb (Nat.sub_le i j)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  ring

/-- The plateau `ψ(t) = s(5 - t) s(5 + t)`. -/
theorem plateau_eq_mul (t : ℝ) :
    plateau t = smoothTransition (5 - t) * smoothTransition (5 + t) := by
  rcases le_total 0 t with ht | ht
  · rw [plateau, abs_of_nonneg ht, smoothTransition.one_of_one_le (x := 5 + t) (by linarith),
      mul_one]
  · rw [plateau, abs_of_nonpos ht, smoothTransition.one_of_one_le (x := 5 - t) (by linarith),
      one_mul, sub_neg_eq_add]

/-- The plateau `ψ` is smooth. -/
theorem contDiff_plateau : ContDiff ℝ ∞ plateau := by
  have h : plateau = fun t => smoothTransition (5 - t) * smoothTransition (5 + t) :=
    funext plateau_eq_mul
  rw [h]
  exact (smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

/-- `ψ(t) = 1` for `|t| ≤ 4`. -/
theorem plateau_eq_one {t : ℝ} (ht : |t| ≤ 4) : plateau t = 1 :=
  smoothTransition.one_of_one_le (by linarith)

/-- `ψ(t) = 0` for `5 ≤ |t|`. -/
theorem plateau_eq_zero {t : ℝ} (ht : 5 ≤ |t|) : plateau t = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

end Erdos408.OneSided.Mellin
