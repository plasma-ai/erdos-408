import Erdos408.OneSided.Cauchy
import Erdos408.OneSided.Major.Mellin.Kernel
import Erdos408.OneSided.Major.Mellin.Plane

/-!
# Mellin separation of the major-arc kernel

The analytic inputs of `blueprint/one_sided_type_ii.md` §6.4.

* `exists_plateauTwist_separation`: for `|λ| ≤ Λ` and `X ≥ 2`, the kernel
  `ψ_λ(X(w - w'))`, `ψ_λ(y) = ψ(y) e(λy)`, separates as
  `∫∫ K(τ, σ) w^{iτ} w'^{iσ}` for `w, w' ∈ [1, 16]`, with
  `|K(τ, σ)| ≤ C₀ Λ⁴ X⁻¹ (1 + |τ|/X)^{-2} (1 + |τ + σ|)^{-2}`. This is 2-D Fourier inversion
  of `Φ(ζ, z) = ψ_λ(X e^z (e^{ζ/X} - 1)) ρ(z) χ(ζ)` with fixed cutoffs: `ρ = 1` on
  `[0, log 16]` and `χ = 1` on `[-5, 5]`. Where `ψ_λ ≠ 0` and `w, w' ∈ [1, 16]`,
  `|ζ| = X |log(w/w')| ≤ 5`. With `y = X e^z (e^{ζ/X} - 1)`, `∂_z y = y` and
  `∂_ζ y = e^z e^{ζ/X}`, so the mixed partials `∂_ζ^a ∂_z^b Φ` with `a, b ≤ 2` are
  `O(Λ⁴)` uniformly in `X ≥ 2`. Integration by parts gives
  `|Φ̂(v, s)| ≪ Λ⁴ (1 + |v|)^{-2} (1 + |s|)^{-2}`. Then substitute `ζ = X log(w/w')`,
  `z = log w'`, `τ = 2πXv`, `σ = 2πs - τ`.
* `exists_bumpTwist_mellin`: `η(y) e(-λy) = ∫ g(ξ) y^{iξ} dξ` for `y > 0`, with
  `∫ |g| ≤ C₀ (1 + |λ|)²`. This is `ft_inversion` applied to `z ↦ η(e^z) e(-λ e^z)`.
-/

namespace Erdos408.OneSided

open MeasureTheory Real ContDiff Mellin

/-- `ψ_λ(y) = ψ(y) e(λ y)`. -/
noncomputable def plateauTwist (lam y : ℝ) : ℂ :=
  (plateau y : ℂ) * Complex.exp (2 * π * Complex.I * ((lam * y : ℝ) : ℂ))

/-! ### The twisted plateau -/

private theorem contDiff_plateauTwist (lam : ℝ) : ContDiff ℝ ∞ (plateauTwist lam) :=
  (Complex.ofRealCLM.contDiff.comp contDiff_plateau).mul
    (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id))))

/-- `‖D^i ψ_λ‖ ≪ Λ⁴` for `i ≤ 4` and `|λ| ≤ Λ`, `1 ≤ Λ`. -/
private theorem exists_norm_iteratedFDeriv_plateauTwist_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ Λ lam : ℝ, 1 ≤ Λ → |lam| ≤ Λ → ∀ i ≤ 4, ∀ y,
      ‖iteratedFDeriv ℝ i (plateauTwist lam) y‖ ≤ C * Λ ^ 4 := by
  -- the derivatives of `ψ` are bounded
  have hc : HasCompactSupport fun t => (plateau t : ℂ) := by
    refine hasCompactSupport_of_lt_abs (R := 5) fun t ht => ?_
    rw [plateau_eq_zero ht.le, Complex.ofReal_zero]
  obtain ⟨P, hP⟩ := exists_norm_iteratedFDeriv_le
    (Complex.ofRealCLM.contDiff.comp contDiff_plateau) hc 4
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (Nat.zero_le _) 0)
  refine ⟨16 * P * (4 * π) ^ 4, by positivity, fun Λ lam hΛ hlam i hi y => ?_⟩
  refine (norm_iteratedFDeriv_twist_le (Complex.ofRealCLM.contDiff.comp contDiff_plateau)
    (fun j hj => hP j (hj.trans hi)) lam y).trans ?_
  -- `2π(1 + |λ|) ≤ 4πΛ`
  have h1 : 1 ≤ 2 * π * (1 + |lam|) := by nlinarith [two_le_pi, abs_nonneg lam]
  have h2 : 2 * π * (1 + |lam|) ≤ 4 * π * Λ := by nlinarith [pi_pos]
  calc 2 ^ i * P * (2 * π * (1 + |lam|)) ^ i ≤ 2 ^ 4 * P * (2 * π * (1 + |lam|)) ^ 4 := by
        gcongr
        norm_num
    _ ≤ 2 ^ 4 * P * (4 * π * Λ) ^ 4 := by gcongr
    _ = 16 * P * (4 * π) ^ 4 * Λ ^ 4 := by ring

/-- The substitution `y = a x`: `∫ g(y) dy = a ∫ g(a x) dx` for `a > 0`. -/
private theorem integral_eq_mul_integral_comp_mul (g : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    ∫ y, g y = a * ∫ x, g (a * x) := by
  rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.2 ha), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ ha.ne', Complex.ofReal_one, one_mul]

/-- `((1 + a/(2π))²)⁻¹ ≤ (2π)² ((1 + a)²)⁻¹` for `a ≥ 0`. -/
private theorem inv_one_add_div_two_pi_sq_le {a : ℝ} (ha : 0 ≤ a) :
    ((1 + a / (2 * π)) ^ 2)⁻¹ ≤ (2 * π) ^ 2 * ((1 + a) ^ 2)⁻¹ := by
  have hpi : 1 ≤ 2 * π := by linarith [two_le_pi]
  have h : 1 + a ≤ 2 * π * (1 + a / (2 * π)) := by
    rw [mul_add, mul_div_cancel₀ _ (by positivity), mul_one]
    linarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity),
    ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h 2

/-- `((1 + |u|)²)⁻¹` is integrable. -/
private theorem integrable_inv_one_add_abs_sq :
    Integrable fun u : ℝ => ((1 + |u|) ^ 2)⁻¹ := by
  refine integrable_inv_one_add_sq.mono' ?_ (Filter.Eventually.of_forall fun u => ?_)
  · exact (Continuous.inv₀ (by fun_prop) fun u => by positivity).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_anti₀ (by positivity) (by nlinarith [abs_nonneg u, sq_abs u])

/-- The separation of `ψ_λ(X(w - w'))` into `w^{iτ} w'^{iσ}`, with order-2 decay. -/
theorem exists_plateauTwist_separation : ∃ C₀ : ℝ, ∀ Λ X lam : ℝ, 1 ≤ Λ → 2 ≤ X → |lam| ≤ Λ →
    ∃ Kf : ℝ × ℝ → ℂ, Integrable Kf ∧
      (∀ τ σ : ℝ, ‖Kf (τ, σ)‖ ≤
        C₀ * Λ ^ 4 / X * ((1 + |τ| / X) ^ 2)⁻¹ * ((1 + |τ + σ|) ^ 2)⁻¹) ∧
      ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
        plateauTwist lam (X * (w - w')) =
          ∫ q : ℝ × ℝ, Kf q * (w : ℂ) ^ ((q.1 : ℂ) * Complex.I) *
            (w' : ℂ) ^ ((q.2 : ℂ) * Complex.I) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_iteratedFDeriv_plateauTwist_le
  obtain ⟨B, hB0, hB⟩ := exists_norm_iteratedFDeriv_gapKernel_le
  refine ⟨64 * 20 ^ 2 * (B * C) * (2 * π) ^ 2, fun Λ X lam hΛ hX hlam => ?_⟩
  have hX0 : 0 < X := by linarith
  have hpi : (0 : ℝ) < 2 * π := by positivity
  -- the cut-off kernel `Φ` and its transform
  set Φ := gapKernel (plateauTwist lam) X with hΦ
  have hΦc : ContDiff ℝ ∞ Φ := contDiff_gapKernel (contDiff_plateauTwist lam) X
  have hΦs : ∀ p : ℝ × ℝ, 20 < ‖p‖ → Φ p = 0 := fun p hp => gapKernel_eq_zero _ X hp
  have hΦM : ∀ n ≤ 4, ∀ p, ‖iteratedFDeriv ℝ n Φ p‖ ≤ B * C * Λ ^ 4 := fun n hn p => by
    rw [mul_assoc]
    exact hB _ X _ (contDiff_plateauTwist lam) hX (hC Λ lam hΛ hlam) n hn p
  set M : ℝ := 64 * 20 ^ 2 * (B * C * Λ ^ 4) with hM
  have hdec : ∀ v s, ‖ft2 Φ v s‖ ≤ M * ((1 + |v|) ^ 2)⁻¹ * ((1 + |s|) ^ 2)⁻¹ := fun v s => by
    have h := norm_ft2_mul_le hΦc (by norm_num) hΦs hΦM v s
    rw [mul_assoc, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  -- `K(τ, σ) = ft2 Φ (τ/(2πX), (τ + σ)/(2π)) / ((2π)² X)`
  set c : ℝ := (2 * π) ^ 2 * X with hc
  have hc0 : 0 < c := by positivity
  set Kf : ℝ × ℝ → ℂ := fun q =>
    ft2 Φ (q.1 / (2 * π * X)) ((q.1 + q.2) / (2 * π)) / (c : ℂ) with hKf
  set D : ℝ × ℝ → ℝ := fun q => 64 * 20 ^ 2 * (B * C) * (2 * π) ^ 2 * Λ ^ 4 / X *
    ((1 + |q.1| / X) ^ 2)⁻¹ * ((1 + |q.1 + q.2|) ^ 2)⁻¹ with hD
  have hbound : ∀ τ σ : ℝ, ‖Kf (τ, σ)‖ ≤ D (τ, σ) := by
    intro τ σ
    have h1 : |τ / (2 * π * X)| = |τ| / X / (2 * π) := by
      rw [abs_div, abs_of_pos (mul_pos hpi hX0)]
      ring
    have h2 : |(τ + σ) / (2 * π)| = |τ + σ| / (2 * π) := by
      rw [abs_div, abs_of_pos hpi]
    have hb1 := inv_one_add_div_two_pi_sq_le (by positivity : 0 ≤ |τ| / X)
    have hb2 := inv_one_add_div_two_pi_sq_le (abs_nonneg (τ + σ))
    have hM0 : 0 ≤ M := by positivity
    simp only [hKf, hD, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    have h : ‖ft2 Φ (τ / (2 * π * X)) ((τ + σ) / (2 * π))‖ ≤
        M * ((2 * π) ^ 2 * ((1 + |τ| / X) ^ 2)⁻¹) * ((2 * π) ^ 2 * ((1 + |τ + σ|) ^ 2)⁻¹) := by
      refine (hdec _ _).trans ?_
      rw [h1, h2]
      gcongr
    refine (div_le_div_of_nonneg_right h hc0.le).trans (le_of_eq ?_)
    rw [hM, hc]
    field_simp
  -- continuity and integrability of `K`
  have hKc : Continuous Kf :=
    ((continuous_ft2 hΦc.continuous hΦs).comp ((continuous_fst.div_const _).prodMk
      ((continuous_fst.add continuous_snd).div_const _))).div_const _
  have hDi : Integrable D (volume.prod volume) := by
    have hf : Integrable fun τ : ℝ => 64 * 20 ^ 2 * (B * C) * (2 * π) ^ 2 * Λ ^ 4 / X *
        ((1 + |τ| / X) ^ 2)⁻¹ := by
      refine Integrable.const_mul ?_ _
      refine (integrable_inv_one_add_sq.comp_div hX0.ne').mono' ?_
        (Filter.Eventually.of_forall fun τ => ?_)
      · exact (Continuous.inv₀ (by fun_prop) fun τ => by positivity).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        refine inv_anti₀ (by positivity) ?_
        rw [div_pow, ← sq_abs τ]
        nlinarith [abs_nonneg τ, div_nonneg (abs_nonneg τ) hX0.le, sq_nonneg (|τ| / X),
          show (|τ| / X) ^ 2 = |τ| ^ 2 / X ^ 2 from div_pow _ _ _]
    have hP := hf.mul_prod integrable_inv_one_add_abs_sq
    have hPc : Continuous fun q : ℝ × ℝ => 64 * 20 ^ 2 * (B * C) * (2 * π) ^ 2 * Λ ^ 4 / X *
        ((1 + |q.1| / X) ^ 2)⁻¹ * ((1 + |q.2|) ^ 2)⁻¹ :=
      ((continuous_const.mul (Continuous.inv₀ (by fun_prop) fun q => by positivity)).mul
        (Continuous.inv₀ (by fun_prop) fun q => by positivity))
    exact ((measurePreserving_prod_add volume volume).integrable_comp
      hPc.aestronglyMeasurable).2 hP
  have hKi : Integrable Kf :=
    hDi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall fun q => hbound q.1 q.2)
  refine ⟨Kf, hKi, hbound, fun w w' hw hw16 hw' hw'16 => ?_⟩
  -- the kernel is `Φ` at `ζ = X log(w/w')`, `z = log w'`; invert there
  have hψ : ∀ y, 5 ≤ |y| → plateauTwist lam y = 0 := fun y hy => by
    simp [plateauTwist, plateau_eq_zero hy]
  rw [← gapKernel_log hψ hX0 hw hw' hw'16, ← hΦ, ← ft2_inversion hΦc (by norm_num) hΦs hΦM]
  set a := log w
  set b := log w'
  -- write `w^{iτ} w'^{iσ} = e^{i(τ a + σ b)}`
  set E : ℝ × ℝ → ℂ := fun q => Complex.exp (((q.1 * a + q.2 * b : ℝ) : ℂ) * Complex.I)
    with hE
  have hwE : ∀ q : ℝ × ℝ, Kf q * (w : ℂ) ^ ((q.1 : ℂ) * Complex.I) *
      (w' : ℂ) ^ ((q.2 : ℂ) * Complex.I) = Kf q * E q := fun q => by
    have hw0 : (w : ℂ) ≠ 0 := by exact_mod_cast (by linarith : w ≠ 0)
    have hw0' : (w' : ℂ) ≠ 0 := by exact_mod_cast (by linarith : w' ≠ 0)
    rw [Complex.cpow_def_of_ne_zero hw0, Complex.cpow_def_of_ne_zero hw0',
      ← Complex.ofReal_log (by linarith), ← Complex.ofReal_log (by linarith), mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [hwE]
  have hEc : Continuous E := Complex.continuous_exp.comp (by fun_prop)
  have hKE : Integrable (fun q => Kf q * E q) (volume.prod volume) := by
    refine hKi.norm.mono' (hKc.mul hEc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [norm_mul, hE]
    simp only [Complex.norm_exp_ofReal_mul_I, mul_one, le_refl]
  rw [Measure.volume_eq_prod, integral_prod _ hKE]
  -- substitute `σ = 2πs - τ`, then `τ = 2πXv`
  have hinner : ∀ τ : ℝ, ∫ σ, Kf (τ, σ) * E (τ, σ) =
      (2 * π : ℝ) * ∫ s, Kf (τ, 2 * π * s - τ) * E (τ, 2 * π * s - τ) := fun τ => by
    rw [← integral_sub_right_eq_self (fun σ => Kf (τ, σ) * E (τ, σ)) τ,
      integral_eq_mul_integral_comp_mul _ hpi]
  simp only [hinner]
  conv_rhs => rw [integral_eq_mul_integral_comp_mul _ (mul_pos hpi hX0)]
  rw [← integral_const_mul]
  congr 1 with v
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  congr 1 with s
  have h1 : 2 * π * X * v / (2 * π * X) = v := by field_simp
  have h2 : (2 * π * X * v + (2 * π * s - 2 * π * X * v)) / (2 * π) = s := by field_simp; ring
  have he : Complex.exp (((2 * π * X * v * a + (2 * π * s - 2 * π * X * v) * b : ℝ) : ℂ) *
      Complex.I) = Complex.exp (2 * π * Complex.I * ((X * (a - b) : ℝ) : ℂ) * (v : ℂ)) *
        Complex.exp (2 * π * Complex.I * (b : ℂ) * (s : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [hKf, hE, h1, h2, he]
  have hpi' : (π : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
  have hX' : (X : ℂ) ≠ 0 := by exact_mod_cast hX0.ne'
  rw [hc]
  push_cast
  field_simp

/-- The Mellin form of `η(y) e(-λ y)`. -/
theorem exists_bumpTwist_mellin : ∃ C₀ : ℝ, ∀ lam : ℝ, ∃ g : ℝ → ℂ, Integrable g ∧
    ∫ ξ, ‖g ξ‖ ≤ C₀ * (1 + |lam|) ^ 2 ∧
    ∀ y : ℝ, 0 < y →
      (dyadicBump y : ℂ) * Complex.exp (-(2 * π * Complex.I * ((lam * y : ℝ) : ℂ))) =
        ∫ ξ, g ξ * (y : ℂ) ^ ((ξ : ℂ) * Complex.I) := by
  -- the derivatives of `η` are bounded
  have hηd : ContDiff ℝ ∞ dyadicBump :=
    (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).sub
      (smoothTransition.contDiff.comp ((contDiff_id.div_const 2).sub contDiff_const))
  have hc : HasCompactSupport fun u => (dyadicBump u : ℂ) := by
    refine hasCompactSupport_of_lt_abs (R := 4) fun u hu => ?_
    by_contra h
    have h' := lt_of_dyadicBump_ne_zero fun h0 => h (by rw [h0, Complex.ofReal_zero])
    exact absurd hu (not_lt.2 (abs_le.2 ⟨by linarith, h'.2.le⟩))
  obtain ⟨P, hP⟩ := exists_norm_iteratedFDeriv_le (Complex.ofRealCLM.contDiff.comp hηd) hc 2
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (Nat.zero_le _) 0)
  refine ⟨16 * (1 + 2 * (4 * P * (2 * π) ^ 2) * exp 4 ^ 2), fun lam => ?_⟩
  -- `φ(u) = η(u) e(-λu)` has `‖D^i φ‖ ≤ K = 4 P (2π)² (1 + |λ|)²` for `i ≤ 2`
  set K : ℝ := 4 * P * (2 * π) ^ 2 * (1 + |lam|) ^ 2 with hK
  set φ : ℝ → ℂ := fun u => (dyadicBump u : ℂ) *
    Complex.exp (2 * π * Complex.I * ((-lam * u : ℝ) : ℂ)) with hφ
  have hφd : ContDiff ℝ ∞ φ :=
    (Complex.ofRealCLM.contDiff.comp hηd).mul (Complex.contDiff_exp.comp (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id))))
  have hφM : ∀ i ≤ 2, ∀ u, ‖iteratedFDeriv ℝ i φ u‖ ≤ K := by
    intro i hi u
    refine (norm_iteratedFDeriv_twist_le (Complex.ofRealCLM.contDiff.comp hηd)
      (fun j hj => hP j (hj.trans hi)) (-lam) u).trans ?_
    have h1 : 1 ≤ 2 * π * (1 + |lam|) := by nlinarith [two_le_pi, abs_nonneg lam]
    rw [abs_neg]
    calc 2 ^ i * P * (2 * π * (1 + |lam|)) ^ i ≤ 2 ^ 2 * P * (2 * π * (1 + |lam|)) ^ 2 := by
          gcongr
          norm_num
      _ = K := by ring
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hφM 0 (Nat.zero_le _) 0)
  -- `F(z) = φ(e^z)` is supported in `[-4, 4]` with `|F| ≤ 1` and `|F''| ≤ 2 K e^8`
  set F : ℝ → ℂ := φ ∘ exp with hF
  have hFd : ContDiff ℝ ∞ F := hφd.comp contDiff_exp
  have hFs : ∀ z, 4 < |z| → F z = 0 := by
    intro z hz
    have hη : dyadicBump (exp z) = 0 := by
      by_contra h
      have h' := lt_of_dyadicBump_ne_zero h
      rcases lt_abs.1 hz with hz | hz
      · linarith [add_one_le_exp z]
      · have : exp z < 1 := Real.exp_lt_one_iff.2 (by linarith)
        linarith [h'.1]
    simp [hF, hφ, hη]
  have hF0 : ∀ z, ‖F z‖ ≤ 1 := by
    intro z
    simp only [hF, hφ, Function.comp_apply, norm_mul, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (dyadicBump_nonneg _)]
    simpa using dyadicBump_le_one (exp z)
  have hF2 : ∀ z, ‖iteratedDeriv 2 F z‖ ≤ 2 * K * exp 4 ^ 2 := by
    intro z
    rcases lt_or_ge 4 |z| with hz | hz
    · rw [iteratedDeriv_eq_zero_of_lt_abs hFs 2 z hz, norm_zero]
      positivity
    · rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have hD : ∀ i, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i exp z‖ ≤ exp 4 ^ i := by
        intro i hi1 _
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_exp,
          Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact (exp_le_exp.2 ((le_abs_self z).trans hz)).trans
          (le_self_pow₀ (one_le_exp (by norm_num)) (by omega))
      have h := norm_iteratedFDeriv_comp_le hφd contDiff_exp (by simp) z
        (fun i hi => hφM i hi _) hD
      rwa [Nat.factorial_two, Nat.cast_ofNat] at h
  obtain ⟨hint, hI⟩ := integral_norm_ft_le (hFd.of_le (by simp)) (by norm_num) hFs hF0 hF2
  -- rescale: `g(ξ) = ft F (ξ/(2π)) / (2π)`
  have hpi : (0 : ℝ) < 2 * π := by positivity
  refine ⟨fun ξ => ft F (ξ / (2 * π)) / ((2 * π : ℝ) : ℂ), (hint.comp_div hpi.ne').div_const _,
    ?_, fun y hy => ?_⟩
  · have hg : ∫ ξ, ‖ft F (ξ / (2 * π)) / ((2 * π : ℝ) : ℂ)‖ = ∫ ξ, ‖ft F ξ‖ := by
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
      rw [integral_div, Measure.integral_comp_div (fun ξ => ‖ft F ξ‖), smul_eq_mul, abs_of_pos hpi,
        mul_div_cancel_left₀ _ hpi.ne']
    rw [hg]
    refine hI.trans ?_
    have h1 : 1 ≤ (1 + |lam|) ^ 2 := by nlinarith [abs_nonneg lam]
    have h8 : 0 ≤ 2 * (4 * P * (2 * π) ^ 2) * exp 4 ^ 2 := by positivity
    calc 4 * 4 * (1 + 2 * K * exp 4 ^ 2) =
        16 * (1 + 2 * (4 * P * (2 * π) ^ 2) * exp 4 ^ 2 * (1 + |lam|) ^ 2) := by
          rw [hK]
          ring
      _ ≤ 16 * ((1 + 2 * (4 * P * (2 * π) ^ 2) * exp 4 ^ 2) * (1 + |lam|) ^ 2) := by
          nlinarith
      _ = _ := by ring
  · -- `η(y) e(-λy) = F(log y)`, then invert and substitute `ξ = 2π t`
    have hF' : (dyadicBump y : ℂ) * Complex.exp (-(2 * π * Complex.I * ((lam * y : ℝ) : ℂ))) =
        F (log y) := by
      simp only [hF, hφ, Function.comp_apply, exp_log hy]
      congr 2
      push_cast
      ring
    rw [hF', ← ft_inversion (hFd.of_le (by simp)) hFs (log y)]
    conv_rhs => rw [integral_eq_mul_integral_comp_mul _ hpi]
    rw [← integral_const_mul]
    congr 1 with t
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hpi' : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
    dsimp only
    rw [Complex.cpow_def_of_ne_zero hy0, ← Complex.ofReal_log hy.le,
      mul_div_cancel_left₀ _ hpi.ne']
    field_simp
    push_cast
    ring_nf

end Erdos408.OneSided
