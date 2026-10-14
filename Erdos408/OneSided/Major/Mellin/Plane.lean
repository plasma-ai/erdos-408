import Erdos408.OneSided.Major.Mellin.Smooth
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Fourier transform on the plane

The iterated transform `ft2 F v s = ∫∫ e(-ζ v - z s) F(ζ, z) dζ dz` of a smooth function `F`
supported in the ball `‖(ζ, z)‖ ≤ R` (sup norm), built from the 1-D transform `ft`.

* `ft2_swap`: the two integrations commute.
* `norm_ft2_mul_le`: if `‖D^n F‖ ≤ M` for `n ≤ 4`, then
  `(1 + |v|)² (1 + |s|)² |ft2 F v s| ≤ 64 R² M`.
* `continuous_ft2`: `ft2 F` is jointly continuous.
* `ft2_inversion`: `F(ζ, z) = ∫ e(ζ v) ∫ e(z s) ft2 F v s ds dv`.
-/

namespace Erdos408.OneSided.Mellin

open MeasureTheory ContDiff Real

/-- The iterated transform `ft2 F v s = ∫ e(-z s) ∫ e(-ζ v) F(ζ, z) dζ dz`. -/
noncomputable def ft2 (F : ℝ × ℝ → ℂ) (v s : ℝ) : ℂ :=
  ft (fun z => ft (fun ζ => F (ζ, z)) v) s

/-! ### One-dimensional inputs -/

/-- Differentiating `k` times multiplies the transform by `(2πiξ)^k`. -/
theorem ft_iteratedDeriv {f : ℝ → ℂ} {k : ℕ} (hf : ContDiff ℝ k f) {R : ℝ}
    (hsupp : ∀ x, R < |x| → f x = 0) (ξ : ℝ) :
    ft (iteratedDeriv k f) ξ = (2 * π * Complex.I * ξ) ^ k * ft f ξ := by
  -- the derivatives are continuous with compact support, hence integrable
  have hint : ∀ n : ℕ, n ≤ (k : ℕ∞) → Integrable (iteratedDeriv n f) := fun n hn =>
    (hf.continuous_iteratedDeriv n (by exact_mod_cast hn)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_lt_abs (iteratedDeriv_eq_zero_of_lt_abs hsupp n))
  have hk := congrFun (Real.fourier_iteratedDeriv (N := k) hf hint le_rfl) ξ
  rw [ft_eq_fourier, ft_eq_fourier, hk, smul_eq_mul]

/-- The scaled trivial bound: `c |ft g ξ| ≤ 2 R M` when `c |g| ≤ M` and `g` vanishes outside
`[-R, R]`. -/
theorem mul_norm_ft_le {g : ℝ → ℂ} {R M c : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c)
    (hsupp : ∀ x, R < |x| → g x = 0) (hM : ∀ x, c * ‖g x‖ ≤ M) (ξ : ℝ) :
    c * ‖ft g ξ‖ ≤ 2 * R * M := by
  rcases hc.eq_or_lt with rfl | hc
  · have := (mul_nonneg hc (norm_nonneg (g 0))).trans (hM 0)
    rw [zero_mul]
    positivity
  · have h := norm_ft_le hR hsupp (fun x => (le_div_iff₀' hc).2 (hM x)) ξ
    rw [mul_div_assoc', le_div_iff₀' hc] at h
    linarith

/-- A transform with continuous dependence on a parameter is jointly continuous. -/
theorem continuous_ft_param {f : ℝ → ℝ → ℂ} (hf : Continuous (Function.uncurry f)) {R : ℝ}
    (hsupp : ∀ t x, R < |x| → f t x = 0) :
    Continuous fun q : ℝ × ℝ => ft (f q.1) q.2 := by
  -- restrict the integral to `[-R, R]`
  have h : (fun q : ℝ × ℝ => ft (f q.1) q.2) = fun q => ∫ x in Set.Icc (-R) R,
      Complex.exp (-(2 * π * Complex.I * (x : ℂ) * (q.2 : ℂ))) * f q.1 x := by
    funext q
    rw [ft, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
    rw [hsupp q.1 x ?_, mul_zero]
    by_contra h
    exact hx (abs_le.1 (not_lt.1 h))
  rw [h]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  have hf' : Continuous fun p : (ℝ × ℝ) × ℝ => f p.1.1 p.2 :=
    hf.comp (continuous_fst.fst.prodMk continuous_snd)
  exact (Complex.continuous_exp.comp (by fun_prop)).mul hf'

/-! ### Slices -/

variable {F : ℝ × ℝ → ℂ} {R M : ℝ}

/-- A function vanishing outside the ball of radius `R` has vanishing directional
derivatives there. -/
theorem fderiv_apply_eq_zero (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) (d : ℝ × ℝ) :
    ∀ p : ℝ × ℝ, R < ‖p‖ → fderiv ℝ F p d = 0 := by
  intro p hp
  have h : F =ᶠ[nhds p] fun _ => 0 :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hp)
      fun q hq => hsupp q hq
  rw [h.fderiv_eq, fderiv_const_apply, zero_apply]

/-- The bounds on a horizontal slice `ζ ↦ F(ζ, z)`. -/
theorem slice_fst {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) (z : ℝ) :
    ContDiff ℝ 2 (fun ζ => F (ζ, z)) ∧ (∀ ζ, R < |ζ| → F (ζ, z) = 0) ∧
      ∀ ζ, ‖iteratedDeriv 2 (fun ζ => F (ζ, z)) ζ‖ ≤ ‖iteratedFDeriv ℝ 2 F (ζ, z)‖ := by
  have hl : (fun ζ => F (ζ, z)) = fun ζ => F ((0, z) + ζ • (1, 0)) := by
    funext ζ
    simp
  refine ⟨(hF.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp),
    fun ζ hζ => hsupp _ (hζ.trans_le (le_max_left _ _)), fun ζ => ?_⟩
  rw [hl, iteratedDeriv_two_comp_line hF]
  have h1 := norm_iteratedFDeriv_fderiv_apply_le (contDiff_fderiv_apply hF (1, 0)) (1, 0) 0
    ((0, z) + ζ • (1, 0))
  have h2 := norm_iteratedFDeriv_fderiv_apply_le hF (1, 0) 1 ((0, z) + ζ • (1, 0))
  simp only [norm_iteratedFDeriv_zero, Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
    one_mul] at h1 h2
  convert h1.trans h2 using 3
  simp

/-- The bounds on a vertical slice `z ↦ F(ζ, z)`. -/
theorem slice_snd {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F)
    (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) (ζ : ℝ) :
    ContDiff ℝ 2 (fun z => F (ζ, z)) ∧ (∀ z, R < |z| → F (ζ, z) = 0) ∧
      ∀ z, ‖iteratedDeriv 2 (fun z => F (ζ, z)) z‖ ≤ ‖iteratedFDeriv ℝ 2 F (ζ, z)‖ := by
  have hl : (fun z => F (ζ, z)) = fun z => F ((ζ, 0) + z • (0, 1)) := by
    funext z
    simp
  refine ⟨(hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp),
    fun z hz => hsupp _ (hz.trans_le (le_max_right _ _)), fun z => ?_⟩
  rw [hl, iteratedDeriv_two_comp_line hF]
  have h1 := norm_iteratedFDeriv_fderiv_apply_le (contDiff_fderiv_apply hF (0, 1)) (0, 1) 0
    ((ζ, 0) + z • (0, 1))
  have h2 := norm_iteratedFDeriv_fderiv_apply_le hF (0, 1) 1 ((ζ, 0) + z • (0, 1))
  simp only [norm_iteratedFDeriv_zero, Prod.norm_def, norm_one, norm_zero, max_eq_right zero_le_one,
    one_mul] at h1 h2
  convert h1.trans h2 using 3
  simp

/-- A slice of a function vanishing outside the ball of radius `R` has vanishing transform
outside `[-R, R]`. -/
theorem ft_slice_eq_zero (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) (v z : ℝ) (hz : R < |z|) :
    ft (fun ζ => F (ζ, z)) v = 0 := by
  have h : ∀ ζ, F (ζ, z) = 0 := fun ζ => hsupp _ (hz.trans_le (le_max_right _ _))
  simp [ft, h]

/-! ### The plane transform -/

/-- The two integrations in `ft2` commute. -/
theorem ft2_swap (hF : Continuous F) (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) (v s : ℝ) :
    ft2 F v s = ft (fun ζ => ft (fun z => F (ζ, z)) s) v := by
  -- the integrand on the plane is continuous with compact support
  have hi : Integrable (Function.uncurry fun z ζ : ℝ =>
      Complex.exp (-(2 * π * Complex.I * (z : ℂ) * (s : ℂ))) *
        (Complex.exp (-(2 * π * Complex.I * (ζ : ℂ) * (v : ℂ))) * F (ζ, z)))
      (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).mul
        ((Complex.continuous_exp.comp (by fun_prop)).mul (hF.comp continuous_swap))
    · refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun p hp => ?_
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hp
      have hp' : R < ‖(p.2, p.1)‖ := by
        rwa [Prod.norm_def, max_comm, ← Prod.norm_def]
      show _ * (_ * F (p.2, p.1)) = 0
      rw [hsupp _ hp', mul_zero, mul_zero]
  simp only [ft2, ft, ← integral_const_mul]
  rw [integral_integral_swap hi]
  congr 1 with ζ
  congr 1 with z
  ring

/-- The basic bounds on `ft2 F`, from two derivatives in each variable separately. -/
theorem norm_ft2_le (hF : ContDiff ℝ ∞ F) (hR : 0 ≤ R) (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0)
    (hM : ∀ n ≤ 2, ∀ p, ‖iteratedFDeriv ℝ n F p‖ ≤ M) (v s : ℝ) :
    ‖ft2 F v s‖ ≤ 4 * R ^ 2 * M ∧ (2 * π * |v|) ^ 2 * ‖ft2 F v s‖ ≤ 4 * R ^ 2 * M ∧
      (2 * π * |s|) ^ 2 * ‖ft2 F v s‖ ≤ 4 * R ^ 2 * M := by
  have hM₀ : ∀ p, ‖F p‖ ≤ M := fun p => by
    simpa using hM 0 (Nat.zero_le _) p
  -- the inner transforms in `ζ`
  have hH₀ : ∀ z, ‖ft (fun ζ => F (ζ, z)) v‖ ≤ 2 * R * M := fun z =>
    norm_ft_le hR (slice_fst hF hsupp z).2.1 (fun ζ => hM₀ _) v
  have hH₂ : ∀ z, (2 * π * |v|) ^ 2 * ‖ft (fun ζ => F (ζ, z)) v‖ ≤ 2 * R * M := fun z =>
    norm_ft_mul_le (slice_fst hF hsupp z).1 hR (slice_fst hF hsupp z).2.1
      (fun ζ => ((slice_fst hF hsupp z).2.2 ζ).trans (hM 2 le_rfl _)) v
  -- the inner transforms in `z`
  have hK₂ : ∀ ζ, (2 * π * |s|) ^ 2 * ‖ft (fun z => F (ζ, z)) s‖ ≤ 2 * R * M := fun ζ =>
    norm_ft_mul_le (slice_snd hF hsupp ζ).1 hR (slice_snd hF hsupp ζ).2.1
      (fun z => ((slice_snd hF hsupp ζ).2.2 z).trans (hM 2 le_rfl _)) s
  have hKsupp : ∀ ζ, R < |ζ| → ft (fun z => F (ζ, z)) s = 0 := fun ζ hζ => by
    have h : ∀ z, F (ζ, z) = 0 := fun z => hsupp _ (hζ.trans_le (le_max_left _ _))
    simp [ft, h]
  refine ⟨?_, ?_, ?_⟩
  · refine (norm_ft_le hR (ft_slice_eq_zero hsupp v) hH₀ s).trans (le_of_eq ?_)
    ring
  · refine (mul_norm_ft_le hR (by positivity) (ft_slice_eq_zero hsupp v) hH₂ s).trans
      (le_of_eq ?_)
    ring
  · rw [ft2_swap hF.continuous hsupp]
    refine (mul_norm_ft_le hR (by positivity) hKsupp hK₂ v).trans (le_of_eq ?_)
    ring

/-- The second derivative of a horizontal slice is `∂₁∂₁F`. -/
theorem iteratedDeriv_slice_fst {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (ζ z : ℝ) :
    iteratedDeriv 2 (fun ζ => F (ζ, z)) ζ =
      fderiv ℝ (fun q => fderiv ℝ F q (1, 0)) (ζ, z) (1, 0) := by
  have hl : (fun ζ => F (ζ, z)) = fun ζ => F ((0, z) + ζ • (1, 0)) := by
    funext ζ
    simp
  rw [hl, iteratedDeriv_two_comp_line hF]
  simp

/-- Order-two decay in both variables: `(1 + |v|)² (1 + |s|)² |ft2 F v s| ≤ 64 R² M` when
`‖D^n F‖ ≤ M` for `n ≤ 4`. -/
theorem norm_ft2_mul_le (hF : ContDiff ℝ ∞ F) (hR : 0 ≤ R)
    (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) (hM : ∀ n ≤ 4, ∀ p, ‖iteratedFDeriv ℝ n F p‖ ≤ M)
    (v s : ℝ) : (1 + |v|) ^ 2 * (1 + |s|) ^ 2 * ‖ft2 F v s‖ ≤ 64 * R ^ 2 * M := by
  -- the mixed term comes from `Ψ = ∂₁∂₁F`
  set Ψ : ℝ × ℝ → ℂ := fun p => fderiv ℝ (fun q => fderiv ℝ F q (1, 0)) p (1, 0) with hΨ
  have hΨc : ContDiff ℝ ∞ Ψ := contDiff_fderiv_apply (contDiff_fderiv_apply hF _) _
  have hΨsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → Ψ p = 0 :=
    fderiv_apply_eq_zero (fderiv_apply_eq_zero hsupp _) _
  have hΨM : ∀ n ≤ 2, ∀ p, ‖iteratedFDeriv ℝ n Ψ p‖ ≤ M := by
    intro n hn p
    have h1 := norm_iteratedFDeriv_fderiv_apply_le (contDiff_fderiv_apply hF (1, 0)) (1, 0) n p
    have h2 := norm_iteratedFDeriv_fderiv_apply_le hF (1, 0) (n + 1) p
    simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, one_mul] at h1 h2
    exact h1.trans (h2.trans (hM _ (by omega) p))
  -- `ft2 Ψ = (2πiv)² ft2 F`
  have hid : ft2 Ψ v s = (2 * π * Complex.I * v) ^ 2 * ft2 F v s := by
    have h : ∀ z, ft (fun ζ => Ψ (ζ, z)) v =
        (2 * π * Complex.I * v) ^ 2 * ft (fun ζ => F (ζ, z)) v := fun z => by
      rw [← ft_iteratedDeriv (slice_fst hF hsupp z).1 (slice_fst hF hsupp z).2.1]
      congr 1 with ζ
      rw [iteratedDeriv_slice_fst hF]
    simp only [ft2, h]
    rw [ft, ft, ← integral_const_mul]
    congr 1 with z
    ring
  have hnorm : ‖ft2 Ψ v s‖ = (2 * π * |v|) ^ 2 * ‖ft2 F v s‖ := by
    rw [hid, norm_mul, norm_pow]
    simp [abs_of_pos pi_pos]
  have hmix := (norm_ft2_le hΨc hR hΨsupp hΨM v s).2.2
  rw [hnorm] at hmix
  obtain ⟨h0, hv, hs⟩ := norm_ft2_le hF hR hsupp (fun n hn => hM n (by omega)) v s
  -- combine the four bounds
  set N := ‖ft2 F v s‖
  have hpi : 1 ≤ (2 * π) ^ 2 := by nlinarith [two_le_pi]
  have hv' : (1 + |v|) ^ 2 ≤ 2 * (1 + (2 * π * |v|) ^ 2) := by
    nlinarith [sq_nonneg (1 - |v|), sq_nonneg |v|]
  have hs' : (1 + |s|) ^ 2 ≤ 2 * (1 + (2 * π * |s|) ^ 2) := by
    nlinarith [sq_nonneg (1 - |s|), sq_nonneg |s|]
  have hN : 0 ≤ N := norm_nonneg _
  calc (1 + |v|) ^ 2 * (1 + |s|) ^ 2 * N
      ≤ 2 * (1 + (2 * π * |v|) ^ 2) * (2 * (1 + (2 * π * |s|) ^ 2)) * N := by gcongr
    _ = 4 * (N + (2 * π * |v|) ^ 2 * N + (2 * π * |s|) ^ 2 * N +
        (2 * π * |s|) ^ 2 * ((2 * π * |v|) ^ 2 * N)) := by ring
    _ ≤ 4 * (4 * R ^ 2 * M + 4 * R ^ 2 * M + 4 * R ^ 2 * M + 4 * R ^ 2 * M) := by gcongr
    _ = 64 * R ^ 2 * M := by ring

/-- `ft2 F` is jointly continuous. -/
theorem continuous_ft2 (hF : Continuous F) (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) :
    Continuous fun q : ℝ × ℝ => ft2 F q.1 q.2 := by
  have h1 : Continuous fun q : ℝ × ℝ => ft (fun ζ => F (ζ, q.1)) q.2 :=
    continuous_ft_param (f := fun z ζ => F (ζ, z)) (hF.comp continuous_swap)
      fun z ζ hζ => hsupp _ (hζ.trans_le (le_max_left _ _))
  exact continuous_ft_param (f := fun v z => ft (fun ζ => F (ζ, z)) v) (h1.comp continuous_swap)
    fun v z hz => ft_slice_eq_zero hsupp v z hz

/-- Inversion on the plane: `F(ζ, z) = ∫ e(ζ v) ∫ e(z s) ft2 F v s ds dv`. -/
theorem ft2_inversion (hF : ContDiff ℝ ∞ F) (hR : 0 ≤ R)
    (hsupp : ∀ p : ℝ × ℝ, R < ‖p‖ → F p = 0) (hM : ∀ n ≤ 4, ∀ p, ‖iteratedFDeriv ℝ n F p‖ ≤ M)
    (ζ z : ℝ) :
    ∫ v : ℝ, Complex.exp (2 * π * Complex.I * (ζ : ℂ) * (v : ℂ)) *
      ∫ s : ℝ, Complex.exp (2 * π * Complex.I * (z : ℂ) * (s : ℂ)) * ft2 F v s = F (ζ, z) := by
  -- invert in `ζ`
  conv_rhs => rw [← ft_inversion (slice_fst hF hsupp z).1 (slice_fst hF hsupp z).2.1 ζ]
  congr 1 with v
  congr 1
  -- then invert `H(z) = ft (F(·, z)) v` in `z`
  set H : ℝ → ℂ := fun z => ft (fun ζ => F (ζ, z)) v with hH
  have hc : Continuous H := (continuous_ft_param (f := fun z ζ => F (ζ, z))
    (hF.continuous.comp continuous_swap) fun z ζ hζ =>
      hsupp _ (hζ.trans_le (le_max_left _ _))).comp (continuous_id.prodMk continuous_const)
  have hi : Integrable H :=
    hc.integrable_of_hasCompactSupport (hasCompactSupport_of_lt_abs (ft_slice_eq_zero hsupp v))
  -- its transform is `ft2 F v`, which decays like `(1 + s²)⁻¹`
  have hFc : Continuous (ft H) :=
    (continuous_ft2 hF.continuous hsupp).comp (continuous_const.prodMk continuous_id)
  have hb : ∀ s, ‖ft H s‖ ≤ 64 * R ^ 2 * M * (1 + s ^ 2)⁻¹ := fun s => by
    have h := norm_ft2_mul_le hF hR hsupp hM v s
    have h1 : 1 ≤ (1 + |v|) ^ 2 := by nlinarith [abs_nonneg v]
    have h2 : 1 + s ^ 2 ≤ (1 + |s|) ^ 2 := by nlinarith [abs_nonneg s, sq_abs s]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have hN : 0 ≤ ‖ft2 F v s‖ := norm_nonneg _
    calc ‖ft H s‖ * (1 + s ^ 2) = (1 + s ^ 2) * ‖ft2 F v s‖ := mul_comm _ _
      _ ≤ (1 + |v|) ^ 2 * (1 + |s|) ^ 2 * ‖ft2 F v s‖ :=
          mul_le_mul_of_nonneg_right (by nlinarith) hN
      _ ≤ 64 * R ^ 2 * M := h
  have hFi : Integrable (ft H) :=
    (integrable_inv_one_add_sq.const_mul _).mono' hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  rw [ft_eq_fourier] at hFi
  have hinv := congrFun (hc.fourierInv_fourier_eq hi hFi) z
  rw [fourierInv_eq_integral, ← ft_eq_fourier] at hinv
  exact hinv

end Erdos408.OneSided.Mellin
