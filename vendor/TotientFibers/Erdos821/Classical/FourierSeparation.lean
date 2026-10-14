import Mathlib
import Erdos821.Blueprint.Classical

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap ContDiff

namespace Erdos821.Classical

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The logarithmic parameter used in the analytic blueprint. -/
def L (x : ℝ) : ℝ := Real.log x

/-- The additive character used in the analytic blueprint. -/
def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)

/-- Fourier separation contract copied from the architect's blueprint. -/
def FourierSeparation : Prop :=
  ∀ b : ℕ, ∀ C R : ℝ, 0 < C → 0 < R → ∀ bounds : ℕ → ℝ,
    (∀ j, 0 ≤ bounds j) → ∃ C' K : ℝ, C < C' ∧ 0 < K ∧
      ∀ A : ℝ, 0 < A → ∃ KA : ℝ, 0 < KA ∧
      ∀ᶠ x : ℝ in atTop, ∀ F : (Fin b → ℝ) → ℂ,
        ContDiff ℝ ∞ F → Function.support F ⊆ Metric.closedBall 0 R →
        (∀ j y, ‖iteratedFDeriv ℝ j F y‖ ≤ bounds j * L x ^ (C * (j + 1))) →
        ∃ a : (Fin b → ℝ) → ℂ,
          Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ K ∧
          (∀ y, F y = ∫ ξ, a ξ * e (∑ i, ξ i * y i)) ∧
          (∫ ξ in {ξ : Fin b → ℝ | L x ^ C' < ‖ξ‖}, ‖a ξ‖) ≤ KA * L x ^ (-A)

private lemma fourier_weighted_pointwise {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (φ : 𝓢(V, ℂ)) (m : ℕ) (ξ : V) :
    ‖ξ‖ ^ m * ‖𝓕 φ ξ‖ ≤
      (2 : ℝ) ^ m *
        ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
          ∫ v : V, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (φ : V → ℂ) v‖ := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (φ.smooth ⊤)
    (fun k j _ _ => φ.integrable_pow_mul_iteratedFDeriv volume k j)
    (k := 0) (n := m) (by simp) (by simp) ξ
  simpa [norm_iteratedFDeriv_zero, ← SchwartzMap.fourier_coe] using h

private lemma integral_derivative_on_ball_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (φ : 𝓢(V, ℂ)) (S B : ℝ) (j : ℕ)
    (hSupport : tsupport (φ : V → ℂ) ⊆ Metric.closedBall 0 S)
    (_hB : 0 ≤ B)
    (hDeriv : ∀ v, ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖ ≤ B) :
    (∫ v : V, ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖) ≤
      (volume (Metric.closedBall (0 : V) S)).toReal * B := by
  have hi : Integrable (fun v : V => ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖) := by
    simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 j
  have he : (∫ v in Metric.closedBall (0 : V) S,
      ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖) =
      ∫ v : V, ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hv' : v ∉ Function.support (iteratedFDeriv ℝ j (φ : V → ℂ)) := by
      intro h
      exact hv (hSupport ((support_iteratedFDeriv_subset j) h))
    simpa only [Function.mem_support, not_not, norm_eq_zero] using hv'
  rw [← he]
  calc
    _ ≤ ∫ _v in Metric.closedBall (0 : V) S, B :=
      integral_mono hi.integrableOn
        (integrableOn_const measure_closedBall_lt_top.ne) hDeriv
    _ = (volume (Metric.closedBall (0 : V) S)).toReal * B := by
      simp [measureReal_def]

private lemma fourier_weighted_pointwise_of_deriv
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (φ : 𝓢(V, ℂ)) (S : ℝ) (hSupport : tsupport (φ : V → ℂ) ⊆ Metric.closedBall 0 S)
    (D : ℕ → ℝ) (hDnonneg : ∀ j, 0 ≤ D j)
    (hD : ∀ j v, ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖ ≤ D j) (m : ℕ) :
    ∀ ξ : V, ‖ξ‖ ^ m * ‖𝓕 φ ξ‖ ≤
      (2 : ℝ) ^ m * (m + 1 : ℝ) *
        (volume (Metric.closedBall (0 : V) S)).toReal *
          ∑ j ∈ Finset.range (m + 1), D j := by
  intro ξ
  have hpoint := fourier_weighted_pointwise φ m ξ
  have hDsum_nonneg : 0 ≤ ∑ j ∈ Finset.range (m + 1), D j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hDnonneg j
  have hsum :
      (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
        ∫ v : V, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (φ : V → ℂ) v‖) ≤
      (m + 1 : ℝ) * (volume (Metric.closedBall (0 : V) S)).toReal *
        ∑ j ∈ Finset.range (m + 1), D j := by
    calc
      _ ≤ ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
          (volume (Metric.closedBall (0 : V) S)).toReal * D p.2 := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have hp₁ : p.1 = 0 := by
          have h := Finset.mem_range.mp hp'.1
          omega
        have hp₂ : p.2 ∈ Finset.range (m + 1) := hp'.2
        rw [hp₁]
        simp only [pow_zero, one_mul]
        exact integral_derivative_on_ball_le φ S (D p.2) p.2 hSupport
          (hDnonneg p.2) (hD p.2)
      _ ≤ ∑ _p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
          (volume (Metric.closedBall (0 : V) S)).toReal *
            (∑ j ∈ Finset.range (m + 1), D j) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_product.mp hp
        have hp₂ : p.2 ∈ Finset.range (m + 1) := hp'.2
        have hsingle : D p.2 ≤ ∑ j ∈ Finset.range (m + 1), D j :=
          Finset.single_le_sum (fun j hj => hDnonneg j) hp₂
        gcongr
      _ = (m + 1 : ℝ) * (volume (Metric.closedBall (0 : V) S)).toReal *
          ∑ j ∈ Finset.range (m + 1), D j := by
        simp [mul_assoc]
  calc
    _ ≤ (2 : ℝ) ^ m *
        (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
          ∫ v : V, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (φ : V → ℂ) v‖) := hpoint
    _ ≤ (2 : ℝ) ^ m * ((m + 1 : ℝ) *
        (volume (Metric.closedBall (0 : V) S)).toReal *
        ∑ j ∈ Finset.range (m + 1), D j) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

private lemma fourier_moment_integral_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (φ : 𝓢(V, ℂ)) (q m : ℕ) (hq : Module.finrank ℝ V < q)
    (B₀ Bmq : ℝ)
    (h₀ : ∀ ξ : V, ‖𝓕 φ ξ‖ ≤ B₀)
    (hmq : ∀ ξ : V, ‖ξ‖ ^ (m + q) * ‖𝓕 φ ξ‖ ≤ Bmq) :
    (∫ ξ : V, ‖ξ‖ ^ m * ‖𝓕 φ ξ‖) ≤
      (2 : ℝ) ^ q * (B₀ + Bmq) *
        ∫ ξ : V, (1 + ‖ξ‖) ^ (-(q : ℝ)) := by
  have hweight : Integrable (fun ξ : V => (1 + ‖ξ‖) ^ (-(q : ℝ))) := by
    apply integrable_one_add_norm
    exact_mod_cast hq
  have hfourier : Integrable (fun ξ : V => ‖ξ‖ ^ m * ‖𝓕 φ ξ‖) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 φ).integrable_pow_mul volume m
  calc
    _ ≤ ∫ ξ : V, (2 : ℝ) ^ q * (B₀ + Bmq) * (1 + ‖ξ‖) ^ (-(q : ℝ)) := by
      apply integral_mono hfourier (hweight.const_mul ((2 : ℝ) ^ q * (B₀ + Bmq)))
      intro ξ
      exact pow_mul_le_of_le_of_pow_mul_le (norm_nonneg ξ) (norm_nonneg _)
        (h₀ ξ) (hmq ξ)
    _ = (2 : ℝ) ^ q * (B₀ + Bmq) *
        ∫ ξ : V, (1 + ‖ξ‖) ^ (-(q : ℝ)) := by
      rw [integral_const_mul]

private lemma coordinate_norm_le_euclidean (b : ℕ) (ξ : Fin b → ℝ) :
    ‖ξ‖ ≤ ‖(WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin b))‖ := by
  change ((Finset.univ.sup (fun i : Fin b => ‖ξ i‖₊) : NNReal) : ℝ) ≤
    ((‖(WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin b))‖₊ : NNReal) : ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i hi
  exact_mod_cast PiLp.norm_apply_le (WithLp.toLp 2 ξ) i

private lemma inner_toLp_coord (b : ℕ) (ξ y : Fin b → ℝ) :
    inner ℝ (WithLp.toLp 2 ξ : EuclideanSpace ℝ (Fin b)) (WithLp.toLp 2 y) =
      ∑ i, ξ i * y i := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

private lemma tail_integral_le_moment
    {P V : Type*} [NormedAddCommGroup P] [MeasurableSpace P] [BorelSpace P]
    [NormedAddCommGroup V]
    {μ : Measure P} {a : P → ℂ} {toV : P → V} (ha : Integrable a μ)
    (m : ℕ) (T : ℝ) (hT : 0 < T)
    (hcoord : ∀ ξ, ‖ξ‖ ≤ ‖toV ξ‖)
    (hmom : Integrable (fun ξ => ‖toV ξ‖ ^ m * ‖a ξ‖) μ) :
    (∫ ξ in {ξ : P | T < ‖ξ‖}, ‖a ξ‖ ∂μ) ≤
      (T ^ m)⁻¹ * ∫ ξ, ‖toV ξ‖ ^ m * ‖a ξ‖ ∂μ := by
  let s : Set P := {ξ : P | T < ‖ξ‖}
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const (continuous_norm.measurable)
  have hInv : 0 ≤ (T ^ m)⁻¹ := (inv_nonneg.mpr (pow_nonneg hT.le _))
  have hpoint :
      (fun ξ => ‖a ξ‖) ≤ᵐ[μ.restrict s]
        fun ξ => (T ^ m)⁻¹ * (‖toV ξ‖ ^ m * ‖a ξ‖) := by
    filter_upwards [ae_restrict_mem hs] with ξ hξ
    have hnorm : T ≤ ‖toV ξ‖ := (hξ.trans_le (hcoord ξ)).le
    have hp : T ^ m ≤ ‖toV ξ‖ ^ m := pow_le_pow_left₀ hT.le hnorm m
    have hm : (T ^ m) * ‖a ξ‖ ≤ ‖toV ξ‖ ^ m * ‖a ξ‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    have hm' : ‖a ξ‖ * T ^ m ≤ ‖toV ξ‖ ^ m * ‖a ξ‖ := by
      simpa [mul_comm] using hm
    have hd : ‖a ξ‖ ≤ (‖toV ξ‖ ^ m * ‖a ξ‖) / (T ^ m) :=
      (le_div_iff₀ (pow_pos hT m)).2 hm'
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hd
  calc
    _ ≤ ∫ ξ in s, (T ^ m)⁻¹ * (‖toV ξ‖ ^ m * ‖a ξ‖) ∂μ := by
      simpa only [s] using
        integral_mono_ae ha.norm.restrict (hmom.const_mul (T ^ m)⁻¹).restrict hpoint
    _ ≤ ∫ ξ, (T ^ m)⁻¹ * (‖toV ξ‖ ^ m * ‖a ξ‖) ∂μ := by
      refine setIntegral_le_integral (s := s) (hmom.const_mul (T ^ m)⁻¹) ?_
      filter_upwards with ξ
      exact mul_nonneg hInv (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))
    _ = (T ^ m)⁻¹ * ∫ ξ, ‖toV ξ‖ ^ m * ‖a ξ‖ ∂μ := by
      rw [integral_const_mul]

theorem lem_fourier_separation : FourierSeparation := by
  intro b C R hC hR bounds hBounds
  let V := EuclideanSpace ℝ (Fin b)
  let c : V ≃L[ℝ] (Fin b → ℝ) := EuclideanSpace.equiv (Fin b) ℝ
  let cNorm : ℝ := ‖(c : V →L[ℝ] (Fin b → ℝ))‖
  let S : ℝ := R * (‖(c.symm : (Fin b → ℝ) →L[ℝ] V)‖ + 1)
  let q : ℕ := b + 1
  let vol : ℝ := (volume (Metric.closedBall (0 : V) S)).toReal
  let W : ℝ := ∫ ξ : V, (1 + ‖ξ‖) ^ (-(q : ℝ))
  let H (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), bounds j * cNorm ^ j
  let B (n : ℕ) : ℝ := (2 : ℝ) ^ n * (n + 1 : ℝ) * vol * H n
  let M (n : ℕ) : ℝ := (2 : ℝ) ^ q * W * (B 0 + B (n + q))
  let K : ℝ := C * ((q : ℝ) + 1) + 1
  have hqfin : Module.finrank ℝ V < q := by
    simp [V, q]
  have hWint : Integrable (fun ξ : V => (1 + ‖ξ‖) ^ (-(q : ℝ))) := by
    apply integrable_one_add_norm
    exact_mod_cast hqfin
  have hWnonneg : 0 ≤ W := by
    exact integral_nonneg (fun ξ => by positivity)
  have hvol : 0 ≤ vol := by
    exact ENNReal.toReal_nonneg
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hHnonneg (n : ℕ) : 0 ≤ H n := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hBounds j) (pow_nonneg (norm_nonneg _) _)
  have hBnonneg (n : ℕ) : 0 ≤ B n := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hvol)
      (hHnonneg n)
  have hMnonneg (n : ℕ) : 0 ≤ M n := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg (by positivity) hWnonneg)
      (add_nonneg (hBnonneg 0) (hBnonneg (n + q)))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hlarge : ∀ᶠ x : ℝ in atTop, max (M 0 + 1) 1 ≤ L x := by
    apply Filter.eventually_atTop.2
    refine ⟨Real.exp (max (M 0 + 1) 1), ?_⟩
    intro x hx
    dsimp [L]
    calc
      max (M 0 + 1) 1 = Real.log (Real.exp (max (M 0 + 1) 1)) := by rw [Real.log_exp]
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) hx
  refine ⟨C + 1, K, by linarith, hK, ?_⟩
  intro A hA
  have hdelta : 0 < (C + 1) - C := by norm_num
  obtain ⟨m, hmratio⟩ := exists_nat_gt ((A + C * ((q : ℝ) + 1)) / ((C + 1) - C))
  have hmprod : A + C * ((q : ℝ) + 1) < (m : ℝ) * ((C + 1) - C) := by
    exact (div_lt_iff₀ hdelta).mp hmratio
  have hmcast : ((m + q + 1 : ℕ) : ℝ) = (m : ℝ) + (q : ℝ) + 1 := by norm_cast
  have hExp : C * ((m + q + 1 : ℕ) : ℝ) - (C + 1) * (m : ℝ) ≤ -A := by
    rw [hmcast]
    have heq : C * ((m : ℝ) + (q : ℝ) + 1) - (C + 1) * (m : ℝ) =
        C * ((q : ℝ) + 1) - ((C + 1) - C) * (m : ℝ) := by ring
    rw [heq]
    nlinarith
  let KA : ℝ := M m + 1
  have hKA : 0 < KA := by
    dsimp [KA]
    linarith [hMnonneg m]
  refine ⟨KA, hKA, ?_⟩
  filter_upwards [hlarge] with x hxlarge
  have hL : 1 ≤ L x := le_trans (le_max_right (M 0 + 1) 1) hxlarge
  have hMassThreshold : M 0 + 1 ≤ L x := le_trans (le_max_left (M 0 + 1) 1) hxlarge
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  intro F hF hFSupp hFDeriv
  let G : V → ℂ := fun v => F (c v)
  have hGcont : ContDiff ℝ ∞ G := by
    simpa [G, Function.comp_def] using
      hF.comp_continuousLinearMap (g := (c : V →L[ℝ] (Fin b → ℝ)))
  have hGsup : Function.support G ⊆ Metric.closedBall (0 : V) S := by
    intro v hv
    have hFne : F (c v) ≠ 0 := by
      change G v ≠ 0 at hv
      simpa [G] using hv
    have hFmem : c v ∈ Function.support F := by
      simpa only [Function.mem_support] using hFne
    have hFball := hFSupp hFmem
    have hFnorm : ‖c v‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hFball
    have hvnorm : ‖v‖ ≤ ‖(c.symm : (Fin b → ℝ) →L[ℝ] V)‖ * ‖c v‖ := by
      calc
        ‖v‖ = ‖c.symm (c v)‖ := by rw [c.symm_apply_apply]
        _ ≤ ‖(c.symm : (Fin b → ℝ) →L[ℝ] V)‖ * ‖c v‖ :=
          (c.symm : (Fin b → ℝ) →L[ℝ] V).le_opNorm (c v)
    have hbound : ‖v‖ ≤ ‖(c.symm : (Fin b → ℝ) →L[ℝ] V)‖ * R :=
      le_trans hvnorm (mul_le_mul_of_nonneg_left hFnorm (norm_nonneg _))
    apply Metric.mem_closedBall.mpr
    rw [dist_zero_right]
    dsimp [S]
    nlinarith [norm_nonneg (c.symm : (Fin b → ℝ) →L[ℝ] V), hR]
  have hGcompact : HasCompactSupport G :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : V) S) hGsup
  have hGts : tsupport G ⊆ Metric.closedBall (0 : V) S := by
    change closure (Function.support G) ⊆ Metric.closedBall (0 : V) S
    exact closure_minimal hGsup Metric.isClosed_closedBall
  let φ : 𝓢(V, ℂ) := hGcompact.toSchwartzMap (hGcont.of_le (by simp))
  let φhat : 𝓢(V, ℂ) := 𝓕 φ
  have hφts : tsupport (φ : V → ℂ) ⊆ Metric.closedBall (0 : V) S := by
    change tsupport G ⊆ Metric.closedBall (0 : V) S
    exact hGts
  let D (j : ℕ) : ℝ := bounds j * (L x) ^ (C * ((j : ℝ) + 1)) * cNorm ^ j
  have hDnonneg (j : ℕ) : 0 ≤ D j := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (hBounds j) (Real.rpow_nonneg (le_trans zero_le_one hL) _))
      (pow_nonneg (norm_nonneg _) _)
  have hDφ (j : ℕ) (v : V) :
      ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖ ≤ D j := by
    have hcomp : iteratedFDeriv ℝ j G v =
        (iteratedFDeriv ℝ j F (c v)).compContinuousLinearMap
          (fun _ : Fin j => (c : V →L[ℝ] (Fin b → ℝ))) := by
      simpa [G, Function.comp_def, ContinuousLinearEquiv.coe_coe] using
        (c : V →L[ℝ] (Fin b → ℝ)).iteratedFDeriv_comp_right
          (n := ∞) hF v (by simp)
    calc
      ‖iteratedFDeriv ℝ j (φ : V → ℂ) v‖ =
          ‖(iteratedFDeriv ℝ j F (c v)).compContinuousLinearMap
            (fun _ : Fin j => (c : V →L[ℝ] (Fin b → ℝ)))‖ := by
              change ‖iteratedFDeriv ℝ j G v‖ = _
              rw [hcomp]
      _ ≤ ‖iteratedFDeriv ℝ j F (c v)‖ *
          ∏ _ : Fin j, ‖(c : V →L[ℝ] (Fin b → ℝ))‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ j F (c v)‖ * cNorm ^ j := by simp [cNorm]
      _ ≤ (bounds j * (L x) ^ (C * ((j : ℝ) + 1))) * cNorm ^ j :=
        mul_le_mul_of_nonneg_right (hFDeriv j (c v)) (pow_nonneg (norm_nonneg _) _)
      _ = D j := rfl
  have hsumD (n : ℕ) :
      (∑ j ∈ Finset.range (n + 1), D j) ≤ H n * (L x) ^ (C * ((n : ℝ) + 1)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          (bounds j * cNorm ^ j) * (L x) ^ (C * ((n : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjle : j ≤ n := by
          have hh := Finset.mem_range.mp hj
          omega
        have hexp : C * ((j : ℝ) + 1) ≤ C * ((n : ℝ) + 1) := by
          gcongr
        have hpow := Real.rpow_le_rpow_of_exponent_le hL hexp
        calc
          D j = (bounds j * cNorm ^ j) * (L x) ^ (C * ((j : ℝ) + 1)) := by
            dsimp [D]
            ring
          _ ≤ (bounds j * cNorm ^ j) * (L x) ^ (C * ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hpow
              (mul_nonneg (hBounds j) (pow_nonneg (norm_nonneg _) _))
      _ = H n * (L x) ^ (C * ((n : ℝ) + 1)) := by
        dsimp [H]
        rw [Finset.sum_mul]
  have hpoint (n : ℕ) (ξ : V) :
      ‖ξ‖ ^ n * ‖𝓕 φ ξ‖ ≤ B n * (L x) ^ (C * ((n : ℝ) + 1)) := by
    have hbase := fourier_weighted_pointwise_of_deriv φ S hφts D hDnonneg hDφ n ξ
    calc
      _ ≤ (2 : ℝ) ^ n * (n + 1 : ℝ) * vol *
          ∑ j ∈ Finset.range (n + 1), D j := hbase
      _ ≤ (2 : ℝ) ^ n * (n + 1 : ℝ) * vol *
          (H n * (L x) ^ (C * ((n : ℝ) + 1))) := by
        exact mul_le_mul_of_nonneg_left (hsumD n)
          (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hvol)
      _ = B n * (L x) ^ (C * ((n : ℝ) + 1)) := by
        dsimp [B]
        ring
  have hmoment (n : ℕ) :
      (∫ ξ : V, ‖ξ‖ ^ n * ‖𝓕 φ ξ‖) ≤
        M n * (L x) ^ (C * ((n + q : ℝ) + 1)) := by
    have h0 (ξ : V) : ‖𝓕 φ ξ‖ ≤ B 0 * (L x) ^ C := by
      have hh := hpoint 0 ξ
      simpa using hh
    have hmq (ξ : V) :
        ‖ξ‖ ^ (n + q) * ‖𝓕 φ ξ‖ ≤
          B (n + q) * (L x) ^ (C * ((n + q : ℝ) + 1)) := by
      simpa [Nat.cast_add] using hpoint (n + q) ξ
    have hbase := fourier_moment_integral_bound φ q n hqfin
      (B 0 * (L x) ^ C)
      (B (n + q) * (L x) ^ (C * ((n + q : ℝ) + 1))) h0 hmq
    have hexp : C ≤ C * ((n + q : ℝ) + 1) := by
      have hnq : 0 ≤ (n + q : ℝ) := by positivity
      have hone : (1 : ℝ) ≤ (n + q : ℝ) + 1 := by linarith
      nlinarith [hC, hone]
    have hpow : (L x) ^ C ≤ (L x) ^ (C * ((n + q : ℝ) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hL hexp
    have hsum :
        B 0 * (L x) ^ C + B (n + q) * (L x) ^ (C * ((n + q : ℝ) + 1)) ≤
          (B 0 + B (n + q)) * (L x) ^ (C * ((n + q : ℝ) + 1)) := by
      calc
        _ ≤ B 0 * (L x) ^ (C * ((n + q : ℝ) + 1)) +
            B (n + q) * (L x) ^ (C * ((n + q : ℝ) + 1)) := by
          exact add_le_add_left (mul_le_mul_of_nonneg_left hpow (hBnonneg 0)) _
        _ = _ := by ring
    calc
      _ ≤ (2 : ℝ) ^ q *
          (B 0 * (L x) ^ C +
            B (n + q) * (L x) ^ (C * ((n + q : ℝ) + 1))) * W := by
        simpa [W] using hbase
      _ ≤ (2 : ℝ) ^ q *
          ((B 0 + B (n + q)) * (L x) ^ (C * ((n + q : ℝ) + 1))) * W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum (by positivity)) hWnonneg
      _ = M n * (L x) ^ (C * ((n + q : ℝ) + 1)) := by
        dsimp [M]
        ring
  let toV : (Fin b → ℝ) → V := fun ξ => WithLp.toLp 2 ξ
  have hmp : MeasurePreserving toV volume (volume : Measure V) := by
    simpa [toV, V] using (PiLp.volume_preserving_toLp (Fin b))
  have hme : MeasurableEmbedding toV := by
    change MeasurableEmbedding
      (WithLp.toLp 2 : (Fin b → ℝ) → WithLp 2 (Fin b → ℝ))
    exact (MeasurableEquiv.toLp 2 (Fin b → ℝ)).measurableEmbedding
  have hmassEuclid :
      (∫ ξ : V, ‖φhat ξ‖) ≤ M 0 * (L x) ^ (C * ((q : ℝ) + 1)) := by
    have hh := hmoment 0
    simpa [φhat] using hh
  let a : (Fin b → ℝ) → ℂ := fun ξ => φhat (toV ξ)
  have ha : Integrable a volume := by
    change Integrable (fun ξ => φhat (toV ξ)) volume
    have hFT : Integrable (φhat : V → ℂ) volume := φhat.integrable
    exact hmp.integrable_comp_of_integrable hFT
  have hmassEq :
      (∫ ξ : Fin b → ℝ, ‖a ξ‖) = ∫ ξ : V, ‖φhat ξ‖ := by
    calc
      _ = ∫ ξ : Fin b → ℝ, (fun v : V => ‖φhat v‖) (toV ξ) := by
        apply integral_congr_ae
        filter_upwards with ξ
        simp [a]
      _ = _ := hmp.integral_comp hme (fun v : V => ‖φhat v‖)
  have hmass : (∫ ξ : Fin b → ℝ, ‖a ξ‖) ≤ (L x) ^ K := by
    rw [hmassEq]
    have hMle : M 0 ≤ L x := by linarith [hMassThreshold]
    calc
      _ ≤ M 0 * (L x) ^ (C * ((q : ℝ) + 1)) := hmassEuclid
      _ ≤ (L x) * (L x) ^ (C * ((q : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hMle
          (Real.rpow_nonneg (le_trans zero_le_one hL) _)
      _ = (L x) ^ K := by
        dsimp [K]
        calc
          _ = (L x) ^ (C * ((q : ℝ) + 1)) * (L x) := by ring
          _ = (L x) ^ (C * ((q : ℝ) + 1) + 1) := by
            calc
              _ = (L x) ^ (C * ((q : ℝ) + 1)) * (L x) ^ (1 : ℝ) := by simp
              _ = _ := (Real.rpow_add hLpos (C * ((q : ℝ) + 1)) 1).symm
  have hmomRawInt (n : ℕ) :
      Integrable (fun ξ : Fin b → ℝ => ‖toV ξ‖ ^ n * ‖a ξ‖) volume := by
    change Integrable
      (fun ξ => ‖toV ξ‖ ^ n * ‖φhat (toV ξ)‖) volume
    exact hmp.integrable_comp_of_integrable (φhat.integrable_pow_mul volume n)
  have hmomEq (n : ℕ) :
      (∫ ξ : Fin b → ℝ, ‖toV ξ‖ ^ n * ‖a ξ‖) =
        ∫ ξ : V, ‖ξ‖ ^ n * ‖φhat ξ‖ := by
    calc
      _ = ∫ ξ : Fin b → ℝ,
          (fun v : V => ‖v‖ ^ n * ‖φhat v‖) (toV ξ) := by
        apply integral_congr_ae
        filter_upwards with ξ
        simp [a]
      _ = _ := hmp.integral_comp hme
        (fun ξ : V => ‖ξ‖ ^ n * ‖φhat ξ‖)
  have htail :
      (∫ ξ in {ξ : Fin b → ℝ | (L x) ^ (C + 1) < ‖ξ‖}, ‖a ξ‖) ≤
        (((L x) ^ (C + 1)) ^ m)⁻¹ * (M m *
          (L x) ^ (C * ((m + q : ℝ) + 1))) := by
    have htail0 := tail_integral_le_moment ha m ((L x) ^ (C + 1))
      (Real.rpow_pos_of_pos hLpos _) (by
        intro ξ
        simpa [toV] using coordinate_norm_le_euclidean b ξ)
      (hmomRawInt m)
    rw [hmomEq m] at htail0
    calc
      _ ≤ (((L x) ^ (C + 1)) ^ m)⁻¹ *
          ∫ ξ : V, ‖ξ‖ ^ m * ‖𝓕 φ ξ‖ := htail0
      _ ≤ (((L x) ^ (C + 1)) ^ m)⁻¹ *
          (M m * (L x) ^ (C * ((m + q : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (by simpa [φhat] using hmoment m)
          (inv_nonneg.mpr (pow_nonneg
            (Real.rpow_nonneg (le_trans zero_le_one hL) _) _))
  have hcutPow : ((L x) ^ (C + 1)) ^ m = (L x) ^ ((C + 1) * (m : ℝ)) := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (le_trans zero_le_one hL) (C + 1) (m : ℝ)]
  have hcutInv : (((L x) ^ (C + 1)) ^ m)⁻¹ =
      (L x) ^ (-((C + 1) * (m : ℝ))) := by
    rw [hcutPow, ← Real.rpow_neg (le_trans zero_le_one hL)]
  have hExp' : C * ((m + q : ℝ) + 1) - (C + 1) * (m : ℝ) ≤ -A := by
    have hcast : (m + q : ℝ) + 1 = ((m + q + 1 : ℕ) : ℝ) := by norm_cast
    rw [hcast]
    exact hExp
  have htailFinal :
      (∫ ξ in {ξ : Fin b → ℝ | (L x) ^ (C + 1) < ‖ξ‖}, ‖a ξ‖) ≤
        KA * (L x) ^ (-A) := by
    calc
      _ ≤ M m * (L x) ^ (C * ((m + q : ℝ) + 1) - (C + 1) * (m : ℝ)) := by
        calc
          _ ≤ (((L x) ^ (C + 1)) ^ m)⁻¹ *
              (M m * (L x) ^ (C * ((m + q : ℝ) + 1))) := htail
          _ = M m * (L x) ^ (C * ((m + q : ℝ) + 1) - (C + 1) * (m : ℝ)) := by
            rw [hcutInv]
            calc
              _ = M m * ((L x) ^ (-((C + 1) * (m : ℝ))) *
                  (L x) ^ (C * ((m + q : ℝ) + 1))) := by ring
              _ = M m * (L x) ^ (-((C + 1) * (m : ℝ)) +
                  C * ((m + q : ℝ) + 1)) := by
                rw [← Real.rpow_add hLpos]
              _ = _ := by
                congr 2
                ring
      _ ≤ KA * (L x) ^ (-A) := by
        calc
          _ ≤ KA * (L x) ^ (C * ((m + q : ℝ) + 1) - (C + 1) * (m : ℝ)) :=
            mul_le_mul_of_nonneg_right (by dsimp [KA]; linarith)
              (Real.rpow_nonneg (le_trans zero_le_one hL) _)
          _ ≤ KA * (L x) ^ (-A) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hExp') hKA.le
  refine ⟨a, ha, hmass, ?_, htailFinal⟩
  intro y
  have hinv : (𝓕⁻ (𝓕 φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ)) = φ :=
    FourierTransform.fourierInv_fourier_eq φ
  have hEval := congrArg (fun f : 𝓢(V, ℂ) => f (toV y)) hinv
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', smul_eq_mul] at hEval
  have hIntegral :
      (∫ ξ : Fin b → ℝ, a ξ * e (∑ i, ξ i * y i)) =
        ∫ v : V, (𝓕 φ v) * Complex.exp
          (↑(2 * Real.pi * inner ℝ v (toV y)) * Complex.I) := by
    calc
      _ = ∫ ξ : Fin b → ℝ,
          (fun v : V => (𝓕 φ v) * Complex.exp
            (↑(2 * Real.pi * inner ℝ v (toV y)) * Complex.I)) (toV ξ) := by
        apply integral_congr_ae
        filter_upwards with ξ
        have hinner : inner ℝ (toV ξ) (toV y) = ∑ i, ξ i * y i := by
          simpa [toV] using inner_toLp_coord b ξ y
        simp [a, φhat, e, hinner, mul_comm]
      _ = _ := hmp.integral_comp hme
        (fun v : V => φhat v * Complex.exp
          (↑(2 * Real.pi * inner ℝ v (toV y)) * Complex.I))
  calc
    F y = (φ : V → ℂ) (toV y) := by
      change F y = G (toV y)
      change F y = F (c (toV y))
      have hctoy : c (toV y) = y := by
        change WithLp.ofLp (WithLp.toLp 2 y) = y
        rfl
      rw [hctoy]
    _ = ∫ v : V, (𝓕 φ v) * Complex.exp
          (↑(2 * Real.pi * inner ℝ v (toV y)) * Complex.I) := by
      calc
        _ = ∫ v : V, Complex.exp
              (↑(2 * Real.pi * inner ℝ v (toV y)) * Complex.I) * (𝓕 φ v) := hEval.symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards with v
          ring
    _ = ∫ ξ : Fin b → ℝ, a ξ * e (∑ i, ξ i * y i) := hIntegral.symm

theorem blueprint_lem_fourier_separation : Erdos821.Blueprint.FourierSeparation := by
  exact lem_fourier_separation

end

end Erdos821.Classical

