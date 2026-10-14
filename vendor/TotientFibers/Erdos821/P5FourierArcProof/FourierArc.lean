import Erdos821.P5.FourierArcTask
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical ComplexConjugate
open MeasureTheory

namespace Erdos821.P5FourierArcProof

open Erdos821.P5Core
open Blueprint.Analytic

lemma integral_e_int (q : ℤ) :
    (∫ θ in (0 : ℝ)..1, e (θ * (q : ℝ))) = if q = 0 then 1 else 0 := by
  by_cases hq : q = 0
  · subst q
    simp [Blueprint.Analytic.e]
  · have hcoef : ((2 * Real.pi * (q : ℝ)) * Complex.I : ℂ) ≠ 0 := by
      have hreal : 2 * Real.pi * (q : ℝ) ≠ 0 := by
        apply mul_ne_zero
        · apply mul_ne_zero
          · norm_num
          · exact Real.pi_ne_zero
        · exact_mod_cast hq
      exact mul_ne_zero (by exact_mod_cast hreal) Complex.I_ne_zero
    have hperiod : Complex.exp (2 * (Real.pi : ℂ) * (q : ℂ) * Complex.I) = 1 := by
      have hcast : 2 * (Real.pi : ℂ) * (q : ℂ) * Complex.I =
          (q : ℂ) * (2 * Real.pi * Complex.I) := by ring
      rw [hcast]
      exact Complex.exp_int_mul_two_pi_mul_I q
    rw [show (fun θ : ℝ => e (θ * (q : ℝ))) =
        (fun θ : ℝ => Complex.exp (((2 * Real.pi * (q : ℝ)) * Complex.I) * θ)) by
          funext θ
          simp only [Blueprint.Analytic.e]
          congr 1
          push_cast
          ring]
    rw [integral_exp_mul_complex hcoef]
    simp [hq, hperiod]

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [Blueprint.Analytic.e]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

@[simp] lemma e_zero : e 0 = 1 := by
  simp [Blueprint.Analytic.e]

lemma star_e (x : ℝ) : star (e x) = e (-x) := by
  simp only [Blueprint.Analytic.e]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.star_exp]
  congr 1
  simp [star_mul]
  ring

@[fun_prop] lemma continuous_e : Continuous e := by
  unfold Blueprint.Analytic.e
  fun_prop

@[fun_prop] lemma continuous_integerAdditivePolynomial (s : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (integerAdditivePolynomial s a) := by
  unfold integerAdditivePolynomial
  fun_prop

lemma e_mul3 (x y z : ℝ) : e x * e y * e z = e (x + y + z) := by
  rw [← e_add x y, ← e_add (x + y) z]

lemma shift_integrand_expansion (s t : Finset ℤ) (a b : ℤ → ℂ) (d : ℤ) (θ : ℝ) :
    star (integerAdditivePolynomial s a θ) * integerAdditivePolynomial t b θ * e (-θ * d) =
      ∑ n ∈ s, ∑ m ∈ t,
        (star (a n) * b m) * e (θ * ((m - n - d : ℤ) : ℝ)) := by
  simp only [integerAdditivePolynomial, star_sum, star_mul, star_e]
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _hn
  apply Finset.sum_congr rfl
  intro m _hm
  calc
    _ = (star (a n) * b m) * (e (-θ * n) * e (θ * m) * e (-θ * d)) := by ring
    _ = (star (a n) * b m) * e (θ * ((m - n - d : ℤ) : ℝ)) := by
      rw [e_mul3]
      congr 1
      push_cast
      ring

lemma shift_correlation_proof (s t : Finset ℤ) (a b : ℤ → ℂ) (d : ℤ) :
    (∑ n ∈ s, ∑ m ∈ t, if m = n + d then star (a n) * b m else 0) =
      ∫ θ in (0 : ℝ)..1,
        star (integerAdditivePolynomial s a θ) * integerAdditivePolynomial t b θ * e (-θ * d) := by
  symm
  calc
    ∫ θ in (0 : ℝ)..1,
        star (integerAdditivePolynomial s a θ) * integerAdditivePolynomial t b θ * e (-θ * d) =
      ∫ θ in (0 : ℝ)..1,
        ∑ n ∈ s, ∑ m ∈ t,
          (star (a n) * b m) * e (θ * ((m - n - d : ℤ) : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro θ _hθ
        exact shift_integrand_expansion s t a b d θ
    _ = ∑ n ∈ s, ∑ m ∈ t,
          (star (a n) * b m) *
            (∫ θ in (0 : ℝ)..1, e (θ * ((m - n - d : ℤ) : ℝ))) := by
        have hout : ∀ n ∈ s, IntervalIntegrable
            (fun θ => ∑ m ∈ t,
              (star (a n) * b m) * e (θ * ((m - n - d : ℤ) : ℝ))) volume 0 1 := by
          intro n _hn
          apply Continuous.intervalIntegrable
          fun_prop
        rw [intervalIntegral.integral_finsetSum hout]
        apply Finset.sum_congr rfl
        intro n _hn
        have hin : ∀ m ∈ t, IntervalIntegrable
            (fun θ => (star (a n) * b m) * e (θ * ((m - n - d : ℤ) : ℝ))) volume 0 1 := by
          intro m _hm
          apply Continuous.intervalIntegrable
          fun_prop
        rw [intervalIntegral.integral_finsetSum hin]
        apply Finset.sum_congr rfl
        intro m _hm
        rw [intervalIntegral.integral_const_mul]
    _ = ∑ n ∈ s, ∑ m ∈ t,
          if m = n + d then star (a n) * b m else 0 := by
        apply Finset.sum_congr rfl
        intro n _hn
        apply Finset.sum_congr rfl
        intro m _hm
        rw [integral_e_int]
        by_cases hmn : m = n + d
        · simp [hmn]
        · have hzero : m - n - d ≠ 0 := by omega
          simp [hmn, hzero]

lemma re_star_mul_self (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_re]
  exact Complex.normSq_eq_norm_sq z

lemma sum_re_star_mul_self (s : Finset ℤ) (a : ℤ → ℂ) :
    (∑ n ∈ s, star (a n) * a n).re = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      simp only [Finset.sum_insert hn, Complex.add_re, re_star_mul_self]
      rw [ih]

lemma parseval_proof (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ θ in (0 : ℝ)..1, ‖integerAdditivePolynomial s a θ‖ ^ 2) =
      ∑ n ∈ s, ‖a n‖ ^ 2 := by
  let P := fun θ => integerAdditivePolynomial s a θ
  have hdiag :
      (∑ n ∈ s, ∑ m ∈ s, if m = n then star (a n) * a m else 0) =
        ∑ n ∈ s, star (a n) * a n := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [hn]
  have hshift := shift_correlation_proof s s a a 0
  simp only [add_zero] at hshift
  rw [hdiag] at hshift
  simp only [Int.cast_zero, mul_zero, e_zero, mul_one] at hshift
  have hP : Continuous (integerAdditivePolynomial s a) :=
    continuous_integerAdditivePolynomial s a
  have hcont : Continuous (fun θ =>
      star (integerAdditivePolynomial s a θ) * integerAdditivePolynomial s a θ) := by
    fun_prop
  have hInt : IntervalIntegrable (fun θ => star (P θ) * P θ) volume 0 1 :=
    hcont.intervalIntegrable (μ := volume) 0 1
  have hRe :
      (∫ θ in (0 : ℝ)..1, (star (P θ) * P θ).re) =
        (∫ θ in (0 : ℝ)..1, star (P θ) * P θ).re := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_re hInt.1
  have hsumRe :
      (∑ n ∈ s, star (a n) * a n).re = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    exact sum_re_star_mul_self s a
  calc
    ∫ θ in (0 : ℝ)..1, ‖P θ‖ ^ 2 =
      ∫ θ in (0 : ℝ)..1, (star (P θ) * P θ).re := by
        apply intervalIntegral.integral_congr
        intro θ _hθ
        exact (re_star_mul_self (integerAdditivePolynomial s a θ)).symm
    _ = (∫ θ in (0 : ℝ)..1, star (P θ) * P θ).re := hRe
    _ = (∑ n ∈ s, star (a n) * a n).re := congrArg Complex.re hshift |>.symm
    _ = ∑ n ∈ s, ‖a n‖ ^ 2 := hsumRe

lemma integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ)
    (hIntA : (∫ x, f x ^ 2 ∂μ) ≤ A)
    (hIntB : (∫ x, g x ^ 2 ∂μ) ≤ B) :
    (∫ x, f x * g x ∂μ) ≤ Real.sqrt A * Real.sqrt B := by
  let I : ℝ := ∫ x, f x * g x ∂μ
  have hI0 : 0 ≤ I := integral_nonneg (fun x => mul_nonneg (hf0 x) (hg0 x))
  have hquad : ∀ t : ℝ, 0 ≤ t → 2 * t * I ≤ A + t ^ 2 * B := by
    intro t _ht
    have hnonneg : 0 ≤ ∫ x, (f x - t * g x) ^ 2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg _)
    have hexp : (fun x => (f x - t * g x) ^ 2) =
        fun x => (f x ^ 2 - 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2 := by
      funext x
      ring
    have hInt1 : Integrable (fun x => 2 * t * (f x * g x)) μ := hfg.const_mul (2 * t)
    have hInt2 : Integrable (fun x => t ^ 2 * g x ^ 2) μ := hg2.const_mul (t ^ 2)
    have hIntSub : Integrable (fun x => f x ^ 2 - 2 * t * (f x * g x)) μ := hf2.sub hInt1
    rw [hexp, integral_add hIntSub hInt2, integral_sub hf2 hInt1,
      integral_const_mul, integral_const_mul] at hnonneg
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hB' : t ^ 2 * (∫ x, g x ^ 2 ∂μ) ≤ t ^ 2 * B :=
      mul_le_mul_of_nonneg_left hIntB ht2
    linarith
  have hsq : I ^ 2 ≤ A * B := by
    by_cases hBpos : B = 0
    · subst hBpos
      have hIzero : I = 0 := by
        by_contra hIne
        have hq := hquad ((A + 1) / I) (div_nonneg (by linarith) hI0)
        have hcancel : 2 * ((A + 1) / I) * I = 2 * A + 2 := by
          field_simp [hIne]
        linarith
      simp [hIzero]
    · have hq := hquad (I / B) (div_nonneg hI0 hB)
      have hmul := mul_le_mul_of_nonneg_left hq hB
      have hleft : B * (2 * (I / B) * I) = 2 * I ^ 2 := by
        field_simp [hBpos]
      have hright : B * (A + (I / B) ^ 2 * B) = A * B + I ^ 2 := by
        field_simp [hBpos]
      linarith
  calc
    I = Real.sqrt (I ^ 2) := (Real.sqrt_sq hI0).symm
    _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA B

lemma arc_indicator_sq (S : Set ℝ) (F : ℝ → ℂ) (θ : ℝ) :
    (S.indicator (fun x => ‖F x‖) θ) ^ 2 = S.indicator (fun x => ‖F x‖ ^ 2) θ := by
  by_cases hθ : θ ∈ S <;> simp [hθ]

lemma arc_indicator_mul (S : Set ℝ) (F G : ℝ → ℂ) (θ : ℝ) :
    S.indicator (fun x => ‖F x‖) θ * ‖G θ‖ =
      S.indicator (fun x => ‖F x‖ * ‖G x‖) θ := by
  by_cases hθ : θ ∈ S <;> simp [hθ]

lemma arc_local_cs (F G : ℝ → ℂ) (c Δ B E : ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hΔ : 0 ≤ Δ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hIntB : (∫ θ in (0 : ℝ)..1, ‖G θ‖ ^ 2) ≤ B)
    (hIntE : (∫ θ in (c - Δ)..(c + Δ), ‖F θ‖ ^ 2) ≤ E) :
    (∫ θ in Set.Ioc (0 : ℝ) 1,
      (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ) ≤
        Real.sqrt E * Real.sqrt B := by
  let S : Set ℝ := Set.Icc (c - Δ) (c + Δ)
  have hS : MeasurableSet S := measurableSet_Icc
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let f : ℝ → ℝ := S.indicator (fun x => ‖F x‖)
  let g : ℝ → ℝ := fun x => ‖G x‖
  have hf0 : ∀ x, 0 ≤ f x := fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
  have hg0 : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  have hF2_cont : Continuous (fun x => ‖F x‖ ^ 2) := by fun_prop
  have hG2_cont : Continuous (fun x => ‖G x‖ ^ 2) := by fun_prop
  have hFG_cont : Continuous (fun x => ‖F x‖ * ‖G x‖) := by fun_prop
  have hF2_int_S : IntegrableOn (fun x => ‖F x‖ ^ 2) S volume :=
    hF2_cont.integrableOn_Icc
  have hF2_ind_int : Integrable (S.indicator (fun x => ‖F x‖ ^ 2)) volume :=
    (integrable_indicator_iff hS).2 hF2_int_S
  have hf2_eq : (fun x => f x ^ 2) = S.indicator (fun x => ‖F x‖ ^ 2) := by
    funext x
    exact arc_indicator_sq S F x
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    rw [hf2_eq]
    exact hF2_ind_int.integrableOn
  have hg2 : Integrable (fun x => g x ^ 2) μ :=
    hG2_cont.integrableOn_Ioc
  have hfg_eq : (fun x => f x * g x) = S.indicator (fun x => ‖F x‖ * ‖G x‖) := by
    funext x
    exact arc_indicator_mul S F G x
  have hfg : Integrable (fun x => f x * g x) μ := by
    rw [hfg_eq]
    exact hFG_cont.integrableOn_Ioc.indicator hS
  have hIntF : (∫ x, f x ^ 2 ∂μ) ≤ E := by
    calc
      (∫ x, f x ^ 2 ∂μ) = ∫ x in Set.Ioc (0 : ℝ) 1, S.indicator (fun y => ‖F y‖ ^ 2) x := by
        rw [hf2_eq]
      _ ≤ ∫ x, S.indicator (fun y => ‖F y‖ ^ 2) x := by
        refine setIntegral_le_integral hF2_ind_int ?_
        filter_upwards with x
        exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) x
      _ = ∫ x in S, ‖F x‖ ^ 2 := integral_indicator hS
      _ = ∫ x in Set.Ioc (c - Δ) (c + Δ), ‖F x‖ ^ 2 := by
        dsimp [S]
        exact MeasureTheory.integral_Icc_eq_integral_Ioc
      _ = ∫ x in (c - Δ)..(c + Δ), ‖F x‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith)]
      _ ≤ E := hIntE
  have hIntG : (∫ x, g x ^ 2 ∂μ) ≤ B := by
    have hle : (0 : ℝ) ≤ 1 := by norm_num
    simpa [μ, g, intervalIntegral.integral_of_le hle] using hIntB
  have hcs := integral_mul_le_sqrt_mul_sqrt μ f g E B hE hB hf0 hg0 hf2 hg2 hfg hIntF hIntG
  simpa [μ, hfg_eq] using hcs

lemma major_minor_pointwise_bound (F G M : ℝ → ℂ) (centers : Finset ℝ) (Δ ε θ : ℝ)
    (hε : 0 ≤ ε)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hM1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖M x‖ ≤ 1)
    (hMε : ∀ x ∈ Set.Icc (0 : ℝ) 1, (∀ c ∈ centers, Δ < |x - c|) → ‖M x‖ ≤ ε) :
    ‖star (F θ) * G θ * M θ‖ ≤
      ε * (‖F θ‖ * ‖G θ‖) +
        ∑ c ∈ centers,
          (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ := by
  have hnorm : ‖star (F θ) * G θ * M θ‖ = ‖F θ‖ * ‖G θ‖ * ‖M θ‖ := by
    rw [norm_mul, norm_mul, norm_star]
  rw [hnorm]
  have hFG0 : 0 ≤ ‖F θ‖ * ‖G θ‖ := mul_nonneg (norm_nonneg (F θ)) (norm_nonneg (G θ))
  have hInd0 : ∀ c : ℝ, 0 ≤ (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ := by
    intro c
    exact Set.indicator_nonneg (fun x _ => mul_nonneg (norm_nonneg (F x)) (norm_nonneg (G x))) θ
  have hsum0 : 0 ≤ ∑ c ∈ centers,
      (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ := by
    apply Finset.sum_nonneg
    intro c _hc
    exact hInd0 c
  by_cases hminor : ∀ c ∈ centers, Δ < |θ - c|
  · have hMle : ‖M θ‖ ≤ ε := hMε θ hθ hminor
    have h1 : ‖F θ‖ * ‖G θ‖ * ‖M θ‖ ≤ ε * (‖F θ‖ * ‖G θ‖) := by
      calc
        ‖F θ‖ * ‖G θ‖ * ‖M θ‖ ≤ ‖F θ‖ * ‖G θ‖ * ε :=
          mul_le_mul_of_nonneg_left hMle hFG0
        _ = ε * (‖F θ‖ * ‖G θ‖) := by ring
    linarith
  · simp only [not_forall, not_lt] at hminor
    rcases hminor with ⟨c₀, hc₀, hdist⟩
    have hmem : θ ∈ Set.Icc (c₀ - Δ) (c₀ + Δ) := by
      rw [Set.mem_Icc]
      rcases abs_le.1 hdist with ⟨h1, h2⟩
      constructor <;> linarith
    have hMle : ‖M θ‖ ≤ 1 := hM1 θ hθ
    have h1 : ‖F θ‖ * ‖G θ‖ * ‖M θ‖ ≤ ‖F θ‖ * ‖G θ‖ := by
      calc
        ‖F θ‖ * ‖G θ‖ * ‖M θ‖ ≤ ‖F θ‖ * ‖G θ‖ * 1 :=
          mul_le_mul_of_nonneg_left hMle hFG0
        _ = ‖F θ‖ * ‖G θ‖ := mul_one _
    have hind : (Set.Icc (c₀ - Δ) (c₀ + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ =
        ‖F θ‖ * ‖G θ‖ := Set.indicator_of_mem hmem _
    have hsingle : ‖F θ‖ * ‖G θ‖ ≤ ∑ c ∈ centers,
        (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ := by
      rw [← hind]
      exact Finset.single_le_sum (fun c _ => hInd0 c) hc₀
    have hε0 : 0 ≤ ε * (‖F θ‖ * ‖G θ‖) := mul_nonneg hε hFG0
    linarith

lemma arc_bound_proof
    (F G M : ℝ → ℂ) (centers : Finset ℝ) (Δ A B E ε : ℝ)
    (hF : Continuous F) (hG : Continuous G) (hM : Continuous M)
    (hΔ : 0 ≤ Δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (hIntA : (∫ θ in (0 : ℝ)..1, ‖F θ‖ ^ 2) ≤ A)
    (hIntB : (∫ θ in (0 : ℝ)..1, ‖G θ‖ ^ 2) ≤ B)
    (hM1 : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖M θ‖ ≤ 1)
    (hMε : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      (∀ c ∈ centers, Δ < |θ - c|) → ‖M θ‖ ≤ ε)
    (hIntE : ∀ c ∈ centers, (∫ θ in (c - Δ)..(c + Δ), ‖F θ‖ ^ 2) ≤ E) :
    ‖∫ θ in (0 : ℝ)..1, star (F θ) * G θ * M θ‖ ≤
      ε * Real.sqrt A * Real.sqrt B +
        (centers.card : ℝ) * Real.sqrt E * Real.sqrt B := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hle01 : (0 : ℝ) ≤ 1 := by norm_num
  have hFGM_cont : Continuous (fun θ => star (F θ) * G θ * M θ) := by fun_prop
  have hFG_cont : Continuous (fun θ => ‖F θ‖ * ‖G θ‖) := by fun_prop
  have hF2_cont : Continuous (fun θ => ‖F θ‖ ^ 2) := by fun_prop
  have hG2_cont : Continuous (fun θ => ‖G θ‖ ^ 2) := by fun_prop
  have hFGM_int : Integrable (fun θ => ‖star (F θ) * G θ * M θ‖) μ :=
    hFGM_cont.norm.integrableOn_Ioc
  have hFG_int : Integrable (fun θ => ‖F θ‖ * ‖G θ‖) μ :=
    hFG_cont.integrableOn_Ioc
  have hArc_int : ∀ c ∈ centers,
      Integrable ((Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖)) μ := by
    intro c _hc
    exact hFG_cont.integrableOn_Ioc.indicator measurableSet_Icc
  have hSum_int : Integrable (fun θ => ∑ c ∈ centers,
      (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ) μ :=
    integrable_finsetSum centers hArc_int
  have hRhs_int : Integrable (fun θ =>
      ε * (‖F θ‖ * ‖G θ‖) + ∑ c ∈ centers,
        (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ) μ :=
    (hFG_int.const_mul ε).add hSum_int
  have hdom : (fun θ => ‖star (F θ) * G θ * M θ‖) ≤ᵐ[μ]
      fun θ => ε * (‖F θ‖ * ‖G θ‖) + ∑ c ∈ centers,
        (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact major_minor_pointwise_bound F G M centers Δ ε θ hε (Set.Ioc_subset_Icc_self hθ) hM1 hMε
  have hGlobalCS : (∫ θ, ‖F θ‖ * ‖G θ‖ ∂μ) ≤ Real.sqrt A * Real.sqrt B := by
    refine integral_mul_le_sqrt_mul_sqrt μ (fun θ => ‖F θ‖) (fun θ => ‖G θ‖) A B
      hA hB (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      hF2_cont.integrableOn_Ioc hG2_cont.integrableOn_Ioc hFG_int ?_ ?_
    · simpa [μ, intervalIntegral.integral_of_le hle01] using hIntA
    · simpa [μ, intervalIntegral.integral_of_le hle01] using hIntB
  have hSumBound : (∫ θ, (∑ c ∈ centers,
      (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ) ∂μ) ≤
        (centers.card : ℝ) * Real.sqrt E * Real.sqrt B := by
    rw [integral_finsetSum centers hArc_int]
    calc
      (∑ c ∈ centers, ∫ θ, (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ ∂μ) ≤
        ∑ _c ∈ centers, Real.sqrt E * Real.sqrt B := by
          apply Finset.sum_le_sum
          intro c hc
          exact arc_local_cs F G c Δ B E hF hG hΔ hB hE hIntB (hIntE c hc)
      _ = (centers.card : ℝ) * Real.sqrt E * Real.sqrt B := by
          simp [mul_assoc]
  calc
    ‖∫ θ in (0 : ℝ)..1, star (F θ) * G θ * M θ‖ =
        ‖∫ θ, star (F θ) * G θ * M θ ∂μ‖ := by
      rw [intervalIntegral.integral_of_le hle01]
    _ ≤ ∫ θ, ‖star (F θ) * G θ * M θ‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ, (ε * (‖F θ‖ * ‖G θ‖) + ∑ c ∈ centers,
          (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ) ∂μ :=
      integral_mono_ae hFGM_int hRhs_int hdom
    _ = ε * (∫ θ, ‖F θ‖ * ‖G θ‖ ∂μ) +
        ∫ θ, (∑ c ∈ centers,
          (Set.Icc (c - Δ) (c + Δ)).indicator (fun x => ‖F x‖ * ‖G x‖) θ) ∂μ := by
      rw [integral_add (hFG_int.const_mul ε) hSum_int, integral_const_mul]
    _ ≤ ε * (Real.sqrt A * Real.sqrt B) +
        (centers.card : ℝ) * Real.sqrt E * Real.sqrt B := by
      exact add_le_add (mul_le_mul_of_nonneg_left hGlobalCS hε) hSumBound
    _ = ε * Real.sqrt A * Real.sqrt B +
        (centers.card : ℝ) * Real.sqrt E * Real.sqrt B := by ring

theorem FourierArcTask_proof : Erdos821.P5Core.FourierArcTask :=
  ⟨shift_correlation_proof, parseval_proof, arc_bound_proof⟩


end Erdos821.P5FourierArcProof

namespace Erdos821.P5Core

theorem FourierArcTask_proof : FourierArcTask :=
  Erdos821.P5FourierArcProof.FourierArcTask_proof


end Erdos821.P5Core

