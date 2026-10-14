import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMeanSquare
import Erdos821.Blueprint.Classical
import Mathlib

/-! Dirichlet-polynomial mean squares from §1 of the source paper. -/

open scoped BigOperators
open MeasureTheory

namespace Erdos821.Classical

noncomputable section

/-- Mellin phase used in the analytic blueprint. -/
def mellin (n : ℕ) (t : ℝ) : ℂ := Complex.exp (Complex.I * t * Real.log n)

/-- A finite Dirichlet polynomial. -/
def dp (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, c n * mellin n t

/-- The coefficient square norm on a finite support. -/
def sqNorm (s : Finset ℕ) (c : ℕ → ℂ) : ℝ := ∑ n ∈ s, ‖c n‖ ^ 2

/-- Copy of the architect's `MeanSquares` contract, bridged below. -/
def MeanSquares : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (Y : ℕ) (a : ℕ → ℂ) (lo hi : ℝ), lo ≤ hi →
    (∫ t : ℝ in lo..hi, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
      K * (hi - lo + Y * Real.log (2 * Y)) * sqNorm (Finset.Icc 1 Y) a ∧
    ∀ E : Finset ℝ, (∀ t ∈ E, lo ≤ t ∧ t ≤ hi) →
      (∀ t ∈ E, ∀ u ∈ E, t ≠ u → 1 ≤ |t - u|) →
      (∑ t ∈ E, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
        K * (hi - lo + 1 + Y * Real.log (2 * Y)) * Real.log (2 * Y) ^ 2 *
          sqNorm (Finset.Icc 1 Y) a

lemma ioc_zero_eq_icc_one (Y : ℕ) : Finset.Ioc 0 Y = Finset.Icc 1 Y := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

lemma mellin_add (n : ℕ) (x y : ℝ) :
    mellin n (x + y) = mellin n x * mellin n y := by
  unfold mellin
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma mellin_norm (n : ℕ) (x : ℝ) : ‖mellin n x‖ = 1 := by
  have he : mellin n x = Complex.exp ((x * Real.log n : ℝ) * Complex.I) := by
    unfold mellin
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.norm_exp_ofReal_mul_I _

lemma sqNorm_mellin_mul (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    sqNorm s (fun n => a n * mellin n x) = sqNorm s a := by
  unfold sqNorm
  apply Finset.sum_congr rfl
  intro n hn
  rw [norm_mul, mellin_norm, mul_one]

lemma dp_shift (s : Finset ℕ) (a : ℕ → ℂ) (x y : ℝ) :
    dp s a (x + y) = dp s (fun n => a n * mellin n x) y := by
  unfold dp
  apply Finset.sum_congr rfl
  intro n hn
  rw [mellin_add]
  ring

lemma intervalIntegral_symmetric_reflect (T : ℝ) (f : ℝ → ℝ) :
    (∫ t : ℝ in -T..T, f (-t)) = (∫ t : ℝ in -T..T, f t) := by
  simpa using intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)

lemma mrt_negative_phase_eq_dp (n : ℕ) (t : ℝ) :
    Complex.exp (((-Real.log (n : ℝ) * t : ℝ) * Complex.I)) = mellin n (-t) := by
  unfold mellin
  congr 1
  push_cast
  ring

lemma mrtExponentialPolynomial_eq_dp (Y : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    OAI.TwoPointCorrelations.mrtExponentialPolynomial (Finset.Ioc 0 Y) a
        (fun n => -Real.log (n : ℝ)) t = dp (Finset.Icc 1 Y) a (-t) := by
  unfold OAI.TwoPointCorrelations.mrtExponentialPolynomial dp
  rw [← ioc_zero_eq_icc_one Y]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mrt_negative_phase_eq_dp]

lemma symmetric_mean_square (Y : ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ in -T..T, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + Y) * sqNorm (Finset.Icc 1 Y) a := by
  have hm := OAI.TwoPointCorrelations.mrt_dirichlet_mean_square Y a hT
  have hreflect :
      (∫ t : ℝ in -T..T,
          ‖OAI.TwoPointCorrelations.mrtExponentialPolynomial
            (Finset.Ioc 0 Y) a (fun n => -Real.log (n : ℝ)) t‖ ^ 2) =
        (∫ t : ℝ in -T..T, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) := by
    calc
      _ = ∫ t : ℝ in -T..T, ‖dp (Finset.Icc 1 Y) a (-t)‖ ^ 2 := by
        congr 1
        funext t
        rw [mrtExponentialPolynomial_eq_dp]
      _ = _ := intervalIntegral_symmetric_reflect T
        (fun t => ‖dp (Finset.Icc 1 Y) a t‖ ^ 2)
  rw [hreflect] at hm
  simpa only [sqNorm, ioc_zero_eq_icc_one] using hm





lemma mellin_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t => mellin n t)
      (Complex.I * Real.log n * mellin n x) x := by
  have h := (((hasDerivAt_id x).ofReal_comp).const_mul
    (Complex.I * (Real.log n : ℂ))).cexp
  convert h using 1
  · ext t
    simp [mellin]
    ring
  · simp [mellin]
    ring

lemma dp_hasDerivAt (s : Finset ℕ) (a : ℕ → ℂ) (x : ℝ) :
    HasDerivAt (fun t => dp s a t)
      (dp s (fun n => a n * (Complex.I * Real.log n)) x) x := by
  change HasDerivAt (fun t => ∑ n ∈ s, a n * mellin n t)
    (∑ n ∈ s, (a n * (Complex.I * Real.log n)) * mellin n x) x
  simpa only [mul_assoc] using
    HasDerivAt.fun_sum (fun n (_ : n ∈ s) => (mellin_hasDerivAt n x).const_mul (a n))

lemma dp_derivative_continuous (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (fun t => dp s (fun n => a n * (Complex.I * Real.log n)) t) := by
  unfold dp mellin
  fun_prop

lemma half_lt_log_two_mul_nat {Y : ℕ} (hY : Y ≠ 0) :
    (1 / 2 : ℝ) < Real.log (2 * Y) := by
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hY)
  have htwo : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  apply htwo.trans_le
  apply Real.log_le_log (by norm_num)
  nlinarith

/-- Translation of a symmetric mean-square estimate to an arbitrary
interval; the coefficient phases introduced by translation preserve `sqNorm`. -/
lemma continuous_of_symmetric_mean (Y : ℕ) (a : ℕ → ℂ) (lo hi : ℝ)
    (hlohi : lo ≤ hi)
    (hsym : ∀ (b : ℕ → ℂ) (T : ℝ), 0 < T →
      (∫ t : ℝ in -T..T, ‖dp (Finset.Icc 1 Y) b t‖ ^ 2) ≤
        8 * Real.exp 1 * (T + Y) * sqNorm (Finset.Icc 1 Y) b) :
    (∫ t : ℝ in lo..hi, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
      16 * Real.exp 1 * (hi - lo + Y * Real.log (2 * Y)) *
        sqNorm (Finset.Icc 1 Y) a := by
  by_cases hY : Y = 0
  · simp [hY, dp, sqNorm]
  by_cases hI : lo = hi
  · subst hi
    have hlog : 0 ≤ Real.log (2 * Y) := by
      linarith [half_lt_log_two_mul_nat hY]
    have hS : 0 ≤ sqNorm (Finset.Icc 1 Y) a :=
      Finset.sum_nonneg fun n hn => sq_nonneg _
    simp only [intervalIntegral.integral_same, sub_self, zero_add]
    positivity
  have hlt : lo < hi := by
    by_contra h
    have h' : hi ≤ lo := le_of_not_gt h
    exact hI (le_antisymm hlohi h')
  let T : ℝ := (hi - lo) / 2
  let mid : ℝ := (lo + hi) / 2
  let s := Finset.Icc 1 Y
  let b : ℕ → ℂ := fun n => a n * mellin n mid
  have hT : 0 < T := by dsimp [T]; linarith
  have hleft : mid - T = lo := by dsimp [mid, T]; ring
  have hright : mid + T = hi := by dsimp [mid, T]; ring
  have hdp : ∀ x, dp s a (x + mid) = dp s b x := by
    intro x
    simpa [b, add_comm] using dp_shift s a mid x
  have htranslate :
      (∫ t : ℝ in lo..hi, ‖dp s a t‖ ^ 2) =
        (∫ x : ℝ in -T..T, ‖dp s b x‖ ^ 2) := by
    calc
      _ = ∫ x : ℝ in (-T) + mid..T + mid, ‖dp s a x‖ ^ 2 := by
        simp only [show -T + mid = lo by linarith, show T + mid = hi by linarith]
      _ = ∫ x : ℝ in -T..T, ‖dp s a (x + mid)‖ ^ 2 :=
        (intervalIntegral.integral_comp_add_right (fun x => ‖dp s a x‖ ^ 2) mid).symm
      _ = ∫ x : ℝ in -T..T, ‖dp s b x‖ ^ 2 := by
        congr 1
        funext x
        rw [hdp]
  have hcoeff : sqNorm s b = sqNorm s a := by
    simpa [b] using (sqNorm_mellin_mul s a mid)
  have hS : 0 ≤ sqNorm s a := Finset.sum_nonneg fun n hn => sq_nonneg _
  have hLhalf := half_lt_log_two_mul_nat hY
  have hYbound : (Y : ℝ) ≤ 2 * (Y : ℝ) * Real.log (2 * Y) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg Y)
      (sub_nonneg.mpr (show (1 : ℝ) ≤ 2 * Real.log (2 * Y) by linarith))]
  have htime : T + Y ≤ 2 * (hi - lo + Y * Real.log (2 * Y)) := by
    dsimp [T]
    nlinarith [hYbound, sub_nonneg.mpr hlohi]
  have hm := hsym b T hT
  rw [hcoeff] at hm
  have hscale : 8 * Real.exp 1 * (T + Y) * sqNorm s a ≤
      16 * Real.exp 1 * (hi - lo + Y * Real.log (2 * Y)) * sqNorm s a := by
    calc
      _ ≤ 8 * Real.exp 1 * (2 * (hi - lo + Y * Real.log (2 * Y))) *
            sqNorm s a := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left htime (by positivity)
        · exact hS
      _ = _ := by ring
  rw [htranslate]
  exact hm.trans hscale

lemma dp_derivative_sqNorm_le (Y : ℕ) (a : ℕ → ℂ) :
    sqNorm (Finset.Icc 1 Y) (fun n => a n * (Complex.I * Real.log n)) ≤
      Real.log (2 * Y) ^ 2 * sqNorm (Finset.Icc 1 Y) a := by
  by_cases hY : Y = 0
  · simp [hY, sqNorm]
  have hYpos : 0 < (Y : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hY
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hY)
  have hL : 0 < Real.log (2 * (Y : ℝ)) :=
    Real.log_pos (by nlinarith)
  simp only [sqNorm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'.1
  have hnY : (n : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hn'.2
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hlogn : Real.log (n : ℝ) ≤ Real.log (2 * (Y : ℝ)) := by
    calc
      Real.log (n : ℝ) ≤ Real.log (Y : ℝ) :=
        Real.log_le_log (by positivity) hnY
      _ ≤ Real.log (2 * (Y : ℝ)) :=
        Real.log_le_log hYpos (by nlinarith)
  have hlogabs : |Real.log (n : ℝ)| ≤ Real.log (2 * (Y : ℝ)) := by
    rw [abs_of_nonneg hlog0]
    exact hlogn
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hlogabs 2
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hpow (sq_nonneg ‖a n‖)

/-- The one-dimensional Sobolev inequality on a unit interval. -/
lemma local_sampling (F G : ℝ → ℂ) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : Continuous G) (t : ℝ) :
    ‖F t‖ ^ 2 ≤ ∫ x in t..t + 1, 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2 := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)
  let U : ℝ → ℝ := fun x => ‖F x‖ ^ 2
  let B : ℝ → ℝ := fun x => ‖F x‖ ^ 2 + ‖G x‖ ^ 2
  have huc : Continuous U := hc.norm.pow 2
  have hbc : Continuous B := (hc.norm.pow 2).add (hG.norm.pow 2)
  have hb0 : ∀ x, 0 ≤ B x := fun x => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hud : ∀ x, DifferentiableAt ℝ U x := fun x => (hF x).norm_sq.differentiableAt
  have hbd : ∀ x, ‖deriv U x‖ ≤ B x := by
    intro x
    dsimp only [U]
    rw [(hF x).norm_sq.deriv, norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (F x) (G x)
    norm_num only [Real.norm_ofNat]
    dsimp only [B]
    nlinarith [sq_nonneg (‖F x‖ - ‖G x‖)]
  have hp (x : ℝ) (hx : x ∈ Set.Icc t (t + 1)) :
      U t ≤ U x + ∫ z in t..t + 1, B z := by
    have hd := norm_sub_le_integral_of_norm_deriv_le_of_le hx.1 huc.continuousOn
      (fun z hz => (hud z).differentiableWithinAt)
      (Filter.Eventually.of_forall (fun z _ => hbd z)) (hbc.intervalIntegrable t x)
    have hm := intervalIntegral.integral_mono_interval («μ» := volume) (le_refl t) hx.1 hx.2
      (Filter.Eventually.of_forall hb0) (hbc.intervalIntegrable t (t + 1))
    rw [Real.norm_eq_abs] at hd
    have ha := neg_le_abs (U x - U t)
    linarith
  have hh := intervalIntegral.integral_mono_on («μ» := volume) (by linarith : t ≤ t + 1)
    intervalIntegrable_const
    (huc.intervalIntegrable t (t + 1) |>.add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_add (huc.intervalIntegrable t (t + 1))
    intervalIntegrable_const] at hh
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hh
  have he : ∫ x in t..t + 1, 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2 =
      (∫ x in t..t + 1, U x) + (∫ x in t..t + 1, B x) := by
    rw [← intervalIntegral.integral_add (huc.intervalIntegrable t (t + 1))
      (hbc.intervalIntegrable t (t + 1))]
    congr 1
    ext x
    dsimp [U, B]
    ring
  rw [he]
  dsimp only [U] at hh
  convert hh using 1 <;> ring

/-- Sampling at points separated by one is bounded by the energy on their
unit intervals; those intervals have disjoint interiors. -/
lemma spaced_sampling (F G : ℝ → ℂ) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : Continuous G) (E : Finset ℝ) {lo hi : ℝ}
    (hE : ∀ t ∈ E, t ∈ Set.Icc lo hi)
    (hsep : ∀ t ∈ E, ∀ u ∈ E, t ≠ u → 1 ≤ |t - u|) :
    ∑ t ∈ E, ‖F t‖ ^ 2 ≤
      ∫ x in Set.Icc lo (hi + 1), 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2 := by
  classical
  let Q : ℝ → ℝ := fun x => 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2
  have hfc : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)
  have hqc : Continuous Q := by dsimp [Q]; fun_prop
  have hqd : Set.Pairwise (↑E) (fun t u : ℝ =>
      Disjoint (Set.Ioc t (t + 1)) (Set.Ioc u (u + 1))) := by
    intro t ht u hu htu
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hb := hsep t ht u hu htu
    have hlt : |t - u| < 1 := abs_lt.mpr
      ⟨by linarith [hx.1, hx.2, hy.1, hy.2], by linarith [hx.1, hx.2, hy.1, hy.2]⟩
    linarith
  have hsub : (⋃ t ∈ E, Set.Ioc t (t + 1)) ⊆ Set.Icc lo (hi + 1) := by
    intro x hx
    obtain ⟨t, htE, htx⟩ := Set.mem_iUnion₂.mp hx
    have ht := hE t htE
    exact ⟨by linarith [htx.1, htx.2, ht.1], by linarith [htx.1, htx.2, ht.2]⟩
  calc
    _ ≤ ∑ t ∈ E, ∫ x in Set.Ioc t (t + 1), Q x := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [intervalIntegral.integral_of_le (by linarith : t ≤ t + 1)] using
        local_sampling F G hF hG t
    _ = ∫ x in ⋃ t ∈ E, Set.Ioc t (t + 1), Q x := by
      exact (integral_biUnion_finset E (fun _ _ => measurableSet_Ioc) hqd
        (fun t _ => hqc.integrableOn_Ioc)).symm
    _ ≤ _ := setIntegral_mono_set hqc.integrableOn_Icc
      (Filter.Eventually.of_forall (fun x => by dsimp [Q]; positivity))
      hsub.eventuallyLE

/-- The discrete estimate follows from the continuous bound on the interval
extended by one unit, together with the derivative energy bound. -/
lemma discrete_of_interval_mean (C : ℝ) (hC : 0 < C) (Y : ℕ) (a : ℕ → ℂ)
    (hmean : ∀ (b : ℕ → ℂ) (lo hi : ℝ), lo ≤ hi →
      (∫ t : ℝ in lo..hi, ‖dp (Finset.Icc 1 Y) b t‖ ^ 2) ≤
        C * (hi - lo + Y * Real.log (2 * Y)) * sqNorm (Finset.Icc 1 Y) b)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (E : Finset ℝ)
    (hE : ∀ t ∈ E, lo ≤ t ∧ t ≤ hi)
    (hsep : ∀ t ∈ E, ∀ u ∈ E, t ≠ u → 1 ≤ |t - u|) :
    (∑ t ∈ E, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
      9 * C * (hi - lo + 1 + Y * Real.log (2 * Y)) * Real.log (2 * Y) ^ 2 *
        sqNorm (Finset.Icc 1 Y) a := by
  by_cases hY : Y = 0
  · simp [hY, dp, sqNorm]
  have hYone : (1 : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hY)
  have hLhalf : (1 / 2 : ℝ) < Real.log (2 * (Y : ℝ)) := by
    have htwo : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    apply htwo.trans_le
    apply Real.log_le_log (by norm_num)
    nlinarith
  let s := Finset.Icc 1 Y
  let b : ℕ → ℂ := fun n => a n * (Complex.I * Real.log n)
  let F : ℝ → ℂ := fun t => dp s a t
  let G : ℝ → ℂ := fun t => dp s b t
  let M : ℝ := hi - lo + 1 + Y * Real.log (2 * Y)
  let L : ℝ := Real.log (2 * (Y : ℝ))
  have hM : 0 ≤ M := by
    dsimp [M]
    have hlog : 0 ≤ Real.log (2 * (Y : ℝ)) := by linarith
    positivity
  have hS : 0 ≤ sqNorm s a := Finset.sum_nonneg fun n hn => sq_nonneg _
  have hS' : 0 ≤ sqNorm s b := Finset.sum_nonneg fun n hn => sq_nonneg _
  have hFderiv : ∀ x, HasDerivAt F (G x) x := by
    intro x
    exact dp_hasDerivAt s a x
  have hGcont : Continuous G := by
    exact dp_derivative_continuous s a
  have hsample :
      (∑ t ∈ E, ‖F t‖ ^ 2) ≤
        ∫ x in Set.Icc lo (hi + 1), 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2 :=
    spaced_sampling F G hFderiv hGcont E
      (fun t ht => Set.mem_Icc.mpr (hE t ht)) hsep
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hFderiv x).continuousAt)
  have hFc : Continuous (fun x => ‖F x‖ ^ 2) := hFcont.norm.pow 2
  have hGc : Continuous (fun x => ‖G x‖ ^ 2) := hGcont.norm.pow 2
  have hFi : IntegrableOn (fun x => 2 * ‖F x‖ ^ 2) (Set.Icc lo (hi + 1)) :=
    hFc.integrableOn_Icc.const_mul 2
  have hGi : IntegrableOn (fun x => ‖G x‖ ^ 2) (Set.Icc lo (hi + 1)) :=
    hGc.integrableOn_Icc
  have hFset :
      (∫ x in Set.Icc lo (hi + 1), ‖F x‖ ^ 2) =
        (∫ x : ℝ in lo..hi + 1, ‖F x‖ ^ 2) := by
    calc
      _ = ∫ x in Set.Ioc lo (hi + 1), ‖F x‖ ^ 2 :=
        MeasureTheory.integral_Icc_eq_integral_Ioc
      _ = ∫ x : ℝ in lo..hi + 1, ‖F x‖ ^ 2 :=
        (intervalIntegral.integral_of_le (by linarith : lo ≤ hi + 1)).symm
  have hGset :
      (∫ x in Set.Icc lo (hi + 1), ‖G x‖ ^ 2) =
        (∫ x : ℝ in lo..hi + 1, ‖G x‖ ^ 2) := by
    calc
      _ = ∫ x in Set.Ioc lo (hi + 1), ‖G x‖ ^ 2 :=
        MeasureTheory.integral_Icc_eq_integral_Ioc
      _ = ∫ x : ℝ in lo..hi + 1, ‖G x‖ ^ 2 :=
        (intervalIntegral.integral_of_le (by linarith : lo ≤ hi + 1)).symm
  have henergy :
      (∫ x in Set.Icc lo (hi + 1), 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2) =
        2 * (∫ x : ℝ in lo..hi + 1, ‖F x‖ ^ 2) +
          (∫ x : ℝ in lo..hi + 1, ‖G x‖ ^ 2) := by
    calc
      _ = 2 * (∫ x in Set.Icc lo (hi + 1), ‖F x‖ ^ 2) +
            (∫ x in Set.Icc lo (hi + 1), ‖G x‖ ^ 2) := by
        rw [MeasureTheory.integral_add hFi hGi, MeasureTheory.integral_const_mul]
      _ = _ := by rw [hFset, hGset]
  have hlen : (hi + 1 - lo) + Y * Real.log (2 * Y) = M := by
    dsimp [M]
    ring
  have hmeanF := hmean a lo (hi + 1) (by linarith)
  have hmeanG := hmean b lo (hi + 1) (by linarith)
  rw [hlen] at hmeanF hmeanG
  have hFbound :
      (∫ x : ℝ in lo..hi + 1, ‖F x‖ ^ 2) ≤ C * M * sqNorm s a := by
    simpa [F, s] using hmeanF
  have hGbound :
      (∫ x : ℝ in lo..hi + 1, ‖G x‖ ^ 2) ≤ C * M * sqNorm s b := by
    simpa [G, s, b] using hmeanG
  have hderivNorm : sqNorm s b ≤ L ^ 2 * sqNorm s a := by
    simpa [s, b, L] using dp_derivative_sqNorm_le Y a
  have hGbound' :
      (∫ x : ℝ in lo..hi + 1, ‖G x‖ ^ 2) ≤ C * M * L ^ 2 * sqNorm s a := by
    calc
      _ ≤ C * M * sqNorm s b := hGbound
      _ ≤ C * M * (L ^ 2 * sqNorm s a) :=
        mul_le_mul_of_nonneg_left hderivNorm (mul_nonneg hC.le hM)
      _ = _ := by ring
  have hcombined :
      2 * (∫ x : ℝ in lo..hi + 1, ‖F x‖ ^ 2) +
          (∫ x : ℝ in lo..hi + 1, ‖G x‖ ^ 2) ≤
        C * M * (2 + L ^ 2) * sqNorm s a := by
    calc
      _ ≤ 2 * (C * M * sqNorm s a) + C * M * L ^ 2 * sqNorm s a :=
        add_le_add (mul_le_mul_of_nonneg_left hFbound (by norm_num)) hGbound'
      _ = _ := by ring
  have hLsq : (1 / 2 : ℝ) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hLhalf.le 2
  have hfactor : 2 + L ^ 2 ≤ 9 * L ^ 2 := by nlinarith [hLsq]
  have hscale : C * M * (2 + L ^ 2) * sqNorm s a ≤
      9 * C * M * L ^ 2 * sqNorm s a := by
    calc
      _ ≤ (C * M * (9 * L ^ 2)) * sqNorm s a :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfactor (mul_nonneg hC.le hM)) hS
      _ = _ := by ring
  calc
    (∑ t ∈ E, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) = ∑ t ∈ E, ‖F t‖ ^ 2 := by
      simp [F, s]
    _ ≤ ∫ x in Set.Icc lo (hi + 1), 2 * ‖F x‖ ^ 2 + ‖G x‖ ^ 2 := hsample
    _ = 2 * (∫ x : ℝ in lo..hi + 1, ‖F x‖ ^ 2) +
          (∫ x : ℝ in lo..hi + 1, ‖G x‖ ^ 2) := henergy
    _ ≤ C * M * (2 + L ^ 2) * sqNorm s a := hcombined
    _ ≤ 9 * C * M * L ^ 2 * sqNorm s a := hscale
    _ = 9 * C * (hi - lo + 1 + Y * Real.log (2 * Y)) *
          Real.log (2 * Y) ^ 2 * sqNorm (Finset.Icc 1 Y) a := by
      simp [M, L, s]


lemma continuous_mean_square_bound (Y : ℕ) (a : ℕ → ℂ) (lo hi : ℝ)
    (hlohi : lo ≤ hi) :
    (∫ t : ℝ in lo..hi, ‖dp (Finset.Icc 1 Y) a t‖ ^ 2) ≤
      16 * Real.exp 1 * (hi - lo + Y * Real.log (2 * Y)) *
        sqNorm (Finset.Icc 1 Y) a :=
  continuous_of_symmetric_mean Y a lo hi hlohi
    (fun b T hT => symmetric_mean_square Y b hT)

/-- The uniform continuous and separated-point Dirichlet-polynomial mean
square estimates from Lemma 1.4 of the paper. -/
theorem meanSquares : MeanSquares := by
  let C : ℝ := 16 * Real.exp 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨9 * C, by positivity, ?_⟩
  intro Y a lo hi hlohi
  constructor
  · have hcont := continuous_mean_square_bound Y a lo hi hlohi
    have hlog : 0 ≤ Real.log (2 * Y) := by
      by_cases hY : Y = 0
      · simp [hY]
      · linarith [half_lt_log_two_mul_nat hY]
    have hS : 0 ≤ sqNorm (Finset.Icc 1 Y) a :=
      Finset.sum_nonneg fun n hn => sq_nonneg _
    have hFactor : C ≤ 9 * C := by nlinarith
    have hscale : C * (hi - lo + Y * Real.log (2 * Y)) *
          sqNorm (Finset.Icc 1 Y) a ≤
        9 * C * (hi - lo + Y * Real.log (2 * Y)) *
          sqNorm (Finset.Icc 1 Y) a := by
      have hCX : C * (hi - lo + Y * Real.log (2 * Y)) ≤
          9 * C * (hi - lo + Y * Real.log (2 * Y)) :=
        mul_le_mul_of_nonneg_right hFactor (by positivity)
      exact mul_le_mul_of_nonneg_right hCX hS
    exact hcont.trans hscale
  · intro E hE hsep
    exact discrete_of_interval_mean C hC Y a
      (fun b left right hleft => continuous_mean_square_bound Y b left right hleft)
      lo hi hlohi E hE hsep

theorem blueprint_meanSquares : Erdos821.Blueprint.MeanSquares := by exact meanSquares

end

end Erdos821.Classical
