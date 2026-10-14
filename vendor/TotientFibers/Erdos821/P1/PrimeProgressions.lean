import Erdos821.Blueprint.Classical
import OAI.NumberTheory.PrimeGaps.Main

open scoped BigOperators
open Filter MeasureTheory

namespace Erdos821.P1

private lemma continuousOn_invLogDerivative :
    ContinuousOn (fun x : ℝ => -1 / (x * Real.log x ^ 2)) {0, 1, -1}ᶜ := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp_all)

private theorem integral_log_inv_local (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t)⁻¹ =
      ((Real.log b)⁻¹ * b) - ((Real.log a)⁻¹ * a) +
        ∫ t in a..b, ((Real.log t) ^ 2)⁻¹ := by
  rcases le_iff_lt_or_eq.mp hab with hlt | rfl
  · have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ => (Real.log x)⁻¹)
      (u' := fun x : ℝ => -1 / (x * (Real.log x) ^ 2))
      (v := fun x : ℝ => x) (v' := fun _ => (1 : ℝ)) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (not_le_of_gt hlt), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        rw [show (-1 / (x * Real.log x ^ 2)) = (-1 / Real.log x ^ 2) * x⁻¹ by
          rw [mul_comm x]
          field_simp]
        apply HasDerivAt.comp
          (h := fun z : ℝ => Real.log z) (h₂ := fun z : ℝ => z⁻¹) (x := x)
        · simpa using! HasDerivAt.inv (c := fun z : ℝ => z) (c' := (1 : ℝ))
            (x := Real.log x) (hasDerivAt_id' (Real.log x))
            (by
              simp only [ne_eq, Real.log_eq_zero, not_or]
              refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply Real.hasDerivAt_log
          linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_invLogDerivative.mono fun x hx => ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;> apply MeasureTheory.integrable_const)
    simp only [mul_one] at hparts
    rw [hparts]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le hlt.le,
      intervalIntegral.integral_of_le hlt.le,
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
    · refine .of_forall fun x hx => ?_
      simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
      rw [inv_mul_cancel₀, mul_one]
      linarith
    · exact measurableSet_Ioc
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]

noncomputable def primeCountAP (r a : ℕ) (x : ℝ) : ℝ :=
  ((Erdos821.Blueprint.primesUpTo x).filter (fun p => p % r = a % r)).card

noncomputable def primeThetaAP (r a : ℕ) (x : ℝ) : ℝ :=
  OAI.LargePrimeGaps.residuePrefix OAI.LargePrimeGaps.theta ⌊x⌋₊ r (a % r)

private noncomputable def primeThetaCoefficient (r a n : ℕ) : ℝ :=
  if n.Prime ∧ n % r = a % r then Real.log n else 0

private theorem primeThetaAP_cumulative (r a : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeThetaCoefficient r a n) = primeThetaAP r a x := by
  classical
  have hzero : primeThetaCoefficient r a 0 = 0 := by
    simp [primeThetaCoefficient, Nat.not_prime_zero]
  unfold primeThetaAP OAI.LargePrimeGaps.residuePrefix OAI.LargePrimeGaps.residueSlice
  rw [show Finset.Icc 0 ⌊x⌋₊ = insert 0 (Finset.Ioc 0 ⌊x⌋₊) by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega]
  rw [Finset.sum_insert (by simp)]
  rw [hzero, zero_add, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · by_cases hres : n % r = a % r <;>
      simp [primeThetaCoefficient, hp, hres, OAI.LargePrimeGaps.theta]
  · simp [primeThetaCoefficient, hp, OAI.LargePrimeGaps.theta]

private theorem primeCountAP_eq_theta_formula (r a : ℕ) (hr : 1 ≤ r)
    {x : ℝ} (hx : 2 ≤ x) :
    primeCountAP r a x = primeThetaAP r a x / Real.log x +
      ∫ t in 2..x, primeThetaAP r a t / (t * Real.log t ^ 2) := by
  classical
  let c : ℕ → ℝ := primeThetaCoefficient r a
  have hc0 : c 0 = 0 := by simp [c, primeThetaCoefficient, Nat.not_prime_zero]
  have hc1 : c 1 = 0 := by simp [c, primeThetaCoefficient, Nat.not_prime_one]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) x,
      DifferentiableAt ℝ (fun u : ℝ => (Real.log u)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    fun_prop (disch := simp [ht0, hlog])
  have hint : IntegrableOn
      (deriv (fun u : ℝ => (Real.log u)⁻¹)) (Set.Icc (2 : ℝ) x) := by
    refine ContinuousOn.integrableOn_Icc fun t ht => ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog : Real.log t ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
    have hderiv : (fun u : ℝ => deriv (fun v : ℝ => (Real.log v)⁻¹) u) =
        (fun u => -(u * Real.log u ^ 2)⁻¹) := by
      funext u
      rw [Real.deriv_inv_log_apply]
      field_simp
    change ContinuousWithinAt (fun u : ℝ => deriv (fun v : ℝ => (Real.log v)⁻¹) u)
      (Set.Icc (2 : ℝ) x) t
    rw [hderiv]
    fun_prop (disch := simp [ht0, hlog])
  have habel := sum_mul_eq_sub_integral_mul₁ c hc0 hc1 x hdiff hint
  have htheta (t : ℝ) :
      (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = primeThetaAP r a t := by
    simpa only [c] using primeThetaAP_cumulative r a t
  have hcount :
      (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Real.log n)⁻¹ * c n) = primeCountAP r a x := by
    have hset :
        (Finset.Icc 0 ⌊x⌋₊).filter (fun n => n.Prime ∧ n % r = a % r) =
          (Erdos821.Blueprint.primesUpTo x).filter (fun n => n % r = a % r) := by
      ext n
      simp only [Finset.mem_filter, Erdos821.Blueprint.primesUpTo,
        Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hn0, hnx⟩, ⟨hnprime, hres⟩⟩
        exact ⟨⟨⟨(Nat.Prime.one_lt hnprime).le, hnx⟩, hnprime⟩, hres⟩
      · rintro ⟨⟨⟨hn1, hnx⟩, hnprime⟩, hres⟩
        exact ⟨⟨Nat.zero_le _, hnx⟩, ⟨hnprime, hres⟩⟩
    calc
      _ = ∑ n ∈ (Finset.Icc 0 ⌊x⌋₊).filter
          (fun n => n.Prime ∧ n % r = a % r), (1 : ℝ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hcond : n.Prime ∧ n % r = a % r
        · have hn0 : n ≠ 0 := by
            intro he
            subst n
            exact hcond.1.ne_zero rfl
          have hlog : Real.log n ≠ 0 := by
            apply Real.log_ne_zero_of_pos_of_ne_one
            · exact_mod_cast hcond.1.pos
            · exact_mod_cast hcond.1.ne_one
          simp [c, primeThetaCoefficient, hcond, hlog]
        · simp [c, primeThetaCoefficient, hcond]
      _ = ((Finset.Icc 0 ⌊x⌋₊).filter
          (fun n => n.Prime ∧ n % r = a % r)).card := by simp
      _ = primeCountAP r a x := by rw [hset, primeCountAP]
  have hinterm (t : ℝ) (ht : t ∈ Set.uIcc (2 : ℝ) x) :
      deriv (fun u : ℝ => (Real.log u)⁻¹) t *
          (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(primeThetaAP r a t / (t * Real.log t ^ 2)) := by
    have ht' : t ∈ Set.Icc (2 : ℝ) x := by simpa [Set.uIcc_of_le hx] using ht
    have ht1 : 1 < t := by linarith [ht'.1]
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    rw [htheta, Real.deriv_inv_log_apply]
    field_simp
  have hint_eq :
      (∫ t in 2..x, deriv (fun u : ℝ => (Real.log u)⁻¹) t *
        (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n)) =
      -∫ t in 2..x, primeThetaAP r a t / (t * Real.log t ^ 2) := by
    rw [intervalIntegral.integral_congr (fun t ht => hinterm t ht)]
    rw [intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_of_le hx] at habel
  rw [hcount, htheta] at habel
  rw [hint_eq] at habel
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using habel

private theorem primeThetaAP_le (r a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    primeThetaAP r a x ≤ x * Real.log x := by
  have hfloorReal : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfloorPosNat : 0 < ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ x)
  have hfloorPos : 0 < (⌊x⌋₊ : ℝ) := by
    exact_mod_cast hfloorPosNat
  have hfloorOne : 1 ≤ ⌊x⌋₊ := by omega
  have hlogFloor : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hfloorOne)
  have hlogMono : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log hfloorPos hfloorReal
  have hres : primeThetaAP r a x ≤ (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) := by
    change OAI.LargePrimeGaps.residueSlice OAI.LargePrimeGaps.theta 0 ⌊x⌋₊ r (a % r) ≤ _
    simpa only [Nat.cast_zero, Nat.sub_zero] using
      OAI.LargePrimeGaps.residueSlice_theta_le
        (L := 0) (U := ⌊x⌋₊) (bound := ⌊x⌋₊) le_rfl hfloorOne r (a % r)
  calc
    _ ≤ (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) := hres
    _ ≤ x * Real.log x := mul_le_mul hfloorReal hlogMono hlogFloor (by positivity)

private theorem primeThetaAP_nonneg (r a : ℕ) (x : ℝ) :
    0 ≤ primeThetaAP r a x := by
  unfold primeThetaAP OAI.LargePrimeGaps.residuePrefix OAI.LargePrimeGaps.residueSlice
  exact Finset.sum_nonneg fun n hn => OAI.LargePrimeGaps.theta_nonneg n

private theorem primeThetaAP_integrableOn (r a : ℕ) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    IntegrableOn (fun t : ℝ => primeThetaAP r a t / (t * Real.log t ^ 2))
      (Set.Icc u v) := by
  let c : ℕ → ℝ := primeThetaCoefficient r a
  let g : ℝ → ℝ := fun t => (t * Real.log t ^ 2)⁻¹
  have hgcont : ContinuousOn g (Set.Icc u v) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [hu.trans ht.1]
    have ht1 : 1 < t := by linarith [hu.trans ht.1]
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hden : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero _ hlog)
    apply ContinuousAt.continuousWithinAt
    dsimp [g]
    fun_prop (disch := simp [hden])
  have hgint : IntegrableOn g (Set.Icc u v) := hgcont.integrableOn_Icc
  have hsumInt := integrableOn_mul_sum_Icc (m := 0) (c := c)
    (by linarith : 0 ≤ u) hgint
  apply IntegrableOn.congr_fun hsumInt
  · intro t ht
    change g t * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeThetaCoefficient r a n) = _
    rw [primeThetaAP_cumulative]
    dsimp [g]
    ring
  · exact measurableSet_Icc

private theorem primeThetaAP_errorKernel_integrable (r a : ℕ) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable
      (fun t : ℝ => (primeThetaAP r a t - t / (r.totient : ℝ)) /
        (t * Real.log t ^ 2)) volume u v := by
  have hTheta : IntervalIntegrable
      (fun t : ℝ => primeThetaAP r a t / (t * Real.log t ^ 2)) volume u v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
      (primeThetaAP_integrableOn r a hu huv)
  have hmainCont : ContinuousOn
      (fun t : ℝ => (t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) (Set.Icc u v) := by
    intro t ht
    have ht1 : 1 < t := by linarith [hu.trans ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := simp [ht0, hlog])
  have hmain : IntervalIntegrable
      (fun t : ℝ => (t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) volume u v :=
    hmainCont.intervalIntegrable_of_Icc huv
  convert hTheta.sub hmain using 1
  ext t
  ring

private theorem endpointError_le_sum (t : ℝ) (r Q : ℕ)
    (hr : 1 ≤ r) (hQ : r ≤ Q) :
    (OAI.LargePrimeGaps.endpointError t r : ℝ) ≤
      ∑ q ∈ Finset.Icc 1 Q, (OAI.LargePrimeGaps.endpointError t q : ℝ) := by
  exact Finset.single_le_sum (f := fun q =>
    (OAI.LargePrimeGaps.endpointError t q : ℝ))
    (fun q hq => NNReal.coe_nonneg _) (Finset.mem_Icc.mpr ⟨hr, hQ⟩)

private theorem primeThetaAP_error_of_endpoint (D M : ℝ) {t : ℝ}
    (ht : 2 ≤ t) (r a : ℕ) (hr : 1 ≤ r) (ha : Nat.Coprime a r)
    (hEP : (OAI.LargePrimeGaps.endpointError t r : ℝ) ≤
      M * t * (Real.log t) ^ (-D)) :
    |primeThetaAP r a t - t / (r.totient : ℝ)| ≤
      M * t * (Real.log t) ^ (-D) + 1 + 2 * Real.sqrt t * Real.log t := by
  have hq : 0 < r := by omega
  let c := a % r
  have hc : c < r := Nat.mod_lt _ hq
  have hcop : Nat.Coprime c r := by
    change Nat.gcd (a % r) r = 1
    rw [← Nat.gcd_rec r a, Nat.gcd_comm]
    exact ha
  have hclass :
      |OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt ⌊t⌋₊ r c -
        t / (r.totient : ℝ)| ≤ (OAI.LargePrimeGaps.endpointError t r : ℝ) := by
    have hsup := Finset.le_sup (f := fun d => if Nat.Coprime d r then
        NNReal.mk (|OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt ⌊t⌋₊ r d -
          t / (r.totient : ℝ)|) (abs_nonneg _) else 0)
      (Finset.mem_range.mpr hc)
    have hcast := NNReal.coe_le_coe.mpr hsup
    simpa only [ite_eq_left hcop, NNReal.coe_mk, OAI.LargePrimeGaps.endpointError] using hcast
  have hU : 1 ≤ ⌊t⌋₊ := by
    have hpos : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ t)
    omega
  have hremove := OAI.LargePrimeGaps.residueSlice_primepower_error hU 0 r c
  have hremove' :
      |OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt ⌊t⌋₊ r c -
        primeThetaAP r a t| ≤ 2 * Real.sqrt (⌊t⌋₊ : ℝ) * Real.log (⌊t⌋₊ : ℝ) := by
    simpa [OAI.LargePrimeGaps.residuePrefix, OAI.LargePrimeGaps.residueSlice,
      primeThetaAP, c] using hremove
  have hfloorReal : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlogFloor : 0 ≤ Real.log (⌊t⌋₊ : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hU)
  have hlogT : 0 ≤ Real.log t := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)
  have hfloorPosNat : 0 < ⌊t⌋₊ := by omega
  have hfloorPosReal : 0 < (⌊t⌋₊ : ℝ) := by exact_mod_cast hfloorPosNat
  have hlogMono : Real.log (⌊t⌋₊ : ℝ) ≤ Real.log t :=
    Real.log_le_log hfloorPosReal hfloorReal
  have htail : 2 * Real.sqrt (⌊t⌋₊ : ℝ) * Real.log (⌊t⌋₊ : ℝ) ≤
      2 * Real.sqrt t * Real.log t := by
    gcongr
  rw [abs_sub_comm] at hremove'
  have hremoveBound := hremove'.trans htail
  calc
    _ ≤ |primeThetaAP r a t -
          OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt ⌊t⌋₊ r c| +
        |OAI.LargePrimeGaps.residuePrefix ArithmeticFunction.vonMangoldt ⌊t⌋₊ r c -
          t / (r.totient : ℝ)| := abs_sub_le _ _ _
    _ ≤ 2 * Real.sqrt t * Real.log t + M * t * (Real.log t) ^ (-D) := by
      exact add_le_add hremoveBound (hclass.trans hEP)
    _ ≤ M * t * (Real.log t) ^ (-D) + 1 + 2 * Real.sqrt t * Real.log t := by linarith

private theorem primePowerTail_small (D : ℝ) (hD : 0 < D) :
    ∀ᶠ t : ℝ in atTop,
      1 + 2 * Real.sqrt t * Real.log t ≤ 3 * t * (Real.log t) ^ (-D) := by
  have hlogpow := OAI.LargePrimeGaps.eventually_log_rpow_le_rpow (D + 1)
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hlogpow, eventually_ge_atTop (Real.exp 1)] with t hlogpow ht
  have ht1 : (1 : ℝ) ≤ t := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans ht
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 1) ht
  have hlogpos : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hlog1
  have hpow : (Real.log t) ^ (D + 1) ≤ Real.sqrt t := by
    simpa only [Real.sqrt_eq_rpow] using hlogpow
  have hlogD : (Real.log t) ^ D ≤ t := by
    calc
      _ ≤ (Real.log t) ^ (D + 1) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
      _ ≤ Real.sqrt t := hpow
      _ ≤ t := Real.sqrt_le_self_iff.mpr (Or.inr ht1)
  have hden : 0 < (Real.log t) ^ D := Real.rpow_pos_of_pos hlogpos _
  have hone : (1 : ℝ) ≤ t / (Real.log t) ^ D :=
    (le_div_iff₀ hden).2 (by simpa using hlogD)
  have hpowmul : (Real.log t) ^ D * Real.log t = (Real.log t) ^ (D + 1) := by
    calc
      (Real.log t) ^ D * Real.log t = (Real.log t) ^ D * (Real.log t) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.log t) ^ (D + 1) := by rw [← Real.rpow_add hlogpos]
  have hcross : Real.sqrt t * Real.log t * (Real.log t) ^ D ≤ t := by
    calc
      _ = Real.sqrt t * ((Real.log t) ^ D * Real.log t) := by ring
      _ = Real.sqrt t * (Real.log t) ^ (D + 1) := by rw [hpowmul]
      _ ≤ Real.sqrt t * Real.sqrt t :=
        mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
      _ = t := by simpa only [pow_two] using Real.sq_sqrt (by linarith : (0 : ℝ) ≤ t)
  have hroot : Real.sqrt t * Real.log t ≤ t / (Real.log t) ^ D := by
    apply (le_div_iff₀ hden).2
    simpa [mul_assoc] using hcross
  have hsmall : 1 + 2 * Real.sqrt t * Real.log t ≤ 3 * (t / (Real.log t) ^ D) := by
    nlinarith [hone, hroot]
  calc
    _ ≤ 3 * (t / (Real.log t) ^ D) := hsmall
    _ = 3 * t * (Real.log t) ^ (-D) := by
      rw [Real.rpow_neg hlogpos.le]
      ring

private theorem primeThetaAP_error_of_BV_bound (D b M : ℝ) {t : ℝ}
    (ht : 2 ≤ t) (r a : ℕ) (hr : 1 ≤ r) (ha : Nat.Coprime a r)
    (hcut : (r : ℝ) ≤ t ^ (1 / 2 : ℝ) * (Real.log t) ^ (-b))
    (hBV : (∑ q ∈ Finset.Icc 1
        ⌊t ^ (1 / 2 : ℝ) * (Real.log t) ^ (-b)⌋₊,
        (OAI.LargePrimeGaps.endpointError t q : ℝ)) ≤ M * t * (Real.log t) ^ (-D))
    (htail : 1 + 2 * Real.sqrt t * Real.log t ≤ 3 * t * (Real.log t) ^ (-D)) :
    |primeThetaAP r a t - t / (r.totient : ℝ)| ≤
      (M + 3) * t * (Real.log t) ^ (-D) := by
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hz : 0 ≤ t ^ (1 / 2 : ℝ) * (Real.log t) ^ (-b) :=
    mul_nonneg (Real.rpow_nonneg htpos.le _) (Real.rpow_nonneg hlogpos.le _)
  have hqNat : r ≤ ⌊t ^ (1 / 2 : ℝ) * (Real.log t) ^ (-b)⌋₊ := by
    apply (Nat.le_floor_iff hz).2
    exact_mod_cast hcut
  have hEP := (endpointError_le_sum t r _ hr hqNat).trans hBV
  have hraw := primeThetaAP_error_of_endpoint D M ht r a hr ha hEP
  calc
    _ ≤ M * t * (Real.log t) ^ (-D) + 1 + 2 * Real.sqrt t * Real.log t := hraw
    _ ≤ M * t * (Real.log t) ^ (-D) + 3 * t * (Real.log t) ^ (-D) := by
      nlinarith [htail]
    _ = (M + 3) * t * (Real.log t) ^ (-D) := by ring

private theorem exists_primeThetaAP_profile (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ b Kθ Y₀ : ℝ, 0 < b ∧ 0 < Kθ ∧ Real.exp 4 ≤ Y₀ ∧
      ∀ y : ℝ, Y₀ ≤ y → ∀ r a : ℕ, 1 ≤ r →
        (r : ℝ) ≤ (Real.log y) ^ C → Nat.Coprime a r →
          ∀ t ∈ Set.Icc (Real.sqrt y) y,
            |primeThetaAP r a t - t / (r.totient : ℝ)| ≤
              Kθ * t * (Real.log t) ^ (-(A + 4)) := by
  let D := A + 4
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨b, hb, M, hM, x₀, hx₀, hBV⟩ :=
    OAI.LargePrimeGaps.bombieriVinogradov D hD
  have hlogPow := OAI.LargePrimeGaps.eventually_log_rpow_le_rpow
    (C + 1 + b) (s := (1 / 2 : ℝ)) (by norm_num)
  have hgood : ∀ᶠ t : ℝ in atTop,
      x₀ ≤ t ∧ 2 ≤ t ∧ 2 ^ C ≤ Real.log t ∧
        (Real.log t) ^ (C + 1 + b) ≤ Real.sqrt t ∧
        1 + 2 * Real.sqrt t * Real.log t ≤ 3 * t * (Real.log t) ^ (-D) := by
    filter_upwards [eventually_ge_atTop x₀, eventually_ge_atTop (2 : ℝ),
      eventually_ge_atTop (Real.exp (2 ^ C)), hlogPow, primePowerTail_small D hD]
      with t htx₀ ht2 hexp hpow htail
    have h2C : 2 ^ C ≤ Real.log t := by
      rw [← Real.log_exp (2 ^ C)]
      exact Real.log_le_log (Real.exp_pos _) hexp
    have hpow' : (Real.log t) ^ (C + 1 + b) ≤ Real.sqrt t := by
      simpa only [Real.sqrt_eq_rpow] using hpow
    exact ⟨htx₀, ht2, h2C, hpow', htail⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgood
  let T₀ := max T 2
  let Y₀ := max (Real.exp 4) (T₀ ^ 2)
  have hY₀ : Real.exp 4 ≤ Y₀ := by dsimp [Y₀]; exact le_max_left _ _
  refine ⟨b, M + 3, Y₀, hb, by positivity, hY₀, ?_⟩
  intro y hy r a hr hmod ha t ht
  have hy' : max (Real.exp 4) (T₀ ^ 2) ≤ y := by simpa [Y₀] using hy
  have hT₀sq : T₀ ^ 2 ≤ y := (le_max_right _ _).trans hy'
  have hT₀nonneg : 0 ≤ T₀ := by dsimp [T₀]; positivity
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos 4) (le_trans (le_max_left _ _) hy')
  have hT₀sqrt : T₀ ≤ Real.sqrt y :=
    (Real.le_sqrt hT₀nonneg hypos.le).2 hT₀sq
  have hTlower : T ≤ Real.sqrt y := (le_max_left T 2).trans hT₀sqrt
  have hy4 : 4 ≤ y := by
    have h := Real.add_one_le_exp (4 : ℝ)
    nlinarith [le_trans (le_max_left (Real.exp 4) (T₀ ^ 2)) hy']
  have hsqrtY2 : (2 : ℝ) ≤ Real.sqrt y := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith
  have hgoodT := hT t (le_trans hTlower ht.1)
  rcases hgoodT with ⟨htx₀, ht2, h2pow, hlogpow, htail⟩
  have hlogY : 4 ≤ Real.log y := by
    rw [← Real.log_exp (4 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 4) (le_trans (le_max_left _ _) hy')
  have hlogT : 0 < Real.log t := Real.log_pos (by linarith [ht.1, hsqrtY2])
  have hlogTnonneg : 0 ≤ Real.log t := hlogT.le
  have hlogYnonneg : 0 ≤ Real.log y := by linarith
  have hlogYle : Real.log y ≤ 2 * Real.log t := by
    have hsqrtSq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ y)
    have hsq : y ≤ t ^ 2 := by
      calc
        y = Real.sqrt y * Real.sqrt y := by
          calc
            y = (Real.sqrt y) ^ 2 := hsqrtSq.symm
            _ = Real.sqrt y * Real.sqrt y := by ring
        _ ≤ t * t := mul_le_mul ht.1 ht.1 (Real.sqrt_nonneg y) (by linarith [ht.1])
        _ = t ^ 2 := by ring
    calc
      Real.log y ≤ Real.log (t ^ 2) := Real.log_le_log hypos hsq
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  have hmodLog : (r : ℝ) ≤ (Real.log t) ^ (C + 1) := by
    calc
      (r : ℝ) ≤ (Real.log y) ^ C := hmod
      _ ≤ (2 * Real.log t) ^ C := Real.rpow_le_rpow hlogYnonneg hlogYle hC.le
      _ = 2 ^ C * (Real.log t) ^ C := by
        rw [Real.mul_rpow (by norm_num) hlogTnonneg]
      _ ≤ Real.log t * (Real.log t) ^ C :=
        mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg hlogTnonneg _)
      _ = (Real.log t) ^ (C + 1) := by
        calc
          _ = (Real.log t) ^ (1 : ℝ) * (Real.log t) ^ C := by rw [Real.rpow_one]
          _ = (Real.log t) ^ (1 + C) := by rw [← Real.rpow_add hlogT]
          _ = (Real.log t) ^ (C + 1) := by congr 1 <;> ring
  have hlogB : 0 < (Real.log t) ^ b := Real.rpow_pos_of_pos hlogT _
  have hcross : (Real.log t) ^ (C + 1) * (Real.log t) ^ b =
      (Real.log t) ^ (C + 1 + b) := by rw [← Real.rpow_add hlogT]
  have hcut : (r : ℝ) ≤ Real.sqrt t * (Real.log t) ^ (-b) := by
    calc
      (r : ℝ) ≤ (Real.log t) ^ (C + 1) := hmodLog
      _ ≤ Real.sqrt t / (Real.log t) ^ b := (le_div_iff₀ hlogB).2 (by rw [hcross]; exact hlogpow)
      _ = Real.sqrt t * (Real.log t) ^ (-b) := by
        rw [Real.rpow_neg hlogT.le, div_eq_mul_inv]
  have hcut' : (r : ℝ) ≤ t ^ (1 / 2 : ℝ) * (Real.log t) ^ (-b) := by
    simpa only [Real.sqrt_eq_rpow] using hcut
  have hBvt := hBV t htx₀
  have hprofile := primeThetaAP_error_of_BV_bound D b M ht2 r a hr ha hcut' hBvt htail
  simpa [D] using hprofile

private theorem primeCountAP_error_identity (r a : ℕ) (hr : 1 ≤ r)
    {y : ℝ} (hy : 2 ≤ y) :
    primeCountAP r a y - Erdos821.Blueprint.li y / (r.totient : ℝ) =
      (primeThetaAP r a y - y / (r.totient : ℝ)) / Real.log y +
        (∫ t in 2..y,
          (primeThetaAP r a t - t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) +
          2 / ((r.totient : ℝ) * Real.log 2) := by
  have hφ : 0 < (r.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hthetaInt : IntervalIntegrable
      (fun t : ℝ => primeThetaAP r a t / (t * Real.log t ^ 2)) volume 2 y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr
      (primeThetaAP_integrableOn r a (by norm_num) hy)
  have hmainCont : ContinuousOn
      (fun t : ℝ => (t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) (Set.Icc 2 y) := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := simp [ht0, hlog])
  have hmainInt : IntervalIntegrable
      (fun t : ℝ => (t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) volume 2 y :=
    hmainCont.intervalIntegrable_of_Icc hy
  have hErrIntegral :
      (∫ t in 2..y, primeThetaAP r a t / (t * Real.log t ^ 2)) -
        (∫ t in 2..y, (t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) =
      ∫ t in 2..y,
        (primeThetaAP r a t - t / (r.totient : ℝ)) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_sub hthetaInt hmainInt]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hmainIntegral :
      (∫ t in 2..y, (t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) =
        (r.totient : ℝ)⁻¹ * (∫ t in 2..y, ((Real.log t) ^ 2)⁻¹) := by
    calc
      _ = ∫ t in 2..y, (r.totient : ℝ)⁻¹ * ((Real.log t) ^ 2)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht1 : 1 < t := by
          have ht' : t ∈ Set.Icc (2 : ℝ) y := by simpa [Set.uIcc_of_le hy] using ht
          linarith [ht'.1]
        have ht0 : t ≠ 0 := by linarith
        have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
        field_simp
      _ = (r.totient : ℝ)⁻¹ * (∫ t in 2..y, ((Real.log t) ^ 2)⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
  have hli : Erdos821.Blueprint.li y =
      (Real.log y)⁻¹ * y - (Real.log 2)⁻¹ * 2 +
        ∫ t in 2..y, ((Real.log t) ^ 2)⁻¹ := by
    simpa only [Erdos821.Blueprint.li] using
      integral_log_inv_local 2 y (by norm_num) hy
  have hIntSplit :
      (∫ t in 2..y, primeThetaAP r a t / (t * Real.log t ^ 2)) =
        (r.totient : ℝ)⁻¹ * (∫ t in 2..y, ((Real.log t) ^ 2)⁻¹) +
          (∫ t in 2..y,
            (primeThetaAP r a t - t / (r.totient : ℝ)) / (t * Real.log t ^ 2)) := by
    linarith [hErrIntegral, hmainIntegral]
  rw [primeCountAP_eq_theta_formula r a hr hy, hIntSplit, hli]
  field_simp [hlogy.ne', hlog2.ne', hφ.ne']
  ring

private theorem primeCountAP_error_from_thetaProfile (r a : ℕ) (hr : 1 ≤ r)
    (A D Kθ : ℝ) (hA : 0 < A) (hD : A ≤ D) (hDpos : 0 < D)
    (hKθ : 0 ≤ Kθ) {y : ℝ} (hy : Real.exp 4 ≤ y)
    (hyAbsorb : (Real.log y) ^ A ≤ Real.sqrt y)
    (hθ : ∀ t ∈ Set.Icc (Real.sqrt y) y,
      |primeThetaAP r a t - t / (r.totient : ℝ)| ≤ Kθ * t * (Real.log t) ^ (-D)) :
    |primeCountAP r a y - Erdos821.Blueprint.li y / (r.totient : ℝ)| ≤
      (Kθ + Kθ * 2 ^ D + (Real.log 2)⁻¹ + (Real.log 2 ^ 2)⁻¹ +
        2 / ((r.totient : ℝ) * Real.log 2)) * y * (Real.log y) ^ (-A) := by
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos 4) hy
  have hy4 : 4 ≤ y := by
    have h := Real.add_one_le_exp (4 : ℝ)
    nlinarith
  have hlogy : 4 ≤ Real.log y := by
    rw [← Real.log_exp (4 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 4) hy
  have hlogypos : 0 < Real.log y := by linarith
  have hlogyone : 1 ≤ Real.log y := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    norm_num at h ⊢
    exact h
  have hsqrtY2 : (2 : ℝ) ≤ Real.sqrt y := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith
  have hsqrtYle : Real.sqrt y ≤ y :=
    Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
  have hφNat : 1 ≤ r.totient := by
    have hrpos : 0 < r := by omega
    have hpos := Nat.totient_pos.mpr hrpos
    omega
  have hφ : 0 < (r.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < r by omega)
  have hφone : (1 : ℝ) ≤ r.totient := by exact_mod_cast hφNat
  let Efun (t : ℝ) :=
    (primeThetaAP r a t - t / (r.totient : ℝ)) / (t * Real.log t ^ 2)
  have hlowInt : IntervalIntegrable Efun volume 2 (Real.sqrt y) :=
    primeThetaAP_errorKernel_integrable r a (by norm_num) hsqrtY2
  have hhighInt : IntervalIntegrable Efun volume (Real.sqrt y) y :=
    primeThetaAP_errorKernel_integrable r a hsqrtY2 hsqrtYle
  let lowK : ℝ := (Real.log 2)⁻¹ + (Real.log 2 ^ 2)⁻¹
  have hlowK : 0 < lowK := by dsimp [lowK]; positivity
  have hlowBound : |∫ t in 2..Real.sqrt y, Efun t| ≤ lowK * Real.sqrt y := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 2) (b := Real.sqrt y) (C := lowK) (f := Efun) (by
        intro t ht
        have htI : t ∈ Set.Icc (2 : ℝ) (Real.sqrt y) := by
          have ht' : t ∈ Set.Ioc (2 : ℝ) (Real.sqrt y) := by
            rw [Set.uIoc_of_le hsqrtY2] at ht
            exact ht
          exact ⟨ht'.1.le, ht'.2⟩
        have htpos : 0 < t := by linarith [htI.1]
        have hlog2le : Real.log 2 ≤ Real.log t :=
          Real.log_le_log (by norm_num) htI.1
        have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith [htI.1])
        have hlogt2 : 0 < Real.log t ^ 2 := sq_pos_of_pos hlogtpos
        have hthetaPos := primeThetaAP_nonneg r a t
        have hthetaLe := primeThetaAP_le r a htI.1
        have hmainPos : 0 ≤ t / (r.totient : ℝ) := div_nonneg htpos.le (Nat.cast_nonneg _)
        have hmainLe : t / (r.totient : ℝ) ≤ t := div_le_self htpos.le hφone
        have hErr : |primeThetaAP r a t - t / (r.totient : ℝ)| ≤ t * Real.log t + t := by
          calc
            _ ≤ |primeThetaAP r a t| + |t / (r.totient : ℝ)| := abs_sub _ _
            _ = primeThetaAP r a t + t / (r.totient : ℝ) := by
              rw [abs_of_nonneg hthetaPos, abs_of_nonneg hmainPos]
            _ ≤ _ := add_le_add hthetaLe hmainLe
        have hden : 0 < t * Real.log t ^ 2 := mul_pos htpos hlogt2
        have hInv1 : (Real.log t)⁻¹ ≤ (Real.log 2)⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hlog2pos hlog2le
        have hlogsq : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := by nlinarith [hlog2le]
        have hInv2 : (Real.log t ^ 2)⁻¹ ≤ (Real.log 2 ^ 2)⁻¹ := by
          simpa only [one_div] using
            one_div_le_one_div_of_le (sq_pos_of_pos hlog2pos) hlogsq
        change |(primeThetaAP r a t - t / (r.totient : ℝ)) /
          (t * Real.log t ^ 2)| ≤ lowK
        rw [abs_div, abs_of_pos hden]
        calc
          _ ≤ (t * Real.log t + t) / (t * Real.log t ^ 2) :=
            div_le_div_of_nonneg_right hErr hden.le
          _ = (Real.log t)⁻¹ + (Real.log t ^ 2)⁻¹ := by
            field_simp [htpos.ne', hlogtpos.ne']
          _ ≤ lowK := add_le_add hInv1 hInv2)
    rw [intervalIntegral.integral_of_le hsqrtY2, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hsqrtY2)] at h
    have hset := h.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 2)) hlowK.le)
    rw [intervalIntegral.integral_of_le hsqrtY2]
    exact hset
  have hloghalf : 0 < Real.log y / 2 := by positivity
  have hpowScale : (Real.log y / 2) ^ (-D) = 2 ^ D * (Real.log y) ^ (-D) := by
    rw [Real.div_rpow hlogypos.le (by norm_num) (-D),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hlogDA : (Real.log y) ^ (-D) ≤ (Real.log y) ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogyone (by linarith)
  have hhighConst : 0 ≤ Kθ * 2 ^ D * (Real.log y) ^ (-A) := by positivity
  have hhighBound :
      |∫ t in Real.sqrt y..y, Efun t| ≤ Kθ * 2 ^ D * y * (Real.log y) ^ (-A) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := Real.sqrt y) (b := y) (C := Kθ * 2 ^ D * (Real.log y) ^ (-A))
      (f := Efun) (by
        intro t ht
        have htI : t ∈ Set.Icc (Real.sqrt y) y := by
          have ht' : t ∈ Set.Ioc (Real.sqrt y) y := by
            rw [Set.uIoc_of_le hsqrtYle] at ht
            exact ht
          exact ⟨ht'.1.le, ht'.2⟩
        have htpos : 0 < t := lt_of_lt_of_le (Real.sqrt_pos.2 hypos) htI.1
        have hlogLower : Real.log y / 2 ≤ Real.log t := by
          have hsq : y ≤ t ^ 2 := by
            calc
              y = Real.sqrt y * Real.sqrt y := by
                calc
                  y = (Real.sqrt y) ^ 2 := by rw [Real.sq_sqrt hypos.le]
                  _ = Real.sqrt y * Real.sqrt y := by ring
              _ ≤ t * t := mul_le_mul htI.1 htI.1 (Real.sqrt_nonneg y) (by linarith [htI.1])
              _ = t ^ 2 := by ring
          have hlogle : Real.log y ≤ 2 * Real.log t := by
            calc
              Real.log y ≤ Real.log (t ^ 2) := Real.log_le_log hypos hsq
              _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
          linarith
        have hlogT : 1 ≤ Real.log t := by
          have hlog2 : 1 ≤ Real.log y := by linarith [hlogy]
          linarith [hlogLower]
        have hlogTpos : 0 < Real.log t := by linarith
        have hden : 0 < t * Real.log t ^ 2 := mul_pos htpos (sq_pos_of_pos hlogTpos)
        have hθerr := hθ t htI
        have hnum : 0 ≤ Kθ * t * (Real.log t) ^ (-D) :=
          mul_nonneg (mul_nonneg hKθ htpos.le) (Real.rpow_nonneg hlogTpos.le _)
        have hdenle : t ≤ t * Real.log t ^ 2 := by nlinarith [sq_nonneg (Real.log t - 1)]
        have hkernel : |Efun t| ≤ Kθ * (Real.log t) ^ (-D) := by
          dsimp [Efun]
          rw [abs_div, abs_of_pos hden]
          calc
            _ ≤ (Kθ * t * (Real.log t) ^ (-D)) / (t * Real.log t ^ 2) :=
              div_le_div_of_nonneg_right hθerr hden.le
            _ ≤ (Kθ * t * (Real.log t) ^ (-D)) / t :=
              div_le_div_of_nonneg_left hnum htpos hdenle
            _ = Kθ * (Real.log t) ^ (-D) := by field_simp [htpos.ne']
        have hpow : (Real.log t) ^ (-D) ≤ 2 ^ D * (Real.log y) ^ (-A) := by
          calc
            _ ≤ (Real.log y / 2) ^ (-D) :=
              Real.rpow_le_rpow_of_nonpos hloghalf hlogLower (by linarith)
            _ = 2 ^ D * (Real.log y) ^ (-D) := hpowScale
            _ ≤ 2 ^ D * (Real.log y) ^ (-A) :=
              mul_le_mul_of_nonneg_left hlogDA (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        have hkernel' := hkernel.trans (mul_le_mul_of_nonneg_left hpow hKθ)
        simpa [mul_assoc] using hkernel')
    rw [intervalIntegral.integral_of_le hsqrtYle, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hsqrtYle)] at h
    have hInterval : |∫ t in Real.sqrt y..y, Efun t| ≤
        (Kθ * 2 ^ D * (Real.log y) ^ (-A)) * (y - Real.sqrt y) := by
      rw [intervalIntegral.integral_of_le hsqrtYle]
      exact h
    calc
      _ ≤ (Kθ * 2 ^ D * (Real.log y) ^ (-A)) * (y - Real.sqrt y) := hInterval
      _ ≤ (Kθ * 2 ^ D * (Real.log y) ^ (-A)) * y :=
        mul_le_mul_of_nonneg_left (by linarith) hhighConst
      _ = Kθ * 2 ^ D * y * (Real.log y) ^ (-A) := by ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hlowInt hhighInt
  have hErrInt : ∫ t in 2..y, Efun t =
      (∫ t in 2..Real.sqrt y, Efun t) + (∫ t in Real.sqrt y..y, Efun t) := hsplit.symm
  have hErrAbs : |∫ t in 2..y, Efun t| ≤ lowK * Real.sqrt y +
      Kθ * 2 ^ D * y * (Real.log y) ^ (-A) := by
    rw [hErrInt]
    have hnorm := norm_add_le (∫ t in 2..Real.sqrt y, Efun t)
      (∫ t in Real.sqrt y..y, Efun t)
    have hlowNorm : ‖∫ t in 2..Real.sqrt y, Efun t‖ ≤ lowK * Real.sqrt y := by
      simpa only [Real.norm_eq_abs] using hlowBound
    have hhighNorm : ‖∫ t in Real.sqrt y..y, Efun t‖ ≤
        Kθ * 2 ^ D * y * (Real.log y) ^ (-A) := by
      simpa only [Real.norm_eq_abs] using hhighBound
    have hsum := hnorm.trans (add_le_add hlowNorm hhighNorm)
    simpa only [Real.norm_eq_abs] using hsum
  have hθy := hθ y ⟨hsqrtYle, le_rfl⟩
  have hendpoint :
      |(primeThetaAP r a y - y / (r.totient : ℝ)) / Real.log y| ≤
        Kθ * y * (Real.log y) ^ (-A) := by
    rw [abs_div, abs_of_pos hlogypos]
    calc
      _ ≤ (Kθ * y * (Real.log y) ^ (-D)) / Real.log y :=
        div_le_div_of_nonneg_right hθy hlogypos.le
      _ ≤ Kθ * y * (Real.log y) ^ (-D) := div_le_self (by positivity) hlogyone
      _ ≤ Kθ * y * (Real.log y) ^ (-A) :=
        mul_le_mul_of_nonneg_left hlogDA (by positivity)
  have hmainIdent : primeCountAP r a y - Erdos821.Blueprint.li y / (r.totient : ℝ) =
      (primeThetaAP r a y - y / (r.totient : ℝ)) / Real.log y +
        (∫ t in 2..y, Efun t) + 2 / ((r.totient : ℝ) * Real.log 2) :=
    primeCountAP_error_identity r a hr (by linarith [hy4])
  have hconst : 0 ≤ 2 / ((r.totient : ℝ) * Real.log 2) := by positivity
  have hlogPowPos : 0 < (Real.log y) ^ A := Real.rpow_pos_of_pos hlogypos _
  have hsqrtAbsorb : Real.sqrt y ≤ y * (Real.log y) ^ (-A) := by
    have hcross : Real.sqrt y * (Real.log y) ^ A ≤ y := by
      calc
        _ ≤ Real.sqrt y * Real.sqrt y :=
          mul_le_mul_of_nonneg_left hyAbsorb (Real.sqrt_nonneg y)
        _ = y := by
          calc
            _ = (Real.sqrt y) ^ 2 := by ring
            _ = y := Real.sq_sqrt hypos.le
    calc
      Real.sqrt y ≤ y / (Real.log y) ^ A := (le_div_iff₀ hlogPowPos).2 hcross
      _ = y * (Real.log y) ^ (-A) := by rw [Real.rpow_neg hlogypos.le]; ring
  have hconstAbsorb : 1 ≤ y * (Real.log y) ^ (-A) := by
    have hlogPowLeY : (Real.log y) ^ A ≤ y := by
      calc
        _ ≤ Real.sqrt y := hyAbsorb
        _ ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith [hy4]))
    calc
      1 ≤ y / (Real.log y) ^ A :=
        (le_div_iff₀ hlogPowPos).2 (by simpa using hlogPowLeY)
      _ = y * (Real.log y) ^ (-A) := by rw [Real.rpow_neg hlogypos.le]; ring
  have hfinalCoeff :
      Kθ * y * (Real.log y) ^ (-A) + lowK * Real.sqrt y +
        Kθ * 2 ^ D * y * (Real.log y) ^ (-A) +
        2 / ((r.totient : ℝ) * Real.log 2) ≤
      (Kθ + Kθ * 2 ^ D + lowK + 2 / ((r.totient : ℝ) * Real.log 2)) *
        y * (Real.log y) ^ (-A) := by
    have hlowAbsorb := mul_le_mul_of_nonneg_left hsqrtAbsorb hlowK.le
    have hconstBound := mul_le_mul_of_nonneg_left hconstAbsorb hconst
    nlinarith [hlowAbsorb, hconstBound]
  calc
    _ = |(primeThetaAP r a y - y / (r.totient : ℝ)) / Real.log y +
        (∫ t in 2..y, Efun t) + 2 / ((r.totient : ℝ) * Real.log 2)| := by rw [hmainIdent]
    _ ≤ |(primeThetaAP r a y - y / (r.totient : ℝ)) / Real.log y| +
        |∫ t in 2..y, Efun t| + 2 / ((r.totient : ℝ) * Real.log 2) := by
      have h1 := norm_add_le ((primeThetaAP r a y - y / (r.totient : ℝ)) / Real.log y)
        (∫ t in 2..y, Efun t)
      have h2 := norm_add_le
        ((primeThetaAP r a y - y / (r.totient : ℝ)) / Real.log y + ∫ t in 2..y, Efun t)
        (2 / ((r.totient : ℝ) * Real.log 2))
      simp only [Real.norm_eq_abs, abs_of_nonneg hconst] at h1 h2
      linarith
    _ ≤ _ := by
      calc
        _ ≤ Kθ * y * (Real.log y) ^ (-A) + lowK * Real.sqrt y +
            Kθ * 2 ^ D * y * (Real.log y) ^ (-A) +
            2 / ((r.totient : ℝ) * Real.log 2) := by
          linarith [hendpoint, hErrAbs]
    _ ≤ _ := by
      have hcoef : Kθ + Kθ * 2 ^ D + lowK +
          2 / ((r.totient : ℝ) * Real.log 2) =
        Kθ + Kθ * 2 ^ D + (Real.log 2)⁻¹ +
          (Real.log 2 ^ 2)⁻¹ + 2 / ((r.totient : ℝ) * Real.log 2) := by
        simp [lowK]
        ring
      calc
        _ ≤ (Kθ + Kθ * 2 ^ D + lowK +
            2 / ((r.totient : ℝ) * Real.log 2)) * y * (Real.log y) ^ (-A) := hfinalCoeff
        _ = _ := by rw [hcoef]

theorem prime_progressions_proof : Erdos821.Blueprint.PrimeProgressions := by
  intro A C hA hC
  obtain ⟨b, Kθ, Y₀, hb, hKθ, hY₀, hprofile⟩ :=
    exists_primeThetaAP_profile A C hA hC
  let D : ℝ := A + 4
  have hDpos : 0 < D := by dsimp [D]; linarith
  have hD : A ≤ D := by dsimp [D]; linarith
  have hAbsorb : ∀ᶠ y : ℝ in atTop,
      (Real.log y) ^ A ≤ Real.sqrt y := by
    simpa only [Real.sqrt_eq_rpow] using
      OAI.LargePrimeGaps.eventually_log_rpow_le_rpow A (s := (1 / 2 : ℝ))
        (by norm_num)
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hAbsorb
  let K : ℝ := Kθ + Kθ * 2 ^ D + (Real.log 2)⁻¹ + (Real.log 2 ^ 2)⁻¹ +
    2 / Real.log 2
  have hK : 0 < K := by
    dsimp [K]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max Y₀ Y₁)] with y hy
  have hy₀ : Y₀ ≤ y := (le_max_left _ _).trans hy
  have hy₁ : Y₁ ≤ y := (le_max_right _ _).trans hy
  have hyExp : Real.exp 4 ≤ y := hY₀.trans hy₀
  have hAbs : (Real.log y) ^ A ≤ Real.sqrt y := hY₁ y hy₁
  intro r a hr hmod ha
  have hφNat : 1 ≤ r.totient := by
    have hpos : 0 < r.totient := Nat.totient_pos.mpr (by omega)
    omega
  have hφone : (1 : ℝ) ≤ r.totient := by exact_mod_cast hφNat
  have hmain := primeCountAP_error_from_thetaProfile r a hr A D Kθ hA hD hDpos
    hKθ.le (y := y) hyExp hAbs (hprofile y hy₀ r a hr hmod ha)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconst : 2 / ((r.totient : ℝ) * Real.log 2) ≤ 2 / Real.log 2 := by
    calc
      _ = (2 / Real.log 2) / (r.totient : ℝ) := by field_simp
      _ ≤ 2 / Real.log 2 := div_le_self (by positivity) hφone
  have hcoef :
      Kθ + Kθ * 2 ^ D + (Real.log 2)⁻¹ + (Real.log 2 ^ 2)⁻¹ +
        2 / ((r.totient : ℝ) * Real.log 2) ≤ K := by
    dsimp [K]
    linarith [hconst]
  have hypos : 0 < y := lt_of_lt_of_le (Real.exp_pos 4) hyExp
  have hlogypos : 0 < Real.log y :=
    Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hyExp)
  have hscale : 0 ≤ y * (Real.log y) ^ (-A) :=
    mul_nonneg hypos.le (Real.rpow_nonneg hlogypos.le _)
  calc
    _ ≤ (Kθ + Kθ * 2 ^ D + (Real.log 2)⁻¹ + (Real.log 2 ^ 2)⁻¹ +
          2 / ((r.totient : ℝ) * Real.log 2)) * y * (Real.log y) ^ (-A) := hmain
    _ = (Kθ + Kθ * 2 ^ D + (Real.log 2)⁻¹ + (Real.log 2 ^ 2)⁻¹ +
          2 / ((r.totient : ℝ) * Real.log 2)) *
          (y * (Real.log y) ^ (-A)) := by ring
    _ ≤ K * (y * (Real.log y) ^ (-A)) :=
      mul_le_mul_of_nonneg_right hcoef hscale
    _ = K * y * (Real.log y) ^ (-A) := by ring

example : Erdos821.Blueprint.PrimeProgressions := prime_progressions_proof


end Erdos821.P1
