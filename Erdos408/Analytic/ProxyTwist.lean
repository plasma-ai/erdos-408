import Erdos408.Analytic.IntegerKernel
import Erdos408.Analytic.PNT
import Erdos408.Analytic.PrimeTwist
import Erdos408.Extraction.Defs
import PrimeNumberTheoremAnd.IEANTN.Mertens
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Twisted sums of primes minus the damped proxy

AC1 of `blueprint/rectangle_input.md` §3, the twisted-cancellation property P4
that `OneSidedTypeII` requires of its coefficient. On intervals
`I ⊂ [H, 2H]` with `x^γ / 2 ≤ H ≤ x^{K_an}`, for characters of modulus at
most `L^{C_m}` and `|t| ≤ x^{K_an}`,

  `H⁻¹ ∑_{n ∈ I} χ(n) n^{it} ([n prime, n > x^γ] - a_j^0(n)) = O(L^{-A})`,

uniformly in `1 ≤ j ≤ C_j s + 1`. Here `a_j^0` is the unstripped damped
proxy of `Erdos408.Extraction.Defs`.

The damped weight is multiplicative, `g_j(n) = ∏_{p^e ∥ n} w_p^e`, so
`g_j = λ * 1` with `λ = g_j * μ` supported on `Y`-smooth numbers and
`|λ| ≤ 1`. Then `∑_{n ∈ I} g_j(n) χ(n) n^{it} / log n` is
`∑_d λ(d) χ(d) ∑_{m ∈ I/d} χ(m) (dm)^{it} / log(dm)`.

* Divisors `d > H^{1/2}`: Rankin's trick bounds their number and their
  reciprocal mass by `H^{-1/(2 log Y)} L^{O(1)} ≤ exp(-γ T²⁵ / 2) L^{O(1)}`.
* Low frequencies `|t| ≤ L^E`: count in progressions by complete periods and
  sum by parts. The principal main terms are `D_j ∫_I u^{it} / log u` exactly,
  by the Euler product of `λ χ₀ / d`, and cancel the prime main term from the
  prime number theorem in progressions (AC0, `Erdos408.Analytic.PNT`).
* High frequencies: each inner sum is an integer kernel sum at scale
  `H / d ≥ H^{1/2}`, bounded by AC3 (`Erdos408.Analytic.IntegerKernel`); the
  prime sum is bounded by AC2 (`Erdos408.Analytic.PrimeTwist`). Both are applied
  at `x' = x^{max(K_an, 1)}`, which covers every `H, |t| ≤ x^{K_an}`.

The only other input is Mertens' bound `∑_{p ≤ Y} 1/p ≤ log log Y + O(1)`,
which gives `D_j⁻¹ ≪ L²` and Rankin's majorant `≪ L^{12}`.
-/

namespace Erdos408

open Filter Real Finset MeasureTheory ArithmeticFunction

/-! ### Partial summation -/

/-- Partial summation against a counting function with linear main term `ρ (y - a)` and
error at most `B`. -/
private theorem norm_sum_mul_sub_integral_le (c : ℕ → ℂ) {f f' : ℝ → ℂ} {a b B M : ℝ} (ρ : ℂ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hf : ∀ y ∈ Set.Icc a b, HasDerivAt f (f' y) y)
    (hf' : ContinuousOn f' (Set.Icc a b)) (hM : ∀ y ∈ Set.Icc a b, ‖f' y‖ ≤ M)
    (hB : ∀ y ∈ Set.Icc a b, ‖∑ m ∈ Ioc ⌊a⌋₊ ⌊y⌋₊, c m - ρ * (y - a)‖ ≤ B) :
    ‖∑ m ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c m * f m - ρ * ∫ y in a..b, f y‖ ≤ B * (‖f b‖ + M * (b - a)) := by
  classical
  -- the coefficients beyond `⌊a⌋₊`
  set c' : ℕ → ℂ := fun m ↦ if ⌊a⌋₊ < m then c m else 0 with hc'
  have hsum' : ∀ y, a ≤ y → ∑ m ∈ Icc 0 ⌊y⌋₊, c' m = ∑ m ∈ Ioc ⌊a⌋₊ ⌊y⌋₊, c m := by
    intro y hy
    rw [hc', ← Finset.sum_filter]
    congr 1
    ext m
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  have hderiv : Set.EqOn (deriv f) f' (Set.Icc a b) := fun y hy ↦ (hf y hy).deriv
  have hf'int : IntegrableOn f' (Set.Icc a b) := hf'.integrableOn_Icc
  have hdint : IntegrableOn (deriv f) (Set.Icc a b) :=
    hf'int.congr_fun hderiv.symm measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul c' ha hab
    (fun y hy ↦ (hf y hy).differentiableAt) hdint
  have hleft : ∑ m ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f m * c' m = ∑ m ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, c m * f m := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    simp only [hc', (mem_Ioc.mp hm).1, ite_true, mul_comm]
  have ha0 : ∑ m ∈ Icc 0 ⌊a⌋₊, c' m = 0 := by
    rw [hsum' a le_rfl, Ioc_self, sum_empty]
  rw [hleft, ha0, mul_zero, sub_zero, hsum' b hab] at habel
  -- the error term `R(y)`
  set R : ℝ → ℂ := fun y ↦ ∑ m ∈ Icc 0 ⌊y⌋₊, c' m - ρ * (y - a) with hR
  have hint1 : IntegrableOn (fun y ↦ deriv f y * ∑ m ∈ Icc 0 ⌊y⌋₊, c' m) (Set.Icc a b) :=
    integrableOn_mul_sum_Icc c' ha hdint
  have hcont2 : ContinuousOn (fun y ↦ f' y * (ρ * (y - a))) (Set.Icc a b) :=
    hf'.mul (by fun_prop)
  have hint2 : IntegrableOn (fun y ↦ deriv f y * (ρ * (y - a))) (Set.Icc a b) :=
    hcont2.integrableOn_Icc.congr_fun (fun y hy ↦ by simp only [hderiv hy]) measurableSet_Icc
  have hsplit : ∫ y in Set.Ioc a b, deriv f y * ∑ m ∈ Icc 0 ⌊y⌋₊, c' m =
      (∫ y in Set.Ioc a b, deriv f y * (ρ * (y - a))) +
        ∫ y in Set.Ioc a b, deriv f y * R y := by
    rw [← integral_add (hint2.mono_set Set.Ioc_subset_Icc_self)]
    · refine setIntegral_congr_fun measurableSet_Ioc fun y _ ↦ ?_
      simp only [hR]
      ring
    · refine (hint1.sub hint2).mono_set Set.Ioc_subset_Icc_self |>.congr_fun ?_ measurableSet_Ioc
      intro y _
      simp only [hR, Pi.sub_apply]
      ring
  -- integration by parts for the main term
  have hibp : ∫ y in a..b, f' y * (y - a) + f y * 1 = f b * (b - a) - f a * (a - a) := by
    refine intervalIntegral.integral_deriv_mul_eq_sub (u := f) (v := fun y : ℝ ↦ ((y : ℂ) - a))
      (fun y hy ↦ hf y (by rwa [Set.uIcc_of_le hab] at hy)) (fun y _ ↦ ?_) ?_ ?_
    · simpa using ((hasDerivAt_id y).ofReal_comp).sub_const (a : ℂ)
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hf'.integrableOn_Icc
    · exact intervalIntegrable_const
  have hint3 : IntervalIntegrable (fun y ↦ f' y * ((y : ℂ) - a)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hf'.mul (by fun_prop)).integrableOn_Icc
  have hint4 : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (HasDerivAt.continuousOn fun y hy ↦ hf y hy).integrableOn_Icc
  rw [intervalIntegral.integral_add hint3 (by simpa using hint4)] at hibp
  simp only [mul_one, sub_self, mul_zero, sub_zero] at hibp
  have hmain : ∫ y in Set.Ioc a b, deriv f y * (ρ * (y - a)) =
      ρ * (f b * (b - a) - ∫ y in a..b, f y) := by
    rw [← intervalIntegral.integral_of_le hab, ← hibp, add_sub_cancel_right,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y hy ↦ ?_
    rw [Set.uIcc_of_le hab] at hy
    simp only [hderiv hy]
    ring
  rw [habel, hsplit, hmain]
  have hRb : ‖R b‖ ≤ B := by
    simp only [hR, hsum' b hab]
    exact hB b ⟨hab, le_rfl⟩
  have hRint : ‖∫ y in Set.Ioc a b, deriv f y * R y‖ ≤ M * B * (b - a) := by
    rw [← intervalIntegral.integral_of_le hab]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun y hy ↦ ?_).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.mpr hab)])
    rw [Set.uIoc_of_le hab] at hy
    have hy' : y ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hy
    rw [norm_mul, hderiv hy']
    have := hB y hy'
    simp only [hR, hsum' y hy'.1]
    exact mul_le_mul (hM y hy') this (norm_nonneg _) ((norm_nonneg _).trans (hM y hy'))
  calc _ = ‖f b * R b - ∫ y in Set.Ioc a b, deriv f y * R y‖ := by
          congr 1
          simp only [hR, hsum' b hab]
          ring
    _ ≤ ‖f b‖ * B + M * B * (b - a) := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ hRint)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hRb (norm_nonneg _)
    _ = B * (‖f b‖ + M * (b - a)) := by ring

/-! ### The twisted logarithmic weight -/

/-- The twisted logarithmic weight `u^{it} / log u`. -/
private noncomputable def twistWeight (t u : ℝ) : ℂ :=
  (u : ℂ) ^ ((t : ℂ) * Complex.I) / (Real.log u : ℂ)

/-- The derivative of `twistWeight t`. -/
private noncomputable def twistWeightDeriv (t u : ℝ) : ℂ :=
  (t : ℂ) * Complex.I * (u : ℂ) ^ ((t : ℂ) * Complex.I - 1) / (Real.log u : ℂ) -
    (u : ℂ) ^ ((t : ℂ) * Complex.I) * (u⁻¹ : ℝ) / (Real.log u : ℂ) ^ 2

/-- A pure imaginary power of a positive real has norm one. -/
private theorem norm_ofReal_cpow_mul_I {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ‖(u : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp

/-- The derivative of `y ↦ y^{it}` at `u > 0`. -/
private theorem hasDerivAt_ofReal_cpow_mul_I {u : ℝ} (hu : 0 < u) (t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ ((t : ℂ) * Complex.I))
      ((t : ℂ) * Complex.I * (u : ℂ) ^ ((t : ℂ) * Complex.I - 1)) u :=
  (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hu)).hasDerivAt.comp_ofReal

/-- The derivative of `u^{it} / log u` at `u > 1`. -/
private theorem hasDerivAt_twistWeight {u : ℝ} (hu : 1 < u) (t : ℝ) :
    HasDerivAt (twistWeight t) (twistWeightDeriv t u) u := by
  have hu0 : 0 < u := by linarith
  have hlog : (Real.log u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have h1 := hasDerivAt_ofReal_cpow_mul_I hu0 t
  have h2 : HasDerivAt (fun y : ℝ ↦ (Real.log y : ℂ)) ((u⁻¹ : ℝ) : ℂ) u :=
    (Real.hasDerivAt_log hu0.ne').ofReal_comp
  convert h1.div h2 hlog using 1
  · ext y
    rfl
  · unfold twistWeightDeriv
    field_simp

/-- The derivative of the twisted weight is continuous on `u > 1`. -/
private theorem continuousOn_twistWeightDeriv (t : ℝ) :
    ContinuousOn (twistWeightDeriv t) (Set.Ioi 1) := by
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  have hlog : (Real.log u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have hslit : (u : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hu0
  have hc : ∀ s : ℂ, ContinuousAt (fun y : ℝ ↦ (y : ℂ) ^ s) u := fun s ↦
    (continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt
  have hl : ContinuousAt (fun y : ℝ ↦ (Real.log y : ℂ)) u :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hu0.ne')
  have hi : ContinuousAt (fun y : ℝ ↦ ((y⁻¹ : ℝ) : ℂ)) u :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_inv₀ hu0.ne')
  refine ContinuousAt.continuousWithinAt ?_
  exact ((continuousAt_const.mul (hc _)).div hl hlog).sub
    (((hc _).mul hi).div (hl.pow 2) (pow_ne_zero 2 hlog))

/-- `|u^{it} / log u| ≤ 1` for `u ≥ e`. -/
private theorem norm_twistWeight_le {u : ℝ} (hu : Real.exp 1 ≤ u) (t : ℝ) :
    ‖twistWeight t u‖ ≤ 1 := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu
  have hlog : 1 ≤ Real.log u := by rwa [Real.le_log_iff_exp_le hu0]
  rw [twistWeight, norm_div, norm_ofReal_cpow_mul_I hu0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith)]
  exact div_le_one_of_le₀ hlog (by linarith)

/-- `|(u^{it} / log u)'| ≤ (|t| + 1) / u` for `u ≥ e`. -/
private theorem norm_twistWeightDeriv_le {u : ℝ} (hu : Real.exp 1 ≤ u) (t : ℝ) :
    ‖twistWeightDeriv t u‖ ≤ (|t| + 1) / u := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos 1) hu
  have hlog : 1 ≤ Real.log u := by rwa [Real.le_log_iff_exp_le hu0]
  have hc : ‖(u : ℂ) ^ ((t : ℂ) * Complex.I - 1)‖ = u⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    simp [Real.rpow_neg_one]
  rw [twistWeightDeriv]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul, hc, norm_ofReal_cpow_mul_I hu0, norm_pow,
    Complex.norm_real, Complex.norm_real, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < Real.log u),
    abs_of_pos (inv_pos.mpr hu0)]
  have h1 : |t| * 1 * u⁻¹ / Real.log u ≤ |t| / u := by
    rw [mul_one, ← div_eq_mul_inv]
    exact div_le_self (div_nonneg (abs_nonneg t) hu0.le) hlog
  have h2 : 1 * u⁻¹ / Real.log u ^ 2 ≤ 1 / u := by
    rw [one_mul, one_div]
    exact div_le_self (inv_nonneg.mpr hu0.le) (one_le_pow₀ hlog)
  calc _ ≤ |t| / u + 1 / u := add_le_add h1 h2
    _ = (|t| + 1) / u := by ring

/-! ### Character sums in progressions -/

/-- A sum over the residues `0 ≤ r < k` is a sum over `ZMod k`. -/
private theorem sum_range_eq_sum_zmod {k : ℕ} [NeZero k] (g : ZMod k → ℂ) :
    ∑ r ∈ range k, g r = ∑ a : ZMod k, g a := by
  refine Finset.sum_nbij' (fun r ↦ (r : ZMod k)) (fun a ↦ a.val) (by simp) ?_ ?_ ?_ ?_
  · intro a _
    simpa using ZMod.val_lt a
  · intro r hr
    simp [ZMod.val_cast_of_lt (mem_range.mp hr)]
  · intro a _
    simp
  · intro r _
    rfl

open scoped Classical in
/-- The sum of a Dirichlet character over a complete residue system. -/
private theorem sum_range_char {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    ∑ r ∈ range k, χ r = if χ = 1 then (k.totient : ℂ) else 0 := by
  rw [sum_range_eq_sum_zmod (fun a ↦ χ a)]
  split_ifs with h
  · subst h
    classical
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one h

/-- A character sum splits along the residue classes modulo `k`. -/
private theorem sum_char_mul_eq_sum_range {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    (S : Finset ℕ) (F : ℕ → ℂ) :
    ∑ m ∈ S, χ m * F m = ∑ r ∈ range k, χ r * ∑ m ∈ S with m ≡ r [MOD k], F m := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun m ↦ m % k) (t := range k)
    (fun m _ ↦ mem_range.mpr (Nat.mod_lt m (NeZero.pos k)))]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr ?_ fun m hm ↦ ?_
  · ext m
    simp [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hr)]
  · have hm' : m % k = r := by
      have := (mem_filter.mp hm).2
      rwa [Nat.ModEq, Nat.mod_eq_of_lt (mem_range.mp hr)] at this
    congr 1
    rw [← hm', ← ZMod.natCast_mod]

/-- The number of `m ∈ (M, N]` in a residue class modulo `k` is `(N - M) / k + O(1)`. -/
private theorem abs_card_filter_modEq_sub_le {k : ℕ} (hk : 0 < k) (r : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    |(#{m ∈ Ioc M N | m ≡ r [MOD k]} : ℝ) - ((N : ℝ) - M) / k| ≤ 2 := by
  have hsplit : #{m ∈ range (N + 1) | m ≡ r [MOD k]} =
      #{m ∈ range (M + 1) | m ≡ r [MOD k]} + #{m ∈ Ioc M N | m ≡ r [MOD k]} := by
    have hr : range (N + 1) = range (M + 1) ∪ Ioc M N := by
      ext m
      simp only [mem_range, mem_union, mem_Ioc]
      omega
    rw [hr, filter_union, card_union_of_disjoint]
    refine disjoint_filter_filter (disjoint_left.mpr fun m h1 h2 ↦ ?_)
    simp only [mem_range, mem_Ioc] at h1 h2
    omega
  have hcount : ∀ b : ℕ, |(#{m ∈ range b | m ≡ r [MOD k]} : ℝ) - b / k| ≤ 1 := by
    intro b
    rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hk]
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 : ((b / k : ℕ) : ℝ) ≤ b / k := Nat.cast_div_le
    have h2 : (b : ℝ) / k - 1 < ((b / k : ℕ) : ℝ) := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ hk']
      have := Nat.lt_div_mul_add (a := b) hk
      have : (b : ℝ) < ((b / k : ℕ) : ℝ) * k + k := by exact_mod_cast this
      linarith
    rw [abs_le]
    split_ifs <;> push_cast <;> constructor <;> linarith
  have hN := hcount (N + 1)
  have hM := hcount (M + 1)
  rw [hsplit] at hN
  push_cast at hN hM
  rw [abs_le] at *
  have : ((N : ℝ) + 1) / k - ((M : ℝ) + 1) / k = ((N : ℝ) - M) / k := by ring
  constructor <;> linarith

/-- A character sum over `(M, N]` is `(N - M) / k ∑_r χ(r) + O(k)`. -/
private theorem norm_sum_Ioc_char_sub_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {M N : ℕ}
    (hMN : M ≤ N) :
    ‖∑ m ∈ Ioc M N, χ m - (((N : ℝ) - M) / k : ℝ) * ∑ r ∈ range k, χ r‖ ≤ 2 * k := by
  have h := sum_char_mul_eq_sum_range χ (Ioc M N) (fun _ ↦ 1)
  simp only [mul_one, sum_const, nsmul_eq_mul, mul_one] at h
  rw [h, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r ∈ range k, ‖χ r * (#{m ∈ Ioc M N | m ≡ r [MOD k]} : ℂ) -
        (((N : ℝ) - M) / k : ℝ) * χ r‖
      ≤ ∑ r ∈ range k, (2 : ℝ) := by
        refine Finset.sum_le_sum fun r _ ↦ ?_
        rw [mul_comm, ← sub_mul, norm_mul]
        have hχ := DirichletCharacter.norm_le_one χ r
        have hcount := abs_card_filter_modEq_sub_le (NeZero.pos k) r hMN
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact (mul_le_of_le_one_right (abs_nonneg _) hχ).trans hcount
    _ = 2 * k := by simp [mul_comm]

/-! ### The multiplicative structure of the damped weight -/

/-- The local value `w_p` of the damped weight: `g_j(p^e) = w_p^e`. -/
private noncomputable def dampedLocal (x : ℝ) (j p : ℕ) : ℝ :=
  if p ∈ candidatePrimes x then (j : ℝ)⁻¹ else if (p : ℝ) ≤ proxyCutoff x then 0 else 1

/-- The damped weight as an arithmetic function, `n ↦ ∏_{p^e ∥ n} w_p^e`. -/
private noncomputable def dampedFun (x : ℝ) (j : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else n.factorization.prod fun p e ↦ dampedLocal x j p ^ e,
    ite_eq_left rfl⟩

/-- The Möbius transform `λ = g_j * μ` of the damped weight. -/
private noncomputable def dampedMobius (x : ℝ) (j : ℕ) : ArithmeticFunction ℝ :=
  dampedFun x j * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

/-- The local values `w_p` are nonnegative. -/
private theorem dampedLocal_nonneg (x : ℝ) {j : ℕ} (p : ℕ) : 0 ≤ dampedLocal x j p := by
  unfold dampedLocal
  split_ifs <;> positivity

/-- The local values `w_p` are at most one. -/
private theorem dampedLocal_le_one (x : ℝ) {j : ℕ} (hj : 1 ≤ j) (p : ℕ) :
    dampedLocal x j p ≤ 1 := by
  unfold dampedLocal
  split_ifs
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hj)
  · exact zero_le_one
  · exact le_rfl

/-- `g_j(n) = ∏_{p^e ∥ n} w_p^e` for `n ≠ 0`. -/
private theorem dampedFun_apply {x : ℝ} {j n : ℕ} (hn : n ≠ 0) :
    dampedFun x j n = n.factorization.prod fun p e ↦ dampedLocal x j p ^ e := by
  simp [dampedFun, hn]

/-- The damped weight is multiplicative. -/
private theorem isMultiplicative_dampedFun (x : ℝ) (j : ℕ) : (dampedFun x j).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [dampedFun_apply one_ne_zero], fun {m n} hm hn hmn ↦ ?_⟩
  rw [dampedFun_apply (mul_ne_zero hm hn), dampedFun_apply hm, dampedFun_apply hn,
    Nat.factorization_mul hm hn,
    Finsupp.prod_add_index_of_disjoint (by simpa using hmn.disjoint_primeFactors)]

/-- `g_j(p^e) = w_p^e`. -/
private theorem dampedFun_prime_pow (x : ℝ) (j : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dampedFun x j (p ^ e) = dampedLocal x j p ^ e := by
  rw [dampedFun_apply (pow_ne_zero e hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (by simp)]

/-- The prime factors of `stripPrimes P n` are those of `n` outside `P`. -/
private theorem mem_primeFactors_stripPrimes {P : Finset ℕ} {n p : ℕ} (hn : n ≠ 0) :
    p ∈ (stripPrimes P n).primeFactors ↔ p ∈ n.primeFactors ∧ p ∉ P := by
  have hne : stripPrimes P n ≠ 0 := by
    unfold stripPrimes
    exact Finset.prod_ne_zero_iff.mpr fun q hq ↦
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors (mem_filter.mp hq).1).ne_zero
  rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    unfold stripPrimes at hdvd
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
    have hq' := mem_filter.mp hq
    have hqp := Nat.prime_of_mem_primeFactors hq'.1
    have := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (hp.dvd_of_dvd_pow hpq)
    subst this
    exact ⟨⟨hp, Nat.dvd_of_mem_primeFactors hq'.1, hn⟩, hq'.2⟩
  · rintro ⟨⟨hp, hdvd, -⟩, hP⟩
    refine ⟨hp, ?_, hne⟩
    unfold stripPrimes
    refine (dvd_pow_self p ?_).trans (Finset.dvd_prod_of_mem _ (mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩, hP⟩))
    exact (Nat.Prime.factorization_pos_of_dvd hp hn hdvd).ne'

/-- The damped weight is the multiplicative function `dampedFun`. -/
private theorem dampedWeight_eq_dampedFun (x : ℝ) (j : ℕ) {n : ℕ} (hn : n ≠ 0) :
    dampedWeight x j n = dampedFun x j n := by
  classical
  rw [dampedFun_apply hn, Finsupp.prod, Nat.support_factorization,
    ← prod_filter_mul_prod_filter_not n.primeFactors (· ∈ candidatePrimes x)]
  have h1 : ∏ p ∈ n.primeFactors with p ∈ candidatePrimes x,
      dampedLocal x j p ^ n.factorization p = ((j : ℝ)⁻¹) ^ candidateOmega x n := by
    rw [candidateOmega, ← prod_pow_eq_pow_sum]
    refine prod_congr rfl fun p hp ↦ ?_
    rw [dampedLocal, ite_eq_left (mem_filter.mp hp).2]
  rw [h1, dampedWeight]
  split_ifs with h
  · rw [prod_eq_one, mul_one]
    intro p hp
    have hp' := mem_filter.mp hp
    have hY := h p ((mem_primeFactors_stripPrimes hn).mpr hp')
    rw [dampedLocal, ite_eq_right hp'.2, ite_eq_right (not_le.mpr hY), one_pow]
  · simp only [not_forall, not_lt] at h
    obtain ⟨p, hp, hY⟩ := h
    have hp' := (mem_primeFactors_stripPrimes hn).mp hp
    rw [prod_eq_zero (i := p) (mem_filter.mpr hp'), mul_zero]
    rw [dampedLocal, ite_eq_right hp'.2, ite_eq_left hY]
    exact zero_pow (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp'.1) hn
      (Nat.dvd_of_mem_primeFactors hp'.1)).ne'

/-- `λ = g_j * μ` is multiplicative. -/
private theorem isMultiplicative_dampedMobius (x : ℝ) (j : ℕ) :
    (dampedMobius x j).IsMultiplicative :=
  (isMultiplicative_dampedFun x j).mul isMultiplicative_moebius.intCast

/-- `λ * 1 = g_j`. -/
private theorem dampedMobius_mul_zeta (x : ℝ) (j : ℕ) :
    dampedMobius x j * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = dampedFun x j := by
  rw [dampedMobius, mul_assoc, coe_moebius_mul_coe_zeta (R := ℝ), mul_one]

/-- `g_j(n) = ∑_{d ∣ n} λ(d)`. -/
private theorem sum_divisors_dampedMobius (x : ℝ) (j n : ℕ) :
    ∑ d ∈ n.divisors, dampedMobius x j d = dampedFun x j n := by
  rw [← coe_mul_zeta_apply, dampedMobius_mul_zeta]

/-- `λ(p^{e+1}) = w_p^{e+1} - w_p^e`. -/
private theorem dampedMobius_prime_pow_succ (x : ℝ) (j : ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dampedMobius x j (p ^ (e + 1)) = dampedLocal x j p ^ (e + 1) - dampedLocal x j p ^ e := by
  have h := fun e ↦ sum_divisors_dampedMobius x j (p ^ e)
  simp only [Nat.sum_divisors_prime_pow hp, dampedFun_prime_pow x j hp] at h
  rw [← h (e + 1), ← h e, Finset.sum_range_succ _ (e + 1)]
  ring

/-- `λ(1) = 1`. -/
private theorem dampedMobius_one (x : ℝ) (j : ℕ) : dampedMobius x j 1 = 1 :=
  (isMultiplicative_dampedMobius x j).map_one

/-- `|λ(n)| ≤ 1`. -/
private theorem abs_dampedMobius_le (x : ℝ) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    |dampedMobius x j n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [(isMultiplicative_dampedMobius x j).multiplicative_factorization _ hn, Finsupp.prod,
    abs_prod]
  refine prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun p hp ↦ ?_
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  obtain ⟨e, he⟩ : ∃ e, n.factorization p = e + 1 :=
    Nat.exists_eq_add_one.mpr (Finsupp.mem_support_iff.mp hp |>.bot_lt)
  rw [he, dampedMobius_prime_pow_succ x j hp', abs_le]
  have h0 := dampedLocal_nonneg x (j := j) p
  have h1 := dampedLocal_le_one x hj p
  have := pow_le_one₀ h0 h1 (n := e + 1)
  have := pow_le_one₀ h0 h1 (n := e)
  have := pow_nonneg h0 (e + 1)
  have := pow_nonneg h0 e
  constructor <;> linarith

/-- `λ` is supported on `Y`-smooth numbers, once the candidate primes lie below `Y`. -/
private theorem mem_factoredNumbers_of_dampedMobius_ne_zero {x : ℝ} {j n : ℕ}
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) (h : dampedMobius x j n ≠ 0) :
    n ∈ Nat.factoredNumbers (primesIcc 2 (proxyCutoff x)) := by
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h
  rw [Nat.mem_factoredNumbers]
  refine ⟨hn, fun p hp ↦ ?_⟩
  have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  have hpn : p ∈ n.primeFactors := Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp
  have hY : (p : ℝ) ≤ proxyCutoff x := by
    by_contra hY
    apply h
    rw [(isMultiplicative_dampedMobius x j).multiplicative_factorization _ hn, Finsupp.prod]
    refine prod_eq_zero (i := p) (by simpa using hpn) ?_
    obtain ⟨e, he⟩ : ∃ e, n.factorization p = e + 1 :=
      Nat.exists_eq_add_one.mpr (Nat.Prime.factorization_pos_of_dvd hpp hn
        (Nat.dvd_of_mem_primeFactors hpn))
    have hP' : p ∉ candidatePrimes x := fun hc ↦ hY (hP p hc)
    rw [he, dampedMobius_prime_pow_succ x j hpp, dampedLocal, ite_eq_right hP', ite_eq_right hY]
    simp
  simp only [primesIcc, mem_filter, mem_Icc]
  refine ⟨⟨?_, Nat.le_floor hY⟩, hpp⟩
  simpa using hpp.two_le

/-- The local Euler factor `∑_e λ(p^e) χ(p)^e p^{-e} = (1 - z) / (1 - w z)` with `z = χ(p)/p`. -/
private theorem tsum_dampedMobius_prime_pow {x : ℝ} {j : ℕ} (hj : 1 ≤ j) {k : ℕ}
    (χ : DirichletCharacter ℂ k) {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, (dampedMobius x j (p ^ e) : ℂ) * χ (p ^ e : ℕ) / ((p ^ e : ℕ) : ℂ) =
      (1 - χ p / p) / (1 - dampedLocal x j p * χ p / p) := by
  set z : ℂ := χ p / p with hz
  set w : ℂ := (dampedLocal x j p : ℂ) with hw
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hznorm : ‖z‖ ≤ 1 / 2 := by
    rw [hz, norm_div, Complex.norm_natCast]
    calc ‖χ p‖ / p ≤ 1 / p := by gcongr; exact DirichletCharacter.norm_le_one χ _
      _ ≤ 1 / 2 := by gcongr
  have hwnorm : ‖w‖ ≤ 1 := by
    rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dampedLocal_nonneg x p)]
    exact dampedLocal_le_one x hj p
  have hwz : ‖w * z‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg z]
  have hterm : ∀ e : ℕ, (dampedMobius x j (p ^ (e + 1)) : ℂ) * χ (p ^ (e + 1) : ℕ) /
      ((p ^ (e + 1) : ℕ) : ℂ) = (w - 1) * z * (w * z) ^ e := by
    intro e
    rw [dampedMobius_prime_pow_succ x j hp, Nat.cast_pow, map_pow, Nat.cast_pow, hz, hw]
    push_cast
    have : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    simp only [mul_pow, div_pow]
    field_simp
    ring
  have hgeom : Summable fun e : ℕ ↦ (w - 1) * z * (w * z) ^ e :=
    (summable_geometric_of_norm_lt_one hwz).mul_left _
  have hsum : Summable fun e : ℕ ↦ (dampedMobius x j (p ^ e) : ℂ) * χ (p ^ e : ℕ) /
      ((p ^ e : ℕ) : ℂ) := by
    rw [← summable_nat_add_iff 1]
    simpa only [hterm] using hgeom
  rw [hsum.tsum_eq_zero_add]
  simp only [hterm, pow_zero, dampedMobius_one, Nat.cast_one, map_one, div_one,
    Complex.ofReal_one, mul_one]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hwz]
  have h1 : 1 - w * z ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at hwz
    exact lt_irrefl _ hwz
  have : w * χ p / p = w * z := by rw [hz, mul_div_assoc]
  rw [this]
  field_simp
  ring

/-- The Euler product of `λ(d) χ(d) / d` over `Y`-smooth numbers. -/
private theorem hasSum_dampedMobius_char {x : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) {k : ℕ}
    (χ : DirichletCharacter ℂ k) :
    HasSum (fun d : ℕ ↦ (dampedMobius x j d : ℂ) * χ d / d)
      (∏ p ∈ primesIcc 2 (proxyCutoff x),
        (1 - χ p / p) / (1 - dampedLocal x j p * χ p / p)) := by
  set f : ℕ → ℂ := fun d ↦ (dampedMobius x j d : ℂ) * χ d / d with hf
  have hf1 : f 1 = 1 := by simp [hf, dampedMobius_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hf, (isMultiplicative_dampedMobius x j).map_mul_of_coprime hmn, Nat.cast_mul,
      map_mul, Complex.ofReal_mul]
    ring
  have hsum : ∀ {p : ℕ}, p.Prime → Summable fun e : ℕ ↦ ‖f (p ^ e)‖ := by
    intro p hp
    have hp1 : (1 / p : ℝ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hp.pos)]
      exact_mod_cast hp.one_lt
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun e ↦ ?_)
      (summable_geometric_of_lt_one (by positivity) hp1)
    rw [hf, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast,
      one_div_pow, Nat.cast_pow]
    have := mul_le_mul (abs_dampedMobius_le x hj (p ^ e))
      (DirichletCharacter.norm_le_one χ ((p : ZMod k) ^ e)) (norm_nonneg _) zero_le_one
    rw [one_mul] at this
    rw [Nat.cast_pow]
    exact div_le_div_of_nonneg_right this (pow_nonneg (Nat.cast_nonneg p) e)
  obtain ⟨-, hS⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hf1 hmul hsum (primesIcc 2 (proxyCutoff x))
  have hsupp : Function.support f ⊆ Nat.factoredNumbers (primesIcc 2 (proxyCutoff x)) := by
    intro d hd
    refine mem_factoredNumbers_of_dampedMobius_ne_zero (j := j) hP fun h ↦ hd ?_
    simp [hf, h]
  convert (hasSum_subtype_iff_of_support_subset hsupp).mp hS using 1
  have hprime : ∀ p ∈ primesIcc 2 (proxyCutoff x), p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  rw [filter_true_of_mem hprime]
  refine prod_congr rfl fun p hp ↦ ?_
  rw [← tsum_dampedMobius_prime_pow hj χ (hprime p hp)]

/-- The primes of the groups `[e^y, e^{2y})`, `y = 2^i L^a`, `2y ≤ L^b`, lie in
`[exp(L^a), exp(L^b)]`. -/
private theorem mem_doublingGroups {x a b : ℝ} (hx : 0 ≤ Real.log x) {G : Finset ℕ}
    (hG : G ∈ doublingGroups x a b) {p : ℕ} (hp : p ∈ G) :
    p.Prime ∧ Real.exp (Real.log x ^ a) ≤ p ∧ (p : ℝ) ≤ Real.exp (Real.log x ^ b) := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hG
  have hi' := (mem_filter.mp hi).2
  have hp' := mem_filter.mp hp
  have hIcc := mem_Icc.mp hp'.1
  have hLa : 0 ≤ Real.log x ^ a := Real.rpow_nonneg hx a
  refine ⟨hp'.2, ?_, ?_⟩
  · calc Real.exp (Real.log x ^ a) ≤ Real.exp (2 ^ i * Real.log x ^ a) := by
          gcongr
          exact le_mul_of_one_le_left hLa (one_le_pow₀ (by norm_num))
      _ ≤ ⌈Real.exp (2 ^ i * Real.log x ^ a)⌉₊ := Nat.le_ceil _
      _ ≤ p := by exact_mod_cast hIcc.1
  · have h1 : (p : ℝ) < Real.exp (2 * (2 ^ i * Real.log x ^ a)) := by
      have h2 := hIcc.2
      rw [Nat.floor_natCast] at h2
      have h3 := Nat.ceil_lt_add_one (Real.exp_pos (2 * (2 ^ i * Real.log x ^ a))).le
      have h4 : (p : ℝ) + 1 ≤ ⌈Real.exp (2 * (2 ^ i * Real.log x ^ a))⌉₊ := by
        have : p + 1 ≤ ⌈Real.exp (2 * (2 ^ i * Real.log x ^ a))⌉₊ := by
          have hpos : 0 < ⌈Real.exp (2 * (2 ^ i * Real.log x ^ a))⌉₊ :=
            Nat.ceil_pos.mpr (Real.exp_pos _)
          omega
        exact_mod_cast this
      linarith
    refine h1.le.trans (Real.exp_le_exp.mpr ?_)
    calc 2 * (2 ^ i * Real.log x ^ a) = 2 ^ (i + 1) * Real.log x ^ a := by ring
      _ ≤ Real.log x ^ b := hi'

/-- The candidate primes are primes in `[exp(L^{0.28}), exp(L^{0.45})]`. -/
private theorem mem_candidatePrimes {x : ℝ} {p : ℕ} (hx : 1 ≤ Real.log x)
    (hp : p ∈ candidatePrimes x) :
    p.Prime ∧ Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (45 / 100 : ℝ)) := by
  obtain ⟨G, hG, hpG⟩ := mem_biUnion.mp hp
  rcases mem_union.mp hG with hG | hG
  · obtain ⟨h1, h2, h3⟩ := mem_doublingGroups (zero_le_one.trans hx) hG hpG
    refine ⟨h1, h2, h3.trans (Real.exp_le_exp.mpr ?_)⟩
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  · obtain ⟨h1, h2, h3⟩ := mem_doublingGroups (zero_le_one.trans hx) hG hpG
    refine ⟨h1, (Real.exp_le_exp.mpr ?_).trans h2, h3⟩
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

/-- The candidate primes are prime. -/
private theorem prime_of_mem_candidatePrimes {x : ℝ} {p : ℕ} (hp : p ∈ candidatePrimes x) :
    p.Prime := by
  obtain ⟨G, hG, hpG⟩ := mem_biUnion.mp hp
  rcases mem_union.mp hG with hG | hG <;>
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hG
    exact (mem_filter.mp hpG).2

/-- The principal character at a prime `p` is `[p ∤ k]`. -/
private theorem one_apply_prime {k p : ℕ} (hp : p.Prime) :
    (1 : DirichletCharacter ℂ k) p = if p ∣ k then 0 else 1 := by
  split_ifs with h
  · refine MulChar.map_nonunit _ fun hu ↦ ?_
    rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd] at hu
    exact hu h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime p k).mpr (hp.coprime_iff_not_dvd.mpr h))

/-- The principal Euler product times `φ(k) / k` is exactly `D_j`. -/
private theorem totient_div_mul_prod_eq_dampedDensity {x : ℝ} {j k : ℕ} (hk : 1 ≤ k)
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x)
    (hkY : (k : ℝ) ≤ proxyCutoff x) (hkP : ∀ p ∈ candidatePrimes x, k < p) :
    ((k.totient : ℂ) / k) * ∏ p ∈ primesIcc 2 (proxyCutoff x),
        (1 - (1 : DirichletCharacter ℂ k) p / p) /
          (1 - dampedLocal x j p * (1 : DirichletCharacter ℂ k) p / p) =
      (dampedDensity x j : ℂ) := by
  classical
  set s := primesIcc 2 (proxyCutoff x) with hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hmem : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ proxyCutoff x → p ∈ s := by
    intro p hp hpY
    simp only [hs, primesIcc, mem_filter, mem_Icc]
    exact ⟨⟨by simpa using hp.two_le, Nat.le_floor hpY⟩, hp⟩
  have hsY : ∀ p ∈ s, (p : ℝ) ≤ proxyCutoff x := by
    intro p hp
    have h := (mem_Icc.mp (mem_filter.mp hp).1).2
    have hY0 : 0 ≤ proxyCutoff x := (Real.exp_pos _).le
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le hY0)
  -- the primes of `k` are exactly the primes of `s` dividing `k`
  have hpk : s.filter (· ∣ k) = k.primeFactors := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd⟩
      exact ⟨hprime p hp, hdvd, by omega⟩
    · rintro ⟨hp, hdvd, -⟩
      refine ⟨hmem p hp ?_, hdvd⟩
      exact (Nat.cast_le.mpr (Nat.le_of_dvd (by omega) hdvd)).trans hkY
  -- the candidate primes are exactly the primes of `s` not dividing `k` with `w_p ≠ 0`
  have hPs : ∀ p ∈ candidatePrimes x, p ∈ s.filter (¬ · ∣ k) := by
    intro p hp
    have hpp : p.Prime := prime_of_mem_candidatePrimes hp
    refine mem_filter.mpr ⟨hmem p hpp (hP p hp), fun hdvd ↦ ?_⟩
    have := Nat.le_of_dvd (by omega) hdvd
    have := hkP p hp
    omega
  have hloc : ∀ p ∈ s.filter (¬ · ∣ k),
      (1 - (1 : DirichletCharacter ℂ k) p / p) /
          (1 - dampedLocal x j p * (1 : DirichletCharacter ℂ k) p / p) =
        (1 - 1 / (p : ℂ)) * (if p ∈ candidatePrimes x then (1 - (j : ℂ)⁻¹ / p)⁻¹ else 1) := by
    intro p hp
    have hp' := mem_filter.mp hp
    rw [one_apply_prime (hprime p hp'.1), ite_eq_right hp'.2, dampedLocal]
    split_ifs with hc hY
    · push_cast
      ring
    · simp
    · exact absurd (hsY p hp'.1) hY
  have hdiv : ∀ p ∈ s.filter (· ∣ k),
      (1 - (1 : DirichletCharacter ℂ k) p / p) /
          (1 - dampedLocal x j p * (1 : DirichletCharacter ℂ k) p / p) = 1 := by
    intro p hp
    have hp' := mem_filter.mp hp
    rw [one_apply_prime (hprime p hp'.1), ite_eq_left hp'.2]
    simp
  rw [← prod_filter_mul_prod_filter_not s (· ∣ k), prod_congr rfl hdiv, prod_const_one, one_mul,
    prod_congr rfl hloc, prod_mul_distrib, ← prod_filter, dampedDensity]
  have hfilt : (s.filter (¬ · ∣ k)).filter (· ∈ candidatePrimes x) = candidatePrimes x := by
    ext p
    simp only [mem_filter]
    constructor
    · exact fun h ↦ h.2
    · exact fun h ↦ ⟨mem_filter.mp (hPs p h), h⟩
  rw [hfilt]
  -- `φ(k) / k = ∏_{p ∣ k} (1 - 1/p)`
  have htot : ((k.totient : ℂ) / k) = ∏ p ∈ s.filter (· ∣ k), (1 - 1 / (p : ℂ)) := by
    rw [hpk]
    have h := Nat.totient_eq_mul_prod_factors k
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h' : ((k.totient : ℚ) / k) = ∏ p ∈ k.primeFactors, (1 - (p : ℚ)⁻¹) := by
      rw [h]
      field_simp
    have := congrArg (fun q : ℚ ↦ (q : ℂ)) h'
    push_cast at this
    simpa [one_div] using this
  rw [htot, ← mul_assoc, prod_filter_mul_prod_filter_not]
  push_cast
  rfl

/-! ### Rankin's trick -/

/-- Rankin's majorant `∏_{p ∈ s} (1 - p^{ε - 1})⁻¹ = ∑_{d s-factored} d^{ε - 1}`. -/
private noncomputable def rankinProd (s : Finset ℕ) (ε : ℝ) : ℝ :=
  ∏ p ∈ s with p.Prime, (1 - (p : ℝ) ^ (ε - 1))⁻¹

/-- The completely multiplicative function `n ↦ n^r`. -/
private noncomputable def natRpowHom (r : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ r
  map_one' := by simp
  map_mul' m n := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)

/-- Rankin's series `∑_{d s-factored} d^{ε - 1}` converges to `rankinProd s ε`. -/
private theorem hasSum_rankin (s : Finset ℕ) {ε : ℝ} (hε : ε < 1) :
    HasSum ((Nat.factoredNumbers s).indicator fun d : ℕ ↦ (d : ℝ) ^ (ε - 1)) (rankinProd s ε) := by
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := natRpowHom (ε - 1)) (fun {p} hp ↦ ?_) s).2
  · rw [← hasSum_subtype_iff_indicator]
    exact h
  · change ‖(p : ℝ) ^ (ε - 1)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- The terms of Rankin's series are nonnegative. -/
private theorem rankin_indicator_nonneg (s : Finset ℕ) (ε : ℝ) (d : ℕ) :
    0 ≤ (Nat.factoredNumbers s).indicator (fun d : ℕ ↦ (d : ℝ) ^ (ε - 1)) d :=
  Set.indicator_nonneg (fun _ _ ↦ by positivity) d

/-- A finite part of Rankin's series is at most its sum. -/
private theorem sum_rpow_le_rankinProd (s : Finset ℕ) {ε : ℝ} (hε : ε < 1) (F : Finset ℕ)
    (hF : ∀ d ∈ F, d ∈ Nat.factoredNumbers s) :
    ∑ d ∈ F, (d : ℝ) ^ (ε - 1) ≤ rankinProd s ε := by
  have h := sum_le_hasSum F (fun d _ ↦ rankin_indicator_nonneg s ε d) (hasSum_rankin s hε)
  refine le_of_eq_of_le (sum_congr rfl fun d hd ↦ ?_) h
  rw [Set.indicator_of_mem (hF d hd)]

/-- Rankin's bound for the tail `∑_{d ≥ X} 1/d` over `s`-factored numbers. -/
private theorem sum_inv_le_rankinProd (s : Finset ℕ) {ε X : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hX : 0 < X)
    (F : Finset ℕ) (hF : ∀ d ∈ F, d ∈ Nat.factoredNumbers s ∧ X ≤ d) :
    ∑ d ∈ F, (1 : ℝ) / d ≤ X ^ (-ε) * rankinProd s ε := by
  have hR := sum_rpow_le_rankinProd s hε F fun d hd ↦ (hF d hd).1
  calc ∑ d ∈ F, (1 : ℝ) / d ≤ ∑ d ∈ F, X ^ (-ε) * (d : ℝ) ^ (ε - 1) := by
        refine sum_le_sum fun d hd ↦ ?_
        have hd0 : 0 < (d : ℝ) := hX.trans_le (hF d hd).2
        have h1 : (1 : ℝ) / d = (d : ℝ) ^ (-ε) * (d : ℝ) ^ (ε - 1) := by
          rw [← Real.rpow_add hd0, show -ε + (ε - 1) = -1 by ring, Real.rpow_neg_one, one_div]
        rw [h1]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd0.le _)
        exact Real.rpow_le_rpow_of_nonpos hX (hF d hd).2 (by linarith : -ε ≤ 0)
    _ = X ^ (-ε) * ∑ d ∈ F, (d : ℝ) ^ (ε - 1) := by rw [mul_sum]
    _ ≤ X ^ (-ε) * rankinProd s ε := by gcongr

/-- Rankin's bound for the number of `s`-factored numbers up to `N`. -/
private theorem card_le_rankinProd (s : Finset ℕ) {ε N : ℝ} (hε : ε < 1) (hN : 0 < N)
    (F : Finset ℕ) (hF : ∀ d ∈ F, d ∈ Nat.factoredNumbers s ∧ (d : ℝ) ≤ N) :
    (F.card : ℝ) ≤ N ^ (1 - ε) * rankinProd s ε := by
  have hR := sum_rpow_le_rankinProd s hε F fun d hd ↦ (hF d hd).1
  rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  calc ∑ d ∈ F, (1 : ℝ) ≤ ∑ d ∈ F, N ^ (1 - ε) * (d : ℝ) ^ (ε - 1) := by
        refine sum_le_sum fun d hd ↦ ?_
        have hd0 : d ≠ 0 := ((hF d hd).1).1
        have hd1 : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd0
        have h1 : (d : ℝ) ^ (1 - ε) * (d : ℝ) ^ (ε - 1) = 1 := by
          rw [← Real.rpow_add hd1, show 1 - ε + (ε - 1) = 0 by ring, Real.rpow_zero]
        calc (1 : ℝ) = (d : ℝ) ^ (1 - ε) * (d : ℝ) ^ (ε - 1) := h1.symm
          _ ≤ N ^ (1 - ε) * (d : ℝ) ^ (ε - 1) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd1.le (hF d hd).2 (by linarith))
              (Real.rpow_nonneg hd1.le _)
    _ = N ^ (1 - ε) * ∑ d ∈ F, (d : ℝ) ^ (ε - 1) := by rw [mul_sum]
    _ ≤ N ^ (1 - ε) * rankinProd s ε := by gcongr

/-- Rankin's bound for the tail of a series supported on `s`-factored numbers and dominated
by `1/d`. -/
private theorem norm_sub_sum_range_le_rankinProd (s : Finset ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    {F : ℕ → ℂ} {a : ℂ} (hF : HasSum F a)
    (hFle : ∀ d, ‖F d‖ ≤ (Nat.factoredNumbers s).indicator (fun d : ℕ ↦ (1 : ℝ) / d) d)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖a - ∑ d ∈ range M, F d‖ ≤ (M : ℝ) ^ (-ε) * rankinProd s ε := by
  set g := (Nat.factoredNumbers s).indicator fun d : ℕ ↦ (d : ℝ) ^ (ε - 1) with hg
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hFt := (hasSum_nat_add_iff' M).mpr hF
  have hgt := ((hasSum_nat_add_iff' M).mpr (hasSum_rankin s hε)).mul_left ((M : ℝ) ^ (-ε))
  have hle : ∀ n, ‖F (n + M)‖ ≤ (M : ℝ) ^ (-ε) * g (n + M) := by
    intro n
    refine (hFle (n + M)).trans ?_
    by_cases hn : n + M ∈ Nat.factoredNumbers s
    · rw [Set.indicator_of_mem hn, hg, Set.indicator_of_mem hn]
      have hd : (M : ℝ) ≤ (n + M : ℕ) := by exact_mod_cast Nat.le_add_left M n
      have hd0 : (0 : ℝ) < (n + M : ℕ) := hM0.trans_le hd
      have h1 : (1 : ℝ) / (n + M : ℕ) = ((n + M : ℕ) : ℝ) ^ (-ε) * ((n + M : ℕ) : ℝ) ^ (ε - 1) := by
        rw [← Real.rpow_add hd0, show -ε + (ε - 1) = -1 by ring, Real.rpow_neg_one, one_div]
      rw [h1]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hM0 hd (by linarith))
        (Real.rpow_nonneg hd0.le _)
    · rw [Set.indicator_of_notMem hn, hg, Set.indicator_of_notMem hn, mul_zero]
  have h := tsum_of_norm_bounded hgt hle
  rw [hFt.tsum_eq] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hM0.le _))
  have : 0 ≤ ∑ i ∈ range M, g i := sum_nonneg fun i _ ↦ rankin_indicator_nonneg s ε i
  linarith

/-- `(1 - v)⁻¹ ≤ exp(4 v)` for `0 ≤ v ≤ 3/4`. -/
private theorem inv_one_sub_le_exp {v : ℝ} (hv0 : 0 ≤ v) (hv : v ≤ 3 / 4) :
    (1 - v)⁻¹ ≤ Real.exp (4 * v) := by
  have h1 : 0 < 1 - v := by linarith
  refine (inv_le_iff_one_le_mul₀ h1).mpr ?_
  have h2 := Real.add_one_le_exp (4 * v)
  have h3 : 1 ≤ (4 * v + 1) * (1 - v) := by nlinarith
  exact h3.trans (mul_le_mul_of_nonneg_right (by linarith) h1.le)

/-- Rankin's majorant over the primes up to `Y` is at most `exp(4 Y^ε ∑_{p ≤ Y} 1/p)`. -/
private theorem rankinProd_le {Y ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) :
    rankinProd (primesIcc 2 Y) ε ≤
      Real.exp (4 * Y ^ ε * ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p) := by
  have hprime : ∀ p ∈ primesIcc 2 Y, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  rw [rankinProd, filter_true_of_mem hprime, mul_sum, Real.exp_sum]
  refine prod_le_prod₀ (fun p _ ↦ ?_) fun p hp ↦ ?_
  · have hp := hprime p ‹_›
    have : (p : ℝ) ^ (ε - 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
    exact inv_nonneg.mpr (by linarith)
  · have hpp := hprime p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpY : (p : ℝ) ≤ Y := by
      have h := (mem_Icc.mp (mem_filter.mp hp).1).2
      have hY : 0 ≤ Y := by
        by_contra hY
        rw [Nat.floor_eq_zero.mpr (by linarith)] at h
        have := hpp.two_le
        omega
      exact (Nat.cast_le.mpr h).trans (Nat.floor_le hY)
    have hv0 : 0 ≤ (p : ℝ) ^ (ε - 1) := Real.rpow_nonneg hp0.le _
    have hv : (p : ℝ) ^ (ε - 1) ≤ 3 / 4 := by
      calc (p : ℝ) ^ (ε - 1) ≤ (p : ℝ) ^ (-(1 / 2) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
        _ ≤ 3 / 4 := by
          rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
          rw [inv_le_comm₀ (by positivity) (by norm_num), Real.le_sqrt (by norm_num) (by norm_num)]
          norm_num
    refine (inv_one_sub_le_exp hv0 hv).trans (Real.exp_le_exp.mpr ?_)
    have : (p : ℝ) ^ (ε - 1) ≤ Y ^ ε * (1 / p) := by
      rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le hpY hε0) (by positivity)
    linarith

/-! ### The density and the prime harmonic sum -/

/-- `exp(-2u) ≤ 1 - u` for `0 ≤ u ≤ 1/2`. -/
private theorem exp_neg_two_mul_le_one_sub {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    Real.exp (-(2 * u)) ≤ 1 - u := by
  rw [Real.exp_neg]
  have h1 := Real.add_one_le_exp (2 * u)
  have h2 : 1 ≤ (1 - u) * (2 * u + 1) := by nlinarith
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (by linarith))

/-- `D_j ≥ exp(-2 ∑_{p ≤ Y} 1/p)`. -/
private theorem exp_le_dampedDensity (x : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    Real.exp (-(2 * ∑ p ∈ primesIcc 2 (proxyCutoff x), (1 : ℝ) / p)) ≤ dampedDensity x j := by
  have hprime : ∀ p ∈ primesIcc 2 (proxyCutoff x), p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [dampedDensity, ← mul_one (Real.exp _), mul_sum, ← sum_neg_distrib, Real.exp_sum]
  have hA : ∏ p ∈ primesIcc 2 (proxyCutoff x), Real.exp (-(2 * (1 / (p : ℝ)))) ≤
      ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) := by
    refine prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    exact exp_neg_two_mul_le_one_sub (by positivity)
      (by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
  have hB : 1 ≤ ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
    refine one_le_prod₀ fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).two_le
    have h1 : (j : ℝ)⁻¹ / p ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      have := inv_le_one_of_one_le₀ hj'
      linarith
    have h2 : 0 ≤ (j : ℝ)⁻¹ / p := by positivity
    exact one_le_inv₀ (by linarith) |>.mpr (by linarith)
  exact mul_le_mul hA hB zero_le_one (prod_nonneg fun p hp ↦ by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith)

/-- Mertens' bound `∑_{p ≤ Y} 1/p ≤ log log Y + C`. -/
private theorem exists_sum_primesIcc_inv_le : ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y →
    ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ Real.log (Real.log Y) + C := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨C, fun Y hY ↦ ?_⟩
  have h := (abs_le.mp (hC Y hY)).2
  have hset : primesIcc 2 Y = (Ioc 0 ⌊Y⌋₊).filter Nat.Prime := by
    ext p
    simp only [primesIcc, mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨-, h2⟩, hp⟩
      exact ⟨⟨hp.pos, h2⟩, hp⟩
    · rintro ⟨⟨-, h2⟩, hp⟩
      exact ⟨⟨by simpa using hp.two_le, h2⟩, hp⟩
  rw [hset]
  linarith

/-! ### Sums over divisors -/

/-- Exchanging `∑_{n ∈ (A, B]} ∑_{d ∣ n}`, for any `B' ≥ B`. -/
private theorem sum_Ioc_sum_divisors {A B B' : ℕ} (hB : B ≤ B') (F : ℕ → ℕ → ℂ) :
    ∑ n ∈ Ioc A B, ∑ d ∈ n.divisors, F d n =
      ∑ d ∈ Icc 1 B', ∑ m ∈ Ioc (A / d) (B / d), F d (d * m) := by
  rw [Finset.sum_comm' (t' := Icc 1 B') (s' := fun d ↦ (Ioc A B).filter (d ∣ ·))]
  · refine sum_congr rfl fun d hd ↦ ?_
    have hd1 : 0 < d := (mem_Icc.mp hd).1
    symm
    refine sum_nbij' (fun m ↦ d * m) (fun n ↦ n / d) (fun m hm ↦ ?_) (fun n hn ↦ ?_)
      (fun m _ ↦ by simp [Nat.mul_div_cancel_left _ hd1]) (fun n hn ↦ ?_) (fun _ _ ↦ rfl)
    · have hm' := mem_Ioc.mp hm
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, dvd_mul_right d m⟩
      · rw [mul_comm]
        exact (Nat.div_lt_iff_lt_mul hd1).mp hm'.1
      · rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hd1).mp hm'.2
    · have hn' := mem_filter.mp hn
      obtain ⟨m, rfl⟩ := hn'.2
      have hI := mem_Ioc.mp hn'.1
      rw [Nat.mul_div_cancel_left _ hd1]
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hd1).mpr (by rw [mul_comm]; exact hI.1)
      · exact (Nat.le_div_iff_mul_le hd1).mpr (by rw [mul_comm]; exact hI.2)
    · obtain ⟨m, rfl⟩ := (mem_filter.mp hn).2
      simp [Nat.mul_div_cancel_left _ hd1]
  · intro n d
    simp only [mem_Ioc, Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd, -⟩
      have hn : 0 < n := by omega
      exact ⟨⟨⟨h1, h2⟩, hdvd⟩, Nat.pos_of_dvd_of_pos hdvd hn,
        (Nat.le_of_dvd hn hdvd).trans (h2.trans hB)⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, -⟩
      exact ⟨⟨h1, h2⟩, hdvd, by omega⟩

/-- The damped sum as a sum over the divisors `d` of its Möbius transform. -/
private theorem sum_dampedFun_eq (x : ℝ) (j : ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k) (f : ℝ → ℂ)
    {A B B' : ℕ} (hB : B ≤ B') :
    ∑ n ∈ Ioc A B, (dampedFun x j n : ℂ) * (χ n * f n) =
      ∑ d ∈ Icc 1 B', (dampedMobius x j d : ℂ) * χ d *
        ∑ m ∈ Ioc (A / d) (B / d), χ m * f ((d : ℝ) * m) := by
  have h : ∀ n, (dampedFun x j n : ℂ) * (χ n * f n) =
      ∑ d ∈ n.divisors, (dampedMobius x j d : ℂ) * (χ n * f n) := by
    intro n
    rw [← sum_mul, ← sum_divisors_dampedMobius, Complex.ofReal_sum]
  simp_rw [h]
  rw [sum_Ioc_sum_divisors hB]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  push_cast
  rw [map_mul]
  ring

/-! ### The inner sums -/

/-- Partial summation against `twistWeight t (d y)` on `[lo/d, hi/d]`. -/
private theorem norm_sum_twistWeight_scaled_sub_le (c : ℕ → ℂ) (t : ℝ) (ρ : ℂ) {B lo hi : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hlo : Real.exp 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi - lo ≤ lo)
    (hB : ∀ y ∈ Set.Icc (lo / d) (hi / d),
      ‖∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊y⌋₊, c m - ρ * ((y : ℂ) - ((lo / d : ℝ) : ℂ))‖ ≤ B) :
    ‖∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊hi / d⌋₊, c m * twistWeight t ((d : ℝ) * m) -
        ρ * (((d : ℂ))⁻¹ * ∫ u in lo..hi, twistWeight t u)‖ ≤ B * (|t| + 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo0 : 0 < lo := (Real.exp_pos 1).trans_le hlo
  have hmem : ∀ y ∈ Set.Icc (lo / d) (hi / d), lo ≤ d * y := by
    intro y hy
    have := mul_le_mul_of_nonneg_left hy.1 hd0.le
    rwa [mul_div_cancel₀ _ hd0.ne'] at this
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hderiv : ∀ y ∈ Set.Icc (lo / d) (hi / d), HasDerivAt (fun y ↦ twistWeight t (d * y))
      ((d : ℝ) • twistWeightDeriv t (d * y)) y := by
    intro y hy
    have h1 : 1 < (d : ℝ) * y := by linarith [hmem y hy]
    exact (hasDerivAt_twistWeight h1 t).scomp y ((hasDerivAt_id y).const_mul (d : ℝ) |>.congr_deriv
      (by simp))
  have hcont : ContinuousOn (fun y ↦ (d : ℝ) • twistWeightDeriv t (d * y))
      (Set.Icc (lo / d) (hi / d)) := by
    refine ContinuousOn.const_smul (c := (d : ℝ)) ((continuousOn_twistWeightDeriv t).comp
      (continuous_const.mul continuous_id).continuousOn fun y hy ↦ ?_)
    have := hmem y hy
    exact Set.mem_Ioi.mpr (show 1 < (d : ℝ) * y by linarith)
  have hM : ∀ y ∈ Set.Icc (lo / d) (hi / d),
      ‖(d : ℝ) • twistWeightDeriv t (d * y)‖ ≤ d * ((|t| + 1) / lo) := by
    intro y hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd0]
    refine mul_le_mul_of_nonneg_left ?_ hd0.le
    refine (norm_twistWeightDeriv_le (hlo.trans (hmem y hy)) t).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) hlo0 (hmem y hy)
  have hab : lo / d ≤ hi / d := div_le_div_of_nonneg_right hlohi hd0.le
  have h := norm_sum_mul_sub_integral_le c ρ (by positivity) hab hderiv hcont hM hB
  have hint : ∫ y in lo / d..hi / d, twistWeight t (d * y) =
      ((d : ℂ))⁻¹ * ∫ u in lo..hi, twistWeight t u := by
    rw [intervalIntegral.integral_comp_mul_left _ hd0.ne', mul_div_cancel₀ _ hd0.ne',
      mul_div_cancel₀ _ hd0.ne', Complex.real_smul]
    push_cast
    rfl
  rw [hint] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ((norm_nonneg _).trans (hB _ ⟨le_rfl, hab⟩)))
  have h1 : ‖twistWeight t (d * (hi / d))‖ ≤ 1 :=
    norm_twistWeight_le (hlo.trans (hmem _ ⟨hab, le_rfl⟩)) t
  have h2 : d * ((|t| + 1) / lo) * (hi / d - lo / d) ≤ |t| + 1 := by
    rw [← sub_div, mul_comm (d : ℝ), mul_assoc, mul_div_cancel₀ _ hd0.ne', div_mul_eq_mul_div,
      div_le_iff₀ hlo0]
    exact mul_le_mul_of_nonneg_left hhi (by positivity)
  linarith

/-- The inner sum `T_d = ∑_{m ∈ I/d} χ(m) (dm)^{it} / log(dm)`. -/
private noncomputable def innerSum {k : ℕ} (χ : DirichletCharacter ℂ k) (t lo hi : ℝ) (d : ℕ) : ℂ :=
  ∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊hi / d⌋₊, χ m * twistWeight t ((d : ℝ) * m)

/-- The damped twisted sum is `∑_d λ(d) χ(d) T_d`. -/
private theorem sum_dampedFun_eq_innerSum (x : ℝ) (j : ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (t : ℝ) {lo hi : ℝ} {B' : ℕ} (hB' : ⌊hi⌋₊ ≤ B') :
    ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (dampedFun x j n : ℂ) * (χ n * twistWeight t n) =
      ∑ d ∈ Icc 1 B', (dampedMobius x j d : ℂ) * χ d * innerSum χ t lo hi d := by
  rw [sum_dampedFun_eq x j χ (twistWeight t) hB']
  refine sum_congr rfl fun d _ ↦ ?_
  rw [innerSum, Nat.floor_div_natCast, Nat.floor_div_natCast]

/-- Trivially, `‖T_d‖ ≤ (hi - lo) / d + 1`. -/
private theorem norm_innerSum_le {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ) {lo hi : ℝ}
    (hlo : Real.exp 1 ≤ lo) (hlohi : lo ≤ hi) {d : ℕ} (hd : 1 ≤ d) :
    ‖innerSum χ t lo hi d‖ ≤ (hi - lo) / d + 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo0 : 0 ≤ lo := ((Real.exp_pos 1).trans_le hlo).le
  rw [innerSum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m ∈ Ioc ⌊lo / d⌋₊ ⌊hi / d⌋₊, ‖χ m * twistWeight t ((d : ℝ) * m)‖ ≤ 1 := by
    intro m hm
    rw [norm_mul]
    refine (mul_le_mul (DirichletCharacter.norm_le_one χ _) (norm_twistWeight_le (hlo.trans ?_) t)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have h1 : lo / d < m := Nat.lt_of_floor_lt (mem_Ioc.mp hm).1
    have := mul_lt_mul_of_pos_left h1 hd0
    rw [mul_div_cancel₀ _ hd0.ne'] at this
    exact this.le
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
  have h1 : ((⌊hi / d⌋₊ : ℕ) : ℝ) ≤ hi / d := Nat.floor_le (div_nonneg (hlo0.trans hlohi) hd0.le)
  have h2 : lo / d - 1 < ((⌊lo / d⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (lo / d)
    linarith
  rw [Nat.cast_sub (Nat.floor_le_floor (div_le_div_of_nonneg_right hlohi hd0.le)), sub_div]
  linarith

/-- The divisors `d > D₀` contribute `O(H D₀^{-ε} Π + hi^{1-ε} Π)` by Rankin's trick. -/
private theorem norm_sum_large_divisors_le {x : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (t : ℝ) {lo hi ε : ℝ} (hlo : Real.exp 1 ≤ lo) (hlohi : lo ≤ hi)
    (hε0 : 0 ≤ ε) (hε : ε < 1) {D₀ B' : ℕ} (hB' : B' ≤ max ⌊hi⌋₊ D₀) :
    ‖∑ d ∈ (Icc 1 B').filter (D₀ < ·), (dampedMobius x j d : ℂ) * χ d * innerSum χ t lo hi d‖ ≤
      (hi - lo) * (((D₀ : ℝ) + 1) ^ (-ε) * rankinProd (primesIcc 2 (proxyCutoff x)) ε) +
        hi ^ (1 - ε) * rankinProd (primesIcc 2 (proxyCutoff x)) ε := by
  classical
  set s := primesIcc 2 (proxyCutoff x)
  set F := ((Icc 1 B').filter (D₀ < ·)).filter fun d ↦ dampedMobius x j d ≠ 0 with hF
  have hFs : ∀ d ∈ F, d ∈ Nat.factoredNumbers s := fun d hd ↦
    mem_factoredNumbers_of_dampedMobius_ne_zero hP (mem_filter.mp hd).2
  have hFd : ∀ d ∈ F, 1 ≤ d ∧ D₀ < d ∧ d ≤ ⌊hi⌋₊ := by
    intro d hd
    have h1 := mem_filter.mp (mem_filter.mp hd).1
    have h2 := mem_Icc.mp h1.1
    exact ⟨h2.1, h1.2, by have := h2.2; have := h1.2; omega⟩
  have hlo0 : 0 ≤ lo := ((Real.exp_pos 1).trans_le hlo).le
  have hhi0 : 0 < hi := ((Real.exp_pos 1).trans_le hlo).trans_le hlohi
  rw [← sum_filter_of_ne (p := fun d ↦ dampedMobius x j d ≠ 0) fun d _ h h0 ↦ h (by simp [h0])]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d ∈ F, ‖(dampedMobius x j d : ℂ) * χ d * innerSum χ t lo hi d‖ ≤
      (hi - lo) * (1 / d) + 1 := by
    intro d hd
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_dampedMobius_le x hj d
    have h2 := DirichletCharacter.norm_le_one χ d
    have h3 := norm_innerSum_le χ t hlo hlohi (hFd d hd).1
    have h4 : |dampedMobius x j d| * ‖χ d‖ ≤ 1 :=
      (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    calc _ ≤ 1 * ((hi - lo) / d + 1) :=
          mul_le_mul h4 h3 (norm_nonneg _) zero_le_one
      _ = (hi - lo) * (1 / d) + 1 := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
  have hinv := sum_inv_le_rankinProd s hε0 hε (X := (D₀ : ℝ) + 1) (by positivity) F
    fun d hd ↦ ⟨hFs d hd, by have := (hFd d hd).2.1; exact_mod_cast this⟩
  have hcard := card_le_rankinProd s hε hhi0 F fun d hd ↦ ⟨hFs d hd,
    (Nat.cast_le.mpr (hFd d hd).2.2).trans (Nat.floor_le hhi0.le)⟩
  exact add_le_add (mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr hlohi)) hcard

/-- The mean `k⁻¹ ∑_{r < k} χ(r)` of a character over a period, `[χ = 1] φ(k)/k`. -/
private noncomputable def charMean {k : ℕ} (χ : DirichletCharacter ℂ k) : ℂ :=
  (∑ r ∈ range k, χ r) / k

/-- The mean of a character over a period has norm at most one. -/
private theorem norm_charMean_le {k : ℕ} (χ : DirichletCharacter ℂ k) : ‖charMean χ‖ ≤ 1 := by
  rw [charMean, norm_div, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_one hk']
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum (g := fun _ ↦ (1 : ℝ))
    fun r _ ↦ DirichletCharacter.norm_le_one χ _).trans ?_
  simp

open scoped Classical in
/-- The principal mean times the Euler product of `λ χ / d` is `[χ = 1] D_j`. -/
private theorem charMean_mul_prod_eq {x : ℝ} {j k : ℕ} [NeZero k]
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x)
    (hkY : (k : ℝ) ≤ proxyCutoff x) (hkP : ∀ p ∈ candidatePrimes x, k < p)
    (χ : DirichletCharacter ℂ k) :
    charMean χ * ∏ p ∈ primesIcc 2 (proxyCutoff x),
        (1 - χ p / p) / (1 - dampedLocal x j p * χ p / p) =
      if χ = 1 then (dampedDensity x j : ℂ) else 0 := by
  rw [charMean, sum_range_char]
  split_ifs with h
  · subst h
    exact totient_div_mul_prod_eq_dampedDensity (NeZero.pos k) hP hkY hkP
  · simp

/-- The character count in `(lo/d, y]` has main term `charMean χ (y - lo/d)`. -/
private theorem norm_sum_char_sub_charMean_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {a y : ℝ} (ha : 0 ≤ a) (hay : a ≤ y) :
    ‖∑ m ∈ Ioc ⌊a⌋₊ ⌊y⌋₊, χ m - charMean χ * ((y : ℂ) - (a : ℂ))‖ ≤ 2 * k + 1 := by
  have hk : (0 : ℝ) < k := by exact_mod_cast NeZero.pos k
  have hMN : ⌊a⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hay
  have h1 := norm_sum_Ioc_char_sub_le χ hMN
  have hS : ‖∑ r ∈ range k, χ r‖ ≤ k := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum (g := fun _ ↦ (1 : ℝ))
    fun r _ ↦ DirichletCharacter.norm_le_one χ _).trans ?_
    simp
  have hfl : |(((⌊y⌋₊ : ℝ) - ⌊a⌋₊) - (y - a))| ≤ 1 := by
    have := Nat.floor_le ha
    have := Nat.lt_floor_add_one a
    have := Nat.floor_le (ha.trans hay)
    have := Nat.lt_floor_add_one y
    rw [abs_le]
    constructor <;> linarith
  have h2 : ‖(((⌊y⌋₊ : ℝ) - ⌊a⌋₊) / k : ℝ) * ∑ r ∈ range k, χ r -
      charMean χ * ((y : ℂ) - (a : ℂ))‖ ≤ 1 := by
    rw [charMean]
    have : ((((⌊y⌋₊ : ℝ) - ⌊a⌋₊) / k : ℝ) : ℂ) * ∑ r ∈ range k, χ r -
        (∑ r ∈ range k, χ r) / k * ((y : ℂ) - (a : ℂ)) =
        (((((⌊y⌋₊ : ℝ) - ⌊a⌋₊) - (y - a)) / k : ℝ) : ℂ) * ∑ r ∈ range k, χ r := by
      push_cast
      ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hk]
    calc |((⌊y⌋₊ : ℝ) - ⌊a⌋₊) - (y - a)| / k * ‖∑ r ∈ range k, χ r‖ ≤ 1 / k * k := by
          gcongr
      _ = 1 := by field_simp
  calc _ = ‖(∑ m ∈ Ioc ⌊a⌋₊ ⌊y⌋₊, χ m - (((⌊y⌋₊ : ℝ) - ⌊a⌋₊) / k : ℝ) * ∑ r ∈ range k, χ r) +
        ((((⌊y⌋₊ : ℝ) - ⌊a⌋₊) / k : ℝ) * ∑ r ∈ range k, χ r - charMean χ * ((y : ℂ) - a))‖ := by
        ring_nf
    _ ≤ 2 * k + 1 := (norm_add_le _ _).trans (add_le_add h1 h2)

/-- Low frequencies: `T_d = charMean χ · d⁻¹ ∫ u^{it} / log u + O(k (|t| + 1))`. -/
private theorem norm_innerSum_sub_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (t : ℝ)
    {lo hi : ℝ} (hlo : Real.exp 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi - lo ≤ lo) {d : ℕ}
    (hd : 1 ≤ d) :
    ‖innerSum χ t lo hi d - charMean χ * (((d : ℂ))⁻¹ * ∫ u in lo..hi, twistWeight t u)‖ ≤
      (2 * k + 1) * (|t| + 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo0 : 0 ≤ lo := ((Real.exp_pos 1).trans_le hlo).le
  refine norm_sum_twistWeight_scaled_sub_le (fun m ↦ χ m) t (charMean χ) hd hlo hlohi hhi
    fun y hy ↦ ?_
  exact norm_sum_char_sub_charMean_le χ (div_nonneg hlo0 hd0.le) hy.1

/-- The twisted weight integrates to at most `hi - lo`. -/
private theorem norm_integral_twistWeight_le (t : ℝ) {lo hi : ℝ} (hlo : Real.exp 1 ≤ lo)
    (hlohi : lo ≤ hi) : ‖∫ u in lo..hi, twistWeight t u‖ ≤ hi - lo := by
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun u hu ↦ ?_).trans_eq ?_
  · rw [Set.uIoc_of_le hlohi] at hu
    exact norm_twistWeight_le (hlo.trans hu.1.le) t
  · rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hlohi)]

open scoped Classical in
/-- The damped sum at low frequencies: `∑ g_j χ n^{it} / log n = [χ = 1] D_j ∫ + error`. -/
private theorem norm_sum_dampedFun_sub_le {x : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) {k : ℕ} [NeZero k]
    (hkY : (k : ℝ) ≤ proxyCutoff x) (hkP : ∀ p ∈ candidatePrimes x, k < p)
    (χ : DirichletCharacter ℂ k) (t : ℝ) {lo hi ε : ℝ} (hlo : Real.exp 1 ≤ lo)
    (hlohi : lo ≤ hi) (hhi : hi - lo ≤ lo) (hε0 : 0 ≤ ε) (hε : ε < 1) (D₀ : ℕ) :
    ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (dampedFun x j n : ℂ) * (χ n * twistWeight t n) -
        (if χ = 1 then (dampedDensity x j : ℂ) * ∫ u in lo..hi, twistWeight t u else 0)‖ ≤
      2 * ((hi - lo) * (((D₀ : ℝ) + 1) ^ (-ε) * rankinProd (primesIcc 2 (proxyCutoff x)) ε)) +
        hi ^ (1 - ε) * rankinProd (primesIcc 2 (proxyCutoff x)) ε +
          D₀ * ((2 * k + 1) * (|t| + 2)) := by
  set B' := max ⌊hi⌋₊ D₀
  set J := ∫ u in lo..hi, twistWeight t u with hJ
  set R := rankinProd (primesIcc 2 (proxyCutoff x)) ε
  set a := ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - χ p / p) / (1 - dampedLocal x j p * χ p / p)
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 B') (D₀ < ·)
    fun d ↦ (dampedMobius x j d : ℂ) * χ d * innerSum χ t lo hi d
  have hsmall : (Icc 1 B').filter (fun d ↦ ¬ D₀ < d) = Icc 1 D₀ := by
    ext d
    simp only [mem_filter, mem_Icc, not_lt, B']
    omega
  rw [hsmall] at hsplit
  have hmain : (if χ = 1 then (dampedDensity x j : ℂ) * J else 0) = charMean χ * a * J := by
    rw [charMean_mul_prod_eq hP hkY hkP χ]
    split_ifs <;> simp
  rw [sum_dampedFun_eq_innerSum x j χ t (le_max_left _ _), ← hsplit, hmain]
  -- the small divisors
  set E : ℕ → ℂ := fun d ↦ innerSum χ t lo hi d - charMean χ * (((d : ℂ))⁻¹ * J) with hE
  set S₀ := ∑ d ∈ range (D₀ + 1), (dampedMobius x j d : ℂ) * χ d / d
  have hsmall_eq : ∑ d ∈ Icc 1 D₀, (dampedMobius x j d : ℂ) * χ d * innerSum χ t lo hi d =
      charMean χ * J * S₀ + ∑ d ∈ Icc 1 D₀, (dampedMobius x j d : ℂ) * χ d * E d := by
    have hr : S₀ = ∑ d ∈ Icc 1 D₀, (dampedMobius x j d : ℂ) * χ d / d := by
      simp only [S₀]
      rw [sum_range_succ']
      simp only [Nat.cast_zero, div_zero, add_zero]
      refine sum_nbij' (· + 1) (· - 1) (fun i hi ↦ ?_) (fun i hi ↦ ?_) (fun i _ ↦ by simp)
        (fun i hi ↦ ?_) (fun i _ ↦ by push_cast; rfl)
      · simp only [mem_range] at hi
        simp only [mem_Icc]
        omega
      · simp only [mem_Icc] at hi
        simp only [mem_range]
        omega
      · simp only [mem_Icc] at hi
        omega
    rw [hr, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun d _ ↦ ?_
    simp only [hE]
    ring
  rw [hsmall_eq]
  -- the three error terms
  have htail := norm_sum_large_divisors_le hj hP χ t hlo hlohi hε0 hε (D₀ := D₀) (B' := B') le_rfl
  have hE_le : ‖∑ d ∈ Icc 1 D₀, (dampedMobius x j d : ℂ) * χ d * E d‖ ≤
      D₀ * ((2 * k + 1) * (|t| + 2)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum (g := fun _ ↦ (2 * (k : ℝ) + 1) * (|t| + 2)) fun d hd ↦ ?_).trans ?_
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h4 : |dampedMobius x j d| * ‖χ d‖ ≤ 1 :=
        (mul_le_mul (abs_dampedMobius_le x hj d) (DirichletCharacter.norm_le_one χ _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
      have h5 := norm_innerSum_sub_le χ t hlo hlohi hhi (mem_Icc.mp hd).1
      exact (mul_le_mul h4 h5 (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · simp
  have hS₀ : ‖a - S₀‖ ≤ ((D₀ : ℝ) + 1) ^ (-ε) * R := by
    have h := norm_sub_sum_range_le_rankinProd (primesIcc 2 (proxyCutoff x)) hε0 hε
      (hasSum_dampedMobius_char hj hP χ) (fun d ↦ ?_) (M := D₀ + 1) (by omega)
    · push_cast at h
      exact h
    by_cases hd : dampedMobius x j d = 0
    · simp only [hd, Complex.ofReal_zero, zero_mul, zero_div, norm_zero]
      exact Set.indicator_nonneg (fun d _ ↦ by positivity) d
    · rw [Set.indicator_of_mem (mem_factoredNumbers_of_dampedMobius_ne_zero hP hd), norm_div,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right ((mul_le_mul (abs_dampedMobius_le x hj d)
        (DirichletCharacter.norm_le_one χ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
        (Nat.cast_nonneg d)
  have hJ_le := norm_integral_twistWeight_le t hlo hlohi
  have hmainerr : ‖charMean χ * J * S₀ - charMean χ * a * J‖ ≤
      (hi - lo) * (((D₀ : ℝ) + 1) ^ (-ε) * R) := by
    have : charMean χ * J * S₀ - charMean χ * a * J = -(charMean χ * J * (a - S₀)) := by ring
    rw [this, norm_neg, norm_mul, norm_mul]
    calc ‖charMean χ‖ * ‖J‖ * ‖a - S₀‖ ≤ 1 * (hi - lo) * (((D₀ : ℝ) + 1) ^ (-ε) * R) := by
          gcongr
          exact norm_charMean_le χ
      _ = _ := by ring
  calc _ = ‖∑ d ∈ (Icc 1 B').filter (D₀ < ·), (dampedMobius x j d : ℂ) * χ d *
          innerSum χ t lo hi d + (charMean χ * J * S₀ - charMean χ * a * J) +
        ∑ d ∈ Icc 1 D₀, (dampedMobius x j d : ℂ) * χ d * E d‖ := by ring_nf
    _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add (norm_add_le _ _) hE_le).trans ?_
        linarith

/-- `T_d = d^{it} ∑_{m ∈ I/d} χ(m) m^{it} / log(dm)`. -/
private theorem innerSum_eq {k : ℕ} (χ : DirichletCharacter ℂ k) (t lo hi : ℝ) (d : ℕ) :
    innerSum χ t lo hi d = (d : ℂ) ^ ((t : ℂ) * Complex.I) *
      ∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊hi / d⌋₊, χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I) *
        twistWeight 0 ((d : ℝ) * m) := by
  rw [innerSum, mul_sum]
  refine sum_congr rfl fun m _ ↦ ?_
  simp only [twistWeight, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, Complex.ofReal_mul,
    Complex.ofReal_natCast]
  have h : ((d : ℂ) * m) ^ ((t : ℂ) * Complex.I) =
      (d : ℂ) ^ ((t : ℂ) * Complex.I) * (m : ℂ) ^ ((t : ℂ) * Complex.I) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m) _
  rw [h]
  ring

/-- High frequencies: given kernel bounds `K / d` on the inner sums for `d ≤ D₀`, the damped
sum is `O(K Π + H D₀^{-ε} Π + hi^{1-ε} Π)`. -/
private theorem norm_sum_dampedFun_le_of_kernel {x : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (t : ℝ) {lo hi ε K : ℝ} (hlo : Real.exp 1 ≤ lo)
    (hlohi : lo ≤ hi) (hhi : hi - lo ≤ lo) (hε0 : 0 ≤ ε) (hε : ε < 1) (D₀ : ℕ) (hK0 : 0 ≤ K)
    (hK : ∀ d : ℕ, 1 ≤ d → d ≤ D₀ → ∀ y ∈ Set.Icc (lo / d) (hi / d),
      ‖∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊y⌋₊, χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ K / d) :
    ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (dampedFun x j n : ℂ) * (χ n * twistWeight t n)‖ ≤
      2 * K * rankinProd (primesIcc 2 (proxyCutoff x)) ε +
        ((hi - lo) * (((D₀ : ℝ) + 1) ^ (-ε) * rankinProd (primesIcc 2 (proxyCutoff x)) ε) +
          hi ^ (1 - ε) * rankinProd (primesIcc 2 (proxyCutoff x)) ε) := by
  classical
  set B' := max ⌊hi⌋₊ D₀
  set R := rankinProd (primesIcc 2 (proxyCutoff x)) ε
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 B') (D₀ < ·)
    fun d ↦ (dampedMobius x j d : ℂ) * χ d * innerSum χ t lo hi d
  have hsmall : (Icc 1 B').filter (fun d ↦ ¬ D₀ < d) = Icc 1 D₀ := by
    ext d
    simp only [mem_filter, mem_Icc, not_lt, B']
    omega
  rw [hsmall] at hsplit
  rw [sum_dampedFun_eq_innerSum x j χ t (le_max_left _ _), ← hsplit]
  have htail := norm_sum_large_divisors_le hj hP χ t hlo hlohi hε0 hε (D₀ := D₀) (B' := B') le_rfl
  refine (norm_add_le _ _).trans ?_
  rw [add_comm (2 * K * R)]
  refine add_le_add htail ?_
  -- each small divisor contributes at most `2K / d`
  have hterm : ∀ d ∈ Icc 1 D₀, ‖(dampedMobius x j d : ℂ) * χ d * innerSum χ t lo hi d‖ ≤
      (if dampedMobius x j d = 0 then 0 else 2 * K * (1 / d)) := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    split_ifs with h0
    · simp [h0]
    have h1 : ‖innerSum χ t lo hi d‖ ≤ K / d * (|0| + 2) := by
      have hn : ‖(d : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
        simpa using norm_ofReal_cpow_mul_I hd0 t
      rw [innerSum_eq, norm_mul, hn, one_mul]
      have h := norm_sum_twistWeight_scaled_sub_le (fun m ↦ χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I))
        0 0 hd1 hlo hlohi hhi (B := K / d) fun y hy ↦ by
          simpa using hK d hd1 (mem_Icc.mp hd).2 y hy
      simpa using h
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h4 : |dampedMobius x j d| * ‖χ d‖ ≤ 1 :=
      (mul_le_mul (abs_dampedMobius_le x hj d) (DirichletCharacter.norm_le_one χ _)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    refine (mul_le_mul h4 h1 (norm_nonneg _) zero_le_one).trans_eq ?_
    simp only [abs_zero, zero_add, one_mul]
    ring
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← sum_filter_of_ne (p := fun d ↦ dampedMobius x j d ≠ 0) fun d _ h h0 ↦ h (by simp [h0])]
  rw [sum_congr rfl fun d hd ↦ ite_eq_right (mem_filter.mp hd).2, ← mul_sum]
  have h := sum_inv_le_rankinProd (primesIcc 2 (proxyCutoff x)) hε0 hε (X := 1) one_pos
    ((Icc 1 D₀).filter fun d ↦ dampedMobius x j d ≠ 0) fun d hd ↦
      ⟨mem_factoredNumbers_of_dampedMobius_ne_zero hP (mem_filter.mp hd).2,
        by exact_mod_cast (mem_Icc.mp (mem_filter.mp hd).1).1⟩
  rw [Real.one_rpow, one_mul] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ### The prime sum -/

/-- There are at most `√N (log₂ N + 1)` proper prime powers up to `N`. -/
private theorem card_isPrimePow_not_prime_le (N : ℕ) :
    #{n ∈ Ioc 0 N | IsPrimePow n ∧ ¬ n.Prime} ≤ Nat.sqrt N * (Nat.log 2 N + 1) := by
  classical
  have hsub : {n ∈ Ioc 0 N | IsPrimePow n ∧ ¬ n.Prime} ⊆
      (Icc 1 (Nat.sqrt N) ×ˢ range (Nat.log 2 N + 1)).image fun pe ↦ pe.1 ^ pe.2 := by
    intro n hn
    obtain ⟨hnN, hpow, hnp⟩ := by simpa only [mem_filter] using hn
    obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hpow
    have hN := (mem_Ioc.mp hnN).2
    have he2 : 2 ≤ e := by
      by_contra h
      have : e = 1 := by omega
      subst this
      exact hnp (by simpa using hp)
    refine mem_image.mpr ⟨(p, e), mem_product.mpr ⟨mem_Icc.mpr ⟨hp.one_lt.le, ?_⟩,
      mem_range.mpr ?_⟩, rfl⟩
    · refine Nat.le_sqrt.mpr ?_
      calc p * p = p ^ 2 := (sq p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he2
        _ ≤ N := hN
    · refine Nat.lt_succ_of_le (Nat.le_log_of_pow_le one_lt_two ?_)
      exact (Nat.pow_le_pow_left hp.two_le e).trans hN
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_product, Nat.card_Icc, card_range, Nat.add_sub_cancel]

/-- Replacing `∑ χ(p) p^{it}` by `∑ Λ(n) χ(n) n^{it} / log n` costs the proper prime powers. -/
private theorem norm_sum_vonMangoldt_sub_sum_prime_le {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ)
    (A N : ℕ) :
    ‖∑ n ∈ Ioc A N, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * twistWeight t n -
        ∑ n ∈ Ioc A N, ((if n.Prime then 1 else 0 : ℝ) : ℂ) *
          (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I))‖ ≤
      Nat.sqrt N * (Nat.log 2 N + 1) := by
  classical
  rw [← sum_sub_distrib]
  have hterm : ∀ n ∈ Ioc A N, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n * twistWeight t n -
      ((if n.Prime then 1 else 0 : ℝ) : ℂ) * (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I))‖ ≤
      if IsPrimePow n ∧ ¬ n.Prime then 1 else 0 := by
    intro n hn
    have hn0 : 0 < n := by have := (mem_Ioc.mp hn).1; omega
    by_cases hp : n.Prime
    · have hlog : (Real.log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp, twistWeight]
      simp only [hp, ite_true, Complex.ofReal_one, one_mul, not_true_eq_false, and_false,
        Complex.ofReal_natCast, ite_false]
      rw [norm_le_zero_iff, sub_eq_zero]
      field_simp
    · simp only [hp, ite_false, Complex.ofReal_zero, zero_mul, sub_zero, not_false_eq_true,
        and_true]
      by_cases hpp : IsPrimePow n
      · rw [ite_eq_left hpp, norm_mul, norm_mul, twistWeight, norm_div,
          norm_ofReal_cpow_mul_I (by exact_mod_cast hn0), Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := n)
        have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hpp.one_lt)
        rw [abs_of_nonneg hΛ0, abs_of_pos hlog]
        calc ArithmeticFunction.vonMangoldt n * ‖χ n‖ * (1 / Real.log n)
            ≤ Real.log n * 1 * (1 / Real.log n) := by
              gcongr
              exact DirichletCharacter.norm_le_one χ _
          _ = 1 := by field_simp
      · rw [ite_eq_right hpp, ArithmeticFunction.vonMangoldt_apply, ite_eq_right hpp]
        simp
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Ioc A N).filter (fun n ↦ IsPrimePow n ∧ ¬ n.Prime) ⊆
      (Ioc 0 N).filter (fun n ↦ IsPrimePow n ∧ ¬ n.Prime) := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn ⊢
    exact ⟨⟨hn.2.1.pos, hn.1.2⟩, hn.2⟩
  exact_mod_cast (card_le_card hsub).trans (card_isPrimePow_not_prime_le N)

open scoped Classical in
/-- Low frequencies: partial summation of the prime number theorem in progressions. -/
private theorem norm_sum_vonMangoldt_sub_le {c C : ℝ} (hc1 : c ≤ 1)
    (hPNT : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
      ‖∑ n ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          (if χ = 1 then (y : ℂ) else 0)‖ ≤ C * (k : ℝ) ^ C * y ^ (1 - c))
    {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (t : ℝ) {lo hi : ℝ}
    (hlo : Real.exp 1 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi - lo ≤ lo) :
    ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * twistWeight t n -
        (if χ = 1 then ∫ u in lo..hi, twistWeight t u else 0)‖ ≤
      2 * C * (k : ℝ) ^ C * hi ^ (1 - c) * (|t| + 2) := by
  have hlo2 : 2 ≤ lo := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  set ρ : ℂ := if χ = 1 then 1 else 0 with hρ
  have h := norm_sum_twistWeight_scaled_sub_le
    (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) t ρ (d := 1)
    (B := 2 * C * (k : ℝ) ^ C * hi ^ (1 - c)) le_rfl hlo hlohi hhi fun y hy ↦ ?_
  · simp only [Nat.cast_one, div_one, one_mul, inv_one] at h
    convert h using 3
    rw [hρ]
    split_ifs <;> simp
  · simp only [Nat.cast_one, div_one] at hy ⊢
    have hy2 : 2 ≤ y := hlo2.trans hy.1
    have hsplit := sum_Ioc_consecutive (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ) * χ n)
      (Nat.zero_le ⌊lo⌋₊) (Nat.floor_le_floor hy.1)
    have e : ∀ n : ℕ, Ioc 0 n = Icc 1 n := fun n ↦ by
      ext m
      simp only [mem_Ioc, mem_Icc]
      omega
    rw [e, e] at hsplit
    have h1 := hPNT k χ y hy2
    have h2 := hPNT k χ lo hlo2
    have hrp : ∀ z ∈ Set.Icc lo hi, z ^ (1 - c) ≤ hi ^ (1 - c) := fun z hz ↦
      Real.rpow_le_rpow (by linarith [hz.1]) hz.2 (by linarith)
    have hCk : 0 ≤ C * (k : ℝ) ^ C :=
      (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (by linarith) _)).mp
        ((norm_nonneg _).trans h1)
    have hC1 : C * (k : ℝ) ^ C * y ^ (1 - c) ≤ C * (k : ℝ) ^ C * hi ^ (1 - c) :=
      mul_le_mul_of_nonneg_left (hrp y hy) hCk
    have hC2 : C * (k : ℝ) ^ C * lo ^ (1 - c) ≤ C * (k : ℝ) ^ C * hi ^ (1 - c) :=
      mul_le_mul_of_nonneg_left (hrp lo ⟨le_rfl, hlohi⟩) hCk
    have heq : ∑ m ∈ Ioc ⌊lo⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt m : ℂ) * χ m -
        ρ * ((y : ℂ) - (lo : ℂ)) =
        (∑ n ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          (if χ = 1 then (y : ℂ) else 0)) -
        (∑ n ∈ Icc 1 ⌊lo⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          (if χ = 1 then (lo : ℂ) else 0)) := by
      rw [← hsplit, hρ]
      split_ifs <;> ring
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    linarith

/-- High frequencies: partial summation of bounds for `∑ χ(p) p^{-1+it}`. -/
private theorem norm_sum_prime_le_of_twist {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ)
    {lo hi B : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (hB : ∀ y ∈ Set.Icc lo hi, ‖∑ p ∈ (Ioc ⌊lo⌋₊ ⌊y⌋₊).filter Nat.Prime,
      χ p * (p : ℂ) ^ ((-1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B) :
    ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊,
        ((if n.Prime then 1 else 0 : ℝ) : ℂ) * (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I))‖ ≤
      B * (2 * hi - lo) := by
  classical
  set c : ℕ → ℂ := fun n ↦ if n.Prime then χ n * (n : ℂ) ^ ((-1 : ℂ) + (t : ℂ) * Complex.I)
    else 0 with hc
  have h := norm_sum_mul_sub_integral_le c (f := fun y : ℝ ↦ (y : ℂ)) (f' := fun _ ↦ 1)
    (M := 1) (B := B) 0 hlo hlohi (fun y _ ↦ (hasDerivAt_id y).ofReal_comp) continuousOn_const
    (fun _ _ ↦ by simp) fun y hy ↦ by
      simpa [hc, sum_filter] using hB y hy
  have hhi : 0 ≤ hi := hlo.trans hlohi
  rw [zero_mul, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hhi] at h
  refine le_of_eq_of_le ?_ (h.trans_eq (by ring))
  congr 1
  refine sum_congr rfl fun n hn ↦ ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (mem_Ioc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  simp only [hc]
  split_ifs
  · rw [Complex.cpow_add _ _ hn0, Complex.cpow_neg_one]
    field_simp
    push_cast
    ring
  · simp

/-! ### The parameters at scale `x` -/

/-- `T = log log x → ∞`. -/
private theorem tendsto_logLog : Tendsto logLog atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

/-- Exponentials beat polynomials: `C T^n ≤ exp(a T)` for large `T`. -/
private theorem eventually_mul_pow_le_exp {a : ℝ} (ha : 0 < a) (n : ℕ) (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, C * T ^ n ≤ Real.exp (a * T) := by
  have h := (tendsto_exp_div_pow_atTop n).comp (tendsto_id.const_mul_atTop ha)
  filter_upwards [h.eventually_ge_atTop ((|C| + 1) / a ^ n), eventually_ge_atTop 1]
    with T hT hT1
  simp only [Function.comp_apply, id] at hT
  have hpos : 0 < (a * T) ^ n := by positivity
  have h1 := (le_div_iff₀ hpos).mp hT
  have h2 : (|C| + 1) / a ^ n * (a * T) ^ n = (|C| + 1) * T ^ n := by
    rw [mul_pow]
    field_simp
  have h3 : C * T ^ n ≤ (|C| + 1) * T ^ n :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
  linarith

/-- The presieve exponent is at least `c₂ / T²¹`. -/
private theorem presieveExponent_ge {c Ch x : ℝ} (hc : 0 < c) (hT : 1 ≤ logLog x) :
    c / (4 * (8 * |Ch| + 11)) / logLog x ^ 21 ≤ presieveExponent c Ch x := by
  set T := logLog x
  have hs0 : 0 ≤ logLogLog x := Real.log_nonneg hT
  have hsT : logLogLog x ≤ T := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hceil : (⌈Ch * logLogLog x⌉₊ : ℝ) ≤ |Ch| * T + 1 := by
    rcases le_or_gt (Ch * logLogLog x) 0 with h | h
    · rw [Nat.ceil_eq_zero.mpr h, Nat.cast_zero]
      have := abs_nonneg Ch
      nlinarith
    · have := Nat.ceil_lt_add_one h.le
      have : Ch * logLogLog x ≤ |Ch| * T :=
        (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg hs0]; gcongr)
      linarith
  have hdepth : 4 * (sieveDepth Ch x : ℝ) + 3 ≤ (8 * |Ch| + 11) * T := by
    rw [sieveDepth]
    push_cast
    nlinarith [abs_nonneg Ch]
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < 4 * (sieveDepth Ch x : ℝ) + 3 := by positivity
  rw [presieveExponent]
  calc c / (4 * (8 * |Ch| + 11)) / T ^ 21 = c / T ^ 20 / 4 / ((8 * |Ch| + 11) * T) := by
        field_simp
    _ ≤ c / T ^ 20 / 4 / (4 * (sieveDepth Ch x : ℝ) + 3) := by
        gcongr

/-- The inequalities between the parameters that hold for large `x`. -/
private theorem eventually_params (c Ch : ℝ) (hc : 0 < c) (M Cm K : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 < Real.log x ∧ 1 ≤ logLog x ∧
      M * logLog x ≤ presieveExponent c Ch x * Real.log x - Real.log 2 ∧
      M * logLog x + 1 ≤ presieveExponent c Ch x * logLog x ^ 25 ∧
      2 * K * Real.log x / logLog x ^ 22 ≤
        presieveExponent c Ch x * Real.log x - Real.log 2 ∧
      M * logLog x ≤ Real.log x ^ (95 / 100 : ℝ) ∧
      Cm * logLog x < Real.log x ^ (28 / 100 : ℝ) ∧
      Real.log x ^ (45 / 100 : ℝ) ≤ Real.log x / logLog x ^ 25 ∧
      2 * logLog x ^ 25 ≤ Real.log x := by
  obtain ⟨c₂, hc₂0, hγ⟩ : ∃ c₂ > 0, ∀ x, 1 ≤ logLog x →
      c₂ / logLog x ^ 21 ≤ presieveExponent c Ch x :=
    ⟨_, by positivity, fun x hx ↦ presieveExponent_ge hc hx⟩
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog2' : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- the statements in `T`, with `L = exp T`
  have hQ : ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧
      M * T + Real.log 2 ≤ c₂ * Real.exp T / T ^ 21 ∧
      M * T + 1 ≤ c₂ * T ^ 4 ∧
      2 * K * Real.exp T / T ^ 22 + Real.log 2 ≤ c₂ * Real.exp T / T ^ 21 ∧
      M * T ≤ Real.exp (95 / 100 * T) ∧
      Cm * T < Real.exp (28 / 100 * T) ∧
      Real.exp (45 / 100 * T) ≤ Real.exp T / T ^ 25 ∧
      2 * T ^ 25 ≤ Real.exp T := by
    filter_upwards [eventually_ge_atTop 1,
      eventually_ge_atTop ((|M| + 1) / c₂ + 1), eventually_ge_atTop ((2 * |K| + 1) / c₂),
      eventually_mul_pow_le_exp one_pos 22 ((|M| + 1) / c₂),
      eventually_mul_pow_le_exp one_pos 22 1,
      eventually_mul_pow_le_exp (by norm_num : (0 : ℝ) < 95 / 100) 1 M,
      eventually_mul_pow_le_exp (by norm_num : (0 : ℝ) < 28 / 100) 1 (|Cm| + 1),
      eventually_mul_pow_le_exp (by norm_num : (0 : ℝ) < 55 / 100) 25 1,
      eventually_mul_pow_le_exp one_pos 25 2] with T h1 h2 h3 h4 h5 h6 h7 h8 h9
    have hT0 : 0 < T := by linarith
    have hpow : ∀ n : ℕ, 0 < T ^ n := fun n ↦ pow_pos hT0 n
    simp only [one_mul, pow_one] at h4 h5 h6 h7 h8 h9
    have hMc : |M| + 1 ≤ T * c₂ := (div_le_iff₀ hc₂0).mp (by linarith)
    have hKc : 2 * |K| + 1 ≤ T * c₂ := (div_le_iff₀ hc₂0).mp h3
    have h4' : (|M| + 1) * T ^ 22 ≤ c₂ * Real.exp T := by
      have := mul_le_mul_of_nonneg_left h4 hc₂0.le
      have e : c₂ * ((|M| + 1) / c₂ * T ^ 22) = (|M| + 1) * T ^ 22 := by
        field_simp
      linarith
    refine ⟨h1, ?_, ?_, ?_, h6, ?_, ?_, h9⟩
    · rw [le_div_iff₀ (hpow 21)]
      have hM : M * T + Real.log 2 ≤ (|M| + 1) * T := by
        nlinarith [le_abs_self M]
      calc (M * T + Real.log 2) * T ^ 21 ≤ (|M| + 1) * T * T ^ 21 :=
            mul_le_mul_of_nonneg_right hM (hpow 21).le
        _ = (|M| + 1) * T ^ 22 := by ring
        _ ≤ _ := h4'
    · have hTT : 1 ≤ T * T := by nlinarith
      have h44 : T * T ≤ T ^ 4 := by nlinarith
      have hM : M * T + 1 ≤ (|M| + 1) * T := by nlinarith [le_abs_self M]
      nlinarith
    · -- `c₂ e^T / T^21 - 2K e^T / T^22 = (c₂ T - 2K) e^T / T^22 ≥ e^T / T^22 ≥ 1`
      have hE : 1 ≤ Real.exp T / T ^ 22 := by
        rw [le_div_iff₀ (hpow 22)]
        linarith
      have heq : c₂ * Real.exp T / T ^ 21 - 2 * K * Real.exp T / T ^ 22 =
          (c₂ * T - 2 * K) * (Real.exp T / T ^ 22) := by
        field_simp
      have hK : 1 ≤ c₂ * T - 2 * K := by nlinarith [le_abs_self K]
      have : 1 ≤ (c₂ * T - 2 * K) * (Real.exp T / T ^ 22) := by nlinarith
      linarith
    · have := le_abs_self Cm
      nlinarith
    · rw [le_div_iff₀ (hpow 25)]
      calc Real.exp (45 / 100 * T) * T ^ 25 ≤ Real.exp (45 / 100 * T) * Real.exp (55 / 100 * T) :=
            mul_le_mul_of_nonneg_left h8 (Real.exp_pos _).le
        _ = Real.exp T := by rw [← Real.exp_add]; ring_nf
  -- transfer to `x`
  filter_upwards [tendsto_logLog.eventually hQ, Real.tendsto_log_atTop.eventually_gt_atTop 1]
    with x hx hL
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  have hL0 : 0 < Real.log x := by linarith
  have hLe : Real.exp (logLog x) = Real.log x := Real.exp_log hL0
  have hrpow : ∀ y : ℝ, Real.log x ^ y = Real.exp (y * logLog x) := fun y ↦ by
    rw [Real.rpow_def_of_pos hL0, mul_comm]
    rfl
  rw [hLe] at h2 h4 h7 h8
  have hγx := hγ x h1
  have hT0 : 0 < logLog x := by linarith
  refine ⟨hL, h1, ?_, ?_, ?_, ?_, ?_, ?_, h8⟩
  · have : c₂ * Real.log x / logLog x ^ 21 ≤ presieveExponent c Ch x * Real.log x := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right hγx hL0.le
    linarith
  · have : c₂ * logLog x ^ 4 ≤ presieveExponent c Ch x * logLog x ^ 25 := by
      have := mul_le_mul_of_nonneg_right hγx (pow_pos hT0 25).le
      have e : c₂ / logLog x ^ 21 * logLog x ^ 25 = c₂ * logLog x ^ 4 := by
        field_simp
      linarith
    linarith
  · have : c₂ * Real.log x / logLog x ^ 21 ≤ presieveExponent c Ch x * Real.log x := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right hγx hL0.le
    linarith
  · rw [hrpow]
    exact h5
  · rw [hrpow]
    exact h6
  · rw [hrpow]
    exact h7

/-! ### The centered coefficient -/

/-- Above the cutoff, the centered twisted sum is the prime sum minus `D_j⁻¹` times the damped
sum. -/
private theorem sum_centered_eq (x γ : ℝ) (j : ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k) (t : ℝ)
    {A N : ℕ} (hA : ∀ n ∈ Ioc A N, x ^ γ < n) :
    ∑ n ∈ Ioc A N, χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I) *
        (((if n.Prime ∧ x ^ γ < n then 1 else 0 : ℝ) : ℂ) - (unstrippedProxy x γ j n : ℂ)) =
      ∑ n ∈ Ioc A N, ((if n.Prime then 1 else 0 : ℝ) : ℂ) *
          (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I)) -
        ((dampedDensity x j : ℂ))⁻¹ *
          ∑ n ∈ Ioc A N, (dampedFun x j n : ℂ) * (χ n * twistWeight t n) := by
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  have hxn := hA n hn
  have hn0 : n ≠ 0 := by
    have := (mem_Ioc.mp hn).1
    omega
  rw [unstrippedProxy, ite_eq_left hxn, dampedWeight_eq_dampedFun x j hn0, twistWeight]
  by_cases hp : n.Prime
  · simp only [hp, hxn, and_self, ite_true]
    push_cast
    ring
  · simp only [hp, false_and, ite_false]
    push_cast
    ring

/-- The summands vanish at or below the cutoff `x^γ`, so the interval may start there. -/
private theorem sum_centered_eq_max (x γ : ℝ) (j : ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (t lo hi : ℝ)
    (hγ : 0 ≤ x ^ γ) :
    ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I) *
        (((if n.Prime ∧ x ^ γ < n then 1 else 0 : ℝ) : ℂ) - (unstrippedProxy x γ j n : ℂ)) =
      ∑ n ∈ Ioc ⌊max lo (x ^ γ)⌋₊ ⌊hi⌋₊, χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I) *
        (((if n.Prime ∧ x ^ γ < n then 1 else 0 : ℝ) : ℂ) - (unstrippedProxy x γ j n : ℂ)) := by
  classical
  symm
  refine sum_subset (fun n hn ↦ ?_) fun n hn hn' ↦ ?_
  · simp only [mem_Ioc] at hn ⊢
    refine ⟨lt_of_le_of_lt ?_ hn.1, hn.2⟩
    rcases le_total lo 0 with h | h
    · rw [Nat.floor_eq_zero.mpr (by linarith)]
      exact Nat.zero_le _
    · exact Nat.floor_le_floor (le_max_left _ _)
  · have hle : ¬ x ^ γ < n := by
      intro hlt
      apply hn'
      simp only [mem_Ioc] at hn ⊢
      refine ⟨?_, hn.2⟩
      rw [Nat.floor_lt (le_max_of_le_right hγ)]
      exact max_lt (Nat.floor_lt' (by omega) |>.mp hn.1) hlt
    simp [unstrippedProxy, hle]

/-! ### Numerical bounds -/

/-- `H^{-a} ≤ exp(-a l)` when `log H ≥ l`. -/
private theorem rpow_neg_le_exp {H l a : ℝ} (hH : 0 < H) (hl : l ≤ Real.log H) (ha : 0 ≤ a) :
    H ^ (-a) ≤ Real.exp (-(a * l)) := by
  rw [Real.rpow_def_of_pos hH, Real.exp_le_exp]
  nlinarith

/-- The proper prime powers up to `N ≤ 2H` number at most `14 H^{3/4}`. -/
private theorem sqrt_mul_log_le {N : ℕ} {H : ℝ} (hH : 1 ≤ H) (hN : (N : ℝ) ≤ 2 * H) :
    (Nat.sqrt N : ℝ) * (Nat.log 2 N + 1) ≤ 14 * H ^ (3 / 4 : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp only [Nat.sqrt_zero, Nat.cast_zero, zero_mul]
    positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hlog2 : 2 / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  -- `log₂ N ≤ log N / log 2 ≤ 6 N^{1/4}`
  have hlogN : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    have h := Nat.pow_log_le_self 2 hN0.ne'
    have : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by exact_mod_cast h
    have := Real.log_le_log (by positivity) this
    rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
  have hlogle : Real.log N ≤ (N : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (Nat.cast_nonneg N) (by norm_num)
  have hq : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
  have hlog : (Nat.log 2 N : ℝ) + 1 ≤ 7 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    have : (Nat.log 2 N : ℝ) ≤ 4 * (N : ℝ) ^ (1 / 4 : ℝ) / Real.log 2 := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have : 4 * (N : ℝ) ^ (1 / 4 : ℝ) / Real.log 2 ≤ 6 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hsqrt : (Nat.sqrt N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.nat_sqrt_le_real_sqrt
  have h34 : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) = (N : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have hN34 : (N : ℝ) ^ (3 / 4 : ℝ) ≤ (2 * H) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hN (by norm_num)
  have h2 : (2 * H) ^ (3 / 4 : ℝ) ≤ 2 * H ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
    gcongr
    calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  calc (Nat.sqrt N : ℝ) * (Nat.log 2 N + 1) ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (7 * (N : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul hsqrt hlog (by positivity) (by positivity)
    _ = 7 * (N : ℝ) ^ (3 / 4 : ℝ) := by rw [← h34]; ring
    _ ≤ 7 * (2 * H ^ (3 / 4 : ℝ)) := by gcongr; exact hN34.trans h2
    _ = 14 * H ^ (3 / 4 : ℝ) := by ring

/-- The integer kernel bound (AC3) at scale `H / d` bounds the twisted character sums over
subintervals of `I / d`. -/
private theorem norm_sum_char_cpow_le_of_kernel {x' Cm κ : ℝ} (hIK : IntegerKernelBound x' Cm κ)
    {k : ℕ} (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ Real.log x' ^ Cm) (χ : DirichletCharacter ℂ k)
    {t H lo hi : ℝ} (ht1 : 1 ≤ |t|) (htx : |t| ≤ x' ^ 3) (hH0 : 0 < H)
    (hHx : H ≤ x') (hHlo : H ≤ lo) (hhi : hi ≤ 2 * H) {d : ℕ} (hd : 1 ≤ d)
    (hHd : Real.exp (Real.log x' / Real.log (Real.log x') ^ 22) ≤ H / d) :
    ∀ y ∈ Set.Icc (lo / d) (hi / d),
      ‖∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊y⌋₊, χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        k * |κ| * H * ((1 + |t|)⁻¹ + Real.exp (-Real.log x' ^ (0.95 : ℝ))) / d := by
  intro y hy
  have : NeZero k := ⟨by omega⟩
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hHd0 : 0 < H / d := div_pos hH0 hd0
  rw [sum_char_mul_eq_sum_range]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ r ∈ range k, ‖χ r * ∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊y⌋₊ with m ≡ r [MOD k],
      (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
      |κ| * ((1 + |t|)⁻¹ + Real.exp (-Real.log x' ^ (0.95 : ℝ))) * (H / d) := by
    intro r _
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)).trans ?_
    have h := hIK (H / d) (lo / d) y hHd ((div_le_self hH0.le hd1).trans hHx)
      (div_le_div_of_nonneg_right hHlo hd0.le)
      (hy.2.trans (by rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hhi hd0.le))
      k r hk hkx t ht1 htx
    rw [inv_mul_le_iff₀ hHd0] at h
    refine h.trans ?_
    rw [mul_comm]
    gcongr
    exact le_abs_self κ
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  apply le_of_eq
  field_simp



/-! ### The parameters at a fixed large `x` -/

/-- The candidate primes lie below `Y`, and above any modulus `k ≤ L^{C_m}`. -/
private theorem candidate_facts {x Cm : ℝ} (hL1 : 1 < Real.log x)
    (hF6 : Cm * logLog x < Real.log x ^ (28 / 100 : ℝ))
    (hF7 : Real.log x ^ (45 / 100 : ℝ) ≤ Real.log x / logLog x ^ 25) {k : ℕ}
    (hkexp : (k : ℝ) ≤ Real.exp (Cm * logLog x)) :
    (∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) ∧
      (∀ p ∈ candidatePrimes x, k < p) ∧ (k : ℝ) ≤ proxyCutoff x ∧ 2 ≤ proxyCutoff x := by
  have hY45 : Real.exp (Real.log x ^ (45 / 100 : ℝ)) ≤ proxyCutoff x := Real.exp_le_exp.mpr hF7
  have hk28 : Real.exp (Cm * logLog x) < Real.exp (Real.log x ^ (28 / 100 : ℝ)) :=
    Real.exp_lt_exp.mpr hF6
  have hL2845 : Real.log x ^ (28 / 100 : ℝ) ≤ Real.log x ^ (45 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1.le (by norm_num)
  refine ⟨fun p hp ↦ (mem_candidatePrimes hL1.le hp).2.2.trans hY45, fun p hp ↦ ?_,
    (hkexp.trans hk28.le).trans ((Real.exp_le_exp.mpr hL2845).trans hY45), ?_⟩
  · have := (mem_candidatePrimes hL1.le hp).2.1
    exact_mod_cast (hkexp.trans_lt hk28).trans_le this
  · have h1 : (1 : ℝ) ≤ Real.log x ^ (45 / 100 : ℝ) := Real.one_le_rpow hL1.le (by norm_num)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact h2.trans ((Real.exp_le_exp.mpr h1).trans hY45)

/-- Rankin's exponent `ε = 1 / log Y = T²⁵ / L`, the majorant `Π ≤ exp(12 (T + |C_M|))`, and
`D_j⁻¹ ≤ exp(2 (T + |C_M|))`. -/
private theorem rankin_facts {x CM : ℝ}
    (hCM : ∀ Y : ℝ, 2 ≤ Y → ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ Real.log (Real.log Y) + CM)
    (hL1 : 1 < Real.log x) (hT1 : 1 ≤ logLog x) (hF8 : 2 * logLog x ^ 25 ≤ Real.log x)
    (hY2 : 2 ≤ proxyCutoff x) {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ 1 / Real.log (proxyCutoff x) ∧ 1 / Real.log (proxyCutoff x) ≤ 1 / 2 ∧
      1 / Real.log (proxyCutoff x) = logLog x ^ 25 / Real.log x ∧
      0 ≤ rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)) ∧
      rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)) *
          (dampedDensity x j)⁻¹ ≤ Real.exp (14 * |CM|) * Real.exp (14 * logLog x) ∧
      0 < dampedDensity x j ∧
      (dampedDensity x j)⁻¹ ≤ Real.exp (14 * |CM|) * Real.exp (2 * logLog x) := by
  set L := Real.log x
  set T := logLog x
  set Y := proxyCutoff x with hYdef
  have hL0 : 0 < L := by linarith
  have hT25 : 0 < T ^ 25 := by positivity
  have hlogY : Real.log Y = L / T ^ 25 := Real.log_exp _
  have hε : 1 / Real.log Y = T ^ 25 / L := by
    rw [hlogY]
    field_simp
  have hε0 : 0 ≤ 1 / Real.log Y := by rw [hε]; positivity
  have hε2 : 1 / Real.log Y ≤ 1 / 2 := by
    rw [hε, div_le_iff₀ hL0]
    linarith
  have hYε : Y ^ (1 / Real.log Y) = Real.exp 1 := by
    have hne : L / T ^ 25 ≠ 0 := by positivity
    rw [hlogY, hYdef, proxyCutoff, ← Real.exp_mul, mul_one_div_cancel hne]
  have hloglogY : Real.log (Real.log Y) ≤ T := by
    rw [hlogY]
    exact Real.log_le_log (by positivity) (div_le_self hL0.le (one_le_pow₀ hT1))
  have hsum : ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ T + |CM| := by
    have := hCM Y hY2
    linarith [le_abs_self CM]
  have hsum0 : 0 ≤ ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p := sum_nonneg fun p _ ↦ by positivity
  have hR : rankinProd (primesIcc 2 Y) (1 / Real.log Y) ≤ Real.exp (12 * T + 12 * |CM|) := by
    refine (rankinProd_le hε0 hε2).trans (Real.exp_le_exp.mpr ?_)
    rw [hYε]
    have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
    calc 4 * Real.exp 1 * ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤
          4 * 3 * ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p := by gcongr
      _ ≤ 12 * T + 12 * |CM| := by linarith
  have hR0 : 0 ≤ rankinProd (primesIcc 2 Y) (1 / Real.log Y) :=
    (hasSum_rankin _ (by linarith)).nonneg (rankin_indicator_nonneg _ _)
  have hDlow := exp_le_dampedDensity x hj
  have hD0 : 0 < dampedDensity x j := (Real.exp_pos _).trans_le hDlow
  have hDinv : (dampedDensity x j)⁻¹ ≤ Real.exp (2 * T + 2 * |CM|) := by
    rw [inv_le_comm₀ hD0 (Real.exp_pos _), ← Real.exp_neg]
    refine (Real.exp_le_exp.mpr ?_).trans hDlow
    linarith
  have hCM0 : 0 ≤ |CM| := abs_nonneg CM
  refine ⟨hε0, hε2, hε, hR0, ?_, hD0, ?_⟩
  · calc rankinProd (primesIcc 2 Y) (1 / Real.log Y) * (dampedDensity x j)⁻¹ ≤
          Real.exp (12 * T + 12 * |CM|) * Real.exp (2 * T + 2 * |CM|) :=
          mul_le_mul hR hDinv (inv_nonneg.mpr hD0.le) (Real.exp_pos _).le
      _ = Real.exp (14 * |CM|) * Real.exp (14 * T) := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf
  · refine hDinv.trans ?_
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith


/-! ### The error terms at scale `H` -/

/-- The proper prime powers: `√N (log₂ N + 1) ≤ 14 H exp(-A' T)`. -/
private theorem primePower_term_le {N : ℕ} {H T M A' : ℝ} (hH1 : 1 ≤ H) (hN : (N : ℝ) ≤ 2 * H)
    (hMT : M * T ≤ Real.log H) (hMA : 4 * A' ≤ M) (hT0 : 0 ≤ T) :
    (Nat.sqrt N : ℝ) * (Nat.log 2 N + 1) ≤ H * (14 * Real.exp (-(A' * T))) := by
  have hH0 : 0 < H := by linarith
  refine (sqrt_mul_log_le hH1 hN).trans ?_
  have h1 : H ^ (3 / 4 : ℝ) = H * H ^ (-(1 / 4) : ℝ) := by
    rw [← Real.rpow_one_add' hH0.le (by norm_num)]
    norm_num
  have h2 : H ^ (-(1 / 4) : ℝ) ≤ Real.exp (-(A' * T)) := by
    refine (rpow_neg_le_exp hH0 hMT (by norm_num)).trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  rw [h1]
  nlinarith

/-- The prime number theorem error: `2 C₀ k^{C₀} hi^{1 - c₁} (|t| + 2) ≤ 4 |C₀| (K'^E + 2) H
exp(-A' T)`. -/
private theorem pnt_term_le {k : ℕ} {H hi t T M A' C₀ c₁ Cm' K' E : ℝ} (hk : 1 ≤ k)
    (hkexp : (k : ℝ) ≤ Real.exp (Cm' * T)) (hH1 : 1 ≤ H) (hHhi : H ≤ hi) (hhi : hi ≤ 2 * H)
    (hMT : M * T ≤ Real.log H) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hMc : A' + Cm' * |C₀| + E ≤ c₁ * M) (ht : |t| ≤ K' ^ E * Real.exp (E * T)) (hE0 : 0 ≤ E)
    (hK' : 1 ≤ K') (hT0 : 0 ≤ T) :
    2 * C₀ * (k : ℝ) ^ C₀ * hi ^ (1 - c₁) * (|t| + 2) ≤
      H * (4 * |C₀| * (K' ^ E + 2) * Real.exp (-(A' * T))) := by
  have hH0 : 0 < H := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hhi0 : 0 < hi := by linarith
  have hKE : 1 ≤ K' ^ E := Real.one_le_rpow hK' hE0
  have hET : 1 ≤ Real.exp (E * T) := Real.one_le_exp (by positivity)
  -- `C₀ k^{C₀} ≤ |C₀| exp(|C₀| C_m' T)`
  have hC : C₀ * (k : ℝ) ^ C₀ ≤ |C₀| * Real.exp (|C₀| * Cm' * T) := by
    rcases le_or_gt C₀ 0 with h | h
    · have : C₀ * (k : ℝ) ^ C₀ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h (Real.rpow_nonneg (by linarith) _)
      exact this.trans (by positivity)
    · rw [abs_of_pos h]
      refine mul_le_mul_of_nonneg_left ?_ h.le
      calc (k : ℝ) ^ C₀ ≤ Real.exp (Cm' * T) ^ C₀ :=
            Real.rpow_le_rpow (by linarith) hkexp h.le
        _ = Real.exp (C₀ * Cm' * T) := by rw [← Real.exp_mul]; ring_nf
  -- `hi^{1 - c₁} ≤ 2 H exp(-c₁ M T)`
  have hhic : hi ^ (1 - c₁) ≤ 2 * H * Real.exp (-(c₁ * (M * T))) := by
    have h1 : hi ^ (1 - c₁) ≤ (2 * H) ^ (1 - c₁) :=
      Real.rpow_le_rpow hhi0.le hhi (by linarith)
    have h2 : (2 * H) ^ (1 - c₁) = 2 ^ (1 - c₁) * (H * H ^ (-c₁)) := by
      rw [Real.mul_rpow (by norm_num) hH0.le, sub_eq_add_neg, Real.rpow_add hH0, Real.rpow_one]
    have h3 : (2 : ℝ) ^ (1 - c₁) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - c₁) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 := rpow_neg_le_exp hH0 hMT hc₁0.le
    rw [h2] at h1
    calc hi ^ (1 - c₁) ≤ 2 ^ (1 - c₁) * (H * H ^ (-c₁)) := h1
      _ ≤ 2 * (H * Real.exp (-(c₁ * (M * T)))) := by gcongr
      _ = _ := by ring
  have ht2 : |t| + 2 ≤ (K' ^ E + 2) * Real.exp (E * T) := by nlinarith
  have hexp : Real.exp (|C₀| * Cm' * T) * Real.exp (-(c₁ * (M * T))) * Real.exp (E * T) ≤
      Real.exp (-(A' * T)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have : c₁ * (M * T) = (c₁ * M) * T := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hMc hT0
    nlinarith [abs_nonneg C₀]
  calc 2 * C₀ * (k : ℝ) ^ C₀ * hi ^ (1 - c₁) * (|t| + 2) =
        2 * (C₀ * (k : ℝ) ^ C₀) * hi ^ (1 - c₁) * (|t| + 2) := by ring
    _ ≤ 2 * (|C₀| * Real.exp (|C₀| * Cm' * T)) * (2 * H * Real.exp (-(c₁ * (M * T)))) *
        ((K' ^ E + 2) * Real.exp (E * T)) := by
        have : 0 ≤ hi ^ (1 - c₁) := Real.rpow_nonneg hhi0.le _
        gcongr
    _ = 4 * |C₀| * (K' ^ E + 2) * H * (Real.exp (|C₀| * Cm' * T) *
        Real.exp (-(c₁ * (M * T))) * Real.exp (E * T)) := by ring
    _ ≤ 4 * |C₀| * (K' ^ E + 2) * H * Real.exp (-(A' * T)) := by gcongr
    _ = _ := by ring

/-- The Rankin terms: `D⁻¹ (2 (hi - lo) D₀^{-ε} Π + hi^{1-ε} Π) ≤ 4 W H exp(-A' T)`. -/
private theorem rankin_term_le {H lo hi ε R D T M A' W : ℝ} (hH1 : 1 ≤ H) (hHlo : H ≤ lo)
    (hlohi : lo ≤ hi) (hhi : hi ≤ 2 * H) (hε0 : 0 ≤ ε) (hR0 : 0 ≤ R) (hD0 : 0 < D) (hW : 0 ≤ W)
    (hRD : R * D⁻¹ ≤ W * Real.exp (14 * T)) (hHε : H ^ (-(ε / 2)) ≤ Real.exp (-(M / 2 * T)))
    (hM : 2 * (A' + 14) ≤ M) (hT0 : 0 ≤ T) :
    D⁻¹ * (2 * ((hi - lo) * (((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-ε) * R)) + hi ^ (1 - ε) * R) ≤
      H * (4 * W * Real.exp (-(A' * T))) := by
  have hH0 : 0 < H := by linarith
  have hhi0 : 0 < hi := by linarith
  have hsq : Real.sqrt H ≤ (⌊Real.sqrt H⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hsq0 : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH0
  have h1 : ((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-ε) ≤ H ^ (-(ε / 2)) := by
    calc ((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-ε) ≤ Real.sqrt H ^ (-ε) :=
          Real.rpow_le_rpow_of_nonpos hsq0 hsq (by linarith)
      _ = H ^ (-(ε / 2)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hH0.le]
          ring_nf
  have h2 : hi ^ (1 - ε) ≤ 2 * H * H ^ (-(ε / 2)) := by
    have e : hi ^ (1 - ε) = hi * hi ^ (-ε) := by
      rw [sub_eq_add_neg, Real.rpow_add hhi0, Real.rpow_one]
    have h3 : hi ^ (-ε) ≤ H ^ (-ε) := Real.rpow_le_rpow_of_nonpos hH0 (hHlo.trans hlohi)
      (by linarith)
    have h4 : H ^ (-ε) ≤ H ^ (-(ε / 2)) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    rw [e]
    exact mul_le_mul (by linarith) (h3.trans h4) (Real.rpow_nonneg hhi0.le _) (by linarith)
  have hσ : H ^ (-(ε / 2)) * (W * Real.exp (14 * T)) ≤ W * Real.exp (-(A' * T)) := by
    have hW0 : 0 ≤ W * Real.exp (14 * T) := mul_nonneg hW (Real.exp_pos _).le
    calc H ^ (-(ε / 2)) * (W * Real.exp (14 * T)) ≤
          Real.exp (-(M / 2 * T)) * (W * Real.exp (14 * T)) :=
          mul_le_mul_of_nonneg_right hHε hW0
      _ = W * Real.exp (-(M / 2 * T) + 14 * T) := by rw [Real.exp_add]; ring
      _ ≤ W * Real.exp (-(A' * T)) := by
          gcongr
          nlinarith
  have hsum : 2 * ((hi - lo) * (((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-ε) * R)) + hi ^ (1 - ε) * R ≤
      4 * H * H ^ (-(ε / 2)) * R := by
    have hd : 0 ≤ hi - lo := by linarith
    have hd' : hi - lo ≤ H := by linarith
    have hp : 0 ≤ ((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-ε) := Real.rpow_nonneg (by positivity) _
    have : (hi - lo) * (((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-ε) * R) ≤ H * (H ^ (-(ε / 2)) * R) :=
      mul_le_mul hd' (mul_le_mul_of_nonneg_right h1 hR0) (mul_nonneg hp hR0) hH0.le
    nlinarith [mul_le_mul_of_nonneg_right h2 hR0]
  calc D⁻¹ * (2 * ((hi - lo) * (((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-ε) * R)) + hi ^ (1 - ε) * R) ≤
        D⁻¹ * (4 * H * H ^ (-(ε / 2)) * R) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hD0.le)
    _ = 4 * H * (H ^ (-(ε / 2)) * (R * D⁻¹)) := by ring
    _ ≤ 4 * H * (H ^ (-(ε / 2)) * (W * Real.exp (14 * T))) := by gcongr
    _ ≤ 4 * H * (W * Real.exp (-(A' * T))) := by gcongr
    _ = H * (4 * W * Real.exp (-(A' * T))) := by ring

/-- The small divisors at low frequency:
`D⁻¹ D₀ (2k + 1)(|t| + 2) ≤ 3 (K'^E + 2) W H exp(-A' T)`. -/
private theorem smallDivisor_term_le {k : ℕ} {H t D T M A' Cm' K' E W : ℝ} (hH1 : 1 ≤ H)
    (hD0 : 0 < D) (hDinv : D⁻¹ ≤ W * Real.exp (2 * T)) (hkexp : (k : ℝ) ≤ Real.exp (Cm' * T))
    (ht : |t| ≤ K' ^ E * Real.exp (E * T)) (hMT : M * T ≤ Real.log H)
    (hM : 2 * (A' + Cm' + E + 2) ≤ M) (hE0 : 0 ≤ E) (hK' : 1 ≤ K') (hCm' : 0 ≤ Cm')
    (hT0 : 0 ≤ T) :
    D⁻¹ * (⌊Real.sqrt H⌋₊ * ((2 * k + 1) * (|t| + 2))) ≤
      H * (3 * (K' ^ E + 2) * W * Real.exp (-(A' * T))) := by
  have hH0 : 0 < H := by linarith
  have hKE : 1 ≤ K' ^ E := Real.one_le_rpow hK' hE0
  have hET : 1 ≤ Real.exp (E * T) := Real.one_le_exp (by positivity)
  have hCT : 1 ≤ Real.exp (Cm' * T) := Real.one_le_exp (by positivity)
  have hW : 0 ≤ W := by
    have := (inv_pos.mpr hD0).le.trans hDinv
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp this
  have hsqrt : (⌊Real.sqrt H⌋₊ : ℝ) ≤ H * Real.exp (-(M / 2 * T)) := by
    refine (Nat.floor_le (Real.sqrt_nonneg H)).trans ?_
    have e : Real.sqrt H = H * H ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hH0.le (by norm_num)]
      norm_num
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hH0.le
    refine (rpow_neg_le_exp hH0 hMT (by norm_num)).trans (Real.exp_le_exp.mpr ?_)
    linarith
  have hk3 : 2 * (k : ℝ) + 1 ≤ 3 * Real.exp (Cm' * T) := by linarith
  have ht2 : |t| + 2 ≤ (K' ^ E + 2) * Real.exp (E * T) := by nlinarith
  have hexp : Real.exp (2 * T) * Real.exp (-(M / 2 * T)) * Real.exp (Cm' * T) *
      Real.exp (E * T) ≤ Real.exp (-(A' * T)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    nlinarith
  calc D⁻¹ * (⌊Real.sqrt H⌋₊ * ((2 * k + 1) * (|t| + 2))) ≤
        (W * Real.exp (2 * T)) * ((H * Real.exp (-(M / 2 * T))) *
          ((3 * Real.exp (Cm' * T)) * ((K' ^ E + 2) * Real.exp (E * T)))) := by
        gcongr
    _ = 3 * (K' ^ E + 2) * W * H * (Real.exp (2 * T) * Real.exp (-(M / 2 * T)) *
        Real.exp (Cm' * T) * Real.exp (E * T)) := by ring
    _ ≤ 3 * (K' ^ E + 2) * W * H * Real.exp (-(A' * T)) := by gcongr
    _ = _ := by ring

/-- The kernel terms at high frequency:
`D⁻¹ 2 K_I Π ≤ 4 |κ₃| W H exp(-A' T)`, with `K_I = k |κ₃| H ((1 + |t|)⁻¹ + exp(-L'^{0.95}))`. -/
private theorem kernel_term_le {k : ℕ} {H t R D T M A' Cm' E W κ₃ L' : ℝ} (hH0 : 0 < H)
    (hR0 : 0 ≤ R) (hD0 : 0 < D) (hRD : R * D⁻¹ ≤ W * Real.exp (14 * T))
    (hkexp : (k : ℝ) ≤ Real.exp (Cm' * T)) (ht : (1 + |t|)⁻¹ ≤ Real.exp (-(E * T)))
    (hL' : Real.exp (-L' ^ (0.95 : ℝ)) ≤ Real.exp (-(M * T)))
    (hE : A' + Cm' + 14 ≤ E) (hM : A' + Cm' + 14 ≤ M) (hT0 : 0 ≤ T) :
    D⁻¹ * (2 * (k * |κ₃| * H * ((1 + |t|)⁻¹ + Real.exp (-L' ^ (0.95 : ℝ)))) * R) ≤
      H * (4 * |κ₃| * W * Real.exp (-(A' * T))) := by
  have hW : 0 ≤ W := by
    have := (mul_nonneg hR0 (inv_nonneg.mpr hD0.le)).trans hRD
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp this
  have h1 : Real.exp (Cm' * T) * (Real.exp (-(E * T)) + Real.exp (-(M * T))) *
      Real.exp (14 * T) ≤ 2 * Real.exp (-(A' * T)) := by
    have e1 : Real.exp (Cm' * T) * Real.exp (-(E * T)) * Real.exp (14 * T) ≤
        Real.exp (-(A' * T)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith
    have e2 : Real.exp (Cm' * T) * Real.exp (-(M * T)) * Real.exp (14 * T) ≤
        Real.exp (-(A' * T)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith
    nlinarith
  calc D⁻¹ * (2 * (k * |κ₃| * H * ((1 + |t|)⁻¹ + Real.exp (-L' ^ (0.95 : ℝ)))) * R) =
        2 * k * |κ₃| * H * ((1 + |t|)⁻¹ + Real.exp (-L' ^ (0.95 : ℝ))) * (R * D⁻¹) := by ring
    _ ≤ 2 * Real.exp (Cm' * T) * |κ₃| * H * (Real.exp (-(E * T)) + Real.exp (-(M * T))) *
        (W * Real.exp (14 * T)) := by
        gcongr
    _ = 2 * |κ₃| * W * H * (Real.exp (Cm' * T) * (Real.exp (-(E * T)) + Real.exp (-(M * T))) *
        Real.exp (14 * T)) := by ring
    _ ≤ 2 * |κ₃| * W * H * (2 * Real.exp (-(A' * T))) := by gcongr
    _ = _ := by ring


/-! ### The two frequency ranges -/

open scoped Classical in
/-- Low frequencies: the prime and proxy main terms cancel, up to `O(H exp(-A' T))`. -/
private theorem low_frequency_bound {x : ℝ} {j : ℕ} (hj : 1 ≤ j) {k : ℕ} [NeZero k]
    (χ : DirichletCharacter ℂ k) (t : ℝ) {H lo hi c₁ C₀ T M A' Cm' K' E W : ℝ}
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) (hkY : (k : ℝ) ≤ proxyCutoff x)
    (hkP : ∀ p ∈ candidatePrimes x, k < p) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hPNT : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
      ‖∑ n ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          (if χ = 1 then (y : ℂ) else 0)‖ ≤ C₀ * (k : ℝ) ^ C₀ * y ^ (1 - c₁))
    (hlo : Real.exp 1 ≤ lo) (hH1 : 1 ≤ H) (hHlo : H ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 2 * H)
    (hε0 : 0 ≤ 1 / Real.log (proxyCutoff x)) (hε2 : 1 / Real.log (proxyCutoff x) ≤ 1 / 2)
    (hR0 : 0 ≤ rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)))
    (hRD : rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)) *
      (dampedDensity x j)⁻¹ ≤ W * Real.exp (14 * T))
    (hD0 : 0 < dampedDensity x j) (hDinv : (dampedDensity x j)⁻¹ ≤ W * Real.exp (2 * T))
    (hHε : H ^ (-(1 / Real.log (proxyCutoff x) / 2)) ≤ Real.exp (-(M / 2 * T)))
    (hMT : M * T ≤ Real.log H) (hkexp : (k : ℝ) ≤ Real.exp (Cm' * T))
    (ht : |t| ≤ K' ^ E * Real.exp (E * T)) (hMA : 4 * A' ≤ M)
    (hMc : A' + Cm' * |C₀| + E ≤ c₁ * M) (hM : 2 * (A' + Cm' + E + 2) ≤ M)
    (hE : A' + 14 ≤ E) (hK' : 1 ≤ K') (hA'0 : 0 ≤ A') (hCm' : 0 ≤ Cm') (hT0 : 0 ≤ T) :
    ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, ((if n.Prime then 1 else 0 : ℝ) : ℂ) *
          (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I)) -
        ((dampedDensity x j : ℂ))⁻¹ *
          ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (dampedFun x j n : ℂ) * (χ n * twistWeight t n)‖ ≤
      H * ((14 + 4 * |C₀| * (K' ^ E + 2) + 4 * W + 3 * (K' ^ E + 2) * W) *
        Real.exp (-(A' * T))) := by
  have hhi' : hi - lo ≤ lo := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hW : 0 ≤ W := by
    have := (inv_pos.mpr hD0).le.trans hDinv
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp this
  have h1 := norm_sum_vonMangoldt_sub_le hc₁1 hPNT χ t hlo hlohi hhi'
  have h2 := norm_sum_vonMangoldt_sub_sum_prime_le χ t ⌊lo⌋₊ ⌊hi⌋₊
  have h3 := norm_sum_dampedFun_sub_le hj hP hkY hkP χ t hlo hlohi hhi' hε0 (by linarith)
    ⌊Real.sqrt H⌋₊
  set J := ∫ u in lo..hi, twistWeight t u
  set SΛ := ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n * twistWeight t n
  set SP := ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, ((if n.Prime then 1 else 0 : ℝ) : ℂ) *
    (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I))
  set SG := ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (dampedFun x j n : ℂ) * (χ n * twistWeight t n)
  set D := dampedDensity x j
  have hid : SP - (D : ℂ)⁻¹ * SG = (SΛ - (if χ = 1 then J else 0)) - (SΛ - SP) -
      (D : ℂ)⁻¹ * (SG - (if χ = 1 then (D : ℂ) * J else 0)) := by
    have hD : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD0.ne'
    split_ifs
    · field_simp
      ring
    · ring
  have hnorm : ‖SP - (D : ℂ)⁻¹ * SG‖ ≤
      2 * C₀ * (k : ℝ) ^ C₀ * hi ^ (1 - c₁) * (|t| + 2) +
        (Nat.sqrt ⌊hi⌋₊ : ℝ) * (Nat.log 2 ⌊hi⌋₊ + 1) +
        D⁻¹ * (2 * ((hi - lo) * (((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-(1 / Real.log (proxyCutoff x))) *
            rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)))) +
          hi ^ (1 - 1 / Real.log (proxyCutoff x)) *
            rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)) +
          ⌊Real.sqrt H⌋₊ * ((2 * k + 1) * (|t| + 2))) := by
    rw [hid]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2)) ?_)
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]
    exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hD0.le)
  refine hnorm.trans ?_
  have hN : ((⌊hi⌋₊ : ℕ) : ℝ) ≤ 2 * H := (Nat.floor_le (by linarith)).trans hhi
  have t1 := pnt_term_le (k := k) (t := t) (C₀ := C₀) (by have := NeZero.pos k; omega) hkexp
    hH1 (hHlo.trans hlohi) hhi hMT hc₁0 hc₁1 hMc ht hE0 hK' hT0
  have t2 := primePower_term_le (A' := A') hH1 hN hMT hMA hT0
  have t3 := rankin_term_le (A' := A') hH1 hHlo hlohi hhi hε0 hR0 hD0 hW hRD hHε (by linarith) hT0
  have t4 := smallDivisor_term_le (k := k) (t := t) hH1 hD0 hDinv hkexp ht hMT hM hE0 hK' hCm'
    hT0
  rw [mul_add D⁻¹]
  nlinarith

/-- High frequencies: the prime and proxy sums are each `O(H exp(-A' T))`. -/
private theorem high_frequency_bound {x : ℝ} {j : ℕ} (hj : 1 ≤ j) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (t : ℝ) {H lo hi T M A' Cm' E W κ₂ κ₃ L' B : ℝ}
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x)
    (hlo : Real.exp 1 ≤ lo) (hH1 : 1 ≤ H) (hHlo : H ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 2 * H)
    (hε0 : 0 ≤ 1 / Real.log (proxyCutoff x)) (hε2 : 1 / Real.log (proxyCutoff x) ≤ 1 / 2)
    (hR0 : 0 ≤ rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)))
    (hRD : rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)) *
      (dampedDensity x j)⁻¹ ≤ W * Real.exp (14 * T))
    (hD0 : 0 < dampedDensity x j)
    (hHε : H ^ (-(1 / Real.log (proxyCutoff x) / 2)) ≤ Real.exp (-(M / 2 * T)))
    (hkexp : (k : ℝ) ≤ Real.exp (Cm' * T))
    (ht : (1 + |t|)⁻¹ ≤ Real.exp (-(E * T)))
    (hL' : Real.exp (-L' ^ (0.95 : ℝ)) ≤ Real.exp (-(M * T)))
    (hB : ∀ y ∈ Set.Icc lo hi, ‖∑ p ∈ (Ioc ⌊lo⌋₊ ⌊y⌋₊).filter Nat.Prime,
      χ p * (p : ℂ) ^ ((-1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B)
    (hBκ : B ≤ |κ₂| * Real.exp (-(A' * T)))
    (hK : ∀ d : ℕ, 1 ≤ d → d ≤ ⌊Real.sqrt H⌋₊ → ∀ y ∈ Set.Icc (lo / d) (hi / d),
      ‖∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊y⌋₊, χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        k * |κ₃| * H * ((1 + |t|)⁻¹ + Real.exp (-L' ^ (0.95 : ℝ))) / d)
    (hM : 2 * (A' + Cm' + E + 2) ≤ M) (hE : A' + Cm' + 14 ≤ E) (hA'0 : 0 ≤ A')
    (hCm' : 0 ≤ Cm') (hT0 : 0 ≤ T) :
    ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, ((if n.Prime then 1 else 0 : ℝ) : ℂ) *
          (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I)) -
        ((dampedDensity x j : ℂ))⁻¹ *
          ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (dampedFun x j n : ℂ) * (χ n * twistWeight t n)‖ ≤
      H * ((3 * |κ₂| + 4 * |κ₃| * W + 4 * W) * Real.exp (-(A' * T))) := by
  have hH0 : 0 < H := by linarith
  have hhi' : hi - lo ≤ lo := by linarith
  have hlo0 : 0 ≤ lo := by linarith
  have hW : 0 ≤ W := by
    have := (mul_nonneg hR0 (inv_nonneg.mpr hD0.le)).trans hRD
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp this
  have hKI0 : 0 ≤ k * |κ₃| * H * ((1 + |t|)⁻¹ + Real.exp (-L' ^ (0.95 : ℝ))) :=
    mul_nonneg (by positivity) (add_nonneg (inv_nonneg.mpr (by positivity)) (Real.exp_pos _).le)
  have h1 := norm_sum_prime_le_of_twist χ t hlo0 hlohi hB
  have h2 := norm_sum_dampedFun_le_of_kernel hj hP χ t hlo hlohi hhi' hε0 (by linarith)
    ⌊Real.sqrt H⌋₊ hKI0 fun d hd hdD y hy ↦ (hK d hd hdD y hy).trans_eq (by ring)
  have t5 := kernel_term_le (k := k) (t := t) (κ₃ := κ₃) (A' := A') hH0 hR0 hD0 hRD hkexp ht hL' hE
    (by linarith) hT0
  have t3 := rankin_term_le (A' := A') hH1 hHlo hlohi hhi hε0 hR0 hD0 hW hRD hHε (by linarith) hT0
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB lo ⟨le_rfl, hlohi⟩)
  have hP1 : B * (2 * hi - lo) ≤ H * (3 * |κ₂| * Real.exp (-(A' * T))) := by
    have : 2 * hi - lo ≤ 3 * H := by linarith
    nlinarith [abs_nonneg κ₂, Real.exp_pos (-(A' * T))]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD0]
  have hX : 0 ≤ (hi - lo) * ((((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^ (-(1 / Real.log (proxyCutoff x)))) *
      rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x))) :=
    mul_nonneg (by linarith) (mul_nonneg (Real.rpow_nonneg (by positivity) _) hR0)
  have h2' : (dampedDensity x j)⁻¹ * ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊,
      (dampedFun x j n : ℂ) * (χ n * twistWeight t n)‖ ≤
      (dampedDensity x j)⁻¹ * (2 * (k * |κ₃| * H * ((1 + |t|)⁻¹ + Real.exp (-L' ^ (0.95 : ℝ)))) *
        rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x))) +
      (dampedDensity x j)⁻¹ * (2 * ((hi - lo) * ((((⌊Real.sqrt H⌋₊ : ℝ) + 1) ^
        (-(1 / Real.log (proxyCutoff x)))) *
          rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)))) +
        hi ^ (1 - 1 / Real.log (proxyCutoff x)) *
          rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x))) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (inv_nonneg.mpr hD0.le)
  have e : H * ((3 * |κ₂| + 4 * |κ₃| * W + 4 * W) * Real.exp (-(A' * T))) =
      H * (3 * |κ₂| * Real.exp (-(A' * T))) + H * (4 * |κ₃| * W * Real.exp (-(A' * T))) +
        H * (4 * W * Real.exp (-(A' * T))) := by ring
  linarith


/-! ### Assembly -/

/-- The scale `H ≥ x^γ / 2` satisfies `log H ≥ γ L - log 2 ≥ M T`, and Rankin's saving
`H^{-ε/2} ≤ exp(-(M/2) T)` holds. -/
private theorem scale_facts {x γ H M ε : ℝ} (hx : 0 < x) (hL1 : 1 < Real.log x)
    (hT1 : 1 ≤ logLog x) (hM1 : 1 ≤ M) (hF2 : M * logLog x ≤ γ * Real.log x - Real.log 2)
    (hF1 : M * logLog x + 1 ≤ γ * logLog x ^ 25) (hε : ε = logLog x ^ 25 / Real.log x)
    (hε2 : ε ≤ 1 / 2) (hH : x ^ γ / 2 ≤ H) :
    0 < H ∧ Real.exp 1 ≤ H ∧ γ * Real.log x - Real.log 2 ≤ Real.log H ∧
      M * logLog x ≤ Real.log H ∧ H ^ (-(ε / 2)) ≤ Real.exp (-(M / 2 * logLog x)) := by
  have hL0 : 0 < Real.log x := by linarith
  have hxγ : x ^ γ = Real.exp (γ * Real.log x) := by rw [Real.rpow_def_of_pos hx, mul_comm]
  have hH0 : 0 < H := lt_of_lt_of_le (by rw [hxγ]; positivity) hH
  have hlogH : γ * Real.log x - Real.log 2 ≤ Real.log H := by
    have h1 : Real.log (x ^ γ / 2) ≤ Real.log H :=
      Real.log_le_log (by rw [hxγ]; positivity) hH
    rwa [Real.log_div (by rw [hxγ]; positivity) two_ne_zero, hxγ, Real.log_exp] at h1
  have hMT : M * logLog x ≤ Real.log H := hF2.trans hlogH
  refine ⟨hH0, ?_, hlogH, hMT, ?_⟩
  · rw [← Real.exp_log hH0]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · have hε0 : 0 ≤ ε := by rw [hε]; positivity
    refine (rpow_neg_le_exp hH0 hlogH (by positivity)).trans (Real.exp_le_exp.mpr ?_)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hlog20 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have e : ε * (γ * Real.log x - Real.log 2) = γ * logLog x ^ 25 - ε * Real.log 2 := by
      rw [hε]
      field_simp
    have : ε * Real.log 2 ≤ 1 := by nlinarith
    nlinarith

/-- At `x' = x^{K'}`: `log x' = K' L ≥ L`, `log log x' ≥ T`, and the scale threshold
`exp(log x' / (log log x')²²)` of the contracts is at most `exp(K' L / T²²)`. -/
private theorem xprime_facts {x K' : ℝ} (hx : 0 < x) (hK' : 1 ≤ K') (hL1 : 1 < Real.log x)
    (hT1 : 1 ≤ logLog x) :
    Real.log (x ^ K') = K' * Real.log x ∧ Real.log x ≤ Real.log (x ^ K') ∧
      Real.exp (Real.log (x ^ K') / Real.log (Real.log (x ^ K')) ^ 22) ≤
        Real.exp (K' * Real.log x / logLog x ^ 22) := by
  have hL0 : 0 < Real.log x := by linarith
  have hlog : Real.log (x ^ K') = K' * Real.log x := Real.log_rpow hx K'
  have hLL : Real.log x ≤ Real.log (x ^ K') := by
    rw [hlog]
    exact le_mul_of_one_le_left hL0.le hK'
  refine ⟨hlog, hLL, Real.exp_le_exp.mpr ?_⟩
  have hTT : logLog x ≤ Real.log (Real.log (x ^ K')) := Real.log_le_log hL0 hLL
  rw [hlog]
  rw [hlog] at hTT
  have hT0 : 0 < logLog x := by linarith
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hT0.le hTT 22)

open scoped Classical in
/-- The bound above the cutoff, in both frequency ranges. -/
private theorem proxyTwist_reduced {x c₁ C₀ E₂ κ₂ κ₃ A' Cm' K' E M W : ℝ} {j k : ℕ} [NeZero k]
    (χ : DirichletCharacter ℂ k) (t : ℝ) {H lo hi : ℝ} (hj : 1 ≤ j)
    (hP : ∀ p ∈ candidatePrimes x, (p : ℝ) ≤ proxyCutoff x) (hkY : (k : ℝ) ≤ proxyCutoff x)
    (hkP : ∀ p ∈ candidatePrimes x, k < p) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hPNT : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
      ‖∑ n ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          (if χ = 1 then (y : ℂ) else 0)‖ ≤ C₀ * (k : ℝ) ^ C₀ * y ^ (1 - c₁))
    (hPTx : PrimeTwistBound (x ^ K') A' E₂ Cm' κ₂) (hIKx : IntegerKernelBound (x ^ K') Cm' κ₃)
    (hx : 0 < x) (hL1 : 1 < Real.log x) (hT1 : 1 ≤ logLog x)
    (hF5 : M * logLog x ≤ Real.log x ^ (95 / 100 : ℝ))
    (hlo : Real.exp 1 ≤ lo) (hH1 : 1 ≤ H) (hHlo : H ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 2 * H)
    (hHx : H ≤ x ^ K') (htx : |t| ≤ (x ^ K') ^ 3)
    (hscale : Real.exp (K' * Real.log x / logLog x ^ 22) ≤ Real.sqrt H)
    (hk : 1 ≤ k) (hkx : (k : ℝ) ≤ Real.log (x ^ K') ^ Cm')
    (hkexp : (k : ℝ) ≤ Real.exp (Cm' * logLog x))
    (hε0 : 0 ≤ 1 / Real.log (proxyCutoff x)) (hε2 : 1 / Real.log (proxyCutoff x) ≤ 1 / 2)
    (hR0 : 0 ≤ rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)))
    (hRD : rankinProd (primesIcc 2 (proxyCutoff x)) (1 / Real.log (proxyCutoff x)) *
      (dampedDensity x j)⁻¹ ≤ W * Real.exp (14 * logLog x))
    (hD0 : 0 < dampedDensity x j)
    (hDinv : (dampedDensity x j)⁻¹ ≤ W * Real.exp (2 * logLog x))
    (hHε : H ^ (-(1 / Real.log (proxyCutoff x) / 2)) ≤ Real.exp (-(M / 2 * logLog x)))
    (hMT : M * logLog x ≤ Real.log H) (hK'1 : 1 ≤ K') (hE2 : E₂ ≤ E) (hE : A' + Cm' + 14 ≤ E)
    (hMA : 4 * A' ≤ M) (hMc : A' + Cm' * |C₀| + E ≤ c₁ * M) (hM : 2 * (A' + Cm' + E + 2) ≤ M)
    (hA'0 : 0 ≤ A') (hCm'0 : 0 ≤ Cm') :
    ‖∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, ((if n.Prime then 1 else 0 : ℝ) : ℂ) *
          (χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I)) -
        ((dampedDensity x j : ℂ))⁻¹ *
          ∑ n ∈ Ioc ⌊lo⌋₊ ⌊hi⌋₊, (dampedFun x j n : ℂ) * (χ n * twistWeight t n)‖ ≤
      H * ((14 + 4 * |C₀| * (K' ^ E + 2) + 3 * (K' ^ E + 2) * W + 8 * W + 3 * |κ₂| +
        4 * |κ₃| * W) * Real.exp (-(A' * logLog x))) := by
  set T := logLog x with hT
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hW : 0 ≤ W := by
    have := (inv_pos.mpr hD0).le.trans hDinv
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp this
  obtain ⟨hlogx', hLL', hthr⟩ := xprime_facts hx hK'1 hL1 hT1
  have hrpowL : ∀ y : ℝ, L ^ y = Real.exp (y * T) := fun y ↦ by
    rw [Real.rpow_def_of_pos hL0, mul_comm]
    rfl
  have hKE : 1 ≤ K' ^ E := Real.one_le_rpow hK'1 hE0
  have hthrE : Real.log (x ^ K') ^ E = K' ^ E * Real.exp (E * T) := by
    rw [hlogx', Real.mul_rpow (by linarith) hL0.le, hrpowL]
  have hW0 : 0 ≤ Real.exp (-(A' * T)) := (Real.exp_pos _).le
  rcases le_or_gt |t| (Real.log (x ^ K') ^ E) with htU | htU
  · -- low frequencies
    rw [hthrE] at htU
    have h := low_frequency_bound hj χ t hP hkY hkP hc₁0 hc₁1 hPNT hlo hH1 hHlo hlohi hhi hε0 hε2
      hR0 hRD hD0 hDinv hHε hMT hkexp htU hMA hMc hM (by linarith) hK'1 hA'0 hCm'0 hT0
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hW0) (by linarith))
    have : 0 ≤ 4 * W + 3 * |κ₂| + 4 * |κ₃| * W := by positivity
    linarith
  · -- high frequencies
    have hH0 : 0 < H := by linarith
    have hET1 : 1 ≤ Real.exp (E * T) := Real.one_le_exp (by positivity)
    have hU1 : 1 ≤ Real.log (x ^ K') ^ E := by
      rw [hthrE]
      exact one_le_mul_of_one_le_of_one_le hKE hET1
    have ht1 : 1 ≤ |t| := hU1.trans htU.le
    have hsqrtH : Real.sqrt H ≤ H := by
      refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
      rw [sq]
      exact le_mul_of_one_le_left (by linarith) hH1
    have hscale' : Real.exp (Real.log (x ^ K') / Real.log (Real.log (x ^ K')) ^ 22) ≤
        Real.sqrt H := hthr.trans hscale
    have hlogx'1 : 1 ≤ Real.log (x ^ K') := by linarith
    -- the prime twist bound
    have hE₂ : Real.log (x ^ K') ^ E₂ ≤ |t| :=
      (Real.rpow_le_rpow_of_exponent_le hlogx'1 hE2).trans htU.le
    have hB : ∀ y ∈ Set.Icc lo hi, ‖∑ p ∈ (Ioc ⌊lo⌋₊ ⌊y⌋₊).filter Nat.Prime,
        χ p * (p : ℂ) ^ ((-1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        κ₂ * Real.log (x ^ K') ^ (-A') := fun y hy ↦
      hPTx H lo y (hscale'.trans hsqrtH) hHx hHlo (hy.2.trans hhi) k hk hkx χ t hE₂ htx
    have hBκ : κ₂ * Real.log (x ^ K') ^ (-A') ≤ |κ₂| * Real.exp (-(A' * T)) := by
      have h1 : Real.log (x ^ K') ^ (-A') ≤ L ^ (-A') :=
        Real.rpow_le_rpow_of_nonpos hL0 hLL' (by linarith)
      rw [hrpowL] at h1
      calc κ₂ * Real.log (x ^ K') ^ (-A') ≤ |κ₂| * Real.log (x ^ K') ^ (-A') :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ |κ₂| * Real.exp (-(A' * T)) := by
            refine mul_le_mul_of_nonneg_left (h1.trans_eq ?_) (abs_nonneg _)
            ring_nf
    -- the integer kernel bound at the scales `H / d`, `d ≤ √H`
    have hK : ∀ d : ℕ, 1 ≤ d → d ≤ ⌊Real.sqrt H⌋₊ → ∀ y ∈ Set.Icc (lo / d) (hi / d),
        ‖∑ m ∈ Ioc ⌊lo / d⌋₊ ⌊y⌋₊, χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
          k * |κ₃| * H * ((1 + |t|)⁻¹ + Real.exp (-Real.log (x ^ K') ^ (0.95 : ℝ))) / d := by
      intro d hd hdD
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      have hdsq : (d : ℝ) ≤ Real.sqrt H :=
        (Nat.cast_le.mpr hdD).trans (Nat.floor_le (Real.sqrt_nonneg H))
      have hHd : Real.sqrt H ≤ H / d := by
        rw [le_div_iff₀ hd0]
        calc Real.sqrt H * d ≤ Real.sqrt H * Real.sqrt H :=
              mul_le_mul_of_nonneg_left hdsq (Real.sqrt_nonneg H)
          _ = H := Real.mul_self_sqrt hH0.le
      exact norm_sum_char_cpow_le_of_kernel hIKx hk hkx χ ht1 htx hH0 hHx hHlo hhi hd
        (hscale'.trans hHd)
    have ht' : (1 + |t|)⁻¹ ≤ Real.exp (-(E * T)) := by
      have h1 : Real.exp (E * T) ≤ 1 + |t| := by
        have : Real.exp (E * T) ≤ Real.log (x ^ K') ^ E := by
          rw [hthrE]
          exact le_mul_of_one_le_left (Real.exp_pos _).le hKE
        linarith
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) h1
    have hL' : Real.exp (-Real.log (x ^ K') ^ (0.95 : ℝ)) ≤ Real.exp (-(M * T)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      refine hF5.trans ?_
      have h := Real.rpow_le_rpow hL0.le hLL' (by norm_num : (0 : ℝ) ≤ 95 / 100)
      norm_num at h ⊢
      exact h
    have h := high_frequency_bound hj χ t hP hlo hH1 hHlo hlohi hhi hε0 hε2 hR0 hRD hD0 hHε hkexp
      ht' hL' hB hBκ hK hM hE hA'0 hCm'0 hT0
    refine h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hW0) (by linarith))
    have : 0 ≤ 14 + 4 * |C₀| * (K' ^ E + 2) + 3 * (K' ^ E + 2) * W + 4 * W := by
      have : 0 ≤ K' ^ E + 2 := by linarith
      positivity
    linarith

open scoped Classical in
/-- AC1 at a fixed large `x`, from the parameter inequalities and the analytic inputs. -/
private theorem proxyTwist_at {c Ch A Cm Kan x c₁ C₀ E₂ κ₂ κ₃ CM A' Cm' K' E M : ℝ}
    (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hPNT : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
      ‖∑ n ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          (if χ = 1 then (y : ℂ) else 0)‖ ≤ C₀ * (k : ℝ) ^ C₀ * y ^ (1 - c₁))
    (hCM : ∀ Y : ℝ, 2 ≤ Y → ∑ p ∈ primesIcc 2 Y, (1 : ℝ) / p ≤ Real.log (Real.log Y) + CM)
    (hAA' : A ≤ A') (hA'0 : 0 ≤ A') (hCm : Cm ≤ Cm') (hCm'0 : 0 ≤ Cm') (hKan : Kan ≤ K')
    (hK'1 : 1 ≤ K') (hE2 : E₂ ≤ E) (hE : A' + Cm' + 14 ≤ E) (hMA : 4 * A' ≤ M)
    (hMc : A' + Cm' * |C₀| + E ≤ c₁ * M) (hM : 2 * (A' + Cm' + E + 2) ≤ M) (hM1 : 1 ≤ M)
    (hpar : 1 < Real.log x ∧ 1 ≤ logLog x ∧
      M * logLog x ≤ presieveExponent c Ch x * Real.log x - Real.log 2 ∧
      M * logLog x + 1 ≤ presieveExponent c Ch x * logLog x ^ 25 ∧
      2 * K' * Real.log x / logLog x ^ 22 ≤
        presieveExponent c Ch x * Real.log x - Real.log 2 ∧
      M * logLog x ≤ Real.log x ^ (95 / 100 : ℝ) ∧
      Cm' * logLog x < Real.log x ^ (28 / 100 : ℝ) ∧
      Real.log x ^ (45 / 100 : ℝ) ≤ Real.log x / logLog x ^ 25 ∧
      2 * logLog x ^ 25 ≤ Real.log x)
    (hPTx : PrimeTwistBound (x ^ K') A' E₂ Cm' κ₂) (hIKx : IntegerKernelBound (x ^ K') Cm' κ₃)
    (hx1 : 1 < x) {j : ℕ} (hj : 1 ≤ j) {H lo hi : ℝ}
    (hH : x ^ presieveExponent c Ch x / 2 ≤ H) (hHK : H ≤ x ^ Kan) (hHlo : H ≤ lo)
    (hhi : hi ≤ 2 * H) {k : ℕ} (hk : 1 ≤ k) (hkL : (k : ℝ) ≤ Real.log x ^ Cm)
    (χ : DirichletCharacter ℂ k) {t : ℝ} (ht : |t| ≤ x ^ Kan) :
    ‖(H : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊,
        χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I) *
          (((if n.Prime ∧ x ^ presieveExponent c Ch x < n then 1 else 0 : ℝ) : ℂ) -
            (unstrippedProxy x (presieveExponent c Ch x) j n : ℂ))‖ ≤
      (14 + 4 * |C₀| * (K' ^ E + 2) + 3 * (K' ^ E + 2) * Real.exp (14 * |CM|) +
        8 * Real.exp (14 * |CM|) + 3 * |κ₂| + 4 * |κ₃| * Real.exp (14 * |CM|)) *
          Real.log x ^ (-A) := by
  obtain ⟨hL1, hT1, hF2, hF1, hF4, hF5, hF6, hF7, hF8⟩ := hpar
  have : NeZero k := ⟨by omega⟩
  have hx : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hrpowL : ∀ y : ℝ, Real.log x ^ y = Real.exp (y * logLog x) := fun y ↦ by
    rw [Real.rpow_def_of_pos hL0, mul_comm]
    rfl
  have hkexp : (k : ℝ) ≤ Real.exp (Cm' * logLog x) := by
    rw [← hrpowL]
    exact hkL.trans (Real.rpow_le_rpow_of_exponent_le hL1.le hCm)
  obtain ⟨hP, hkP, hkY, hY2⟩ := candidate_facts hL1 hF6 hF7 hkexp
  obtain ⟨hε0, hε2, hε, hR0, hRD, hD0, hDinv⟩ := rankin_facts hCM hL1 hT1 hF8 hY2 hj
  obtain ⟨hH0, he, hlogH, hMT, hHε⟩ := scale_facts hx hL1 hT1 hM1 hF2 hF1 hε hε2 hH
  have hH1 : 1 ≤ H := (Real.one_le_exp zero_le_one).trans he
  have hscale : Real.exp (K' * Real.log x / logLog x ^ 22) ≤ Real.sqrt H := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [← Real.exp_nat_mul, ← Real.exp_log hH0, Real.exp_le_exp]
    have e : ((2 : ℕ) : ℝ) * (K' * Real.log x / logLog x ^ 22) =
        2 * K' * Real.log x / logLog x ^ 22 := by push_cast; ring
    linarith
  have hx'1 : 1 ≤ x ^ K' := Real.one_le_rpow hx1.le (by linarith)
  have hHx : H ≤ x ^ K' := hHK.trans (Real.rpow_le_rpow_of_exponent_le hx1.le hKan)
  have htx : |t| ≤ (x ^ K') ^ 3 := by
    refine (ht.trans (Real.rpow_le_rpow_of_exponent_le hx1.le hKan)).trans ?_
    exact le_self_pow₀ hx'1 (by norm_num)
  obtain ⟨-, hLL', -⟩ := xprime_facts hx hK'1 hL1 hT1
  have hkx : (k : ℝ) ≤ Real.log (x ^ K') ^ Cm' :=
    (hkL.trans (Real.rpow_le_rpow_of_exponent_le hL1.le hCm)).trans
      (Real.rpow_le_rpow hL0.le hLL' hCm'0)
  have hA : Real.exp (-(A' * logLog x)) ≤ Real.log x ^ (-A) := by
    rw [hrpowL, Real.exp_le_exp]
    nlinarith
  -- restrict to `n > x^γ`
  have hxγ0 : 0 ≤ x ^ presieveExponent c Ch x := Real.rpow_nonneg hx.le _
  rw [sum_centered_eq_max x _ j χ t lo hi hxγ0]
  set lo' := max lo (x ^ presieveExponent c Ch x) with hlo'
  have hHlo' : H ≤ lo' := hHlo.trans (le_max_left _ _)
  have hκ0 : 0 ≤ (14 + 4 * |C₀| * (K' ^ E + 2) + 3 * (K' ^ E + 2) * Real.exp (14 * |CM|) +
      8 * Real.exp (14 * |CM|) + 3 * |κ₂| + 4 * |κ₃| * Real.exp (14 * |CM|)) := by
    have : 0 ≤ K' ^ E + 2 := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ K') E
      linarith
    positivity
  rcases le_or_gt hi lo' with hhilo | hhilo
  · have hempty : Ioc ⌊lo'⌋₊ ⌊hi⌋₊ = ∅ :=
      Finset.Ioc_eq_empty (not_lt.mpr (Nat.floor_le_floor hhilo))
    rw [hempty, sum_empty, mul_zero, norm_zero]
    exact mul_nonneg hκ0 (Real.rpow_nonneg hL0.le _)
  have hcut : ∀ n ∈ Ioc ⌊lo'⌋₊ ⌊hi⌋₊, x ^ presieveExponent c Ch x < n := by
    intro n hn
    have h := (Nat.floor_lt (le_max_of_le_right hxγ0)).mp (mem_Ioc.mp hn).1
    exact (le_max_right _ _).trans_lt h
  rw [sum_centered_eq x _ j χ t hcut, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hH0, inv_mul_le_iff₀ hH0]
  have h := proxyTwist_reduced χ t (E₂ := E₂) (W := Real.exp (14 * |CM|)) hj hP hkY hkP hc₁0
    hc₁1 hPNT hPTx hIKx hx hL1 hT1 hF5 (he.trans hHlo') hH1 hHlo' hhilo.le hhi hHx htx hscale hk
    hkx hkexp hε0 hε2 hR0 hRD hD0 hDinv hHε hMT hK'1 hE2 hE hMA hMc hM hA'0 hCm'0
  exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hκ0) hH0.le)

/-- The damped-proxy twist bound (AC1). -/
theorem eventually_proxyTwist (c Ch Cj A Cm Kan : ℝ) (hc : 0 < c) :
    ∃ κ : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ (j : ℕ), 1 ≤ j → (j : ℝ) ≤ Cj * logLogLog x + 1 →
      ∀ H lo hi : ℝ, x ^ presieveExponent c Ch x / 2 ≤ H → H ≤ x ^ Kan → H ≤ lo →
        hi ≤ 2 * H →
      ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm → ∀ (χ : DirichletCharacter ℂ k)
        (t : ℝ), |t| ≤ x ^ Kan →
        ‖(H : ℂ)⁻¹ * ∑ n ∈ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊,
            χ n * (n : ℂ) ^ ((t : ℂ) * Complex.I) *
              (((if n.Prime ∧ x ^ presieveExponent c Ch x < n then 1 else 0 : ℝ) : ℂ) -
                (unstrippedProxy x (presieveExponent c Ch x) j n : ℂ))‖ ≤
          κ * Real.log x ^ (-A) := by
  classical
  -- the analytic inputs: AC0, AC2, AC3, and Mertens
  obtain ⟨c₀, hc₀, C₀, hPNT⟩ := sum_vonMangoldt_mul_char_sub_le
  obtain ⟨E₂, κ₂, hPT⟩ := eventually_primeTwistBound (max A 0) (max Cm 0)
  obtain ⟨κ₃, hIK⟩ := eventually_integerKernelBound (max Cm 0)
  obtain ⟨CM, hCM⟩ := exists_sum_primesIcc_inv_le
  -- the constants
  set A' := max A 0
  set Cm' := max Cm 0
  set K' := max Kan 1
  set c₁ := min c₀ 1
  set E := max E₂ 0 + A' + Cm' + 14
  set M := 4 * A' + (A' + Cm' * |C₀| + E) / c₁ + 2 * (A' + Cm' + E + 2) + 1
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hCm'0 : 0 ≤ Cm' := le_max_right _ _
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hc₁0 : 0 < c₁ := lt_min hc₀ one_pos
  have hc₁1 : c₁ ≤ 1 := min_le_right _ _
  have hE2 : E₂ ≤ E := by
    have := le_max_left E₂ 0
    linarith
  have hE : A' + Cm' + 14 ≤ E := by
    have := le_max_right E₂ 0
    linarith
  have hQ0 : 0 ≤ (A' + Cm' * |C₀| + E) / c₁ := by
    have : 0 ≤ Cm' * |C₀| := by positivity
    exact div_nonneg (by linarith) hc₁0.le
  have hMA : 4 * A' ≤ M := by linarith
  have hMM : 2 * (A' + Cm' + E + 2) ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hMc : A' + Cm' * |C₀| + E ≤ c₁ * M := by
    have e : c₁ * ((A' + Cm' * |C₀| + E) / c₁) = A' + Cm' * |C₀| + E :=
      mul_div_cancel₀ _ hc₁0.ne'
    have : 0 ≤ c₁ * (4 * A' + 2 * (A' + Cm' + E + 2) + 1) := by positivity
    have : c₁ * M = c₁ * ((A' + Cm' * |C₀| + E) / c₁) +
        c₁ * (4 * A' + 2 * (A' + Cm' + E + 2) + 1) := by ring
    linarith
  -- the prime number theorem with exponent `c₁ ≤ 1`
  have hPNT' : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k) (y : ℝ), 2 ≤ y →
      ‖∑ n ∈ Icc 1 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n -
          (if χ = 1 then (y : ℂ) else 0)‖ ≤ C₀ * (k : ℝ) ^ C₀ * y ^ (1 - c₁) := by
    intro k _ χ y hy
    have h := hPNT k χ y hy
    have hy0 : 0 < y ^ (1 - c₀) := Real.rpow_pos_of_pos (by linarith) _
    have hCk : 0 ≤ C₀ * (k : ℝ) ^ C₀ :=
      (mul_nonneg_iff_of_pos_right hy0).mp ((norm_nonneg _).trans h)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hCk)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [min_le_left c₀ 1])
  refine ⟨14 + 4 * |C₀| * (K' ^ E + 2) + 3 * (K' ^ E + 2) * Real.exp (14 * |CM|) +
    8 * Real.exp (14 * |CM|) + 3 * |κ₂| + 4 * |κ₃| * Real.exp (14 * |CM|), ?_⟩
  have hx' : Tendsto (fun x : ℝ ↦ x ^ K') atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [eventually_params c Ch hc M Cm' K', hx'.eventually hPT, hx'.eventually hIK,
    eventually_gt_atTop 1] with x hpar hPTx hIKx hx1
  intro j hj _ H lo hi hH hHK hHlo hhi k hk hkL χ t ht
  exact proxyTwist_at hc₁0 hc₁1 hPNT' hCM (le_max_left _ _) hA'0 (le_max_left _ _) hCm'0
    (le_max_left _ _) hK'1 hE2 hE hMA hMc hMM hM1 hpar hPTx hIKx hx1 hj hH hHK hHlo hhi hk hkL
    χ ht

end Erdos408
