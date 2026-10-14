module

public import Erdos408.Analytic.QuasiRH

/-!
# Dirichlet L-functions near the line `re s = 1`

Bounds for `L(s, χ)` and its logarithmic derivative, for every Dirichlet
character `χ` of modulus `k`, in the part `re s ≥ 15/16` of the zero-free
half-plane `re s > 7/8`. Put `ℓ = log(k (|im s| + 3))`.

* Polynomial growth: `|L(s, χ)| ≪ k (|im s| + 3)` on `re s ≥ 1/2`, away from
  the pole, by partial summation.
* Borel–Carathéodory on discs centred at `2 + it`, inside the zero-free
  half-plane, gives `|L'/L(s, χ)| ≪ ℓ` on `15/16 ≤ re s ≤ 2`. For the
  principal character the pole is removed with `(s - 1) L(s, χ)`.
* Hadamard's three circles for `log L` around `2 + it`, deduced from the three
  lines theorem, give `|L(s, χ)| ≤ exp(C √ℓ)` on `63/64 ≤ re s ≤ 2`, `|im s| ≥ 3`.

These are the inputs of the contour shifts in `Erdos408.Analytic.Contracts`,
as outlined in *The normal order of the number of iterations of Euler's
function* (Plasma AI, 2026), §6.2. No zero of `L(s, χ)` is located or counted.
-/

@[expose] public section

namespace Erdos408

open Complex Metric DirichletCharacter MeasureTheory Filter Asymptotics

open scoped LSeries.notation Topology

/-! ### Partial summation -/

/-- **Partial summation.** If `f` is bounded by one and its partial sums are `a t + O(B)`,
then `L(f, s) = a s / (s - 1) + s I(s)` on `1 < re s`, where `I` is holomorphic on
`0 < re s` and bounded by `B / re s` there. Adapted from `Erdos770.norm_LFunction_le`. -/
lemma exists_LSeries_eq_add {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (a : ℂ) {B : ℝ}
    (hB : ∀ t : ℝ, 1 ≤ t → ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) - a * t‖ ≤ B) :
    ∃ I : ℂ → ℂ, DifferentiableOn ℂ I {s | 0 < s.re} ∧
      (∀ s : ℂ, 0 < s.re → ‖I s‖ ≤ B / s.re) ∧
      ∀ s : ℂ, 1 < s.re → LSeries f s = a * s / (s - 1) + s * I s := by
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 1 le_rfl)
  let S : ℝ → ℂ := fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k
  let A : ℝ → ℂ := fun t ↦ S t - a * t
  -- the remainder cut off below one, as a Mellin transform input
  let g : ℝ → ℂ := (Set.Ioi (1 : ℝ)).indicator fun _ ↦ (1 : ℂ)
  let F : ℝ → ℂ := fun t ↦ g t * S t - g t * (a * t)
  have hF (t : ℝ) : ‖F t‖ ≤ B := by
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simpa [F, g, ht, S] using hB t (Set.mem_Ioi.mp ht).le
    · simpa [F, g, ht] using hB₀
  let I : ℂ → ℂ := fun z ↦ ∫ t in Set.Ioi (1 : ℝ), A t * (t : ℂ) ^ (-(z + 1))
  have hImellin : I = fun z ↦ mellin F (-z) := by
    funext z
    have hint : (fun t : ℝ ↦ (t : ℂ) ^ (-z - 1) • F t) =
        (Set.Ioi (1 : ℝ)).indicator (fun t ↦ A t * (t : ℂ) ^ (-(z + 1))) := by
      funext t
      rw [show -z - 1 = -(z + 1) by ring]
      by_cases ht : t ∈ Set.Ioi (1 : ℝ)
      · simp [F, g, A, ht, mul_comm, mul_sub]
      · simp [F, g, ht]
    rw [mellin, hint, setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
      sup_eq_right.mpr zero_le_one]
  refine ⟨I, ?_, ?_, ?_⟩
  · -- `I` is a Mellin transform, holomorphic on the right half-plane
    intro z hz
    have hmellin : DifferentiableAt ℂ (mellin F) (-z) := by
      refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -z.re - 1) ?_ ?_
        (by simpa using (show 0 < z.re from hz)) ?_ (by simp)
      · have hg : LocallyIntegrableOn g (Set.Ici 0) :=
          ((locallyIntegrable_const 1).indicator measurableSet_Ioi).locallyIntegrableOn _
        have h₁ := (locallyIntegrableOn_mul_sum_Icc (m := 1) f le_rfl hg).mono_set
          Set.Ioi_subset_Ici_self
        have h₂ : LocallyIntegrableOn (fun t : ℝ ↦ g t * (a * t)) (Set.Ioi 0) := by
          have : (fun t : ℝ ↦ g t * (a * t)) =
              (Set.Ioi (1 : ℝ)).indicator fun t : ℝ ↦ a * t := by
            funext t
            by_cases ht : t ∈ Set.Ioi (1 : ℝ) <;> simp [g, ht]
          rw [this]
          exact ((Continuous.locallyIntegrable (by fun_prop)).indicator
            measurableSet_Ioi).locallyIntegrableOn _
        exact h₁.sub h₂
      · exact IsBigO.of_bound B (Eventually.of_forall fun t ↦ by simpa using hF t)
      · refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with t ht
        simp [F, g, not_lt.mpr (Set.mem_Iio.mp ht).le]
    rw [hImellin]
    exact (hmellin.comp z differentiableAt_id.neg).differentiableWithinAt
  · -- bound the integral
    intro s hs
    have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ (-s.re - 1)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    calc ‖I s‖
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), B * t ^ (-s.re - 1) := by
        refine norm_integral_le_of_norm_le (hrpow.const_mul _) ?_
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
        have ht₀ : 0 < t := zero_lt_one.trans ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
        have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
        rw [hre]
        gcongr
        exact hB t (Set.mem_Ioi.mp ht).le
      _ = B / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
          show -s.re - 1 + 1 = -s.re by ring, Real.one_rpow]
        field_simp
  · -- the integral representation to the right of one
    intro s hs
    have hs₁ : s - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)
      have h₁ : ∑ k ∈ Finset.Icc 1 n, ‖f k‖ ≤ n := by
        calc ∑ k ∈ Finset.Icc 1 n, ‖f k‖
          _ ≤ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ hf k
          _ = n := by simp
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _), Real.rpow_one,
        Real.norm_natCast, one_mul]
      exact h₁
    rw [LSeries_eq_mul_integral' f zero_le_one hs hO]
    -- split off the main term `a t`
    have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ A t * (t : ℂ) ^ (-(s + 1)))
        (volume.restrict (Set.Ioi 1)) := by
      have hS : Measurable S :=
        (measurable_from_nat (f := fun n ↦ ∑ k ∈ Finset.Icc 1 n, f k)).comp
          Nat.measurable_floor
      refine ((hS.sub (by fun_prop)).aestronglyMeasurable).mul ?_
      exact (measurable_ofReal.pow_const _).aestronglyMeasurable
    have hA : IntegrableOn (fun t : ℝ ↦ A t * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
      have hrpow : IntegrableOn (fun t : ℝ ↦ B * t ^ (-s.re - 1)) (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
      refine hrpow.mono' hmeas (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_)
      have ht₀ : 0 < t := zero_lt_one.trans ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      gcongr
      exact hB t (Set.mem_Ioi.mp ht).le
    have hpow : IntegrableOn (fun t : ℝ ↦ a * (t : ℂ) ^ (-s)) (Set.Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one).const_mul _
    have hsplit : ∫ t in Set.Ioi (1 : ℝ), S t * (t : ℂ) ^ (-(s + 1)) =
        ∫ t in Set.Ioi (1 : ℝ), (A t * (t : ℂ) ^ (-(s + 1)) + a * (t : ℂ) ^ (-s)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
      have hcpow : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-(s + 1)) * t := by
        rw [show -s = -(s + 1) + 1 by ring, cpow_add _ _ ht₀, cpow_one]
      simp only [A, hcpow]
      ring
    have hmain : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
      have hs₂ : -s + 1 ≠ 0 := by
        rw [show -s + 1 = -(s - 1) by ring]
        exact neg_ne_zero.mpr hs₁
      rw [integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one, ofReal_one, one_cpow,
        show s - 1 = -(-s + 1) by ring]
      field_simp
    rw [hsplit, integral_add hA hpow, integral_const_mul, hmain]
    field_simp
    ring

/-- The partial sums of a nontrivial Dirichlet character are bounded by its modulus.
Copied from `Erdos770.norm_sum_Icc_le`. -/
lemma norm_sum_Icc_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ N := by
  let f : ℕ → ℂ := fun k ↦ χ k
  -- a full period of values sums to zero
  have h₀ : ∑ k ∈ Finset.range N, f k = 0 := by
    rw [← χ.sum_eq_zero_of_ne_one hχ]
    exact Finset.sum_nbij' (fun k ↦ (k : ZMod N)) ZMod.val (by simp)
      (fun x _ ↦ Finset.mem_range.mpr (ZMod.val_lt x))
      (fun k hk ↦ ZMod.val_cast_of_lt (Finset.mem_range.mp hk))
      (fun x _ ↦ ZMod.natCast_zmod_val x) (fun _ _ ↦ rfl)
  -- so does a shifted full period
  have hperiod : ∑ k ∈ Finset.range N, f (k + 1) = 0 := by
    have h₁ := Finset.sum_range_succ f N
    have h₂ := Finset.sum_range_succ' f N
    have hN : f N = f 0 := by simp [f]
    linear_combination h₁ - h₂ + h₀ + hN
  -- rewrite the partial sums over `range`
  have hIcc (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, f k = ∑ k ∈ Finset.range n, f (k + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  -- bound by strong induction, peeling off full periods
  have hbound (n : ℕ) : ‖∑ k ∈ Finset.range n, f (k + 1)‖ ≤ N := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases lt_or_ge n N with hn | hn
      · calc ‖∑ k ∈ Finset.range n, f (k + 1)‖
          _ ≤ ∑ k ∈ Finset.range n, ‖f (k + 1)‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum fun k _ ↦ χ.norm_le_one _
          _ = n := by simp
          _ ≤ N := by exact_mod_cast hn.le
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
        have hshift (k : ℕ) : f (N + k + 1) = f (k + 1) := by
          change χ ((N + k + 1 : ℕ) : ZMod N) = χ ((k + 1 : ℕ) : ZMod N)
          push_cast
          rw [ZMod.natCast_self, zero_add]
        rw [Finset.sum_range_add, hperiod, zero_add]
        simp_rw [hshift]
        exact ih m (by have := NeZero.pos N; omega)
  exact (hIcc n).symm ▸ hbound n

/-- A nontrivial Dirichlet L-function grows at most linearly in `‖s‖` to the right of zero.
Adapted from `Erdos770.norm_LFunction_le`. -/
theorem norm_LFunction_le_of_ne_one {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) : ‖LFunction χ s‖ ≤ k * ‖s‖ / s.re := by
  obtain ⟨I, hI, hIb, hL⟩ := exists_LSeries_eq_add (f := fun n ↦ χ n)
    (fun n ↦ χ.norm_le_one n) 0 (B := k) (fun t _ ↦ by simpa using norm_sum_Icc_le hχ ⌊t⌋₊)
  -- both sides are analytic on the right half-plane
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hEq : Set.EqOn (LFunction χ) (fun z ↦ z * I z) U := by
    have hLan := (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
    refine hLan.eqOn_of_preconnected_of_eventuallyEq
      ((differentiableOn_id.mul hI).analyticOnNhd hU)
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp [U]) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    rw [LFunction_eq_LSeries χ hz, hL z hz]
    simp
  calc ‖LFunction χ s‖
    _ = ‖s‖ * ‖I s‖ := by rw [hEq hs, norm_mul]
    _ ≤ ‖s‖ * (k / s.re) := by gcongr; exact hIb s hs
    _ = k * ‖s‖ / s.re := by ring

/-- The Riemann zeta function is `s / (s - 1) + O(‖s‖ / re s)` to the right of zero. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by
  have hfloor (t : ℝ) (ht : 1 ≤ t) :
      ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) - 1 * t‖ ≤ 1 := by
    have h₁ := Nat.floor_le (zero_le_one.trans ht)
    have h₂ := Nat.lt_floor_add_one t
    simp only [Pi.one_apply, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
      nsmul_eq_mul, mul_one, one_mul]
    rw [show (⌊t⌋₊ : ℂ) - t = ((⌊t⌋₊ - t : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨I, hI, hIb, hL⟩ := exists_LSeries_eq_add (f := 1) (fun n ↦ by simp) 1 hfloor
  -- `(s - 1) ζ(s)` is entire, and equals `s + (s - 1) s I(s)` on the right half-plane
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hEq : Set.EqOn (LFunctionTrivChar₁ 1) (fun z ↦ z + (z - 1) * z * I z) U := by
    have hZan := (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd hU
    refine hZan.eqOn_of_preconnected_of_eventuallyEq
      ((differentiableOn_id.add (((differentiableOn_id.sub_const 1).mul
        differentiableOn_id).mul hI)).analyticOnNhd hU)
      (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp [U]) ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz₁ : z - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    rw [LFunctionTrivChar₁, Function.update_of_ne (sub_ne_zero.mp hz₁), LFunctionTrivChar,
      LFunction_modOne_eq, ← LSeries_one_eq_riemannZeta hz, hL z hz]
    field_simp
  have hs₁' : s - 1 ≠ 0 := sub_ne_zero.mpr hs₁
  have hζ : riemannZeta s = s / (s - 1) + s * I s := by
    have h := hEq hs
    rw [LFunctionTrivChar₁, Function.update_of_ne hs₁, LFunctionTrivChar,
      LFunction_modOne_eq] at h
    field_simp
    linear_combination h
  calc ‖riemannZeta s‖
    _ ≤ ‖s / (s - 1)‖ + ‖s * I s‖ := by rw [hζ]; exact norm_add_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / s.re) := by
      rw [norm_div, norm_mul]
      gcongr
      exact hIb s hs
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ / s.re := by ring

/-- The L-function of the trivial character mod `k` is at most `k` times the bound
`norm_riemannZeta_le` for zeta. -/
theorem norm_LFunction_one_le {k : ℕ} [NeZero k] {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    ‖LFunction (1 : DirichletCharacter ℂ k) s‖ ≤ k * (‖s‖ / ‖s - 1‖ + ‖s‖ / s.re) := by
  rw [← LFunctionTrivChar, LFunctionTrivChar_eq_mul_riemannZeta hs₁, norm_mul]
  gcongr
  · -- each Euler factor is at most `2 ≤ p`, and `∏ p ∣ k`
    rw [norm_prod]
    calc ∏ p ∈ k.primeFactors, ‖1 - (p : ℂ) ^ (-s)‖
      _ ≤ ∏ p ∈ k.primeFactors, (p : ℝ) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ ?_)
        have hp := Nat.prime_of_mem_primeFactors hp
        calc ‖1 - (p : ℂ) ^ (-s)‖
          _ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
            rw [norm_one, norm_natCast_cpow_of_pos hp.pos]
            gcongr
            exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_lt.le)
              (by simp; linarith)
          _ ≤ p := by exact_mod_cast hp.two_le
      _ ≤ k := by
        rw [← Nat.cast_prod]
        exact_mod_cast Nat.le_of_dvd (NeZero.pos k) (Nat.prod_primeFactors_dvd k)
  · exact norm_riemannZeta_le hs hs₁

/-- `‖s‖ / re s ≤ 1 + 2 |im s|` on `re s ≥ 1/2`. -/
private lemma norm_div_re_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖s‖ / s.re ≤ 1 + 2 * |s.im| := by
  have hσ : 0 < s.re := by linarith
  have h := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hσ] at h
  rw [div_le_iff₀ hσ]
  nlinarith [abs_nonneg s.im]

/-- Polynomial growth of Dirichlet L-functions on `re s ≥ 1/2`, away from `s = 1`, with an
explicit constant. -/
theorem norm_LFunction_le_two_mul {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (hs₁ : 1 ≤ ‖s - 1‖) :
    ‖LFunction χ s‖ ≤ 2 * k * (|s.im| + 3) := by
  have hσ : 0 < s.re := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have ht := norm_div_re_le hs
  have hti := abs_nonneg s.im
  rcases eq_or_ne χ 1 with rfl | hχ
  · have hs₁' : s ≠ 1 := by
      rintro rfl
      norm_num at hs₁
    -- `‖s‖ / ‖s - 1‖ ≤ 1 + 1 / ‖s - 1‖ ≤ 2`
    have hpole : ‖s‖ / ‖s - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      have := norm_le_norm_sub_add s 1
      rw [norm_one] at this
      linarith
    calc ‖LFunction 1 s‖
      _ ≤ k * (‖s‖ / ‖s - 1‖ + ‖s‖ / s.re) := norm_LFunction_one_le hσ hs₁'
      _ ≤ k * (2 + (1 + 2 * |s.im|)) := by gcongr
      _ ≤ 2 * k * (|s.im| + 3) := by nlinarith
  · calc ‖LFunction χ s‖
      _ ≤ k * ‖s‖ / s.re := norm_LFunction_le_of_ne_one hχ hσ
      _ = k * (‖s‖ / s.re) := by ring
      _ ≤ k * (1 + 2 * |s.im|) := by gcongr
      _ ≤ 2 * k * (|s.im| + 3) := by nlinarith

/-! ### Bounds to the right of one -/

/-- The zeta series `∑ (n + 1) ^ (-σ)` is bounded by `σ / (σ - 1)`. Copied from the proof of
`Erdos770.le_norm_LFunction`. -/
private lemma tsum_one_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ ≤ σ / (σ - 1) := by
  have hσ₀ : 0 < σ := by linarith
  have hσ₁ : 0 < σ - 1 := by linarith
  have h₀ : 0 ≤ ZetaAsymptotics.termTSum σ :=
    tsum_nonneg fun n ↦ ZetaAsymptotics.term_nonneg (n + 1) σ
  rw [ZetaAsymptotics.termTSum_of_lt hσ] at h₀
  rw [le_div_iff₀ hσ₁]
  have h₁ := mul_le_mul_of_nonneg_left (sub_nonneg.mp h₀) (mul_nonneg hσ₀.le hσ₁.le)
  field_simp at h₁
  linarith

/-- A Dirichlet L-function is bounded above by `re s / (re s - 1)` to the right of one. -/
theorem norm_LFunction_le_of_one_lt_re {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {s : ℂ} (hs : 1 < s.re) : ‖LFunction χ s‖ ≤ s.re / (s.re - 1) := by
  have hsum : LSeriesSummable (fun n ↦ χ n) s := LSeriesSummable_of_one_lt_re χ hs
  have hζsum : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ s.re := by
    exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  -- each term is bounded by the corresponding zeta term
  have hterm (n : ℕ) : ‖LSeries.term (fun n ↦ χ n) s (n + 1)‖ ≤ 1 / ((n : ℝ) + 1) ^ s.re := by
    simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, ↓reduceIte]
    push_cast
    gcongr
    exact χ.norm_le_one _
  have hshift : Summable fun n : ℕ ↦ ‖LSeries.term (fun n ↦ χ n) s (n + 1)‖ :=
    (summable_nat_add_iff 1).mpr hsum.norm
  rw [LFunction_eq_LSeries χ hs, LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  calc ‖∑' n : ℕ, LSeries.term (fun n ↦ χ n) s (n + 1)‖
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n ↦ χ n) s (n + 1)‖ := norm_tsum_le_tsum_norm hshift
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := hshift.tsum_le_tsum hterm hζsum
    _ ≤ s.re / (s.re - 1) := tsum_one_div_rpow_le hs

open scoped ArithmeticFunction.Moebius in
/-- A Dirichlet L-function is bounded below by `(re s - 1) / re s` to the right of one.
Copied from `Erdos770.le_norm_LFunction`. -/
theorem le_norm_LFunction {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) {s : ℂ}
    (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖LFunction χ s‖ := by
  -- the L-series of `μ χ` inverts `L(s, χ)`
  have hmul : LFunction χ s * LSeries (↗χ * ↗μ) s = 1 := by
    rw [LFunction_eq_LSeries χ hs]
    exact LSeries.mul_mu_eq_one χ hs
  have hsum : LSeriesSummable (↗χ * ↗μ) s :=
    LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hζsum : Summable fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ s.re := by
    exact_mod_cast (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  -- each term of the `μ χ` series is bounded by the corresponding zeta term
  have hterm (n : ℕ) :
      ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ ≤ 1 / ((n : ℝ) + 1) ^ s.re := by
    simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, ↓reduceIte, Pi.mul_apply, norm_mul]
    push_cast
    gcongr
    calc ‖χ (n + 1)‖ * ‖(μ (n + 1) : ℂ)‖
      _ ≤ 1 * 1 := by
        gcongr
        · exact χ.norm_le_one _
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      _ = 1 := one_mul 1
  have hM : ‖LSeries (↗χ * ↗μ) s‖ ≤ s.re / (s.re - 1) := by
    have hshift : Summable fun n : ℕ ↦ ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ :=
      (summable_nat_add_iff 1).mpr hsum.norm
    rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    calc ‖∑' n : ℕ, LSeries.term (↗χ * ↗μ) s (n + 1)‖
      _ ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗μ) s (n + 1)‖ :=
        norm_tsum_le_tsum_norm hshift
      _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re := hshift.tsum_le_tsum hterm hζsum
      _ ≤ s.re / (s.re - 1) := tsum_one_div_rpow_le hs
  -- invert the bound
  have hnorm : ‖LFunction χ s‖ * ‖LSeries (↗χ * ↗μ) s‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hMpos : 0 < ‖LSeries (↗χ * ↗μ) s‖ := by
    refine norm_pos_iff.mpr fun h ↦ ?_
    simp [h] at hmul
  rw [eq_comm, ← div_eq_iff hMpos.ne'] at hnorm
  rw [← hnorm, ← one_div_div]
  exact one_div_le_one_div_of_le hMpos hM

/-! ### Borel–Carathéodory and three circles -/

/-- A holomorphic function on an open set whose exponential is holomorphic is holomorphic.
Copied from `Erdos770.differentiableOn_of_exp_eq`. -/
lemma differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U) {G g : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G U) (hg : ContinuousOn g U)
    (he : Set.EqOn (Complex.exp ∘ g) G U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hGc : DifferentiableAt ℂ G z := (hG z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z) (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (G z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (G w)) =ᶠ[nhds z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hGc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

/-- A holomorphic function on a ball with no zeros and value `1` at the center has a
holomorphic logarithm vanishing at the center. Copied from `Erdos770.exists_holomorphic_log`. -/
lemma exists_holomorphic_log {G : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hG : DifferentiableOn ℂ G (ball c R)) (h0 : ∀ z ∈ ball c R, G z ≠ 0) (hc : G c = 1) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball c R) ∧
      Set.EqOn (Complex.exp ∘ h) G (ball c R) ∧ h c = 0 := by
  have : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨h, hh, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_ball
    hG.continuousOn (by rintro ⟨z, hz, heq⟩; exact h0 z hz heq)
  refine ⟨fun z ↦ h z - h c, (differentiableOn_of_exp_eq isOpen_ball hG hh he).sub_const _,
    fun z hz ↦ ?_, sub_self _⟩
  have hec : Complex.exp (h c) = 1 := (he (mem_ball_self hR)).trans hc
  simp only [Function.comp_apply, Complex.exp_sub, hec, div_one]
  exact he hz

/-- **Borel–Carathéodory** followed by a **Cauchy estimate**: if `h` is holomorphic on
`ball c r₂` with `h c = 0` and `re h ≤ B` there, then `‖h'‖ = O(B)` on `closedBall c r₁`.
Copied from `Erdos770.norm_deriv_le_of_re_le`. -/
lemma norm_deriv_le_of_re_le {h : ℂ → ℂ} {c z : ℂ} {r₁ r₂ B : ℝ} (h₁ : 0 ≤ r₁)
    (h₁₂ : r₁ < r₂) (hB : 0 ≤ B) (hh : DifferentiableOn ℂ h (ball c r₂)) (hc : h c = 0)
    (hre : ∀ w ∈ ball c r₂, (h w).re ≤ B) (hz : z ∈ closedBall c r₁) :
    ‖deriv h z‖ ≤ 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * B := by
  set r₃ := (r₁ + r₂) / 2 with hr₃
  have h₁₃ : r₁ < r₃ := by linarith
  have h₃₂ : r₃ < r₂ := by linarith
  have hC : 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 = 2 * r₃ / (r₂ - r₃) / (r₃ - r₁) := by
    have : r₂ - r₁ ≠ 0 := by linarith
    rw [show r₂ - r₃ = (r₂ - r₁) / 2 by linarith, show r₃ - r₁ = (r₂ - r₁) / 2 by linarith, hr₃]
    field_simp
    ring
  rw [hC]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set C := 2 * r₃ / (r₂ - r₃) / (r₃ - r₁)
  have hCpos : 0 < C := by
    have : 0 < r₃ := by linarith
    have : 0 < r₂ - r₃ := by linarith
    have : 0 < r₃ - r₁ := by linarith
    positivity
  -- Borel–Carathéodory on `closedBall c r₃`, recentred at the origin
  have hbc : ∀ w ∈ closedBall c r₃, ‖h w‖ ≤ 2 * (B + ε / C) * r₃ / (r₂ - r₃) := by
    intro w hw
    have hw' : ‖w - c‖ ≤ r₃ := by simpa [dist_eq_norm] using hw
    have hh' : DifferentiableOn ℂ (fun v ↦ h (c + v)) (ball 0 r₂) := by
      refine hh.comp (by fun_prop) fun v hv ↦ ?_
      simpa [mem_ball, dist_eq_norm] using hv
    have hb := Complex.borelCaratheodory (M := B + ε / C) (by positivity) hh'
      (fun v hv ↦ (hre _ (by simpa [mem_ball, dist_eq_norm] using hv)).trans
        (le_add_of_nonneg_right (by positivity)))
      (by linarith) (show w - c ∈ ball 0 r₂ by simpa using hw'.trans_lt h₃₂)
    simp only [add_sub_cancel, add_zero, hc, norm_zero, zero_mul, zero_div] at hb
    refine hb.trans ?_
    have : 0 < r₂ - ‖w - c‖ := by linarith
    have : 0 ≤ r₃ := by linarith
    gcongr
  -- Cauchy estimate on `sphere z (r₃ - r₁)`
  have hzc : ‖z - c‖ ≤ r₁ := by simpa [dist_eq_norm] using hz
  have hsub : closedBall z (r₃ - r₁) ⊆ closedBall c r₃ := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ r₃ := by linarith
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith)
    (hh.diffContOnCl_ball (hsub.trans (closedBall_subset_ball h₃₂)))
    (fun w hw ↦ hbc w (hsub (sphere_subset_closedBall hw)))
  refine hd.trans (le_of_eq ?_)
  rw [show 2 * (B + ε / C) * r₃ / (r₂ - r₃) / (r₃ - r₁) = C * (B + ε / C) by simp only [C]; ring,
    mul_add, mul_div_cancel₀ _ hCpos.ne']

/-- **Borel–Carathéodory**, recentred at `c`: if `h` is holomorphic on `ball c R` with
`h c = 0` and `re h ≤ B` there, then `‖h‖ ≤ 2 B r / (R - r)` on `closedBall c r`. -/
lemma norm_le_of_re_le {h : ℂ → ℂ} {c z : ℂ} {r R B : ℝ} (hrR : r < R) (hB : 0 < B)
    (hh : DifferentiableOn ℂ h (ball c R)) (hc : h c = 0)
    (hre : ∀ w ∈ ball c R, (h w).re ≤ B) (hz : z ∈ closedBall c r) :
    ‖h z‖ ≤ 2 * B * r / (R - r) := by
  have hz' : ‖z - c‖ ≤ r := by simpa [dist_eq_norm] using hz
  have hh' : DifferentiableOn ℂ (fun v ↦ h (c + v)) (ball 0 R) := by
    refine hh.comp (by fun_prop) fun v hv ↦ ?_
    simpa [mem_ball, dist_eq_norm] using hv
  have hb := Complex.borelCaratheodory_zero (M := B) hB hh'
    (fun v hv ↦ hre _ (by simpa [mem_ball, dist_eq_norm] using hv))
    (by linarith [norm_nonneg (z - c)]) (show z - c ∈ ball 0 R by simpa using hz'.trans_lt hrR)
    (by simpa using hc)
  simp only [add_sub_cancel] at hb
  refine hb.trans ?_
  have : 0 < R - ‖z - c‖ := by linarith
  have : 0 < R - r := by linarith
  have : 0 ≤ r := (norm_nonneg _).trans hz'
  gcongr

/-- **Borel–Carathéodory** for logarithmic derivatives: if `F` is holomorphic and zero-free
on `ball c r₂` with `‖F‖ ≤ M ‖F c‖` there, then `‖F' / F‖ = O(log M)` on `closedBall c r₁`. -/
theorem norm_logDeriv_le_of_norm_le {F : ℂ → ℂ} {c z : ℂ} {r₁ r₂ M : ℝ} (h₁ : 0 ≤ r₁)
    (h₁₂ : r₁ < r₂) (hM : 1 ≤ M) (hF : DifferentiableOn ℂ F (ball c r₂))
    (h0 : ∀ w ∈ ball c r₂, F w ≠ 0) (hFM : ∀ w ∈ ball c r₂, ‖F w‖ ≤ M * ‖F c‖)
    (hz : z ∈ closedBall c r₁) :
    ‖deriv F z / F z‖ ≤ 4 * (r₁ + r₂) / (r₂ - r₁) ^ 2 * Real.log M := by
  have h₂ : 0 < r₂ := h₁.trans_lt h₁₂
  have hc0 : F c ≠ 0 := h0 c (mem_ball_self h₂)
  -- a holomorphic logarithm `h` of `F / F c`, with `re h ≤ log M`
  obtain ⟨h, hh, hexp, hc⟩ := exists_holomorphic_log h₂ (G := fun w ↦ F w / F c)
    (hF.div_const _) (fun w hw ↦ div_ne_zero (h0 w hw) hc0) (div_self hc0)
  have hre : ∀ w ∈ ball c r₂, (h w).re ≤ Real.log M := by
    intro w hw
    have hFw : 0 < ‖F w‖ := norm_pos_iff.mpr (h0 w hw)
    have hFc : 0 < ‖F c‖ := norm_pos_iff.mpr hc0
    calc (h w).re = Real.log ‖Complex.exp (h w)‖ := by rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log (‖F w‖ / ‖F c‖) := by
        rw [← norm_div]; exact congrArg _ (congrArg _ (hexp hw))
      _ ≤ Real.log M := Real.log_le_log (div_pos hFw hFc) ((div_le_iff₀ hFc).mpr (hFM w hw))
  -- the logarithmic derivative of `F` is `h'`
  have hzb : z ∈ ball c r₂ := closedBall_subset_ball h₁₂ hz
  have hlogh : deriv F z / F z = deriv h z := by
    have hev : (fun w ↦ F w / F c) =ᶠ[nhds z] Complex.exp ∘ h := by
      filter_upwards [isOpen_ball.mem_nhds hzb] with w hw using (hexp hw).symm
    have hFF : logDeriv (fun w ↦ F w / F c) z = logDeriv F z := by
      simp_rw [div_eq_mul_inv]
      exact logDeriv_mul_const z _ (inv_ne_zero hc0)
    rw [← logDeriv_apply, ← hFF, (logDeriv_congr_nhds hev).eq_of_nhds,
      logDeriv_comp Complex.differentiableAt_exp (hh.differentiableAt (isOpen_ball.mem_nhds hzb)),
      Complex.logDeriv_exp, Pi.one_apply, one_mul]
  rw [hlogh]
  exact norm_deriv_le_of_re_le h₁ h₁₂ (Real.log_nonneg hM) hh hc hre hz

/-- **Hadamard's three circles theorem**, from the three lines theorem through
`w ↦ c + exp w`: if `h` is holomorphic on `closedBall c r₃`, with `‖h‖ ≤ a` on
`sphere c r₁` and `‖h‖ ≤ b` on `closedBall c r₃`, then `‖h z‖ ≤ a ^ (1 - θ) * b ^ θ` for
`r₁ ≤ ‖z - c‖ ≤ r₃`, where `θ = log (‖z - c‖ / r₁) / log (r₃ / r₁)`. -/
theorem norm_le_of_three_circles {h : ℂ → ℂ} {c z : ℂ} {r₁ r₃ a b : ℝ} (h₁ : 0 < r₁)
    (h₁₃ : r₁ < r₃) (hh : DifferentiableOn ℂ h (closedBall c r₃))
    (ha : ∀ w ∈ sphere c r₁, ‖h w‖ ≤ a) (hb : ∀ w ∈ closedBall c r₃, ‖h w‖ ≤ b)
    (hz₁ : r₁ ≤ ‖z - c‖) (hz₃ : ‖z - c‖ ≤ r₃) :
    ‖h z‖ ≤ a ^ (1 - (Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) *
      b ^ ((Real.log ‖z - c‖ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  have hlu : Real.log r₁ < Real.log r₃ := Real.log_lt_log h₁ h₁₃
  let g : ℂ → ℂ := fun w ↦ h (c + Complex.exp w)
  have hmem (w : ℂ) (hw : w.re ≤ Real.log r₃) : c + Complex.exp w ∈ closedBall c r₃ := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    calc Real.exp w.re ≤ Real.exp (Real.log r₃) := Real.exp_le_exp.mpr hw
      _ = r₃ := Real.exp_log (h₁.trans h₁₃)
  have hz0 : z - c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz₁
    linarith
  -- `g` is holomorphic on the half-plane `re w ≤ log r₃`
  have hg : DifferentiableOn ℂ g {w | w.re ≤ Real.log r₃} :=
    hh.comp (by fun_prop) fun w hw ↦ hmem w hw
  have hcl : closure (Complex.HadamardThreeLines.verticalStrip (Real.log r₁) (Real.log r₃)) ⊆
      {w | w.re ≤ Real.log r₃} :=
    closure_minimal (fun w hw ↦ hw.2.le) (isClosed_le continuous_re continuous_const)
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' (f := g)
    (z := Complex.log (z - c)) (a := a) (b := b) hlu ?_ ((hg.mono hcl).diffContOnCl) ?_ ?_ ?_
  · rw [Complex.log_re] at key
    calc ‖h z‖ = ‖g (Complex.log (z - c))‖ := by
          simp only [g]
          rw [Complex.exp_log hz0, add_sub_cancel]
      _ ≤ _ := key
  · rw [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Complex.log_re]
    exact ⟨Real.log_le_log h₁ hz₁, Real.log_le_log (h₁.trans_le hz₁) hz₃⟩
  · refine ⟨b, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb _ (hmem w hw.2)
  · intro w hw
    refine ha _ ?_
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
    rw [hw, Real.exp_log h₁]
  · intro w hw
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
    exact hb _ (hmem w hw.le)

/-! ### The three bounds -/

/-- `1 ≤ log (k (|t| + 3))`. -/
private lemma one_le_log_mul (k : ℕ) [NeZero k] (t : ℝ) : 1 ≤ Real.log (k * (|t| + 3)) := by
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  nlinarith [abs_nonneg t]

/-- The distance from `s` to the center `2 + i im s` is `|re s - 2|`. -/
private lemma norm_sub_center (s : ℂ) : ‖s - (2 + s.im * I)‖ = |s.re - 2| := by
  have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [this, norm_real, Real.norm_eq_abs]

/-- Coordinates of a point of `ball c r`. -/
private lemma mem_ball_aux {c w : ℂ} {r : ℝ} (hw : w ∈ ball c r) :
    c.re - r < w.re ∧ w.re < c.re + r ∧ |w.im - c.im| < r := by
  rw [mem_ball, dist_eq_norm] at hw
  have h₁ := abs_re_le_norm (w - c)
  have h₂ := abs_im_le_norm (w - c)
  simp only [sub_re, sub_im] at h₁ h₂
  refine ⟨?_, ?_, by linarith⟩
  · linarith [neg_abs_le (w.re - c.re)]
  · linarith [le_abs_self (w.re - c.re)]

/-- Polynomial growth of Dirichlet L-functions on `re s ≥ 1/2`, away from
`s = 1`. -/
theorem norm_LFunction_le_poly : ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (s : ℂ), 1 / 2 ≤ s.re → 1 ≤ ‖s - 1‖ →
    ‖DirichletCharacter.LFunction χ s‖ ≤ C * k * (|s.im| + 3) :=
  ⟨2, fun _ _ χ _ hs hs₁ ↦ norm_LFunction_le_two_mul χ hs hs₁⟩

/-- The logarithmic derivative of a Dirichlet L-function is `O(log (k (|t| + 3)))`
on `15/16 ≤ re s ≤ 2`, away from `s = 1`. -/
theorem norm_logDeriv_LFunction_le : ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (s : ℂ), 15 / 16 ≤ s.re → s.re ≤ 2 → 1 ≤ ‖s - 1‖ →
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
      C * Real.log (k * (|s.im| + 3)) := by
  refine ⟨11201, fun k _ χ s hσ hσ₂ hs₁ ↦ ?_⟩
  set t := s.im
  set c : ℂ := 2 + t * I with hc
  set M : ℝ := 16 * k * (|t| + 3) ^ 2 with hM
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have ht := abs_nonneg t
  have hℓ := one_le_log_mul k t
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = t := by simp [c]
  -- the disc `ball c (9/8)` lies in `7/8 < re w`, with `‖w‖ ≤ |t| + 17/4` there
  have hball (w : ℂ) (hw : w ∈ ball c (9 / 8)) : 7 / 8 < w.re ∧ ‖w‖ ≤ |t| + 17 / 4 := by
    obtain ⟨h₁, h₂, h₃⟩ := mem_ball_aux hw
    rw [hcre] at h₁ h₂
    rw [hcim] at h₃
    refine ⟨by linarith, ?_⟩
    have h₄ := Complex.norm_le_abs_re_add_abs_im w
    have h₅ : |w.re| ≤ 2 + 9 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h₆ : |w.im| ≤ |t| + 9 / 8 := by
      have := abs_sub_abs_le_abs_sub w.im t
      linarith
    linarith
  have hLc : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have h := le_norm_LFunction χ (s := c) (by rw [hcre]; norm_num)
    rw [hcre] at h
    norm_num at h
    linarith
  have hs : s ∈ closedBall c (17 / 16) := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_center, abs_of_nonpos (by linarith)]
    linarith
  -- a function `F` holomorphic and zero-free on the disc, with `L'/L = F'/F + O(1)` at `s`
  obtain ⟨F, hF, hF0, hFM, hLF⟩ : ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball c (9 / 8)) ∧
      (∀ w ∈ ball c (9 / 8), F w ≠ 0) ∧ (∀ w ∈ ball c (9 / 8), ‖F w‖ ≤ M * ‖F c‖) ∧
      ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ ‖deriv F s / F s‖ + 1 := by
    rcases eq_or_ne χ 1 with rfl | hχ
    · -- the trivial character: remove the pole with `(s - 1) L(s, χ)`
      refine ⟨LFunctionTrivChar₁ k, (differentiable_LFunctionTrivChar₁ k).differentiableOn,
        ?_, ?_, ?_⟩
      · intro w hw
        rcases eq_or_ne w 1 with rfl | hw₁
        · exact LFunctionTrivChar₁_apply_one_ne_zero k
        · rw [LFunctionTrivChar₁, Function.update_of_ne hw₁]
          exact mul_ne_zero (sub_ne_zero.mpr hw₁)
            (LFunction_ne_zero_of_seven_eighths_lt_re 1 (hball w hw).1 (fun h ↦ hw₁ h.2))
      · have hc₁ : c ≠ 1 := by
          intro h
          have := congrArg re h
          rw [hcre] at this
          norm_num at this
        have hFc : 1 / 2 ≤ ‖LFunctionTrivChar₁ k c‖ := by
          rw [LFunctionTrivChar₁, Function.update_of_ne hc₁, norm_mul]
          have h₁ : 1 ≤ ‖c - 1‖ := by
            have := abs_re_le_norm (c - 1)
            rw [sub_re, hcre] at this
            norm_num at this
            exact this
          calc (1 / 2 : ℝ) = 1 * (1 / 2) := by norm_num
            _ ≤ ‖c - 1‖ * ‖LFunction 1 c‖ := mul_le_mul h₁ hLc (by norm_num) (by positivity)
        intro w hw
        obtain ⟨hw₁, hw₂⟩ := hball w hw
        have hbound : ‖LFunctionTrivChar₁ k w‖ ≤ 8 * k * (|t| + 3) ^ 2 := by
          rcases eq_or_ne w 1 with rfl | hw1
          · simp only [LFunctionTrivChar₁, Function.update_self]
            calc ‖∏ p ∈ k.primeFactors, (1 - (p : ℂ)⁻¹)‖
              _ ≤ ∏ p ∈ k.primeFactors, (1 : ℝ) := by
                rw [norm_prod]
                refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ ?_)
                have hp := (Nat.prime_of_mem_primeFactors hp).one_lt
                have hp' : (1 : ℝ) < p := by exact_mod_cast hp
                rw [show (1 - (p : ℂ)⁻¹) = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; ring,
                  norm_real, Real.norm_eq_abs, abs_le]
                have : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by linarith)
                have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp'
                constructor <;> linarith
              _ ≤ 8 * k * (|t| + 3) ^ 2 := by
                rw [Finset.prod_const_one]
                nlinarith
          · rw [LFunctionTrivChar₁, Function.update_of_ne hw1, norm_mul]
            have hL := norm_LFunction_one_le (k := k) (by linarith : 0 < w.re) hw1
            have hw1' : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
            have hw1'' : ‖w - 1‖ ≤ ‖w‖ + 1 := by simpa using norm_sub_le w 1
            have hwre : 0 < w.re := by linarith
            calc ‖w - 1‖ * ‖LFunction 1 w‖
              _ ≤ ‖w - 1‖ * (k * (‖w‖ / ‖w - 1‖ + ‖w‖ / w.re)) := by gcongr
              _ = k * (‖w‖ + ‖w - 1‖ * ‖w‖ / w.re) := by field_simp
              _ ≤ k * ((|t| + 17 / 4) + (|t| + 21 / 4) * (|t| + 17 / 4) / (7 / 8)) := by
                gcongr
                linarith
              _ ≤ k * (8 * (|t| + 3) ^ 2) := by
                gcongr
                rw [add_div' _ _ _ (by norm_num), div_le_iff₀ (by norm_num)]
                nlinarith
              _ = 8 * k * (|t| + 3) ^ 2 := by ring
        calc ‖LFunctionTrivChar₁ k w‖
          _ ≤ 8 * k * (|t| + 3) ^ 2 := hbound
          _ = M * (1 / 2) := by rw [hM]; ring
          _ ≤ M * ‖LFunctionTrivChar₁ k c‖ := by gcongr
      · -- `F'/F = L'/L + 1/(s - 1)`
        have hs1 : s ≠ 1 := by
          rintro rfl
          norm_num at hs₁
        have hLs : LFunction (1 : DirichletCharacter ℂ k) s ≠ 0 :=
          LFunction_ne_zero_of_seven_eighths_lt_re 1 (by linarith) (fun h ↦ hs1 h.2)
        have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
        rw [deriv_LFunctionTrivChar₁_apply_of_ne_one k hs1, LFunctionTrivChar₁,
          Function.update_of_ne hs1]
        have h : ((s - 1) * deriv (LFunctionTrivChar k) s + LFunctionTrivChar k s) /
            ((s - 1) * LFunctionTrivChar k s) =
            deriv (LFunctionTrivChar k) s / LFunctionTrivChar k s + 1 / (s - 1) := by
          field_simp
        rw [h]
        set q := deriv (LFunctionTrivChar k) s / LFunctionTrivChar k s
        calc ‖q‖
          _ = ‖(q + 1 / (s - 1)) - 1 / (s - 1)‖ := by ring_nf
          _ ≤ ‖q + 1 / (s - 1)‖ + ‖1 / (s - 1)‖ := norm_sub_le _ _
          _ ≤ ‖q + 1 / (s - 1)‖ + 1 := by
            gcongr
            rw [norm_div, norm_one]
            exact div_le_one_of_le₀ hs₁ (norm_nonneg _)
    · -- a nontrivial character: `L` itself
      refine ⟨LFunction χ, (differentiable_LFunction hχ).differentiableOn,
        fun w hw ↦ LFunction_ne_zero_of_seven_eighths_lt_re χ (hball w hw).1 (fun h ↦ hχ h.1),
        fun w hw ↦ ?_, le_add_of_nonneg_right zero_le_one⟩
      obtain ⟨hw₁, hw₂⟩ := hball w hw
      calc ‖LFunction χ w‖
        _ ≤ k * ‖w‖ / w.re := norm_LFunction_le_of_ne_one hχ (by linarith)
        _ ≤ k * (|t| + 17 / 4) / (7 / 8) := by gcongr
        _ ≤ k * (8 * (|t| + 3) ^ 2) := by
          rw [mul_div_assoc]
          gcongr
          rw [div_le_iff₀ (by norm_num)]
          nlinarith
        _ = M * (1 / 2) := by rw [hM]; ring
        _ ≤ M * ‖LFunction χ c‖ := by gcongr
  -- Borel–Carathéodory on `ball c (9/8)`
  have hM₁ : 1 ≤ M := by rw [hM]; nlinarith
  have hBC := norm_logDeriv_le_of_norm_le (by norm_num) (by norm_num) hM₁ hF hF0 hFM hs
  have hlogM : Real.log M ≤ 5 * Real.log (k * (|t| + 3)) := by
    have hx : 3 ≤ (k : ℝ) * (|t| + 3) := by nlinarith
    have hx' : |t| + 3 ≤ (k : ℝ) * (|t| + 3) := by nlinarith
    rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, ← Real.log_pow]
    refine Real.log_le_log (by positivity) ?_
    calc M = 16 * (k * (|t| + 3)) * (|t| + 3) := by rw [hM]; ring
      _ ≤ 16 * (k * (|t| + 3)) * (k * (|t| + 3)) := by gcongr
      _ ≤ (k * (|t| + 3)) ^ 3 * (k * (|t| + 3)) * (k * (|t| + 3)) := by
        gcongr
        calc (16 : ℝ) ≤ 3 ^ 3 := by norm_num
          _ ≤ _ := pow_le_pow_left₀ (by norm_num) hx 3
      _ = (k * (|t| + 3)) ^ 5 := by ring
  calc ‖deriv (LFunction χ) s / LFunction χ s‖
    _ ≤ ‖deriv F s / F s‖ + 1 := hLF
    _ ≤ 4 * (17 / 16 + 9 / 8) / (9 / 8 - 17 / 16) ^ 2 * Real.log M + 1 := by gcongr
    _ ≤ 2240 * (5 * Real.log (k * (|t| + 3))) + 1 := by norm_num; linarith
    _ ≤ 11201 * Real.log (k * (|t| + 3)) := by linarith

/-- On `63/64 ≤ re s ≤ 2` and `|im s| ≥ 3`, a Dirichlet L-function is at most
`exp(C √(log (k (|t| + 3))))`. -/
theorem norm_LFunction_le_exp_sqrt : ∃ C : ℝ, ∀ (k : ℕ) [NeZero k]
    (χ : DirichletCharacter ℂ k) (s : ℂ), 63 / 64 ≤ s.re → s.re ≤ 2 → 3 ≤ |s.im| →
    ‖DirichletCharacter.LFunction χ s‖ ≤
      Real.exp (C * Real.sqrt (Real.log (k * (|s.im| + 3)))) := by
  refine ⟨193537, fun k _ χ s hσ hσ₂ ht₃ ↦ ?_⟩
  set t := s.im
  set c : ℂ := 2 + t * I with hc
  set ℓ := Real.log (k * (|t| + 3)) with hℓdef
  set A : ℝ := 193536 with hA
  have hk : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (NeZero.pos k)
  have hℓ : 1 ≤ ℓ := one_le_log_mul k t
  have hcre : c.re = 2 := by simp [c]
  have hcim : c.im = t := by simp [c]
  -- the disc `ball c (9/8)` lies in `7/8 < re w`, at distance at least one from `1`
  have hball (w : ℂ) (hw : w ∈ ball c (9 / 8)) :
      7 / 8 < w.re ∧ 1 ≤ ‖w - 1‖ ∧ |w.im| ≤ |t| + 9 / 8 := by
    obtain ⟨h₁, -, h₃⟩ := mem_ball_aux hw
    rw [hcre] at h₁
    rw [hcim] at h₃
    have h₄ := abs_sub_abs_le_abs_sub w.im t
    have h₅ := abs_sub_abs_le_abs_sub t w.im
    rw [abs_sub_comm] at h₅
    refine ⟨by linarith, ?_, by linarith⟩
    have := abs_im_le_norm (w - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  have hne (w : ℂ) (hw : w ∈ ball c (9 / 8)) : w ≠ 1 := by
    rintro rfl
    have := (hball 1 hw).2.1
    norm_num at this
  have hLd : DifferentiableOn ℂ (LFunction χ) (ball c (9 / 8)) := fun w hw ↦
    (differentiableAt_LFunction χ w (Or.inl (hne w hw))).differentiableWithinAt
  have hL0 (w : ℂ) (hw : w ∈ ball c (9 / 8)) : LFunction χ w ≠ 0 :=
    LFunction_ne_zero_of_seven_eighths_lt_re χ (hball w hw).1 (fun h ↦ hne w hw h.2)
  have hLc : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have h := le_norm_LFunction χ (s := c) (by rw [hcre]; norm_num)
    rw [hcre] at h
    norm_num at h
    linarith
  have hLc₂ : ‖LFunction χ c‖ ≤ 2 := by
    have h := norm_LFunction_le_of_one_lt_re χ (s := c) (by rw [hcre]; norm_num)
    rw [hcre] at h
    norm_num at h
    exact h
  have hc0 : LFunction χ c ≠ 0 := hL0 c (mem_ball_self (by norm_num))
  -- a holomorphic logarithm `h` of `L / L c` on `ball c (9/8)`
  obtain ⟨h, hh, hexp, hc⟩ := exists_holomorphic_log (by norm_num : (0 : ℝ) < 9 / 8)
    (G := fun w ↦ LFunction χ w / LFunction χ c) (hLd.div_const _)
    (fun w hw ↦ div_ne_zero (hL0 w hw) hc0) (div_self hc0)
  have hre (w : ℂ) (hw : w ∈ ball c (9 / 8)) :
      (h w).re = Real.log (‖LFunction χ w‖ / ‖LFunction χ c‖) := by
    calc (h w).re = Real.log ‖Complex.exp (h w)‖ := by rw [Complex.norm_exp, Real.log_exp]
      _ = Real.log (‖LFunction χ w‖ / ‖LFunction χ c‖) := by
        rw [← norm_div]; exact congrArg _ (congrArg _ (hexp hw))
  -- `re h ≤ 768` on `ball c (127/128)`, inside `1 < re w`
  have hre₁ : ∀ w ∈ ball c (127 / 128), (h w).re ≤ 768 := by
    intro w hw
    have hw' : w ∈ ball c (9 / 8) := ball_subset_ball (by norm_num) hw
    obtain ⟨h₁, h₂, -⟩ := mem_ball_aux hw
    rw [hcre] at h₁ h₂
    have hLw := norm_LFunction_le_of_one_lt_re χ (s := w) (by linarith)
    have h₃ : w.re / (w.re - 1) ≤ 384 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hpos : 0 < ‖LFunction χ w‖ / ‖LFunction χ c‖ :=
      div_pos (norm_pos_iff.mpr (hL0 w hw')) (norm_pos_iff.mpr hc0)
    rw [hre w hw']
    calc Real.log (‖LFunction χ w‖ / ‖LFunction χ c‖)
      _ ≤ ‖LFunction χ w‖ / ‖LFunction χ c‖ := Real.log_le_self hpos.le
      _ ≤ 384 / (1 / 2) := by gcongr; linarith
      _ = 768 := by norm_num
  -- `re h ≤ 3 ℓ` on `ball c (9/8)`, by polynomial growth
  have hre₂ : ∀ w ∈ ball c (9 / 8), (h w).re ≤ 3 * ℓ := by
    intro w hw
    obtain ⟨h₁, h₂, h₃⟩ := hball w hw
    have hLw := norm_LFunction_le_two_mul χ (s := w) (by linarith) h₂
    have hpos : 0 < ‖LFunction χ w‖ / ‖LFunction χ c‖ :=
      div_pos (norm_pos_iff.mpr (hL0 w hw)) (norm_pos_iff.mpr hc0)
    have hx : 6 ≤ (k : ℝ) * (|t| + 3) := by nlinarith
    rw [hre w hw, hℓdef, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ← Real.log_pow]
    refine Real.log_le_log hpos ?_
    calc ‖LFunction χ w‖ / ‖LFunction χ c‖
      _ ≤ 2 * k * (|t| + 9 / 8 + 3) / (1 / 2) := by
        refine div_le_div₀ (by positivity) (hLw.trans ?_) (by norm_num) hLc
        gcongr
      _ ≤ 8 * (k * (|t| + 3)) := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith
      _ ≤ (k * (|t| + 3)) ^ 2 * (k * (|t| + 3)) := by gcongr; nlinarith
      _ = (k * (|t| + 3)) ^ 3 := by ring
  -- Borel–Carathéodory: `‖h‖ ≤ A` on `closedBall c (63/64)`, `‖h‖ ≤ A ℓ` on `closedBall c (17/16)`
  have hA₁ : ∀ w ∈ closedBall c (63 / 64), ‖h w‖ ≤ A := by
    intro w hw
    have := norm_le_of_re_le (r := 63 / 64) (R := 127 / 128) (B := 768) (by norm_num)
      (by norm_num) (hh.mono (ball_subset_ball (by norm_num))) hc hre₁ hw
    rw [hA]
    norm_num at this
    linarith
  have hA₃ : ∀ w ∈ closedBall c (17 / 16), ‖h w‖ ≤ A * ℓ := by
    intro w hw
    have := norm_le_of_re_le (r := 17 / 16) (R := 9 / 8) (B := 3 * ℓ) (by norm_num)
      (by linarith) hh hc hre₂ hw
    rw [hA]
    norm_num at this
    linarith
  -- Hadamard's three circles: `‖h s‖ ≤ A √ℓ`
  have hsqrt : 1 ≤ Real.sqrt ℓ := Real.one_le_sqrt.mpr hℓ
  have hhs : ‖h s‖ ≤ A * Real.sqrt ℓ := by
    have hsc : ‖s - c‖ = 2 - s.re := by
      rw [norm_sub_center, abs_of_nonpos (by linarith)]
      ring
    by_cases hρ : ‖s - c‖ ≤ 63 / 64
    · have := hA₁ s (by rw [mem_closedBall, dist_eq_norm]; exact hρ)
      nlinarith
    · push Not at hρ
      have key := norm_le_of_three_circles (by norm_num) (by norm_num)
        (hh.mono (closedBall_subset_ball (by norm_num)))
        (fun w hw ↦ hA₁ w (sphere_subset_closedBall hw)) hA₃ hρ.le (by linarith)
      set θ := (Real.log ‖s - c‖ - Real.log (63 / 64)) /
        (Real.log (17 / 16) - Real.log (63 / 64)) with hθ
      have hθ₂ : θ ≤ 1 / 2 := by
        have hlog : Real.log (63 / 64) < Real.log (17 / 16) := Real.log_lt_log (by norm_num)
          (by norm_num)
        have hρ₂ : Real.log ‖s - c‖ ≤ Real.log (65 / 64) :=
          Real.log_le_log (by linarith) (by linarith)
        have h₂ : 2 * Real.log (65 / 64) ≤ Real.log (17 / 16) + Real.log (63 / 64) := by
          rw [← Real.log_mul (by norm_num) (by norm_num),
            show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.log_pow]
          exact Real.log_le_log (by norm_num) (by norm_num)
        rw [hθ, div_le_iff₀ (by linarith)]
        linarith
      calc ‖h s‖
        _ ≤ A ^ (1 - θ) * (A * ℓ) ^ θ := key
        _ = A * ℓ ^ θ := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← mul_assoc,
            ← Real.rpow_add (by positivity)]
          simp
        _ ≤ A * ℓ ^ (1 / 2 : ℝ) := by
          gcongr
        _ = A * Real.sqrt ℓ := by rw [Real.sqrt_eq_rpow]
  -- conclude from `L s = L c exp (h s)`
  have hsb : s ∈ ball c (9 / 8) := by
    rw [mem_ball, dist_eq_norm, norm_sub_center, abs_of_nonpos (by linarith)]
    linarith
  have hLs : LFunction χ s = LFunction χ c * Complex.exp (h s) := by
    have := hexp hsb
    simp only [Function.comp_apply] at this
    rw [this]
    field_simp
  calc ‖LFunction χ s‖
    _ = ‖LFunction χ c‖ * Real.exp (h s).re := by rw [hLs, norm_mul, Complex.norm_exp]
    _ ≤ 2 * Real.exp (A * Real.sqrt ℓ) := by
      gcongr
      exact (re_le_norm _).trans hhs
    _ ≤ Real.exp 1 * Real.exp (A * Real.sqrt ℓ) := by
      gcongr
      linarith [Real.add_one_le_exp 1]
    _ = Real.exp (1 + A * Real.sqrt ℓ) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (193537 * Real.sqrt ℓ) := by
      gcongr
      rw [hA]
      linarith

end Erdos408
