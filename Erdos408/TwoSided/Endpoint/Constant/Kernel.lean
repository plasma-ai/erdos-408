module

public import Erdos408.Analytic.IntegerKernel

/-!
# The model progression bound

E10.2 of `blueprint/two_sided_correlation.md` §6.6, on an arbitrary integer interval
`(lo, hi]` with `R ≤ lo + 1` and `hi ≤ 2R`: for a model `A` supported on
`d ≤ exp(2L^{0.47})` coprime to `k` with `∑ |A_d|/d ≤ L^{C₈}`,
`|R⁻¹ ∑_{n ∈ (lo, hi], n ≡ β} (∑_{d ∣ n} A_d) n^{it}| ≤ L^{C₈} (12/|t| + x^{-1/150})`.
Write the sum as `∑_d A_d d^{it} ∑_{v ≡ β d⁻¹} v^{it}` over `v ∈ (lo/d, hi/d]` and apply
`IntegerKernel.norm_sum_filter_modEq_le` at the scale `H = R/d ≥ x^{0.99} e^{-2L^{0.47}}`,
which has no upper scale bound.
-/

@[expose] public section

namespace Erdos408.TwoSided.ConstHigh

open Filter Finset IntegerKernel

/-- The growth facts in `L` for the kernel bound: the constants of
`IntegerKernel.norm_sum_filter_modEq_le` are absorbed into the margin
`(0.99/128 - 1/150) L ≥ L/1000`. -/
theorem eventually_kernelGrowth (Cm C K : ℝ) : ∀ᶠ L : ℝ in atTop,
    1 ≤ L ∧ |Cm| * Real.log L + Real.log 2 ≤ L ∧ 128 * Real.log 3 ≤ L / 2 ∧
      Real.log (|K| + 1) + |C| * (2 * Real.sqrt L) +
          (2 * L ^ (0.47 : ℝ) + |Cm| * Real.log L) / 128 ≤ L / 1000 ∧
      2 * L ^ (0.47 : ℝ) + |Cm| * Real.log L ≤ L / 4 := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_log_le_mul_rpow (b := 1) one_pos (ε := 1 / (8000 * (|Cm| + 1))) (by positivity),
    eventually_const_le_mul_rpow (Real.log 2) (b := 1) one_pos (ε := 1 / 2) (by norm_num),
    eventually_const_le_mul_rpow (256 * Real.log 3) (b := 1) one_pos (ε := 1) one_pos,
    eventually_const_le_mul_rpow (Real.log (|K| + 1)) (b := 1) one_pos (ε := 1 / 4000)
      (by norm_num),
    eventually_rpow_le_mul_rpow (a := 1 / 2) (b := 1) (by norm_num)
      (ε := 1 / (8000 * (|C| + 1))) (by positivity),
    eventually_rpow_le_mul_rpow (a := 0.47) (b := 1) (by norm_num) (ε := 1 / 64000)
      (by norm_num)] with L hL1 hlog h2 h3 hK hsqrt h47
  rw [Real.rpow_one] at hlog h2 h3 hK hsqrt h47
  have hL0 : 0 < L := by linarith
  have ha := abs_nonneg Cm
  have hc := abs_nonneg C
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hsq : Real.sqrt L = L ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow L
  -- `|Cm| log L ≤ L/8000` and `|C| √L ≤ L/8000`
  have hCm : |Cm| * Real.log L ≤ L / 8000 := by
    have h := mul_le_mul_of_nonneg_left hlog ha
    have h' : |Cm| * (1 / (8000 * (|Cm| + 1)) * L) ≤ L / 8000 := by
      rw [show |Cm| * (1 / (8000 * (|Cm| + 1)) * L) = |Cm| / (|Cm| + 1) * (L / 8000) by
        field_simp]
      exact mul_le_of_le_one_left (by positivity) ((div_le_one (by linarith)).2 (by linarith))
    linarith
  have hCs : |C| * Real.sqrt L ≤ L / 8000 := by
    rw [hsq]
    have h := mul_le_mul_of_nonneg_left hsqrt hc
    have h' : |C| * (1 / (8000 * (|C| + 1)) * L) ≤ L / 8000 := by
      rw [show |C| * (1 / (8000 * (|C| + 1)) * L) = |C| / (|C| + 1) * (L / 8000) by
        field_simp]
      exact mul_le_of_le_one_left (by positivity) ((div_le_one (by linarith)).2 (by linarith))
    linarith
  refine ⟨hL1, by linarith, by linarith, by linarith, by linarith⟩

/-- The scale condition and the saving of the kernel bound at `H ≥ x^{0.99} e^{-2L^{0.47}}`:
`3^{128} ≤ H/k` and `K exp(C √(log(k(|u| + 3)))) (H/k)^{-1/128} ≤ x^{-1/150}`. -/
theorem eventually_kernel_saving (Cm C K : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ (H : ℝ) (k : ℕ) (u : ℝ),
      x ^ (99 / 100 : ℝ) * Real.exp (-(2 * Real.log x ^ (0.47 : ℝ))) ≤ H → 1 ≤ k →
      (k : ℝ) ≤ Real.log x ^ Cm → |u| ≤ x ^ 3 →
      3 ^ 128 ≤ H / k ∧
        K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) * (H / k) ^ (-(1 / 128 : ℝ)) ≤
          x ^ (-(1 / 150 : ℝ)) := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_kernelGrowth Cm C K),
    eventually_ge_atTop 2] with x hx hx2
  obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := hx
  intro H k u hH hk hkl hux
  set l := Real.log x with hl
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < l := by linarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hloglog : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hlogk : Real.log k ≤ |Cm| * Real.log l := by
    have := Real.log_le_log (by linarith) hkl
    rw [Real.log_rpow hl0] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hloglog)
  have hlogk0 : 0 ≤ Real.log k := Real.log_nonneg hk'
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  -- `log H ≥ 0.99 L - 2 L^{0.47}`
  have hlogH : 99 / 100 * l - 2 * l ^ (0.47 : ℝ) ≤ Real.log H := by
    have := Real.log_le_log (by positivity) hH
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hx0, Real.log_exp] at this
    linarith
  set ℓ := Real.log (H / k) with hℓdef
  have hℓ : 99 / 100 * l - (2 * l ^ (0.47 : ℝ) + |Cm| * Real.log l) ≤ ℓ := by
    rw [hℓdef, Real.log_div hH0.ne' (by linarith)]
    linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_⟩
  · have h3 : (3 : ℝ) ^ 128 = Real.exp (128 * Real.log 3) := by
      rw [show (128 : ℝ) * Real.log 3 = Real.log (3 ^ 128) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [h3, ← Real.exp_log (by positivity : 0 < H / k)]
    exact Real.exp_le_exp.2 (by linarith)
  · -- `log(k(|u| + 3)) ≤ 4L`
    have hlogku : Real.log (k * (|u| + 3)) ≤ 4 * l := by
      have hx3 : |u| + 3 ≤ 2 * x ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num) hx2 3]
      calc Real.log (k * (|u| + 3)) = Real.log k + Real.log (|u| + 3) :=
            Real.log_mul (by linarith) (by positivity)
        _ ≤ |Cm| * Real.log l + Real.log (2 * x ^ 3) := by
            gcongr
        _ = |Cm| * Real.log l + Real.log 2 + 3 * l := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            push_cast
            ring
        _ ≤ 4 * l := by linarith
    have hE : C * Real.sqrt (Real.log (k * (|u| + 3))) ≤ |C| * (2 * Real.sqrt l) := by
      have : Real.sqrt (Real.log (k * (|u| + 3))) ≤ 2 * Real.sqrt l := by
        calc Real.sqrt (Real.log (k * (|u| + 3))) ≤ Real.sqrt (4 * l) :=
              Real.sqrt_le_sqrt hlogku
          _ = 2 * Real.sqrt l := by
              rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_sq (by norm_num)]
      rw [abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_left this hC
    have hR : (H / k) ^ (-(1 / 128 : ℝ)) = Real.exp (-(ℓ / 128)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring
    have hKexp : K ≤ Real.exp (Real.log (|K| + 1)) := by
      rw [Real.exp_log (by positivity)]
      linarith [le_abs_self K]
    have hx150 : x ^ (-(1 / 150 : ℝ)) = Real.exp (-(l / 150)) := by
      rw [Real.rpow_def_of_pos hx0]
      congr 1
      ring
    rw [hR, hx150]
    calc K * Real.exp (C * Real.sqrt (Real.log (k * (|u| + 3)))) * Real.exp (-(ℓ / 128))
        ≤ Real.exp (Real.log (|K| + 1)) * Real.exp (|C| * (2 * Real.sqrt l)) *
            Real.exp (-(ℓ / 128)) := by
          gcongr
      _ = Real.exp (Real.log (|K| + 1) + |C| * (2 * Real.sqrt l) - ℓ / 128) := by
          rw [← Real.exp_add, ← Real.exp_add]
          ring_nf
      _ ≤ Real.exp (-(l / 150)) := Real.exp_le_exp.2 (by nlinarith)

/-- The divisor sum of a model supported in `D`, exchanged with a sum over `n`:
`∑_{n ∈ F} (∑_{d ∣ n} A_d) f(n) = ∑_{d ∈ D} A_d ∑_{n ∈ F, d ∣ n} f(n)`. -/
theorem sum_divisors_mul_eq (A : ℕ → ℂ) (D F : Finset ℕ) (f : ℕ → ℂ)
    (hA : ∀ d, A d ≠ 0 → d ∈ D) (hF : ∀ n ∈ F, n ≠ 0) :
    ∑ n ∈ F, (∑ d ∈ n.divisors, A d) * f n = ∑ d ∈ D, A d * ∑ n ∈ F.filter (d ∣ ·), f n := by
  have h1 : ∀ n ∈ F, (∑ d ∈ n.divisors, A d) = ∑ d ∈ D, if d ∣ n then A d else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    refine (Finset.sum_subset (fun d hd => ?_) fun d hdn hdD => ?_).symm
    · exact Nat.mem_divisors.2 ⟨(Finset.mem_filter.1 hd).2, hF n hn⟩
    · by_contra hAd
      exact hdD (Finset.mem_filter.2 ⟨hA d hAd, Nat.dvd_of_mem_divisors hdn⟩)
  rw [Finset.sum_congr rfl fun n hn => by rw [h1 n hn]]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

/-- The multiples of `d` in a progression `(lo, hi]`, `n ≡ β`, are `d v` with
`v ∈ (lo/d, hi/d]`, `v ≡ e β`, for `d e ≡ 1`. -/
theorem filter_dvd_eq_image {d k e β lo hi : ℕ} (hd : 0 < d) (hde : d * e ≡ 1 [MOD k]) :
    ((Finset.Ioc lo hi).filter (· ≡ β [MOD k])).filter (d ∣ ·) =
      ((Finset.Ioc (lo / d) (hi / d)).filter (· ≡ e * β [MOD k])).image (d * ·) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨hlo, hhi⟩, hβ⟩, v, rfl⟩
    refine ⟨v, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · rw [Nat.div_lt_iff_lt_mul hd, mul_comm]
      exact hlo
    · rw [Nat.le_div_iff_mul_le hd, mul_comm]
      exact hhi
    · have h1 : d * e * v ≡ 1 * v [MOD k] := hde.mul_right v
      have h2 : e * (d * v) ≡ e * β [MOD k] := hβ.mul_left e
      rw [one_mul] at h1
      exact h1.symm.trans (by rw [show d * e * v = e * (d * v) by ring]; exact h2)
  · rintro ⟨v, ⟨⟨hlo, hhi⟩, hv⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, v, rfl⟩
    · rw [Nat.div_lt_iff_lt_mul hd, mul_comm] at hlo
      exact hlo
    · rw [Nat.le_div_iff_mul_le hd, mul_comm] at hhi
      exact hhi
    · have h1 : d * v ≡ d * (e * β) [MOD k] := hv.mul_left d
      have h2 : d * e * β ≡ 1 * β [MOD k] := hde.mul_right β
      rw [one_mul] at h2
      exact h1.trans (by rw [show d * (e * β) = d * e * β by ring]; exact h2)

/-- An inverse of `d` modulo `k` for `d` coprime to `k`. -/
theorem exists_mul_modEq_one {d k : ℕ} (h : Nat.Coprime d k) : ∃ e, d * e ≡ 1 [MOD k] := by
  rcases Nat.lt_or_ge 1 k with hk | hk
  · obtain ⟨e, -, he⟩ := Nat.exists_mul_mod_eq_one_of_coprime h hk
    exact ⟨e, by rw [Nat.ModEq, he, Nat.mod_eq_of_lt hk]⟩
  · interval_cases k
    · exact ⟨1, by
        rw [Nat.coprime_zero_right] at h
        subst h
        rfl⟩
    · exact ⟨0, Nat.modEq_one⟩

/-- **E10.2 on an interval.** For `C_m, C₈`, eventually: for a model `A` supported on
`d ≤ exp(2L^{0.47})` coprime to `k` with `∑ |A_d|/d ≤ L^{C₈}`, a scale `R ≥ x^{0.99}`, an
integer interval `(lo, hi]` with `R ≤ lo + 1` and `hi ≤ 2R`, a class `β` mod `k ≤ L^{C_m}` and
`1 ≤ |t| ≤ x³`,
`|R⁻¹ ∑_{n ∈ (lo, hi], n ≡ β} (∑_{d ∣ n} A_d) n^{it}| ≤ L^{C₈} (12/|t| + x^{-1/150})`. -/
theorem eventually_norm_modelProgression_Ioc_le (Cm C₈ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (A : ℕ → ℂ) (R : ℝ) (k β lo hi : ℕ) (t : ℝ),
      (∀ d, A d ≠ 0 →
        1 ≤ d ∧ (d : ℝ) ≤ Real.exp (2 * Real.log x ^ (0.47 : ℝ)) ∧ Nat.Coprime d k) →
      ∑ d ∈ Finset.Icc 1 ⌊Real.exp (2 * Real.log x ^ (0.47 : ℝ))⌋₊, ‖A d‖ / d ≤
        Real.log x ^ C₈ →
      x ^ (99 / 100 : ℝ) ≤ R → R ≤ lo + 1 → (hi : ℝ) ≤ 2 * R → 1 ≤ k →
      (k : ℝ) ≤ Real.log x ^ Cm → 1 ≤ |t| → |t| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc lo hi).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A d) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |t| + x ^ (-(1 / 150 : ℝ))) := by
  obtain ⟨C, K, hC, hK, hbound⟩ := norm_sum_filter_modEq_le
  filter_upwards [eventually_kernel_saving Cm C K hC, eventually_gt_atTop 0] with x hsave hx0
  intro A R k β lo hi t hA hmass hR hRlo hhi hk hkl ht1 htx
  set E := Real.exp (2 * Real.log x ^ (0.47 : ℝ)) with hEdef
  set D := Finset.Icc 1 ⌊E⌋₊ with hD
  set F := (Finset.Ioc lo hi).filter (· ≡ β [MOD k]) with hF
  set ε := x ^ (-(1 / 150 : ℝ)) with hε
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hε0 : 0 ≤ ε := by positivity
  have hAD : ∀ d, A d ≠ 0 → d ∈ D := fun d hd =>
    Finset.mem_Icc.2 ⟨(hA d hd).1, Nat.le_floor (hA d hd).2.1⟩
  have hF0 : ∀ n ∈ F, n ≠ 0 := fun n hn => by
    have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hn).1).1
    omega
  rw [sum_divisors_mul_eq A D F _ hAD hF0]
  -- each divisor class: `|∑_{n ∈ F, d ∣ n} n^{it}| ≤ (R/d)(12/|t| + ε)`
  have hterm : ∀ d ∈ D, ‖A d * ∑ n ∈ F.filter (d ∣ ·), (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
      ‖A d‖ / d * (R * (12 / |t| + ε)) := by
    intro d hdD
    by_cases hAd : A d = 0
    · rw [hAd, zero_mul, norm_zero, zero_div, zero_mul]
    obtain ⟨hd1, hdE, hcop⟩ := hA d hAd
    have hd0 : 0 < d := hd1
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
    obtain ⟨e, he⟩ := exists_mul_modEq_one hcop
    rw [hF, filter_dvd_eq_image hd0 he, Finset.sum_image fun v _ w _ h =>
      Nat.eq_of_mul_eq_mul_left hd0 h]
    simp_rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    rw [← Finset.mul_sum, norm_mul, norm_mul]
    set H := R / d with hH
    have hH0 : 0 < H := by positivity
    have hHx : x ^ (99 / 100 : ℝ) * Real.exp (-(2 * Real.log x ^ (0.47 : ℝ))) ≤ H := by
      rw [hH, le_div_iff₀ hd', Real.exp_neg, ← div_eq_mul_inv, div_mul_eq_mul_div,
        div_le_iff₀ (Real.exp_pos _)]
      calc x ^ (99 / 100 : ℝ) * d ≤ R * E := mul_le_mul hR hdE hd'.le hR0.le
        _ = R * Real.exp (2 * Real.log x ^ (0.47 : ℝ)) := rfl
    obtain ⟨hHk, hsv⟩ := hsave H k t hHx hk hkl htx
    have hHA : H ≤ ((lo / d : ℕ) : ℝ) + 1 := by
      rw [hH, div_le_iff₀ hd']
      have : lo + 1 ≤ d * (lo / d + 1) := by
        have := Nat.lt_mul_div_succ lo hd0
        omega
      have h' : ((lo : ℝ) + 1) ≤ d * ((lo / d : ℕ) + 1) := by exact_mod_cast this
      linarith
    have hBH : ((hi / d : ℕ) : ℝ) ≤ 2 * H := by
      rw [hH, mul_div_assoc']
      exact (Nat.cast_div_le).trans (div_le_div_of_nonneg_right hhi hd'.le)
    have hb := hbound H (lo / d) (hi / d) k (e * β) t hHk hHA hBH hk ht1
    rw [inv_mul_le_iff₀ hH0] at hb
    have hdI : ‖(d : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ 1 := norm_natCast_cpow_I_mul_le t d
    have h12 : 12 / (1 + |t|) ≤ 12 / |t| :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    have hnorm : ‖∑ v ∈ (Finset.Ioc (lo / d) (hi / d)).filter (· ≡ e * β [MOD k]),
        (v : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ H * (12 / |t| + ε) :=
      hb.trans (mul_le_mul_of_nonneg_left (by linarith) hH0.le)
    calc ‖A d‖ * (‖(d : ℂ) ^ ((t : ℂ) * Complex.I)‖ *
          ‖∑ v ∈ (Finset.Ioc (lo / d) (hi / d)).filter (· ≡ e * β [MOD k]),
            (v : ℂ) ^ ((t : ℂ) * Complex.I)‖)
        ≤ ‖A d‖ * (1 * (H * (12 / |t| + ε))) := by gcongr
      _ = ‖A d‖ / d * (R * (12 / |t| + ε)) := by
          rw [hH]
          field_simp
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR0.le]
  have hsum := norm_sum_le_of_le D hterm
  rw [← Finset.sum_mul] at hsum
  calc R⁻¹ * ‖∑ d ∈ D, A d * ∑ n ∈ F.filter (d ∣ ·), (n : ℂ) ^ ((t : ℂ) * Complex.I)‖
      ≤ R⁻¹ * ((∑ d ∈ D, ‖A d‖ / d) * (R * (12 / |t| + ε))) := by gcongr
    _ = (∑ d ∈ D, ‖A d‖ / d) * (12 / |t| + ε) := by field_simp
    _ ≤ Real.log x ^ C₈ * (12 / |t| + ε) := by gcongr

end Erdos408.TwoSided.ConstHigh
