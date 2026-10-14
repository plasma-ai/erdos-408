import Erdos408.OneSided.Analysis.Divisor
import Erdos408.TwoSided.Endpoint.Factor.Identity

/-!
# Small-prime removal: the pointwise bounds and the mean value

Helpers for `exists_integral_removal_le` in `Erdos408/TwoSided/Endpoint/Factor.lean` (E3–E4
of `blueprint/two_sided_correlation.md` §6.3): the facts of §2 that the remainder needs, with
crude but uniform constants. U7 and U9 are in `Setup.lean`.

* `abs_slotMean_le` (U6): `|C_B| ≤ (1 + L)^{d+1}`.
* `card_primeFactors_le_four_mul_log`: `ω(n) ≤ 4L` for `n ≤ x²`.
* `integral_norm_twistedPoly_sq_le`: the mean value theorem for `twistedPoly`.
-/

namespace Erdos408.TwoSided

namespace FactorAux

open Filter Finset MeasureTheory

/-! ### U6. The slot mean -/

/-- **U6 (crude form).** `|C_B| ≤ (1 + L)^{k+1}` when `∑ v ≤ 1` and `|B| ≤ 1`. -/
theorem abs_slotMean_le {x : ℝ} (hx : 1 < x) {k : ℕ} {u v : Fin (k + 1) → ℝ}
    (hv : ∑ i, v i ≤ 1) {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, |B Q| ≤ 1) :
    |slotMean x u v B| ≤ (1 + Real.log x) ^ (k + 1) := by
  have hprimes : ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p ≤ 1 + Real.log x := by
    have hsub : primesIoc 1 x ⊆ Icc 1 ⌊x⌋₊ := by
      intro p hp
      rw [mem_primesIoc_one] at hp
      exact mem_Icc.2 ⟨hp.1.one_lt.le, Nat.le_floor hp.2⟩
    calc ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p ≤ ∑ p ∈ Icc 1 ⌊x⌋₊, (p : ℝ)⁻¹ := by
          simp only [one_div]
          exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ 1 + Real.log ⌊x⌋₊ := OneSided.sum_Icc_inv_le _
      _ ≤ 1 + Real.log x := by
          have h1 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.2 hx.le
          linarith [Real.log_le_log h1 (Nat.floor_le (by linarith))]
  unfold slotMean
  calc |∑ Q ∈ slotTuples x u v, B (Fin.init Q) / ∏ i, (Q i : ℝ)|
      ≤ ∑ Q ∈ slotTuples x u v, |B (Fin.init Q) / ∏ i, (Q i : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q ∈ slotTuples x u v, 1 / ∏ i, (Q i : ℝ) := by
        refine sum_le_sum fun Q _ => ?_
        rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ∏ i, (Q i : ℝ))]
        exact div_le_div_of_nonneg_right (hB _) (prod_nonneg fun i _ => Nat.cast_nonneg _)
    _ ≤ (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) := Sieve.sum_inv_slotTuples_le hx hv
    _ ≤ (1 + Real.log x) ^ (k + 1) :=
        pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hprimes _

/-! ### Counting -/

/-- `ω(n) ≤ 4L` for `0 < n ≤ x²`. -/
theorem card_primeFactors_le_four_mul_log {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 0 < n)
    (hnx : (n : ℝ) ≤ x ^ 2) : (n.primeFactors.card : ℝ) ≤ 4 * Real.log x := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hε : 0 < 1 / (2 * Real.log x) := by positivity
  have h := Sieve.card_primeFactors_gt_le hx hε hn hnx
  have hfilt : n.primeFactors.filter (fun p : ℕ => x ^ (1 / (2 * Real.log x)) < (p : ℝ)) =
      n.primeFactors := by
    refine filter_true_of_mem fun p hp => ?_
    have hx' : x ^ (1 / (2 * Real.log x)) = Real.exp (1 / 2) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      congr 1
      field_simp
    rw [hx']
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have he : Real.exp (1 / 2) < 2 := by
      have h₁ : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2)]
    linarith
  rw [hfilt] at h
  calc (n.primeFactors.card : ℝ) ≤ 2 / (1 / (2 * Real.log x)) := h
    _ = 4 * Real.log x := by field_simp; ring

/-- The multiples of `m > 0` in `[1, N]` number at most `N / m`. -/
theorem card_filter_dvd_le (N : ℕ) {m : ℕ} (hm : 0 < m) :
    (((Icc 1 N).filter (m ∣ ·)).card : ℝ) ≤ N / m := by
  have h : (Icc 1 N).filter (m ∣ ·) = (range N.succ).filter (fun k => k ≠ 0 ∧ m ∣ k) := by
    ext k
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [h, Nat.card_multiples', le_div_iff₀ (by exact_mod_cast hm)]
  exact_mod_cast Nat.div_mul_le_self N m

/-! ### The mean value theorem -/

/-- The mean value theorem for `twistedPoly`:
`∫_{-T}^{T} |Y⁻¹ ∑ c(w) e(hw/k) w^{it}|² ≤ Y⁻² (2T + 8N(1 + log N)) ∑ |c(w)|²`, `N = ⌊2Y⌋`,
for `Y ≥ 1` and `T ≥ 0`. -/
theorem integral_norm_twistedPoly_sq_le {Y : ℝ} (hY : 1 ≤ Y) (c : ℕ → ℂ) (h : ℤ) (k : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in -T..T, ‖twistedPoly Y c h k t‖ ^ 2 ≤
      (Y ^ 2)⁻¹ * ((T - -T + 8 * ⌊2 * Y⌋₊ * (1 + Real.log ⌊2 * Y⌋₊)) *
        ∑ w ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, ‖c w‖ ^ 2) := by
  set N := ⌊2 * Y⌋₊
  set c' : ℕ → ℂ := fun w => if w ∈ Icc ⌈Y⌉₊ N then
    c w * Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) else 0 with hc'
  have hsub : Icc ⌈Y⌉₊ N ⊆ Icc 1 N := by
    intro w hw
    rw [mem_Icc] at hw ⊢
    exact ⟨le_trans (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne') hw.1, hw.2⟩
  have hpoly : ∀ t : ℝ, twistedPoly Y c h k t =
      (Y : ℂ)⁻¹ * ∑ w ∈ Icc 1 N, c' w * (w : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro t
    unfold twistedPoly
    congr 1
    rw [← sum_subset hsub fun w _ hw => by simp only [hc', ite_eq_right hw, zero_mul]]
    exact sum_congr rfl fun w hw => by simp only [hc', ite_eq_left hw]
  have hsq : ∀ t : ℝ, ‖twistedPoly Y c h k t‖ ^ 2 =
      (Y ^ 2)⁻¹ * ‖∑ w ∈ Icc 1 N, c' w * (w : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
    intro t
    rw [hpoly, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg
      (by linarith), inv_pow]
  simp only [hsq]
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (OneSided.integral_norm_dirichlet_sq_le N c' (-T) T).trans ?_
  have hlog : 0 ≤ 1 + Real.log N := by
    have := Real.log_natCast_nonneg N
    linarith
  refine mul_le_mul_of_nonneg_left ?_ (add_nonneg (by linarith) (mul_nonneg (by positivity) hlog))
  rw [← sum_subset hsub fun w _ hw => by simp only [hc', ite_eq_right hw, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]]
  refine sum_le_sum fun w hw => ?_
  simp only [hc', ite_eq_left hw, norm_mul, Complex.norm_exp]
  simp

/-! ### Growth facts -/

/-- Eventually `K₀ + C_N log T ≤ T`: the number of inert bands is at most `T`. -/
theorem eventually_inert_le (K₀ : ℕ) (CN : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (K₀ : ℝ) + CN * Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) := by
  have hT := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hε : (0 : ℝ) < 1 / (2 * (|CN| + 1)) := by positivity
  filter_upwards [hT.eventually_ge_atTop (2 * K₀ + 1),
    hT.eventually (Real.isLittleO_log_id_atTop.bound hε)] with x h₁ h₂
  simp only [Function.comp_apply, id] at h₁ h₂
  set T := Real.log (Real.log x)
  have hT0 : 0 < T := by have := Nat.cast_nonneg (α := ℝ) K₀; linarith
  rw [Real.norm_of_nonneg hT0.le] at h₂
  have h₃ : CN * Real.log T ≤ |CN| * ‖Real.log T‖ := by
    rw [← Real.norm_eq_abs, ← norm_mul]
    exact Real.le_norm_self _
  have h₄ : |CN| * ‖Real.log T‖ ≤ |CN| * (1 / (2 * (|CN| + 1)) * T) :=
    mul_le_mul_of_nonneg_left h₂ (abs_nonneg _)
  have h₅ : |CN| * (1 / (2 * (|CN| + 1)) * T) ≤ T / 2 := by
    rw [show |CN| * (1 / (2 * (|CN| + 1)) * T) = |CN| / (|CN| + 1) * (T / 2) by
      field_simp]
    have : |CN| / (|CN| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  linarith

/-- Eventually `2 T²⁰ / c ≤ L`: the slot primes `> x^{c/T²⁰}` dividing `n ≤ x²` number at
most `L`. -/
theorem eventually_slot_ratio_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 2 / (c / Real.log (Real.log x) ^ 20) ≤ Real.log x := by
  filter_upwards [((isLittleO_log_rpow_rpow_atTop 20 one_pos).comp_tendsto
      Real.tendsto_log_atTop).bound (half_pos hc),
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with x h₁ hL
  simp only [Function.comp_apply] at h₁
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hT : 0 < Real.log L := Real.log_pos hL
  have h20 : Real.log L ^ (20 : ℝ) = Real.log L ^ 20 := by
    rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hT.le _), Real.norm_of_nonneg
    (Real.rpow_nonneg hL0.le _), h20, Real.rpow_one] at h₁
  rw [div_div_eq_mul_div, div_le_iff₀ hc]
  linarith

/-- Eventually `2 exp(L^{0.47}) ≤ x`. -/
theorem eventually_two_exp_le :
    ∀ᶠ x : ℝ in atTop, 2 * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ x := by
  filter_upwards [((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.53)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop 2, eventually_gt_atTop 0] with x h₁ hL hx
  simp only [Function.comp_apply] at h₁
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hsplit : L ^ (0.47 : ℝ) * L ^ (0.53 : ℝ) = L := by
    rw [← Real.rpow_add hL0]; norm_num
  have h47 : 0 < L ^ (0.47 : ℝ) := Real.rpow_pos_of_pos hL0 _
  have hhalf : L ^ (0.47 : ℝ) ≤ L / 2 := by nlinarith
  have hlog2 : Real.log 2 ≤ L / 2 := by
    have := Real.log_two_lt_d9
    linarith
  calc 2 * Real.exp (L ^ (0.47 : ℝ)) = Real.exp (Real.log 2 + L ^ (0.47 : ℝ)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp L := Real.exp_le_exp.2 (by linarith)
    _ = x := Real.exp_log hx
