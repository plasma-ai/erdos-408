module

public import Erdos408.OneSided.Analysis.Divisor
public import Erdos408.TwoSided.Setup

/-!
# Elementary facts for the constant part at high times

Elementary facts used in S19 of `blueprint/two_sided_correlation.md` §6.6.

* The mean value theorem `OneSided.integral_norm_dirichlet_sq_le` holds for any `S ⊆ [1, N]`.
* `∫ |f + g|² ≤ 2 ∫ |f|² + 2 ∫ |g|²`, from Cauchy–Schwarz under the integral (`Setup.lean`).
* The twist `e(hm/k)` depends only on `m mod k`.
* A sum over `(E 0, E I]` is the sum over the consecutive grid intervals `(E i, E (i + 1)]`.
* A smooth `ψ` with `|ψ'| ≤ M` is `M`-Lipschitz; `∫_a^b t^{-2} ≤ 2/c` when `|t| ≥ c`.
-/

@[expose] public section

namespace Erdos408.TwoSided.ConstHigh

open Finset MeasureTheory

/-- A Dirichlet polynomial supported on `S ⊆ [1, N]` as one over `[1, N]`. -/
theorem sum_cpow_eq_sum_Icc_ite (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (c : ℕ → ℂ)
    (t : ℝ) : ∑ n ∈ S, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) =
      ∑ n ∈ Icc 1 N, (if n ∈ S then c n else 0) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  classical
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hS]

/-- The coefficient norm of a Dirichlet polynomial supported on `S ⊆ [1, N]`. -/
theorem sum_norm_ite_sq (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (c : ℕ → ℂ) :
    ∑ n ∈ Icc 1 N, ‖if n ∈ S then c n else 0‖ ^ 2 = ∑ n ∈ S, ‖c n‖ ^ 2 := by
  classical
  have : ∀ n, ‖if n ∈ S then c n else 0‖ ^ 2 = if n ∈ S then ‖c n‖ ^ 2 else 0 := by
    intro n
    split_ifs <;> simp
  simp_rw [this]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hS]

/-- PD (2.4) for a Dirichlet polynomial supported on `S ⊆ [1, N]`. -/
theorem integral_norm_sum_cpow_sq_le (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N) (c : ℕ → ℂ)
    (a b : ℝ) :
    ∫ t in a..b, ‖∑ n ∈ S, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      (b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  classical
  simp_rw [sum_cpow_eq_sum_Icc_ite N S hS c]
  rw [← sum_norm_ite_sq N S hS c]
  exact OneSided.integral_norm_dirichlet_sq_le N _ a b

/-- `∫_a^b |f + g|² ≤ 2 ∫_a^b |f|² + 2 ∫_a^b |g|²`. -/
theorem integral_norm_add_sq_le {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖f t + g t‖ ^ 2 ≤
      2 * (∫ t in a..b, ‖f t‖ ^ 2) + 2 * ∫ t in a..b, ‖g t‖ ^ 2 := by
  have h := integral_norm_sum_sq_le (Finset.univ : Finset (Fin 2)) (fun _ => 1)
    (fun _ _ => norm_one.le) ![f, g] (fun i _ => by fin_cases i <;> simpa) hab
  simpa [Fin.sum_univ_two, mul_add] using h

/-- The twist `e(hm/k)` depends only on `m mod k`. -/
theorem exp_twist_eq_mod (h : ℤ) {k : ℕ} (hk : k ≠ 0) (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (h * m / k : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * (h * (m % k : ℕ) / k : ℝ)) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  obtain ⟨q, hq⟩ : ∃ q, q = m / k := ⟨_, rfl⟩
  have hm : (m : ℝ) = (m % k : ℕ) + k * q := by
    rw [hq]
    exact_mod_cast (Nat.mod_add_div m k).symm
  have hsplit : (h * m / k : ℝ) = (h * (m % k : ℕ) / k : ℝ) + ((h * q : ℤ) : ℝ) := by
    rw [hm]
    push_cast
    field_simp
  rw [hsplit, Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_intCast]
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((h * q : ℤ) : ℂ)) = 1 := by
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [h1, mul_one]

/-- The twist `e(hm/k)` at congruent `m ≡ m' (mod k)`. -/
theorem exp_twist_eq_of_modEq (h : ℤ) {k : ℕ} (hk : k ≠ 0) {m m' : ℕ} (hm : m ≡ m' [MOD k]) :
    Complex.exp (2 * Real.pi * Complex.I * (h * m / k : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * (h * m' / k : ℝ)) := by
  rw [exp_twist_eq_mod h hk m, exp_twist_eq_mod h hk m', hm]

/-- A sum over `(E 0, E I]` is the sum over the grid intervals `(E i, E (i + 1)]`. -/
theorem sum_Ioc_eq_sum_range {M : Type*} [AddCommMonoid M] (E : ℕ → ℕ) (hE : Monotone E)
    (f : ℕ → M) (I : ℕ) :
    ∑ m ∈ Ioc (E 0) (E I), f m = ∑ i ∈ range I, ∑ m ∈ Ioc (E i) (E (i + 1)), f m := by
  induction I with
  | zero => simp
  | succ I ih =>
      rw [Finset.sum_range_succ, ← ih,
        Finset.sum_Ioc_consecutive f (hE (Nat.zero_le I)) (hE (Nat.le_succ I))]

/-- A smooth `ψ` with `|ψ'| ≤ M` is `M`-Lipschitz. -/
theorem norm_sub_le_of_iteratedDeriv_one {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) {M : ℝ}
    (hM : ∀ y, ‖iteratedDeriv 1 ψ y‖ ≤ M) (y z : ℝ) : ‖ψ y - ψ z‖ ≤ M * |y - z| := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun w _ => hd w)
    (fun w _ => by rw [← iteratedDeriv_one]; exact hM w) (Set.mem_univ z) (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using h

/-- `∫_a^b t^{-2} ≤ 2/c` when `|t| ≥ c > 0` on `[a, b]`. -/
theorem integral_inv_sq_le {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (h : ∀ t ∈ Set.Icc a b, c ≤ |t|) : ∫ t in a..b, (t ^ 2)⁻¹ ≤ 2 / c := by
  have hne : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht h0
    rw [Set.uIcc_of_le hab] at ht
    have := h t ht
    rw [h0, abs_zero] at this
    linarith
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -y⁻¹) ((t ^ 2)⁻¹) t := by
    intro t ht
    have h1 := (hasDerivAt_inv (hne t ht)).neg
    rw [neg_neg] at h1
    exact h1
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht =>
      ((continuous_pow 2).continuousAt.inv₀ (pow_ne_zero 2 (hne t ht))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have ha := h a ⟨le_rfl, hab⟩
  have hb := h b ⟨hab, le_rfl⟩
  have hia : |a⁻¹| ≤ 1 / c := by
    rw [abs_inv, ← one_div]
    exact one_div_le_one_div_of_le hc ha
  have hib : |b⁻¹| ≤ 1 / c := by
    rw [abs_inv, ← one_div]
    exact one_div_le_one_div_of_le hc hb
  calc -b⁻¹ - -a⁻¹ ≤ |b⁻¹| + |a⁻¹| := by linarith [neg_abs_le b⁻¹, le_abs_self a⁻¹]
    _ ≤ 2 / c := by rw [show 2 / c = 1 / c + 1 / c by ring]; linarith

end Erdos408.TwoSided.ConstHigh
