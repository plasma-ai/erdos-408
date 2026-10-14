import Erdos408.CrossTerm
import Erdos408.Cumulative
import Erdos408.IntegerMoments
import Erdos408.PrimeMoments
import Erdos408.Renewal
import Mathlib.Order.Interval.Set.Nat

/-!
# Assembly of Erdős Problem 408: distribution of iterated totient heights

Under `RectangleInput`, `dyadic_moments` gives the dyadic prime moments of `F`,
and `cumulative_moments` the cumulative ones. `first_renewal` produces
`1 / log 3 ≤ α ≤ 1 / log 2` with `B(x) = α L + O(L T⁻⁵)`. Then `cross_term`
and `second_renewal` give `C(x) + D(x) = α² L² + O(L² T⁻⁵)`. With the integer
moments,

  `∑_{n ≤ x} (F n - α L)² = ∑ F(n)² - 2 α L ∑ F n + α² L² ⌊x⌋ = O(x L² T⁻⁵)`.

Since `∑_{n ≤ x} log²(x / n) = O(x)` and `|f n - F n| ≤ 1`, the same bound
holds for `∑ (f n - α log n)²`. The exceptional counts and the two density
statements follow by Chebyshev's inequality on `(√x, x]`.
-/

namespace Erdos408

open Filter
open scoped Topology

/-- `log log x → ∞`. -/
theorem tendsto_log_log_atTop : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

/-- Under `RectangleInput` there is `1 / log 3 ≤ α ≤ 1 / log 2` with
`B(x) = α L + O(L T⁻⁵)` and `C(x) + D(x) = α² L² + O(L² T⁻⁵)`. -/
theorem harmonic_moments (hR : RectangleInput) :
    ∃ α K : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∀ᶠ x : ℝ in atTop,
      |harmonicF x - α * Real.log x| ≤ K * Real.log x / Real.log (Real.log x) ^ 5 ∧
        |harmonicFSq x + harmonicFPair x - α ^ 2 * Real.log x ^ 2| ≤
          K * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 := by
  obtain ⟨K₀, h₀⟩ := dyadic_moments hR
  obtain ⟨K₁, h₁⟩ := cumulative_moments h₀
  obtain ⟨α, K₂, hα₃, hα₂, hB⟩ := first_renewal (h₁.mono fun t ht => ht.1)
  obtain ⟨K₃, hD⟩ := cross_term hB
  have hT := tendsto_log_log_atTop.eventually_ge_atTop 0
  -- one constant for the second cumulative moment and the cross term
  have h₁' : ∀ᶠ t : ℝ in atTop,
      |primeFSq t - (primesIoc 1 t).card * (harmonicFSq t + harmonicFPair t)| ≤
        max K₁ K₃ * t * Real.log t / Real.log (Real.log t) ^ 6 := by
    filter_upwards [h₁, eventually_ge_atTop 1] with t ht ht₁
    have : 0 ≤ t * Real.log t := mul_nonneg (by linarith) (Real.log_nonneg ht₁)
    refine ht.2.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  have hD' : ∀ᶠ x : ℝ in atTop,
      |harmonicFPair x - α ^ 2 / 2 * Real.log x ^ 2| ≤
        max K₁ K₃ * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 := by
    filter_upwards [hD, hT] with x hx hTx
    exact hx.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) (pow_nonneg hTx 5))
  obtain ⟨K₄, hC⟩ := second_renewal h₁' hD'
  refine ⟨α, max K₂ (K₄ + max K₁ K₃), hα₃, hα₂, ?_⟩
  filter_upwards [hB, hC, hD', hT, eventually_ge_atTop 1] with x hBx hCx hDx hTx hx₁
  have hL := Real.log_nonneg hx₁
  refine ⟨hBx.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hL) (pow_nonneg hTx 5)), ?_⟩
  -- `C + D - α² L² = (C - α² L² / 2) + (D - α² L² / 2)`
  calc |harmonicFSq x + harmonicFPair x - α ^ 2 * Real.log x ^ 2|
      = |(harmonicFSq x - α ^ 2 / 2 * Real.log x ^ 2) +
          (harmonicFPair x - α ^ 2 / 2 * Real.log x ^ 2)| := by ring_nf
    _ ≤ K₄ * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 +
          max K₁ K₃ * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 :=
        (abs_add_le _ _).trans (add_le_add hCx hDx)
    _ = (K₄ + max K₁ K₃) * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 := by ring
    _ ≤ max K₂ (K₄ + max K₁ K₃) * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) (pow_nonneg hTx 5)

/-- The variance of `F` about `α L`: `∑_{n ≤ x} (F n - α L)² = O(x L² T⁻⁵ + x L)`. -/
theorem variance_F (hR : RectangleInput) :
    ∃ α K : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∀ᶠ x : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((F n : ℝ) - α * Real.log x) ^ 2 ≤
        K * (x * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 + x * Real.log x) := by
  obtain ⟨α, K, hα₃, hα₂, hBC⟩ := harmonic_moments hR
  obtain ⟨K₁, hK₁⟩ := integer_first_moment
  obtain ⟨K₂, hK₂⟩ := integer_second_moment
  refine ⟨α, 5 * |K| + |K₂| + 4 * |K₁|, hα₃, hα₂, ?_⟩
  filter_upwards [hBC, tendsto_log_log_atTop.eventually_ge_atTop 0, eventually_ge_atTop 2]
    with x ⟨hB, hCD⟩ hT hx
  set L := Real.log x
  set T := Real.log L
  set N := ⌊x⌋₊
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hT5 : 0 ≤ T ^ 5 := pow_nonneg hT 5
  -- `0 ≤ α ≤ 2`, since `log 3 > 0` and `log 2 > 1 / 2`
  have hα₀ : 0 ≤ α := le_trans (by positivity) hα₃
  have hα : α ≤ 2 := by
    refine hα₂.trans ?_
    rw [div_le_iff₀ (Real.log_pos one_lt_two)]
    linarith [Real.log_two_gt_d9]
  have hN₁ : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hid : ∑ n ∈ Finset.Icc 1 N, ((F n : ℝ) - α * L) ^ 2 =
      ∑ n ∈ Finset.Icc 1 N, (F n : ℝ) ^ 2 - 2 * (α * L) * ∑ n ∈ Finset.Icc 1 N, (F n : ℝ) +
        (α * L) ^ 2 * N := by
    rw [Finset.sum_congr rfl fun n _ => show ((F n : ℝ) - α * L) ^ 2 =
        (F n : ℝ) ^ 2 - 2 * (α * L) * F n + (α * L) ^ 2 by ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    ring
  rw [hid]
  set S₁ := ∑ n ∈ Finset.Icc 1 N, (F n : ℝ)
  set S₂ := ∑ n ∈ Finset.Icc 1 N, (F n : ℝ) ^ 2
  set δ₁ := harmonicF x - α * L
  set δ₂ := harmonicFSq x + harmonicFPair x - α ^ 2 * L ^ 2
  have he₁ : |S₁ - x * harmonicF x| ≤ K₁ * x := hK₁ x hx
  have he₂ : |S₂ - x * (harmonicFSq x + harmonicFPair x)| ≤ K₂ * x * L := hK₂ x hx
  replace he₁ := abs_le.mp he₁
  replace he₂ := abs_le.mp he₂
  have hδ₁ := abs_le.mp hB
  have hδ₂ := abs_le.mp hCD
  -- `S₂ - 2 α L S₁ + α² L² N = x δ₂ - 2 α L x δ₁ + e₂ - 2 α L e₁ - α² L² (x - N)`
  have hexp : S₂ - 2 * (α * L) * S₁ + (α * L) ^ 2 * N =
      x * δ₂ - 2 * α * L * x * δ₁ + (S₂ - x * (harmonicFSq x + harmonicFPair x)) -
        2 * α * L * (S₁ - x * harmonicF x) - (α * L) ^ 2 * (x - N) := by
    ring
  rw [hexp]
  have hx₀ : 0 ≤ x := by linarith
  have h₁ : x * δ₂ ≤ |K| * (x * L ^ 2 / T ^ 5) := by
    have : δ₂ ≤ |K| * (L ^ 2 / T ^ 5) := by
      refine hδ₂.2.trans ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self K) (div_nonneg (sq_nonneg _) hT5)
    calc x * δ₂ ≤ x * (|K| * (L ^ 2 / T ^ 5)) := mul_le_mul_of_nonneg_left this hx₀
      _ = |K| * (x * L ^ 2 / T ^ 5) := by ring
  have h₂ : -(2 * α * L * x * δ₁) ≤ 4 * |K| * (x * L ^ 2 / T ^ 5) := by
    have : -δ₁ ≤ |K| * (L / T ^ 5) := by
      have := hδ₁.1
      have : K * L / T ^ 5 ≤ |K| * (L / T ^ 5) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (le_abs_self K) (div_nonneg hL hT5)
      linarith
    have h2αLx : 0 ≤ 2 * α * L * x := by positivity
    calc -(2 * α * L * x * δ₁) = 2 * α * L * x * -δ₁ := by ring
      _ ≤ 2 * α * L * x * (|K| * (L / T ^ 5)) := mul_le_mul_of_nonneg_left this h2αLx
      _ ≤ 2 * 2 * L * x * (|K| * (L / T ^ 5)) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (div_nonneg hL hT5))
          nlinarith [mul_le_mul_of_nonneg_right hα (mul_nonneg hL hx₀)]
      _ = 4 * |K| * (x * L ^ 2 / T ^ 5) := by ring
  have h₃ : S₂ - x * (harmonicFSq x + harmonicFPair x) ≤ |K₂| * (x * L) := by
    refine he₂.2.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hx₀ hL)
  have h₄ : -(2 * α * L * (S₁ - x * harmonicF x)) ≤ 4 * |K₁| * (x * L) := by
    have : -(S₁ - x * harmonicF x) ≤ |K₁| * x := by
      linarith [mul_le_mul_of_nonneg_right (le_abs_self K₁) hx₀]
    calc -(2 * α * L * (S₁ - x * harmonicF x)) = 2 * α * L * -(S₁ - x * harmonicF x) := by ring
      _ ≤ 2 * α * L * (|K₁| * x) := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ 2 * 2 * L * (|K₁| * x) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) hx₀)
          nlinarith
      _ = 4 * |K₁| * (x * L) := by ring
  have h₅ : 0 ≤ (α * L) ^ 2 * (x - N) := mul_nonneg (sq_nonneg _) (by linarith)
  have ha : 0 ≤ x * L ^ 2 / T ^ 5 := div_nonneg (mul_nonneg hx₀ (sq_nonneg _)) hT5
  have hb : 0 ≤ x * L := mul_nonneg hx₀ hL
  nlinarith [mul_nonneg (abs_nonneg K) hb, mul_nonneg (abs_nonneg K₂) ha,
    mul_nonneg (abs_nonneg K₁) ha]

/-- `u² ≤ 16 exp (u / 2)` for `u ≥ 0`, since `u / 4 < exp (u / 4)`. -/
theorem sq_le_exp_half {u : ℝ} (hu : 0 ≤ u) : u ^ 2 ≤ 16 * Real.exp (u / 2) := by
  have h := Real.add_one_le_exp (u / 4)
  have he : Real.exp (u / 2) = Real.exp (u / 4) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [he]
  nlinarith

/-- `∑_{n ≤ N} 1 / √n ≤ 2 √N`, since `1 / √(n + 1) ≤ 2 √(n + 1) - 2 √n`. -/
theorem sum_inv_sqrt_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, 1 / √(n : ℝ) ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    have ha := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N + 1)
    have hb₀ : 0 < √((N : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have : 1 / √((N : ℝ) + 1) ≤ 2 * √((N : ℝ) + 1) - 2 * √(N : ℝ) := by
      rw [div_le_iff₀ hb₀]
      nlinarith [sq_nonneg (√(N : ℝ) - √((N : ℝ) + 1))]
    linarith

/-- `∑_{n ≤ x} log² (x / n) ≤ 32 x`. -/
theorem sum_log_div_sq_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / n) ^ 2 ≤ 32 * x := by
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log (x / n) ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 16 * √x * (1 / √(n : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mem_Icc] at hn
        have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
        have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp hn.2
        have hpos : 0 < x / n := div_pos (by linarith) (by linarith)
        have h := sq_le_exp_half (Real.log_nonneg ((one_le_div (by linarith)).mpr hnx))
        rw [Real.exp_half, Real.exp_log hpos, Real.sqrt_div' _ (by linarith)] at h
        exact h.trans_eq (by ring)
    _ = 16 * √x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, 1 / √(n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 16 * √x * (2 * √x) := by
        gcongr
        exact (sum_inv_sqrt_le _).trans
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hx)) (by norm_num))
    _ = 32 * x := by
        rw [show 16 * √x * (2 * √x) = 32 * (√x * √x) by ring, Real.mul_self_sqrt hx]

/-- The variance of `f` about `α log n`: `∑_{n ≤ x} (f n - α log n)² = O(x L² T⁻⁵)`. -/
theorem variance_f (hR : RectangleInput) :
    ∃ α : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∃ K : ℝ, ∀ᶠ x : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((f n : ℝ) - α * Real.log n) ^ 2 ≤
        K * x * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 := by
  obtain ⟨α, K, hα₃, hα₂, hV⟩ := variance_F hR
  refine ⟨α, hα₃, hα₂, 8 * |K| + 514, ?_⟩
  -- `T⁵ ≤ L`, so `x L ≤ x L² T⁻⁵`
  have hTL : ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ^ 5 ≤ Real.log x := by
    filter_upwards [(Real.isLittleO_pow_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).def
      one_pos, Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx hL
    simp only [Real.norm_eq_abs, Function.comp_apply, id_eq, one_mul, abs_of_nonneg hL] at hx
    exact (le_abs_self _).trans hx
  filter_upwards [hV, hTL, tendsto_log_log_atTop.eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1] with x hVx hTLx hT hL hx
  set L := Real.log x
  set T := Real.log L
  set N := ⌊x⌋₊
  have hx₀ : 0 ≤ x := by linarith
  have hT5 : 0 < T ^ 5 := pow_pos hT 5
  have hα₀ : 0 ≤ α := le_trans (by positivity) hα₃
  have hα : α ≤ 2 := by
    refine hα₂.trans ?_
    rw [div_le_iff₀ (Real.log_pos one_lt_two)]
    linarith [Real.log_two_gt_d9]
  -- `(f n - α log n)² ≤ 4 (F n - α L)² + 16 log² (x / n) + 2`
  have hpt : ∀ n ∈ Finset.Icc 1 N, ((f n : ℝ) - α * Real.log n) ^ 2 ≤
      4 * ((F n : ℝ) - α * L) ^ 2 + 16 * Real.log (x / n) ^ 2 + 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hfF := abs_le.mp (abs_f_sub_F_le_one hn.1)
    have hlog : Real.log n = L - Real.log (x / n) := by
      rw [Real.log_div (by linarith) (by linarith)]
      ring
    rw [hlog]
    have hα2 : α ^ 2 ≤ 4 := by nlinarith
    nlinarith [sq_nonneg ((f n : ℝ) - F n - ((F n : ℝ) - α * (L - Real.log (x / n)))),
      sq_nonneg ((F n : ℝ) - α * L - α * Real.log (x / n)),
      mul_le_mul_of_nonneg_right hα2 (sq_nonneg (Real.log (x / n)))]
  have hN : (N : ℝ) ≤ x := Nat.floor_le hx₀
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hsum
  have hlog := sum_log_div_sq_le hx₀
  have hb : x * L ≤ x * L ^ 2 / T ^ 5 := by
    rw [le_div_iff₀ hT5]
    nlinarith [mul_le_mul_of_nonneg_left hTLx (mul_nonneg hx₀ (by linarith : (0 : ℝ) ≤ L))]
  have hxL : x ≤ x * L := le_mul_of_one_le_right hx₀ hL
  have hK : K * (x * L ^ 2 / T ^ 5 + x * L) ≤ |K| * (2 * (x * L ^ 2 / T ^ 5)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K))
  have : (8 * |K| + 514) * x * L ^ 2 / T ^ 5 =
      8 * |K| * (x * L ^ 2 / T ^ 5) + 514 * (x * L ^ 2 / T ^ 5) := by ring
  rw [this]
  linarith

/-- Chebyshev's inequality: if `c ≤ g` on `t ⊆ s` and `g ≥ 0` on `s`, then
`#t ≤ ∑_{n ∈ s} g n / c`. -/
theorem card_le_sum_div {s t : Finset ℕ} {g : ℕ → ℝ} {c : ℝ} (hts : t ⊆ s)
    (hg : ∀ n ∈ s, 0 ≤ g n) (hc : 0 < c) (ht : ∀ n ∈ t, c ≤ g n) :
    (t.card : ℝ) ≤ (∑ n ∈ s, g n) / c := by
  rw [le_div_iff₀ hc]
  calc (t.card : ℝ) * c = ∑ n ∈ t, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ t, g n := Finset.sum_le_sum ht
    _ ≤ ∑ n ∈ s, g n := Finset.sum_le_sum_of_subset_of_nonneg hts fun n hn _ => hg n hn

/-- Chebyshev's inequality on `(√x, x]` turns the variance bound into the exceptional
count, with at most `√x` further exceptions below `√x`. -/
theorem normal_order_rate_proved (hR : RectangleInput) :
    ∃ α : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧ ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((f n : ℝ) - α * Real.log n) ^ 2 ≤
          C * x * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 ∧
        (((Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
            Real.log n / Real.log (Real.log n) < |(f n : ℝ) - α * Real.log n|).card : ℝ) ≤
          C * (x / Real.log (Real.log x) ^ 3 + √x) := by
  obtain ⟨α, hα₃, hα₂, K, hK⟩ := variance_f hR
  refine ⟨α, hα₃, hα₂, 4 * |K| + 1, ?_⟩
  filter_upwards [hK, tendsto_log_log_atTop.eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually_gt_atTop 2, eventually_ge_atTop 1] with x hKx hT hL hx
  set L := Real.log x
  set T := Real.log L
  have hx₀ : 0 ≤ x := by linarith
  have hT5 : 0 < T ^ 5 := pow_pos hT 5
  have hsq := Real.sqrt_nonneg x
  have hKC : K ≤ 4 * |K| + 1 := (le_abs_self K).trans (by linarith [abs_nonneg K])
  refine ⟨hKx.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKC hx₀) (sq_nonneg _)) hT5.le), ?_⟩
  set s := (Finset.Icc 1 ⌊x⌋₊).filter fun n : ℕ =>
    Real.log n / Real.log (Real.log n) < |(f n : ℝ) - α * Real.log n|
  rw [← Finset.card_filter_add_card_filter_not (fun n : ℕ => √x < n) (s := s)]
  push_cast
  -- at most `√x` exceptions below `√x`
  have hlow : ((s.filter fun n : ℕ => ¬ √x < n).card : ℝ) ≤ √x := by
    have : s.filter (fun n : ℕ => ¬ √x < n) ⊆ Finset.Icc 1 ⌊√x⌋₊ := by
      intro n hn
      simp only [s, Finset.mem_filter, Finset.mem_Icc, not_lt] at hn
      exact Finset.mem_Icc.mpr ⟨hn.1.1.1, Nat.le_floor hn.2⟩
    refine (Nat.cast_le.mpr (Finset.card_le_card this)).trans ?_
    rw [Nat.card_Icc, add_tsub_cancel_right]
    exact Nat.floor_le hsq
  -- above `√x`, an exception has `(f n - α log n)² ≥ L² / (4 T²)`
  have hhigh : ((s.filter fun n : ℕ => √x < n).card : ℝ) ≤ 4 * |K| * (x / T ^ 3) := by
    have hc : 0 < L ^ 2 / (4 * T ^ 2) := by positivity
    refine (card_le_sum_div (Finset.filter_subset _ _ |>.trans (Finset.filter_subset _ _))
      (fun n _ => sq_nonneg ((f n : ℝ) - α * Real.log n)) hc ?_).trans ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨⟨-, hnx⟩, hP⟩, hsn⟩ := hn
      have hn₀ : (0 : ℝ) < n := hsq.trans_lt hsn
      have hnx' : (n : ℝ) ≤ x := (Nat.le_floor_iff hx₀).mp hnx
      -- `L / 2 < log n ≤ L`
      have hlo : L / 2 < Real.log n := by
        rw [← Real.log_sqrt hx₀]
        exact Real.log_lt_log (Real.sqrt_pos.mpr (by linarith)) hsn
      have hhi : Real.log n ≤ L := Real.log_le_log hn₀ hnx'
      have hll₀ : 0 < Real.log (Real.log n) := Real.log_pos (by linarith)
      have hll : Real.log (Real.log n) ≤ T := Real.log_le_log (by linarith) hhi
      have h₁ : L / (2 * T) ≤ Real.log n / Real.log (Real.log n) := by
        rw [← div_div]
        exact div_le_div₀ (by linarith) hlo.le hll₀ hll
      have h₂ : L / (2 * T) ≤ |(f n : ℝ) - α * Real.log n| := h₁.trans hP.le
      have h₃ := pow_le_pow_left₀ (by positivity) h₂ 2
      rw [sq_abs] at h₃
      exact h₃.trans_eq' (by field_simp; ring)
    · rw [div_le_iff₀ hc]
      calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((f n : ℝ) - α * Real.log n) ^ 2
          ≤ K * x * L ^ 2 / T ^ 5 := hKx
        _ = K * (x / T ^ 3) * 4 * (L ^ 2 / (4 * T ^ 2)) := by field_simp
        _ ≤ |K| * (x / T ^ 3) * 4 * (L ^ 2 / (4 * T ^ 2)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self K) ?_) (by norm_num)) hc.le
          exact div_nonneg hx₀ (pow_pos hT 3).le
        _ = 4 * |K| * (x / T ^ 3) * (L ^ 2 / (4 * T ^ 2)) := by ring
  have h3 : 0 ≤ x / T ^ 3 := div_nonneg hx₀ (pow_pos hT 3).le
  nlinarith [mul_nonneg (abs_nonneg K) hsq]

/-- The elements of `{n | p n}` below `b` are those of `range b` satisfying `p`. -/
theorem ncard_setOf_inter_Iio (p : ℕ → Prop) [DecidablePred p] (b : ℕ) :
    ({n | p n} ∩ Set.Iio b).ncard = ((Finset.range b).filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp [and_comm]

/-- For `√b < n < b` outside the set, `(f n - α log n)² ≥ (ε log b / 2)²`, so
Chebyshev's inequality leaves `O(√b + b T⁻⁵)` exceptions below `b`. -/
theorem parts_ii_proved (hR : RectangleInput) :
    ∃ α : ℝ, ∀ ε > (0 : ℝ),
      HasDensity {n : ℕ | |(f n : ℝ) / Real.log n - α| < ε} 1 := by
  classical
  obtain ⟨α, -, -, K, hK⟩ := variance_f hR
  refine ⟨α, fun ε hε => ?_⟩
  set P : ℕ → Prop := fun n => |(f n : ℝ) / Real.log n - α| < ε
  set c := 4 * |K| / ε ^ 2
  -- the proportion of exceptions below `b` is at most `g b`, and `g b → 0`
  set g : ℝ → ℝ := fun y => (√y)⁻¹ + y⁻¹ + c * (Real.log (Real.log y) ^ 5)⁻¹
  have hg : Tendsto g atTop (𝓝 0) := by
    have := ((tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).add
      tendsto_inv_atTop_zero).add ((tendsto_inv_atTop_zero.comp
        ((tendsto_pow_atTop (by norm_num : 5 ≠ 0)).comp tendsto_log_log_atTop)).const_mul c)
    simpa using this
  have hbad : ∀ᶠ b : ℕ in atTop,
      (((Finset.range b).filter fun n => ¬ P n).card : ℝ) ≤ b * g b := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hK,
      tendsto_natCast_atTop_atTop.eventually (tendsto_log_log_atTop.eventually_gt_atTop 0),
      tendsto_natCast_atTop_atTop.eventually (Real.tendsto_log_atTop.eventually_gt_atTop 0),
      eventually_ge_atTop 1] with b hKb hT hL hb
    rw [Nat.floor_natCast] at hKb
    set L := Real.log b
    set T := Real.log L
    have hb₀ : (0 : ℝ) < b := by exact_mod_cast hb
    have hsq := Real.sqrt_nonneg (b : ℝ)
    set s := (Finset.range b).filter fun n => ¬ P n
    rw [← Finset.card_filter_add_card_filter_not (fun n : ℕ => √(b : ℝ) < n) (s := s)]
    push_cast
    -- at most `√b + 1` exceptions up to `√b`
    have hlow : ((s.filter fun n : ℕ => ¬ √(b : ℝ) < n).card : ℝ) ≤ √b + 1 := by
      have : s.filter (fun n : ℕ => ¬ √(b : ℝ) < n) ⊆ Finset.range (⌊√(b : ℝ)⌋₊ + 1) := by
        intro n hn
        simp only [Finset.mem_filter, not_lt] at hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hn.2))
      refine (Nat.cast_le.mpr (Finset.card_le_card this)).trans ?_
      rw [Finset.card_range]
      push_cast
      linarith [Nat.floor_le hsq]
    -- above `√b`, an exception has `(f n - α log n)² ≥ (ε L / 2)²`
    have hhigh : ((s.filter fun n : ℕ => √(b : ℝ) < n).card : ℝ) ≤
        b * (c * (T ^ 5)⁻¹) := by
      have hc : 0 < (ε * L / 2) ^ 2 := by positivity
      have hsub : s.filter (fun n : ℕ => √(b : ℝ) < n) ⊆ Finset.Icc 1 b := by
        intro n hn
        simp only [s, Finset.mem_filter, Finset.mem_range] at hn
        have : (0 : ℝ) < n := hsq.trans_lt hn.2
        exact Finset.mem_Icc.mpr ⟨by exact_mod_cast this, hn.1.1.le⟩
      refine (card_le_sum_div hsub (fun n _ => sq_nonneg ((f n : ℝ) - α * Real.log n)) hc
        ?_).trans ?_
      · intro n hn
        simp only [s, Finset.mem_filter, Finset.mem_range, P, not_lt] at hn
        obtain ⟨⟨-, hP⟩, hsn⟩ := hn
        have hlo : L / 2 < Real.log n := by
          rw [← Real.log_sqrt hb₀.le]
          exact Real.log_lt_log (Real.sqrt_pos.mpr hb₀) hsn
        have hlog₀ : 0 < Real.log n := by linarith
        -- `|f n - α log n| = |f n / log n - α| log n ≥ ε log n`
        have h₁ : ε * L / 2 ≤ |(f n : ℝ) - α * Real.log n| := by
          rw [show (f n : ℝ) - α * Real.log n = ((f n : ℝ) / Real.log n - α) * Real.log n by
            field_simp, abs_mul, abs_of_pos hlog₀]
          nlinarith
        have h₂ := pow_le_pow_left₀ (by positivity) h₁ 2
        rwa [sq_abs] at h₂
      · rw [div_le_iff₀ hc]
        calc ∑ n ∈ Finset.Icc 1 b, ((f n : ℝ) - α * Real.log n) ^ 2
            ≤ K * b * L ^ 2 / T ^ 5 := hKb
          _ ≤ |K| * b * L ^ 2 / T ^ 5 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_abs_self K) hb₀.le) (sq_nonneg _)) (pow_pos hT 5).le
          _ = b * (c * (T ^ 5)⁻¹) * (ε * L / 2) ^ 2 := by
            simp only [c]
            field_simp
            ring
    have : (b : ℝ) * g b = √b + 1 + b * (c * (T ^ 5)⁻¹) := by
      simp only [g, mul_add]
      rw [← div_eq_mul_inv, Real.div_sqrt, mul_inv_cancel₀ hb₀.ne']
    rw [this]
    linarith
  have hratio : ∀ᶠ b : ℕ in atTop,
      ((({n | P n} ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard) =
        1 - (((Finset.range b).filter fun n => ¬ P n).card : ℝ) / b := by
    filter_upwards [eventually_ge_atTop 1] with b hb
    have hb₀ : (0 : ℝ) < b := by exact_mod_cast hb
    have := Finset.card_filter_add_card_filter_not P (s := Finset.range b)
    rw [Finset.card_range] at this
    rw [ncard_setOf_inter_Iio, Set.ncard_Iio_nat, eq_sub_iff_add_eq, ← add_div,
      div_eq_one_iff_eq hb₀.ne']
    exact_mod_cast this
  have h₀ : Tendsto (fun b : ℕ => (((Finset.range b).filter fun n => ¬ P n).card : ℝ) / b)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hg.comp tendsto_natCast_atTop_atTop) (Eventually.of_forall fun b => by positivity) ?_
    filter_upwards [hbad, eventually_ge_atTop 1] with b hb hb₁
    rw [Function.comp_apply, div_le_iff₀ (by exact_mod_cast hb₁), mul_comm]
    exact hb
  have : Tendsto (fun b : ℕ => 1 - (((Finset.range b).filter fun n => ¬ P n).card : ℝ) / b)
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h₀
  rw [sub_zero] at this
  exact this.congr' (hratio.mono fun b hb => hb.symm)

/-- The partial densities of `S` below `b` are at most those of `S'` if `S ⊆ S'`. -/
theorem ncard_inter_Iio_le {S S' : Set ℕ} (h : S ⊆ S') (b : ℕ) :
    ((S ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard ≤
      ((S' ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard :=
  div_le_div_of_nonneg_right (Nat.cast_le.mpr (Set.ncard_le_ncard
    (Set.inter_subset_inter_left _ h) ((Set.finite_Iio b).inter_of_right _))) (Nat.cast_nonneg _)

/-- The distribution function is the point mass at the `α` of `parts_ii_proved`. -/
theorem parts_i_proved (hR : RectangleInput) :
    ∃ F : ℝ → ℝ, Monotone F ∧ Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 1) ∧
      ∀ c : ℝ, ContinuousAt F c →
        HasDensity {n : ℕ | (f n : ℝ) / Real.log n ≤ c} (F c) := by
  obtain ⟨α, hα⟩ := parts_ii_proved hR
  -- the distribution function of the point mass at `α`
  refine ⟨fun c => if c < α then 0 else 1, fun a b hab => ?_,
    tendsto_const_nhds.congr' ((eventually_lt_atBot α).mono fun c hc => (ite_eq_left hc).symm),
    tendsto_const_nhds.congr' ((eventually_ge_atTop α).mono fun c hc =>
      (ite_eq_right (not_lt.mpr hc)).symm), fun c hc => ?_⟩
  · dsimp only
    split_ifs with ha hb hb <;> first | exact absurd (hab.trans_lt hb) ha | norm_num
  -- `F` jumps at `α`
  have hcα : c ≠ α := by
    rintro rfl
    have h₁ := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio c))
    have h₀ : Tendsto (fun c' : ℝ => if c' < c then (0 : ℝ) else 1) (𝓝[<] c) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (ite_eq_left hy).symm)
    rw [ite_eq_right (lt_irrefl c)] at h₁
    exact one_ne_zero (tendsto_nhds_unique h₁ h₀)
  dsimp only
  rcases lt_or_gt_of_ne hcα with h | h
  · -- `{f / log ≤ c}` misses `{|f / log - α| < α - c}`, whose density is one
    rw [ite_eq_left h]
    have hA := hα (α - c) (by linarith)
    set A := {n : ℕ | |(f n : ℝ) / Real.log n - α| < α - c}
    set S := {n : ℕ | (f n : ℝ) / Real.log n ≤ c}
    have hdisj : Disjoint S A := by
      rw [Set.disjoint_left]
      intro n hS hA
      simp only [S, A, Set.mem_ofPred_eq] at hS hA
      linarith [(abs_lt.mp hA).1]
    have hle : ∀ b : ℕ, 0 < b → ((S ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard ≤
        1 - ((A ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard := by
      intro b hb
      have hfin := Set.finite_Iio b
      have hunion := Set.ncard_union_eq (hdisj.mono Set.inter_subset_left Set.inter_subset_left)
        (hfin.inter_of_right S) (hfin.inter_of_right A)
      have hsub := Set.ncard_le_ncard (Set.union_subset (Set.inter_subset_right (s := S))
        (Set.inter_subset_right (s := A))) hfin
      rw [hunion] at hsub
      rw [Set.ncard_Iio_nat] at hsub ⊢
      have hb₀ : (0 : ℝ) < b := by exact_mod_cast hb
      rw [le_sub_iff_add_le, ← add_div, div_le_one hb₀]
      exact_mod_cast hsub
    have : Tendsto (fun b : ℕ => 1 - ((A ∩ Set.Iio b).ncard : ℝ) / (Set.Iio b).ncard) atTop
        (𝓝 (1 - 1)) := tendsto_const_nhds.sub hA
    rw [sub_self] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds this
      (Eventually.of_forall fun b => by positivity)
      ((eventually_gt_atTop 0).mono fun b hb => hle b hb)
  · -- `{f / log ≤ c}` contains `{|f / log - α| < c - α}`, whose density is one
    rw [ite_eq_right (not_lt.mpr h.le)]
    have hA := hα (c - α) (by linarith)
    have hsub : {n : ℕ | |(f n : ℝ) / Real.log n - α| < c - α} ⊆
        {n : ℕ | (f n : ℝ) / Real.log n ≤ c} := by
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn ⊢
      linarith [(abs_lt.mp hn).2]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hA tendsto_const_nhds
      (ncard_inter_Iio_le hsub) fun b => ?_
    have := ncard_inter_Iio_le (Set.subset_univ {n : ℕ | (f n : ℝ) / Real.log n ≤ c}) b
    rw [Set.univ_inter] at this
    exact this.trans (div_self_le_one _)

end Erdos408
