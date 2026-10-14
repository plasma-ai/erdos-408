import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core

/-- Discrete partial summation with a nonnegative decreasing weight. A uniform
bound for prefix sums costs only the first weight, independent of the length. -/
theorem decreasing_weight_sum_bound (n : ℕ) (w : ℕ → ℝ) (f : ℕ → ℂ) (H : ℝ)
    (hH : 0 ≤ H) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (hprefix : ∀ k, k ≤ n → ‖∑ i ∈ Finset.range k, f i‖ ≤ H) :
    ‖∑ i ∈ Finset.range n, (w i : ℂ) * f i‖ ≤ H * w 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg hH (hw 0)
  have hparts := Finset.sum_range_by_parts w f n
  simp only [Complex.real_smul] at hparts
  rw [hparts]
  have htel (m : ℕ) : (∑ i ∈ Finset.range m, (w i - w (i + 1))) = w 0 - w m := by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ ≤ ‖(w (n - 1) : ℂ) * ∑ i ∈ Finset.range n, f i‖ +
        ‖∑ i ∈ Finset.range (n - 1), ((w (i + 1) - w i : ℝ) : ℂ) *
          ∑ j ∈ Finset.range (i + 1), f j‖ := norm_sub_le _ _
    _ ≤ w (n - 1) * H + ∑ i ∈ Finset.range (n - 1), (w i - w (i + 1)) * H := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)]
        exact mul_le_mul_of_nonneg_left (hprefix n le_rfl) (hw _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro i hi
        have hwi : w (i + 1) ≤ w i := hmono (Nat.le_succ i)
        have hip : i + 1 ≤ n := by have := Finset.mem_range.mp hi; omega
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hwi)]
        have hbound := mul_le_mul_of_nonneg_left (hprefix (i + 1) hip) (sub_nonneg.mpr hwi)
        simpa only [neg_sub] using hbound
    _ = H * w 0 := by rw [← Finset.sum_mul, htel]; ring

/-- The normalized reciprocal weight needed after splitting into character classes. -/
theorem reciprocal_weight_sum_bound (n : ℕ) (a b H : ℝ) (f : ℕ → ℂ)
    (ha : 0 < a) (hb : 0 ≤ b) (hH : 0 ≤ H)
    (hprefix : ∀ k, k ≤ n → ‖∑ i ∈ Finset.range k, f i‖ ≤ H) :
    ‖∑ i ∈ Finset.range n, f i / ((a + b * i : ℝ) : ℂ)‖ ≤ H / a := by
  have hw (k : ℕ) : 0 ≤ (a + b * k)⁻¹ := by positivity
  have hm : Antitone (fun k : ℕ => (a + b * k)⁻¹) := by
    intro i j hij
    have hi : 0 < a + b * i := by positivity
    have hle : a + b * i ≤ a + b * j := by gcongr
    exact inv_anti₀ hi hle
  have h := decreasing_weight_sum_bound n (fun k => (a + b * k)⁻¹) f H hH hw hm hprefix
  simpa only [Nat.cast_zero, mul_zero, add_zero, Complex.ofReal_inv, div_eq_mul_inv,
    mul_comm] using h

theorem sum_integer_interval (a b : ℤ) (f : ℤ → ℂ) :
    (∑ y ∈ Finset.Icc a b, f y) =
      ∑ k ∈ Finset.range (b + 1 - a).toNat, f (a + k) := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  rfl

/-- Partial summation on the integer intervals used by the log-phase task. -/
theorem integer_reciprocal_weight_sum_bound (a b : ℤ) (A B H : ℝ) (f : ℤ → ℂ)
    (ha : 0 < A + B * a) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hprefix : ∀ c : ℤ, a ≤ c → c ≤ b → ‖∑ y ∈ Finset.Icc a c, f y‖ ≤ H) :
    ‖∑ y ∈ Finset.Icc a b, f y / ((A + B * y : ℝ) : ℂ)‖ ≤
      H / (A + B * a) := by
  let n := (b + 1 - a).toNat
  have hpref (k : ℕ) (hk : k ≤ n) :
      ‖∑ i ∈ Finset.range k, f (a + i)‖ ≤ H := by
    by_cases hk0 : k = 0
    · subst k
      simpa using hH
    have hc₁ : a ≤ a + (k : ℤ) - 1 := by omega
    have hc₂ : a + (k : ℤ) - 1 ≤ b := by dsimp [n] at hk; omega
    have hlen : (a + (k : ℤ) - 1 + 1 - a).toNat = k := by omega
    have h := hprefix (a + k - 1) hc₁ hc₂
    rwa [sum_integer_interval, hlen] at h
  have h := reciprocal_weight_sum_bound n (A + B * a) B H (fun k => f (a + k)) ha hB hH hpref
  rw [sum_integer_interval]
  calc
    _ = ‖∑ k ∈ Finset.range n, f (a + k) / ((A + B * a + B * k : ℝ) : ℂ)‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      push_cast
      ring
    _ ≤ _ := h

end Erdos821.P5Core
