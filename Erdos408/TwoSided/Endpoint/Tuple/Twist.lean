import Erdos408.Hypotheses

/-!
# The spare prime polynomial

E9 of `blueprint/two_sided_correlation.md` §6.6 (PD (6.38)). Abel summation writes
`∑_{p ∈ (lo, hi]} χ(p) p^{iu}` through the partial sums
`S(y) = ∑_{p ∈ (lo, y]} χ(p) p^{-1 + iu}`, each bounded by `PrimeTwistBound`.
-/

namespace Erdos408.TwoSided.TupleHigh

open Finset

/-- Abel summation with weight `k`: `∑_{k ∈ (m, N]} k a_k = N S(N) - ∑_{n ∈ [m, N)} S(n)`,
where `S(n) = ∑_{k ∈ (m, n]} a_k`. -/
theorem sum_Ioc_natCast_mul_eq (a : ℕ → ℂ) (m : ℕ) {N : ℕ} (hN : m ≤ N) :
    ∑ k ∈ Ioc m N, (k : ℂ) * a k =
      N * ∑ k ∈ Ioc m N, a k - ∑ n ∈ Ico m N, ∑ k ∈ Ioc m n, a k := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hmN ih =>
      rw [sum_Ioc_succ_top hmN, sum_Ioc_succ_top hmN, sum_Ico_succ_top hmN, ih]
      push_cast
      ring

/-- **Lemma E9 (spare prime polynomial from AP1).** Under `PrimeTwistBound x A' E C_m κ'`,
for `H ∈ [exp(L/T²²), x]`, an interval `(lo, hi] ⊂ [H, 2H]`, a character `χ` of modulus
`k ≤ L^{C_m}` and `L^E ≤ |u| ≤ x³`,
`|H⁻¹ ∑_{p ∈ (lo, hi]} χ(p) p^{iu}| ≤ 4κ' L^{-A'}`. -/
theorem norm_primeTwistPoly_le {x A' E Cm κ' : ℝ} (hP : PrimeTwistBound x A' E Cm κ')
    {H lo hi : ℝ} (hH₁ : Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤ H) (hH₂ : H ≤ x)
    (hlo : H ≤ lo) (hhi : hi ≤ 2 * H) {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : (k : ℝ) ≤ Real.log x ^ Cm)
    (χ : DirichletCharacter ℂ k) {u : ℝ} (hu₁ : Real.log x ^ E ≤ |u|) (hu₂ : |u| ≤ x ^ 3) :
    ‖(H : ℂ)⁻¹ * ∑ p ∈ (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime,
        χ p * (p : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤ 4 * κ' * Real.log x ^ (-A') := by
  have hH0 : 0 < H := lt_of_lt_of_le (Real.exp_pos _) hH₁
  set B := κ' * Real.log x ^ (-A') with hB
  set m := ⌊lo⌋₊
  set N := ⌊hi⌋₊
  -- the twisted prime sums `S(n)` over `(lo, n]`
  set a : ℕ → ℂ := fun n => if n.Prime then χ n * (n : ℂ) ^ ((-1 : ℂ) + (u : ℂ) * Complex.I)
    else 0 with ha
  have hS : ∀ n, ∑ k ∈ Ioc m n, a k = ∑ p ∈ (Ioc m n).filter Nat.Prime,
      χ p * (p : ℂ) ^ ((-1 : ℂ) + (u : ℂ) * Complex.I) := fun n => by
    rw [sum_filter]
  -- `B ≥ 0`, from the empty interval
  have hB0 : 0 ≤ B := by
    have h := hP H H H hH₁ hH₂ le_rfl (by linarith) k hk₁ hk₂ χ u hu₁ hu₂
    simp only [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty, norm_zero] at h
    exact h
  -- each partial sum is at most `B`
  have hSn : ∀ n ∈ Icc m N, ‖∑ k ∈ Ioc m n, a k‖ ≤ B := by
    intro n hn
    rw [mem_Icc] at hn
    rcases hn.1.eq_or_lt with h | h
    · rw [← h, Ioc_self, sum_empty, norm_zero]
      exact hB0
    · have hN1 : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (h.trans_le hn.2)
      have hhi0 : 0 ≤ hi := (Nat.floor_pos.1 hN1).trans' zero_le_one
      have hnhi : (n : ℝ) ≤ 2 * H :=
        ((Nat.cast_le.2 hn.2).trans (Nat.floor_le hhi0)).trans hhi
      have h := hP H lo n hH₁ hH₂ hlo hnhi k hk₁ hk₂ χ u hu₁ hu₂
      rw [Nat.floor_natCast] at h
      rw [hS]
      exact h
  -- the sum is `∑ k a_k` over `(m, N]`
  have hT : ∑ p ∈ (Ioc m N).filter Nat.Prime, χ p * (p : ℂ) ^ ((u : ℂ) * Complex.I) =
      ∑ k ∈ Ioc m N, (k : ℂ) * a k := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    simp only [ha]
    split_ifs with hn
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne_zero
      rw [Complex.cpow_add _ _ hn0, Complex.cpow_neg_one]
      field_simp
    · rw [mul_zero]
  rw [hT, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hH0.le]
  rcases le_or_gt m N with hmN | hmN
  · rw [sum_Ioc_natCast_mul_eq a m hmN]
    -- `‖N S(N) - ∑ S(n)‖ ≤ N B + (N - m) B ≤ 2 N B ≤ 4 H B`
    have h₁ : ‖(N : ℂ) * ∑ k ∈ Ioc m N, a k‖ ≤ N * B := by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hSn N (mem_Icc.2 ⟨hmN, le_rfl⟩)) (Nat.cast_nonneg _)
    have h₂ : ‖∑ n ∈ Ico m N, ∑ k ∈ Ioc m n, a k‖ ≤ N * B := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ Ico m N, ‖∑ k ∈ Ioc m n, a k‖ ≤ ∑ _n ∈ Ico m N, B :=
            sum_le_sum fun n hn => hSn n (Ico_subset_Icc_self hn)
        _ = (N - m : ℕ) * B := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ N * B := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le N m) hB0
    have hN : (N : ℝ) ≤ 2 * H := by
      rcases Nat.eq_zero_or_pos N with h0 | hN1
      · rw [h0, Nat.cast_zero]
        linarith
      · exact (Nat.floor_le ((Nat.floor_pos.1 hN1).trans' zero_le_one)).trans hhi
    calc H⁻¹ * ‖(N : ℂ) * ∑ k ∈ Ioc m N, a k - ∑ n ∈ Ico m N, ∑ k ∈ Ioc m n, a k‖
        ≤ H⁻¹ * (N * B + N * B) :=
          mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) (by positivity)
      _ ≤ H⁻¹ * (4 * H * B) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith
      _ = 4 * κ' * Real.log x ^ (-A') := by
          rw [hB]
          field_simp
  · rw [Ioc_eq_empty_of_le hmN.le, sum_empty, norm_zero, mul_zero]
    linarith

end Erdos408.TwoSided.TupleHigh
