import Erdos821.S34.ProbabilityPairing

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section

theorem product_reproduction_error (a b A B : ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hA : ‖A - a‖ ≤ ε) (hB : ‖B - b‖ ≤ ε) : ‖A * B - a * b‖ ≤ 3 * ε := by
  have hnA : ‖A‖ ≤ 1 + ε := by
    have hn : ‖A‖ ≤ ‖A - a‖ + ‖a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (A - a) a
    linarith
  have he : A * B - a * b = (A - a) * b + A * (B - b) := by ring
  rw [he]
  calc
    _ ≤ ‖(A - a) * b‖ + ‖A * (B - b)‖ := norm_add_le _ _
    _ = ‖A - a‖ * ‖b‖ + ‖A‖ * ‖B - b‖ := by simp only [norm_mul]
    _ ≤ ε * 1 + (1 + ε) * ε := add_le_add
      (mul_le_mul hA hb (norm_nonneg _) hε)
      (mul_le_mul hnA hB (norm_nonneg _) (by linarith))
    _ ≤ _ := by nlinarith

theorem finite_character_reproduction_error {γ : Type} [Fintype γ]
    (coeff a b A B : γ → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ha : ∀ c, ‖a c‖ ≤ 1) (hb : ∀ c, ‖b c‖ ≤ 1)
    (hA : ∀ c, ‖A c - a c‖ ≤ ε) (hB : ∀ c, ‖B c - b c‖ ≤ ε) :
    ‖(∑ c, coeff c * A c * B c) - ∑ c, coeff c * a c * b c‖ ≤
      3 * ε * (∑ c, ‖coeff c‖) := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, ‖coeff c * A c * B c - coeff c * a c * b c‖ := norm_sum_le _ _
    _ ≤ ∑ c, 3 * ε * ‖coeff c‖ := by
      apply Finset.sum_le_sum
      intro c _
      have he : coeff c * A c * B c - coeff c * a c * b c =
          coeff c * (A c * B c - a c * b c) := by ring
      rw [he, norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (product_reproduction_error _ _ _ _ ε hε hε1 (ha c) (hb c) (hA c) (hB c)) (norm_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm

theorem kernel_multiplier_freeze {α β : Type} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (K : α → ℂ) (H : β → ℂ) (M phase : α → β → ℂ) (M₀ : ℂ)
    (E CA CB : ℝ) (hE : 0 ≤ E) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hK : (∑ x, w x * ‖K x‖) ≤ CA) (hH : (∑ y, v y * ‖H y‖) ≤ CB)
    (hphase : ∀ x y, ‖phase x y‖ ≤ 1)
    (hM : ∀ x y, K x ≠ 0 → H y ≠ 0 → ‖M x y - M₀‖ ≤ E) :
    ‖∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * K x * H y *
        (M x y - M₀) * phase x y‖ ≤ E * CA * CB := by
  calc
    _ ≤ ∑ x, ∑ y, ‖(w x : ℂ) * (v y : ℂ) * K x * H y * (M x y - M₀) * phase x y‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x, ∑ y, E * (w x * ‖K x‖) * (v y * ‖H y‖) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      by_cases hk : K x = 0
      · simp [hk, mul_nonneg hE (hw x)]
      by_cases hh : H y = 0
      · simp [hh]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw x), abs_of_nonneg (hv y)]
      have hn : 0 ≤ w x * v y * ‖K x‖ * ‖H y‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg (hw x) (hv y)) (norm_nonneg _)) (norm_nonneg _)
      have ht := mul_le_mul
        (mul_le_mul_of_nonneg_left (hM x y hk hh) hn) (hphase x y)
        (norm_nonneg _) (mul_nonneg hn hE)
      convert ht using 1 <;> ring
    _ = E * (∑ x, w x * ‖K x‖) * (∑ y, v y * ‖H y‖) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hK hE) hH
      (Finset.sum_nonneg fun y _ => mul_nonneg (hv y) (norm_nonneg _)) (mul_nonneg hE hCA)

end
end Erdos821.S34Core
