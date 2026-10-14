import Erdos821.S34.FrameBridge

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section

theorem frame_apply_expansion {α κ γ : Type} [Fintype α] [Fintype γ]
    [DecidableEq κ] (w : α → ℝ) (c : α → κ) (χ : γ → α → ℂ)
    (ξ : ℝ) (X : α) (b : γ) (hret : ξ ≤ frameCellMass w c (c X)) :
    frameCellApply w c χ ξ (χ b) X =
      ∑ a, (frameCellMass w c (c X) : ℂ)⁻¹ * χ a X *
        (∑ D, if c D = c X then (w D : ℂ) * star (χ a D) * χ b D else 0) := by
  unfold frameCellApply
  calc
    _ = ∑ D, ∑ a, (frameCellMass w c (c X) : ℂ)⁻¹ * χ a X *
        (if c D = c X then (w D : ℂ) * star (χ a D) * χ b D else 0) := by
      apply Finset.sum_congr rfl
      intro D _
      by_cases hD : c D = c X
      · simp only [frameCellKernel, hD, hret, and_self, ite_true,
          Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      · simp [frameCellKernel, hD]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

theorem frame_reproduction {α κ γ : Type} [Fintype α] [Fintype γ]
    [DecidableEq κ] (w : α → ℝ) (c : α → κ) (χ : γ → α → ℂ)
    (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 ≤ δ)
    (hχ : ∀ a x, ‖χ a x‖ ≤ 1) (X : α) (b : γ)
    (hret : ξ ≤ frameCellMass w c (c X))
    (hdiag : (∑ D, if c D = c X then
      (w D : ℂ) * star (χ b D) * χ b D else 0) = (frameCellMass w c (c X) : ℂ))
    (hgram : ∀ a : γ, a ≠ b →
      ‖∑ D, if c D = c X then (w D : ℂ) * star (χ a D) * χ b D else 0‖ ≤ δ) :
    ‖frameCellApply w c χ ξ (χ b) X - χ b X‖ ≤ (Fintype.card γ : ℝ) * δ / ξ := by
  let ν := frameCellMass w c (c X)
  let F := fun a : γ => (ν : ℂ)⁻¹ * χ a X *
    (∑ D, if c D = c X then (w D : ℂ) * star (χ a D) * χ b D else 0)
  have hν : 0 < ν := hξ.trans_le hret
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hb : F b = χ b X := by
    change (ν : ℂ)⁻¹ * χ b X *
      (∑ D, if c D = c X then (w D : ℂ) * star (χ b D) * χ b D else 0) = χ b X
    rw [hdiag]
    change (ν : ℂ)⁻¹ * χ b X * (ν : ℂ) = χ b X
    field_simp
  have heq : frameCellApply w c χ ξ (χ b) X - χ b X = ∑ a ∈ Finset.univ.erase b, F a := by
    rw [frame_apply_expansion w c χ ξ X b hret]
    change (∑ a, F a) - χ b X = _
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), hb, add_sub_cancel_right]
  rw [heq]
  calc
    _ ≤ ∑ a ∈ Finset.univ.erase b, ‖F a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Finset.univ.erase b, δ / ξ := by
      apply Finset.sum_le_sum
      intro a ha
      have hab := (Finset.mem_erase.mp ha).1
      dsimp [F]
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]
      calc
        _ ≤ ν⁻¹ * 1 * δ := mul_le_mul
          (mul_le_mul_of_nonneg_left (hχ a X) (inv_nonneg.mpr hν.le)) (hgram a hab)
          (norm_nonneg _) (by positivity)
        _ ≤ ξ⁻¹ * δ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (by
            simpa only [one_div] using one_div_le_one_div_of_le hξ hret) hδ
        _ = _ := by ring
    _ ≤ (Fintype.card γ : ℝ) * δ / ξ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.univ.erase b).card : ℝ) ≤ (Fintype.card γ : ℝ) := by
        exact_mod_cast (Finset.card_erase_le (s := Finset.univ) (a := b))
      calc
        _ ≤ (Fintype.card γ : ℝ) * (δ / ξ) := mul_le_mul_of_nonneg_right hc (div_nonneg hδ hξ.le)
        _ = _ := by ring

end
end Erdos821.S34Core
