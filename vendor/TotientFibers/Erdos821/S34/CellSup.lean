import Erdos821.P4Char.Basic
import Erdos821.S34.CharacterTasks

set_option autoImplicit false

open scoped BigOperators Classical

namespace Erdos821.S34Core

theorem primitiveCharacterTask_proof : PrimitiveCharacterTask :=
  Erdos821.P4Char.PrimitiveCharacterTask_proof

end Erdos821.S34Core

namespace Erdos821.Blueprint.Analytic

theorem cell_kernel_sup_proof : Erdos821.Blueprint.Analytic.cell_kernel_sup_statement := by
  intro G k Q h ξ hξ D X
  have hcount := Erdos821.S34Core.primitiveCharacterTask_proof.1 Q
  have hchar := Erdos821.S34Core.primitiveCharacterTask_proof.2
  unfold cellKernel
  split_ifs with hc
  · have hν : 0 < cellMass G k h (cell h X) := hξ.trans_le hc.2
    have hs : ‖∑ χ ∈ primitiveCharacters Q, star (charValue χ D) * charValue χ X‖ ≤ (Q : ℝ) ^ 2 := by
      calc
        _ ≤ ∑ χ ∈ primitiveCharacters Q, ‖star (charValue χ D) * charValue χ X‖ := norm_sum_le _ _
        _ ≤ ∑ _ ∈ primitiveCharacters Q, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro χ _
          rw [norm_mul, norm_star]
          simpa only [one_mul] using mul_le_mul (hchar Q χ D) (hchar Q χ X)
            (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        _ = ((primitiveCharacters Q).card : ℝ) := by simp
        _ ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hcount
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]
    calc
      _ ≤ (cellMass G k h (cell h X))⁻¹ * (Q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hν.le)
      _ ≤ ξ⁻¹ * (Q : ℝ) ^ 2 := mul_le_mul_of_nonneg_right
        (by simpa only [one_div] using one_div_le_one_div_of_le hξ hc.2) (sq_nonneg _)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

example : Erdos821.Blueprint.Analytic.cell_kernel_sup_statement := @cell_kernel_sup_proof

end Erdos821.Blueprint.Analytic
