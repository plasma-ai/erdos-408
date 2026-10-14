import Erdos821.S34.KernelTransport
import Erdos821.S34.ProductSupport

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem kernel_dyadic_localization (G : PrimeGroups) (k : Fin G.size → ℕ)
    (Q : ℕ) (h ξ U : ℝ) (hh : 0 < h) (hh2 : h ≤ Real.log 2)
    (D X : ℕ) (hD : 0 < D) (hX : 0 < X)
    (hlo : U ≤ (X : ℝ)) (hhi : (X : ℝ) ≤ 2 * U)
    (hne : cellKernel G k Q h ξ D X ≠ 0) :
    U / 2 ≤ (D : ℝ) ∧ (D : ℝ) ≤ 4 * U := by
  have hloc := abs_lt.mp (kernel_log_localization G k Q h ξ hh D X hne)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hl : Real.log X - Real.log 2 ≤ Real.log D := by linarith [hloc.1]
  have hu : Real.log D ≤ Real.log X + Real.log 2 := by linarith [hloc.2]
  have hel := Real.exp_le_exp.mpr hl
  have heu := Real.exp_le_exp.mpr hu
  rw [Real.exp_sub, Real.exp_log hXR, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hDR] at hel
  rw [Real.exp_add, Real.exp_log hXR, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_log hDR] at heu
  constructor <;> linarith

theorem transpose_apply_dyadic_support (G : PrimeGroups) (k : Fin G.size → ℕ)
    (Q : ℕ) (h ξ U : ℝ) (hh : 0 < h) (hh2 : h ≤ Real.log 2)
    (f : Tuple G k → ℂ) (hf : ∀ X, f X ≠ 0 → U ≤ (product G k X : ℝ) ∧ (product G k X : ℝ) ≤ 2 * U)
    (D : Tuple G k) (hne : cellTransposeApply G k Q h ξ f D ≠ 0) :
    U / 2 ≤ (product G k D : ℝ) ∧ (product G k D : ℝ) ≤ 4 * U := by
  unfold cellTransposeApply expect at hne
  obtain ⟨X, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hK : cellKernel G k Q h ξ (product G k D) (product G k X) ≠ 0 := by
    intro hz
    simp only [hz, zero_mul, mul_zero] at ht
    exact ht rfl
  have hF : f X ≠ 0 := by
    intro hz
    simp only [hz, mul_zero] at ht
    exact ht rfl
  exact kernel_dyadic_localization G k Q h ξ U hh hh2 _ _
    (tuple_product_pos G k D) (tuple_product_pos G k X) (hf X hF).1 (hf X hF).2 hK

end
end Erdos821.S34Core
