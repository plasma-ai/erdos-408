import Erdos821.S34.TupleBilinear
import Erdos821.S34.KernelDyadicSupport
import Erdos821.S34.KernelReindex

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem dyadic_comparison_bilinear (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q : ℕ) (h ξ U V H θ η ζ : ℝ) (u : ℤ) (r : ℕ)
    (f : Tuple G b → ℂ) (g : Tuple G a → ℂ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : 0 ≤ H) (hr : 1 ≤ r)
    (hu : Nat.Coprime u.natAbs r) (hθ : θ = (u : ℝ) / r + η)
    (hη : |η| ≤ (r : ℝ) ^ (-2 : ℤ)) (hh : 0 < h) (hh2 : h ≤ Real.log 2)
    (hg : ∀ X, g X ≠ 0 → U ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 2 * U)
    (hf : ∀ Y, f Y ≠ 0 → V ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 2 * V)
    (hρa : ∀ n : ℕ, 0 < n → rho G a n ≤ H / n)
    (hρb : ∀ n : ℕ, 0 < n → rho G b n ≤ H / n)
    (hFrameA : ∀ F : Tuple G a → ℂ, tupleNorm G a (cellTransposeApply G a Q h ξ F) ≤ 2 * tupleNorm G a F)
    (hFrameB : ∀ F : Tuple G b → ℂ, tupleNorm G b (cellTransposeApply G b Q h ξ F) ≤ 2 * tupleNorm G b F) :
    ‖comparisonError G a b Q h ξ θ ζ f g‖ ≤
      20 * integerBilinearConstant * H * Real.sqrt (bilinearDecay U V r) * tupleNorm G b f * tupleNorm G a g := by
  let phase := tuplePhase G a b θ ζ
  let R := expect G b (fun Y => expect G a (fun X => star (f Y) * g X * phase X Y))
  let C := expect G b (fun Y => expect G a (fun X => star (f Y) * g X *
    expect G a (fun D => expect G b (fun E =>
      cellKernel G a Q h ξ (product G a D) (product G a X) *
      cellKernel G b Q h ξ (product G b E) (product G b Y) * phase D E))))
  let A := cellTransposeApply G a Q h ξ g
  let B := cellTransposeApply G b Q h ξ (fun Y => star (f Y))
  have hdecomp : comparisonError G a b Q h ξ θ ζ f g = R - C := by
    simp only [comparisonError, R, C, phase, tuplePhase, expect, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  have hR_eq : R = expect G a (fun X => expect G b (fun Y => g X * star (f Y) * phase X Y)) := by
    simp only [R, expect, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro X _
    apply Finset.sum_congr rfl
    intro Y _
    ring
  have hC_eq : C = expect G a (fun D => expect G b (fun E => A D * B E * phase D E)) := by
    have ht := transpose_kernel_pairing (tupleWeight G a) (tupleWeight G b)
      (fun D X => cellKernel G a Q h ξ (product G a D) (product G a X))
      (fun E Y => cellKernel G b Q h ξ (product G b E) (product G b Y)) f g phase
    have hleft : C = (∑ X, ∑ Y, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) * star (f Y) * g X *
        (∑ D, ∑ E, (tupleWeight G a D : ℂ) * (tupleWeight G b E : ℂ) *
          cellKernel G a Q h ξ (product G a D) (product G a X) *
          cellKernel G b Q h ξ (product G b E) (product G b Y) * phase D E)) := by
      simp only [C, expect, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.sum_congr rfl
      intro Y _
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro E _
      ring
    rw [hleft, ht]
    simp only [A, B, cellTransposeApply, expect, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro E _
    apply Finset.sum_congr rfl
    intro Y _
    apply Finset.sum_congr rfl
    intro X _
    ring
  have hg' (X : Tuple G a) (hX : g X ≠ 0) :
      U / 2 ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 4 * U := by
    have hx := hg X hX
    constructor <;> linarith
  have hf' (Y : Tuple G b) (hY : star (f Y) ≠ 0) :
      V / 2 ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 4 * V := by
    have hy := hf Y (by intro hz; simp [hz] at hY)
    constructor <;> linarith
  have hA (D : Tuple G a) (hD : A D ≠ 0) := transpose_apply_dyadic_support G a Q h ξ U hh hh2 g hg D hD
  have hB (E : Tuple G b) (hE : B E ≠ 0) :
      V / 2 ≤ (product G b E : ℝ) ∧ (product G b E : ℝ) ≤ 4 * V := by
    apply transpose_apply_dyadic_support G b Q h ξ V hh hh2 (fun Y => star (f Y)) _ E hE
    intro Y hY
    exact hf Y (by intro hz; simp [hz] at hY)
  have hrb := supported_tuple_bilinear G a b g (fun Y => star (f Y)) U V H θ η ζ u r
    hU hV hH hr hu hθ hη hg' hf' hρa hρb
  rw [← hR_eq, tupleNorm_star] at hrb
  have hcb := supported_tuple_bilinear G a b A B U V H θ η ζ u r
    hU hV hH hr hu hθ hη hA hB hρa hρb
  rw [← hC_eq] at hcb
  have hAn : tupleNorm G a A ≤ 2 * tupleNorm G a g := hFrameA g
  have hBn : tupleNorm G b B ≤ 2 * tupleNorm G b f := by
    simpa only [B, tupleNorm_star] using hFrameB (fun Y => star (f Y))
  have hk : 0 ≤ 4 * integerBilinearConstant * H * Real.sqrt (bilinearDecay U V r) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) integerBilinearConstant_pos.le) hH) (Real.sqrt_nonneg _)
  have hc_bound := hcb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hAn hk) hBn (tuple_norm_nonneg G b B)
      (mul_nonneg hk (mul_nonneg (by norm_num) (tuple_norm_nonneg G a g))))
  rw [hdecomp]
  have hn := (norm_sub_le R C).trans (add_le_add hrb hc_bound)
  convert hn using 1 <;> ring

end
end Erdos821.S34Core
