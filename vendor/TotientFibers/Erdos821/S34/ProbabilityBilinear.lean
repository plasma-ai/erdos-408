import Erdos821.S34.OwnedLeafProofs
import Erdos821.S34.FrameBridge

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def integerBilinearConstant : ℝ :=
  Classical.choose (integer_bilinear_proof 4 (by norm_num))

theorem integerBilinearConstant_pos : 0 < integerBilinearConstant :=
  (Classical.choose_spec (integer_bilinear_proof 4 (by norm_num))).1

theorem sum_product_fibers {α β : Type} [Fintype α] [DecidableEq β]
    (P : α → β) (a : α → ℂ) (F : β → ℂ) :
    (∑ n ∈ Finset.univ.image P, (∑ x, if P x = n then a x else 0) * F n) =
      ∑ x, a x * F (P x) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hp : P x ∈ Finset.univ.image P := Finset.mem_image_of_mem P (Finset.mem_univ x)
  simp [ite_mul, hp]

/-- Collapse arbitrary ordered tests to finite integer-product coefficients;
normalization is not needed for this reduction. -/
theorem weighted_bilinear_reduction {α β : Type} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (P : α → ℤ) (R : β → ℤ) (f : α → ℂ) (g : β → ℂ)
    (U V N M θ η : ℝ) (u : ℤ) (r : ℕ) (H₁ H₂ : ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hr : 1 ≤ r) (hu : Nat.Coprime u.natAbs r)
    (hθ : θ = (u : ℝ) / r + η) (hη : |η| ≤ (r : ℝ) ^ (-2 : ℤ))
    (hP : ∀ x, N ≤ (P x : ℝ) ∧ (P x : ℝ) ≤ N + 4 * U)
    (hR : ∀ y, M ≤ (R y : ℝ) ∧ (R y : ℝ) ≤ M + 4 * V)
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂)
    (hρ₁ : ∀ n ∈ Finset.univ.image P, (∑ x, if P x = n then w x else 0) ≤ H₁)
    (hρ₂ : ∀ n ∈ Finset.univ.image R, (∑ y, if R y = n then v y else 0) ≤ H₂) :
    ‖∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * f x * g y * e (θ * P x * R y)‖ ≤
        integerBilinearConstant * Real.sqrt H₁ * weightedFrameNorm w f *
          Real.sqrt H₂ * weightedFrameNorm v g *
          Real.sqrt (U + (1 + V / r) * (U + r * Real.log (2 * r))) := by
  let K := integerBilinearConstant
  have hK : 0 < K := integerBilinearConstant_pos
  have hbil := (Classical.choose_spec (integer_bilinear_proof 4 (by norm_num))).2
  let a : ℤ → ℂ := fun n => ∑ x, if P x = n then (w x : ℂ) * f x else 0
  let b : ℤ → ℂ := fun n => ∑ y, if R y = n then (v y : ℂ) * g y else 0
  have hcollapse₁ := Erdos821.S34.Proofs.finite_collapse_l2 w hw P f
    (Finset.univ.image P) H₁ hH₁ hρ₁
  have hcollapse₂ := Erdos821.S34.Proofs.finite_collapse_l2 v hv R g
    (Finset.univ.image R) H₂ hH₂ hρ₂
  have hnorm₁ : Real.sqrt (∑ n ∈ Finset.univ.image P, ‖a n‖ ^ 2) ≤
      Real.sqrt H₁ * weightedFrameNorm w f := by
    calc
      _ ≤ Real.sqrt (H₁ * ∑ x, w x * ‖f x‖ ^ 2) := Real.sqrt_le_sqrt hcollapse₁
      _ = _ := by rw [Real.sqrt_mul hH₁]; rfl
  have hnorm₂ : Real.sqrt (∑ n ∈ Finset.univ.image R, ‖b n‖ ^ 2) ≤
      Real.sqrt H₂ * weightedFrameNorm v g := by
    calc
      _ ≤ Real.sqrt (H₂ * ∑ y, v y * ‖g y‖ ^ 2) := Real.sqrt_le_sqrt hcollapse₂
      _ = _ := by rw [Real.sqrt_mul hH₂]; rfl
  have hsum : (∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * f x * g y * e (θ * P x * R y)) =
      ∑ n ∈ Finset.univ.image P, ∑ t ∈ Finset.univ.image R,
        a n * b t * e (θ * n * t) := by
    symm
    calc
      _ = ∑ n ∈ Finset.univ.image P, ∑ y,
          a n * ((v y : ℂ) * g y) * e (θ * n * R y) := by
        apply Finset.sum_congr rfl
        intro n _
        simp only [mul_assoc (a n)]
        rw [← Finset.mul_sum]
        have ht := sum_product_fibers R (fun y => (v y : ℂ) * g y)
          (fun t => e (θ * n * t))
        change a n * (∑ t ∈ Finset.univ.image R, b t * e (θ * n * t)) = _
        rw [show (∑ t ∈ Finset.univ.image R, b t * e (θ * n * t)) =
          ∑ y, (v y : ℂ) * g y * e (θ * n * R y) from ht]
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ y, ∑ x, ((w x : ℂ) * f x) *
          (((v y : ℂ) * g y) * e (θ * P x * R y)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        simpa only [a, mul_assoc] using sum_product_fibers P
          (fun x => (w x : ℂ) * f x)
          (fun n => ((v y : ℂ) * g y) * e (θ * n * R y))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        ring
  rw [hsum]
  have hp' : ∀ n ∈ Finset.univ.image P, N ≤ (n : ℝ) ∧ (n : ℝ) ≤ N + 4 * U := by
    intro n hn
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
    exact hP x
  have hr' : ∀ n ∈ Finset.univ.image R, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ M + 4 * V := by
    intro n hn
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hn
    exact hR y
  have hb := hbil U V N M θ η u r (Finset.univ.image P) (Finset.univ.image R)
    a b hU hV hr hu hθ hη hp' hr'
  have hn : K * Real.sqrt (∑ n ∈ Finset.univ.image P, ‖a n‖ ^ 2) *
      Real.sqrt (∑ t ∈ Finset.univ.image R, ‖b t‖ ^ 2) ≤
      K * (Real.sqrt H₁ * weightedFrameNorm w f) *
        (Real.sqrt H₂ * weightedFrameNorm v g) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hnorm₁ hK.le) hnorm₂
      (Real.sqrt_nonneg _)
    exact mul_nonneg hK.le (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have ht := hb.trans (mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _))
  convert ht using 1 <;> ring

end
end Erdos821.S34Core
