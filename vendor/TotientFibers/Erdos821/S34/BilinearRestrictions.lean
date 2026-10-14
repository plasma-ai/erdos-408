import Erdos821.S34.ProbabilityBilinear

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem restricted_frame_norm_le {α : Type} [Fintype α]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (f : α → ℂ) (s : Finset α) :
    weightedFrameNorm (fun x : ↥s => w x.val) (fun x => f x.val) ≤ weightedFrameNorm w f := by
  unfold weightedFrameNorm
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_coe_sort s (fun x => w x * ‖f x‖ ^ 2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
    mul_nonneg (hw x) (sq_nonneg _)

theorem restricted_fiber_mass_le {α β : Type} [Fintype α] [DecidableEq β]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (P : α → β) (s : Finset α) (n : β) :
    (∑ x : ↥s, if P x.val = n then w x.val else 0) ≤
      ∑ x, if P x = n then w x else 0 := by
  rw [Finset.sum_coe_sort s (fun x => if P x = n then w x else 0)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro x _ _
  split_ifs
  · exact hw x
  · exact le_rfl

theorem bilinear_reduction_restricted {α β : Type} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (P : α → ℤ) (R : β → ℤ) (f : α → ℂ) (g : β → ℂ)
    (s : Finset α) (t : Finset β) (U V N M θ η : ℝ) (u : ℤ) (r : ℕ) (H₁ H₂ : ℝ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hr : 1 ≤ r) (hu : Nat.Coprime u.natAbs r)
    (hθ : θ = (u : ℝ) / r + η) (hη : |η| ≤ (r : ℝ) ^ (-2 : ℤ))
    (hP : ∀ x ∈ s, N ≤ (P x : ℝ) ∧ (P x : ℝ) ≤ N + 4 * U)
    (hR : ∀ y ∈ t, M ≤ (R y : ℝ) ∧ (R y : ℝ) ≤ M + 4 * V)
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂)
    (hρ₁ : ∀ n ∈ s.image P, (∑ x, if P x = n then w x else 0) ≤ H₁)
    (hρ₂ : ∀ n ∈ t.image R, (∑ y, if R y = n then v y else 0) ≤ H₂) :
    ‖∑ x ∈ s, ∑ y ∈ t, (w x : ℂ) * (v y : ℂ) * f x * g y * e (θ * P x * R y)‖ ≤
      integerBilinearConstant * Real.sqrt H₁ * weightedFrameNorm w f *
        Real.sqrt H₂ * weightedFrameNorm v g *
        Real.sqrt (U + (1 + V / r) * (U + r * Real.log (2 * r))) := by
  have hp (n : ℤ) (hn : n ∈ Finset.univ.image (fun x : ↥s => P x.val)) :
      (∑ x : ↥s, if P x.val = n then w x.val else 0) ≤ H₁ := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hn
    exact (restricted_fiber_mass_le w hw P s (P x.val)).trans
      (hρ₁ _ (Finset.mem_image_of_mem P x.property))
  have hq (n : ℤ) (hn : n ∈ Finset.univ.image (fun y : ↥t => R y.val)) :
      (∑ y : ↥t, if R y.val = n then v y.val else 0) ≤ H₂ := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hn
    exact (restricted_fiber_mass_le v hv R t (R y.val)).trans
      (hρ₂ _ (Finset.mem_image_of_mem R y.property))
  have hb := weighted_bilinear_reduction
    (fun x : ↥s => w x.val) (fun y : ↥t => v y.val)
    (fun x => hw x.val) (fun y => hv y.val)
    (fun x => P x.val) (fun y => R y.val) (fun x => f x.val) (fun y => g y.val)
    U V N M θ η u r H₁ H₂ hU hV hr hu hθ hη
    (fun x => hP x.val x.property) (fun y => hR y.val y.property) hH₁ hH₂ hp hq
  have hs := restricted_frame_norm_le w hw f s
  have ht := restricted_frame_norm_le v hv g t
  have heq : (∑ x : ↥s, ∑ y : ↥t, (w x.val : ℂ) * (v y.val : ℂ) *
      f x.val * g y.val * e (θ * P x.val * R y.val)) =
      ∑ x ∈ s, ∑ y ∈ t, (w x : ℂ) * (v y : ℂ) * f x * g y * e (θ * P x * R y) := by
    rw [Finset.sum_coe_sort s (fun x => ∑ y : ↥t, (w x : ℂ) * (v y.val : ℂ) *
      f x * g y.val * e (θ * P x * R y.val))]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_coe_sort t (fun y => (w x : ℂ) * (v y : ℂ) * f x * g y * e (θ * P x * R y))
  change ‖∑ x : ↥s, ∑ y : ↥t, (w x.val : ℂ) * (v y.val : ℂ) *
      f x.val * g y.val * e (θ * P x.val * R y.val)‖ ≤ _ at hb
  rw [heq] at hb
  apply hb.trans
  have hbase : 0 ≤ integerBilinearConstant * Real.sqrt H₁ :=
    mul_nonneg integerBilinearConstant_pos.le (Real.sqrt_nonneg _)
  have hleft := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs hbase) (Real.sqrt_nonneg H₂)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hleft ht (Real.sqrt_nonneg _) (by
      exact mul_nonneg (mul_nonneg hbase (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
    (Real.sqrt_nonneg _)

end
end Erdos821.S34Core
