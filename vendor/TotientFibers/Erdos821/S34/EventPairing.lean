import Erdos821.S34.ProbabilityPairing
import Erdos821.S34.FrameBridge

set_option autoImplicit false
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace Erdos821.S34Core
noncomputable section

theorem weighted_event_pairing {α : Type} [Fintype α]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (event : α → Prop) (F : α → ℂ) :
    ‖∑ x, if event x then (w x : ℂ) * F x else 0‖ ≤
      Real.sqrt (∑ x, if event x then w x else 0) * weightedFrameNorm w F := by
  let v := fun x => if event x then w x else 0
  have hv (x : α) : 0 ≤ v x := by dsimp [v]; split_ifs <;> first | exact hw x | exact le_rfl
  have hc := Erdos821.S34.Proofs.norm_weighted_sum_sq v hv F
  have he : (∑ x, v x * ‖F x‖ ^ 2) ≤ ∑ x, w x * ‖F x‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro x _
    dsimp [v]
    split_ifs
    · rfl
    · simpa only [zero_mul] using mul_nonneg (hw x) (sq_nonneg ‖F x‖)
  have hm : 0 ≤ ∑ x, v x := Finset.sum_nonneg fun x _ => hv x
  have he0 : 0 ≤ ∑ x, w x * ‖F x‖ ^ 2 := Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)
  have hsq := hc.trans (mul_le_mul_of_nonneg_left he hm)
  have hn : ‖∑ x, (v x : ℂ) * F x‖ ≤ Real.sqrt ((∑ x, v x) * (∑ x, w x * ‖F x‖ ^ 2)) := by
    have hs := Real.sq_sqrt (mul_nonneg hm he0)
    nlinarith [Real.sqrt_nonneg ((∑ x, v x) * (∑ x, w x * ‖F x‖ ^ 2))]
  rw [Real.sqrt_mul hm] at hn
  simpa only [v, apply_ite, Complex.ofReal_zero, ite_mul, zero_mul, weightedFrameNorm] using hn

theorem independent_event_pairing {α β : Type} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (hwprob : ∑ x, w x = 1) (hvprob : ∑ y, v y = 1)
    (EA : α → Prop) (EB : β → Prop) (f : β → ℂ) (g : α → ℂ)
    (R : α → β → ℂ) (hR : ∀ x y, ‖R x y‖ ≤ 1) :
    ‖∑ x, ∑ y, if EA x ∨ EB y then
      (w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y else 0‖ ≤
      Real.sqrt ((∑ x, if EA x then w x else 0) + (∑ y, if EB y then v y else 0)) *
        weightedFrameNorm w g * weightedFrameNorm v f := by
  let W := fun p : α × β => w p.1 * v p.2
  let F := fun p : α × β => star (f p.2) * g p.1 * R p.1 p.2
  have hW (p : α × β) : 0 ≤ W p := mul_nonneg (hw p.1) (hv p.2)
  have hmass : (∑ p : α × β, if EA p.1 ∨ EB p.2 then W p else 0) ≤
      (∑ x, if EA x then w x else 0) + (∑ y, if EB y then v y else 0) := by
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ x, ∑ y, ((if EA x then w x else 0) * v y + w x * (if EB y then v y else 0)) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        dsimp [W]
        by_cases ha : EA x <;> by_cases hb : EB y <;>
          simp [ha, hb, mul_nonneg (hw x) (hv y)]
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        rw [hwprob, hvprob]
        ring
  have henergy : (∑ p : α × β, W p * ‖F p‖ ^ 2) ≤
      (∑ x, w x * ‖g x‖ ^ 2) * (∑ y, v y * ‖f y‖ ^ 2) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _
    change w x * v y * ‖star (f y) * g x * R x y‖ ^ 2 ≤
      w x * ‖g x‖ ^ 2 * (v y * ‖f y‖ ^ 2)
    rw [norm_mul, norm_mul, norm_star, mul_pow, mul_pow]
    have hs : ‖R x y‖ ^ 2 ≤ 1 := by nlinarith [hR x y, norm_nonneg (R x y)]
    have hm := mul_le_mul_of_nonneg_left hs
      (mul_nonneg (mul_nonneg (hw x) (hv y)) (mul_nonneg (sq_nonneg ‖f y‖) (sq_nonneg ‖g x‖)))
    convert hm using 1 <;> ring
  have ht := weighted_event_pairing W hW (fun p => EA p.1 ∨ EB p.2) F
  have hmask : (∑ p : α × β, @ite ℝ (EA p.1 ∨ EB p.2)
      (Classical.propDecidable _) (W p) 0) =
      ∑ p : α × β, if EA p.1 ∨ EB p.2 then W p else 0 := by
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : EA p.1 ∨ EB p.2 <;> simp [hp]
  rw [hmask] at ht
  have hnorm : weightedFrameNorm W F ≤ weightedFrameNorm w g * weightedFrameNorm v f := by
    unfold weightedFrameNorm
    calc
      _ ≤ Real.sqrt ((∑ x, w x * ‖g x‖ ^ 2) * (∑ y, v y * ‖f y‖ ^ 2)) := Real.sqrt_le_sqrt henergy
      _ = _ := Real.sqrt_mul (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)) _
  have hb := ht.trans (mul_le_mul (Real.sqrt_le_sqrt hmass) hnorm
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simp only [Fintype.sum_prod_type, W, F, Complex.ofReal_mul] at hb
  convert hb using 1 <;>
    simp only [mul_assoc]

end
end Erdos821.S34Core
