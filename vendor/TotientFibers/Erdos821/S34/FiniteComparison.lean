import Erdos821.S34.EventPairing

set_option autoImplicit false
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace Erdos821.S34Core
noncomputable section

theorem finite_comparison_of_pointwise {α β : Type} [Fintype α] [Fintype β]
    (w : α → ℝ) (v : β → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (hwprob : ∑ x, w x = 1) (hvprob : ∑ y, v y = 1)
    (EA : α → Prop) (EB : β → Prop) (raw comparison : α → β → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (hraw : ∀ x y, ‖raw x y‖ ≤ 1)
    (hzero : ∀ x y, EA x ∨ EB y → comparison x y = 0)
    (hpoint : ∀ x y, ¬ EA x → ¬ EB y → ‖raw x y - comparison x y‖ ≤ E)
    (f : β → ℂ) (g : α → ℂ) :
    ‖∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * star (f y) * g x *
        (raw x y - comparison x y)‖ ≤
      (Real.sqrt ((∑ x, if EA x then w x else 0) + (∑ y, if EB y then v y else 0)) + E) *
        weightedFrameNorm w g * weightedFrameNorm v f := by
  let R := fun x y => if EA x ∨ EB y then 0 else raw x y - comparison x y
  have hR (x : α) (y : β) : ‖R x y‖ ≤ E := by
    dsimp [R]
    split_ifs with he
    · simpa only [norm_zero] using hE
    · exact hpoint x y (fun hx => he (Or.inl hx)) (fun hy => he (Or.inr hy))
  have hbad := independent_event_pairing w v hw hv hwprob hvprob EA EB f g raw hraw
  have hgood := independent_pairing_bound w v hw hv hwprob hvprob f g R E hE hR
  change ‖∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y‖ ≤
    E * weightedFrameNorm w g * weightedFrameNorm v f at hgood
  have heq : (∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * star (f y) * g x * (raw x y - comparison x y)) =
      (∑ x, ∑ y, if EA x ∨ EB y then
        (w x : ℂ) * (v y : ℂ) * star (f y) * g x * raw x y else 0) +
      (∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases he : EA x ∨ EB y
    · simp [R, he, hzero x y he]
    · simp [R, he]
  rw [heq]
  have hn := (norm_add_le _ _).trans (add_le_add hbad hgood)
  convert hn using 1 <;> ring

end
end Erdos821.S34Core
