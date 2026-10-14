import Erdos821.P4Frame.Frame
import Erdos821.S34.FrameTasks
import Erdos821.S34.CellSup
import Erdos821.S34.OwnedLeafProofs

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section

open Blueprint.Analytic

theorem cellFrameTask_proof : CellFrameTask :=
  Erdos821.P4Frame.CellFrameTask_proof

/-- A frame acts on its finite set of occupied cells, even when the cell
index type itself is infinite. -/
theorem frame_any_cell {α κ γ : Type} [Fintype α] [Fintype γ] [DecidableEq κ]
    (w : α → ℝ) (c : α → κ) (χ : γ → α → ℂ) (ξ δ : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hχ : ∀ a x, ‖χ a x‖ ≤ 1)
    (hξ : 0 < ξ) (hδ : 0 ≤ δ)
    (hgram : ∀ j : κ, ξ ≤ frameCellMass w c j → ∀ a b : γ, a ≠ b →
      ‖∑ x, if c x = j then (w x : ℂ) * star (χ a x) * χ b x else 0‖ ≤ δ)
    (f : α → ℂ) :
    weightedFrameNorm w (frameCellApply w c χ ξ f) ≤
      (1 + (Fintype.card γ : ℝ) * δ / ξ) * weightedFrameNorm w f := by
  let cells := Finset.univ.image c
  let c' : α → ↥cells := fun x => ⟨c x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  have heq (x : α) (j : ↥cells) : c' x = j ↔ c x = j.val := Subtype.ext_iff
  have hm (j : ↥cells) : frameCellMass w c' j = frameCellMass w c j.val := by
    simp only [frameCellMass, heq]
  have hk (D X : α) : frameCellKernel w c' χ ξ D X = frameCellKernel w c χ ξ D X := by
    simp only [frameCellKernel, hm, heq]
    rfl
  have hg (j : ↥cells) (hj : ξ ≤ frameCellMass w c' j)
      (a b : γ) (hab : a ≠ b) :
      ‖∑ x, if c' x = j then (w x : ℂ) * star (χ a x) * χ b x else 0‖ ≤ δ := by
    simp only [heq]
    exact hgram j.val (by rwa [hm] at hj) a b hab
  have ht := cellFrameTask_proof α ↥cells γ w c' χ ξ δ hw hχ hξ hδ hg f
  have ha : frameCellApply w c' χ ξ f = frameCellApply w c χ ξ f := by
    funext X
    simp only [frameCellApply, hk]
  rwa [ha] at ht

def cellApply (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ)
    (h ξ : ℝ) (f : Tuple G k → ℂ) (X : Tuple G k) : ℂ :=
  expect G k (fun D => cellKernel G k Q h ξ (product G k D) (product G k X) * f D)

theorem cell_operator_norm (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ)
    (h ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 ≤ δ)
    (hgram : ∀ j : ℤ, ξ ≤ cellMass G k h j →
      ∀ χ ∈ primitiveCharacters Q, ∀ ψ ∈ primitiveCharacters Q, χ ≠ ψ →
      ‖expect G k (fun z => if cell h (product G k z) = j then
        star (charValue χ (product G k z)) * charValue ψ (product G k z) else 0)‖ ≤ δ)
    (f : Tuple G k → ℂ) :
    tupleNorm G k (cellApply G k Q h ξ f) ≤
      (1 + (Q : ℝ) ^ 2 * δ / ξ) * tupleNorm G k f := by
  let w := tupleWeight G k
  let c := fun z : Tuple G k => cell h (product G k z)
  let χ := fun a : ↥(primitiveCharacters Q) => fun z : Tuple G k =>
    charValue a.val (product G k z)
  have hw (z : Tuple G k) : 0 ≤ w z :=
    Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) k z
  have hg (j : ℤ) (hj : ξ ≤ frameCellMass w c j)
      (a b : ↥(primitiveCharacters Q)) (hab : a ≠ b) :
      ‖∑ z, if c z = j then (w z : ℂ) * star (χ a z) * χ b z else 0‖ ≤ δ := by
    have he : a.val ≠ b.val := fun he => hab (Subtype.ext he)
    have ht := hgram j hj a.val a.property b.val b.property he
    simpa only [expect, w, c, χ, mul_ite, mul_zero, mul_assoc] using ht
  have hf := frame_any_cell w c χ ξ δ hw
    (fun a z => primitiveCharacterTask_proof.2 Q a.val (product G k z)) hξ hδ hg f
  have hk (D X : Tuple G k) : frameCellKernel w c χ ξ D X =
      cellKernel G k Q h ξ (product G k D) (product G k X) := by
    unfold frameCellKernel
    change (if cell h (product G k D) = cell h (product G k X) ∧
        ξ ≤ cellMass G k h (cell h (product G k X)) then
      (cellMass G k h (cell h (product G k X)) : ℂ)⁻¹ *
        ∑ a : ↥(primitiveCharacters Q), star (charValue a.val (product G k D)) *
          charValue a.val (product G k X) else 0) = _
    unfold cellKernel
    split_ifs
    · congr 1
      exact Finset.sum_coe_sort (primitiveCharacters Q)
        (fun a => star (charValue a (product G k D)) * charValue a (product G k X))
    · rfl
  have ha : frameCellApply w c χ ξ f = cellApply G k Q h ξ f := by
    funext X
    simp only [frameCellApply, cellApply, expect, hk, w, mul_assoc]
  rw [ha] at hf
  have hc : (Fintype.card ↥(primitiveCharacters Q) : ℝ) ≤ (Q : ℝ) ^ 2 := by
    simpa only [Fintype.card_coe] using (show ((primitiveCharacters Q).card : ℝ) ≤ (Q : ℝ) ^ 2 by
      exact_mod_cast primitiveCharacterTask_proof.1 Q)
  calc
    _ ≤ (1 + (Fintype.card ↥(primitiveCharacters Q) : ℝ) * δ / ξ) * tupleNorm G k f := hf
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact add_le_add (le_refl 1)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hδ) hξ.le)

end
end Erdos821.S34Core
