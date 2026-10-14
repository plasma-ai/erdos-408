import Erdos821.S34.FrameReproduction
import Erdos821.S34.ProductSupport

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem tuple_product_coprime (G : PrimeGroups) (k : Fin G.size → ℕ)
    (r : ℕ) (hr : 0 < r)
    (hp : ∀ g, 0 < k g → ∀ p ∈ G.primes g, r < p) (z : Tuple G k) :
    Nat.Coprime (product G k z) r := by
  unfold product
  apply Nat.coprime_prod_left_iff.mpr
  intro g _
  apply Nat.coprime_prod_left_iff.mpr
  intro j _
  exact Nat.coprime_of_lt_prime hr.ne' (hp g (by have hj := j.isLt; omega) (z g j).val (z g j).property)
    (G.prime g (z g j).val (z g j).property)

theorem charValue_norm_of_coprime {Q : ℕ} (χ : CharacterIndex Q) (n : ℕ)
    (hn : Nat.Coprime n (χ.1.val + 1)) : ‖charValue χ n‖ = 1 := by
  have hu := (ZMod.isUnit_iff_coprime n (χ.1.val + 1)).mpr hn
  simpa only [charValue, IsUnit.unit_spec] using χ.2.unit_norm_eq_one hu.unit

theorem cell_character_reproduction (G : PrimeGroups) (k : Fin G.size → ℕ)
    (Q : ℕ) (h ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 ≤ δ)
    (χ : CharacterIndex Q) (hχ : χ ∈ primitiveCharacters Q)
    (hunit : ∀ z : Tuple G k, Nat.Coprime (product G k z) (χ.1.val + 1))
    (hgram : ∀ j : ℤ, ξ ≤ cellMass G k h j →
      ∀ ψ ∈ primitiveCharacters Q, ψ ≠ χ →
      ‖expect G k (fun z => if cell h (product G k z) = j then
        star (charValue ψ (product G k z)) * charValue χ (product G k z) else 0)‖ ≤ δ)
    (X : Tuple G k) (hret : ξ ≤ cellMass G k h (cell h (product G k X))) :
    ‖cellApply G k Q h ξ (fun z => charValue χ (product G k z)) X -
        charValue χ (product G k X)‖ ≤ (Q : ℝ) ^ 2 * δ / ξ := by
  let w := tupleWeight G k
  let c := fun z : Tuple G k => cell h (product G k z)
  let chars := fun a : ↥(primitiveCharacters Q) => fun z : Tuple G k =>
    charValue a.val (product G k z)
  let b : ↥(primitiveCharacters Q) := ⟨χ, hχ⟩
  have hdiag : (∑ D, if c D = c X then
      (w D : ℂ) * star (chars b D) * chars b D else 0) = (frameCellMass w c (c X) : ℂ) := by
    simp only [frameCellMass, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro D _
    have hn := charValue_norm_of_coprime χ (product G k D) (hunit D)
    have hs : star (chars b D) * chars b D = 1 := by
      change star (charValue χ (product G k D)) * charValue χ (product G k D) = 1
      simp only [Complex.star_def, Complex.conj_mul', hn]
      norm_num
    split_ifs
    · rw [mul_assoc, hs, mul_one]
    · simp
  have hg (a : ↥(primitiveCharacters Q)) (hab : a ≠ b) :
      ‖∑ D, if c D = c X then (w D : ℂ) * star (chars a D) * chars b D else 0‖ ≤ δ := by
    have ha : a.val ≠ χ := fun he => hab (Subtype.ext he)
    simpa only [expect, w, c, chars, b, mul_ite, mul_zero, mul_assoc] using
      hgram (c X) hret a.val a.property ha
  have ht := frame_reproduction w c chars ξ δ hξ hδ
    (fun a D => primitiveCharacterTask_proof.2 Q a.val (product G k D)) X b hret hdiag hg
  have hk (D : Tuple G k) : frameCellKernel w c chars ξ D X =
      cellKernel G k Q h ξ (product G k D) (product G k X) := by
    unfold frameCellKernel
    change (if c D = c X ∧ ξ ≤ cellMass G k h (c X) then
      (cellMass G k h (c X) : ℂ)⁻¹ *
        ∑ a : ↥(primitiveCharacters Q), star (charValue a.val (product G k D)) *
          charValue a.val (product G k X) else 0) = _
    unfold cellKernel
    change (if cell h (product G k D) = cell h (product G k X) ∧ ξ ≤ cellMass G k h (cell h (product G k X)) then _ else _) = _
    split_ifs
    · congr 1
      exact Finset.sum_coe_sort (primitiveCharacters Q)
        (fun a => star (charValue a (product G k D)) * charValue a (product G k X))
    · rfl
  have he : frameCellApply w c chars ξ (chars b) X =
      cellApply G k Q h ξ (fun z => charValue χ (product G k z)) X := by
    simp only [frameCellApply, cellApply, expect, hk, w, chars, b, mul_assoc]
  rw [he] at ht
  change ‖cellApply G k Q h ξ (fun z => charValue χ (product G k z)) X -
    charValue χ (product G k X)‖ ≤ _ at ht
  apply ht.trans
  have hc : (Fintype.card ↥(primitiveCharacters Q) : ℝ) ≤ (Q : ℝ) ^ 2 := by
    simpa only [Fintype.card_coe] using (show ((primitiveCharacters Q).card : ℝ) ≤ (Q : ℝ) ^ 2 by
      exact_mod_cast primitiveCharacterTask_proof.1 Q)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hδ) hξ.le

end
end Erdos821.S34Core
