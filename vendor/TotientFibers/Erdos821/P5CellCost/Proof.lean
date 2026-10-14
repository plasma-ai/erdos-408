import Erdos821.P5.ComparisonCellCostTask
import Erdos821.P5.PatternCosts

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Cell

open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- Extend the auxiliary prefix by the supplied reference endpoint. -/
def extendAux {G : Blueprint.Graph.PrimeGroups} {J ell : ℕ}
    (a₀ : G.BigLabels (J + ell)) (u : G.BigAux J) : G.BigLabels (J + ell) :=
  fun g i => if hi : i.val < J then u g ⟨i.val, hi⟩ else a₀ g i

lemma extendAux_slot {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (a₀ : G.BigLabels (J + ell)) (u : G.BigAux J)
    (g : G.BigGroup) (i : Fin J) :
    extendAux a₀ u g (ν.slot i) = u g i := by
  simp [extendAux, Pattern.slot]

lemma selectedEndpoint_extendAux {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (side : Bool)
    (a₀ : G.BigLabels (J + ell)) (u : G.BigAux J) :
    selectedEndpoint ν block side (extendAux a₀ u) = selectedProduct ν block side u := by
  unfold selectedEndpoint selectedProduct
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hc : block g = side ∧ i ∈ ν.changed g.val
  · simp only [if_pos hc]
    exact congrArg Subtype.val (extendAux_slot ν a₀ u g i)
  · simp only [if_neg hc]

lemma diagonalCharacterSum_re_ge_one {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    1 ≤ (∑ χ ∈ primitiveCharacters Q,
      star (charValue χ n) * charValue χ n).re := by
  classical
  let χ₀ : CharacterIndex Q :=
    ⟨⟨0, Nat.zero_lt_one.trans_le hQ⟩, 1⟩
  have hmem : χ₀ ∈ primitiveCharacters Q := by
    simp only [primitiveCharacters, Finset.mem_filter, Finset.mem_univ, true_and]
    change (1 : DirichletCharacter ℂ 1).IsPrimitive
    exact DirichletCharacter.isPrimitive_one_level_one
  have hval : charValue χ₀ n = 1 := by
    change (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1
    letI : Subsingleton (ZMod 1) := (ZMod.subsingleton_iff).2 rfl
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
    simp
  have hterm (χ : CharacterIndex Q) :
      0 ≤ (star (charValue χ n) * charValue χ n).re := by
    have heq :
        (star (charValue χ n) * charValue χ n).re = ‖charValue χ n‖ ^ 2 := by
      simpa only [Complex.star_def, ← Complex.ofReal_pow, Complex.ofReal_re] using
        congrArg Complex.re (Complex.conj_mul' (charValue χ n))
    rw [heq]
    exact sq_nonneg _
  have hsingle :
      (star (charValue χ₀ n) * charValue χ₀ n).re ≤
        ∑ χ ∈ primitiveCharacters Q, (star (charValue χ n) * charValue χ n).re :=
    Finset.single_le_sum (fun χ hχ => hterm χ) hmem
  calc
    1 = (star (charValue χ₀ n) * charValue χ₀ n).re := by simp [hval]
    _ ≤ ∑ χ ∈ primitiveCharacters Q, (star (charValue χ n) * charValue χ n).re := hsingle
    _ = (∑ χ ∈ primitiveCharacters Q,
          star (charValue χ n) * charValue χ n).re := by simp

lemma selectedKernel_diag_norm_ge_inverse {G : Blueprint.Graph.PrimeGroups}
    {J ell m : ℕ} (ν : Pattern G J ell m) (block : G.BigGroup → Bool)
    (side : Bool) (Q : ℕ) (h ξ : ℝ) (d : ℕ) (hQ : 1 ≤ Q) (hξ : 0 < ξ)
    (hret : ξ ≤ selectedCellMass ν block side h (cell h d)) :
    (selectedCellMass ν block side h (cell h d))⁻¹ ≤
      ‖selectedKernel ν block side Q h ξ d d‖ := by
  let v := selectedCellMass ν block side h (cell h d)
  have hpos : 0 < v := hξ.trans_le hret
  have hs : 1 ≤ (∑ χ ∈ primitiveCharacters Q,
      star (charValue χ d) * charValue χ d).re := diagonalCharacterSum_re_ge_one hQ d
  have hnorm : 1 ≤ ‖∑ χ ∈ primitiveCharacters Q,
      star (charValue χ d) * charValue χ d‖ := hs.trans (Complex.re_le_norm _)
  have hK : selectedKernel ν block side Q h ξ d d =
      (v : ℂ)⁻¹ * ∑ χ ∈ primitiveCharacters Q,
        star (charValue χ d) * charValue χ d := by
    simp [selectedKernel, v, hret]
  change v⁻¹ ≤ ‖selectedKernel ν block side Q h ξ d d‖
  calc
    v⁻¹ = v⁻¹ * 1 := by ring
    _ ≤ v⁻¹ * ‖∑ χ ∈ primitiveCharacters Q,
        star (charValue χ d) * charValue χ d‖ :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hpos.le)
    _ = ‖selectedKernel ν block side Q h ξ d d‖ := by
      rw [hK, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

theorem comparisonCellCostTask_proof : P5Core.ComparisonCellCostTask := by
  intro G J ell m Q ν block h ξ hQ hξ hc a₀ u
  by_cases hA : ξ ≤ selectedCellMass ν block false h
      (cell h (selectedProduct ν block false u))
  · by_cases hB : ξ ≤ selectedCellMass ν block true h
        (cell h (selectedProduct ν block true u))
    · have hcoeff := hc (extendAux a₀ u) (extendAux a₀ u) u
      rw [selectedEndpoint_extendAux ν block false a₀ u,
        selectedEndpoint_extendAux ν block true a₀ u] at hcoeff
      have hposA : 0 < selectedCellMass ν block false h
          (cell h (selectedProduct ν block false u)) := hξ.trans_le hA
      have hposB : 0 < selectedCellMass ν block true h
          (cell h (selectedProduct ν block true u)) := hξ.trans_le hB
      have hIA_norm :
          ‖P5Core.comparisonCellInverse ν block false h ξ
              (cell h (selectedProduct ν block false u))‖ =
            (selectedCellMass ν block false h
              (cell h (selectedProduct ν block false u)))⁻¹ := by
        rw [show P5Core.comparisonCellInverse ν block false h ξ
              (cell h (selectedProduct ν block false u)) =
              (selectedCellMass ν block false h
                (cell h (selectedProduct ν block false u)) : ℂ)⁻¹ by
            simp [P5Core.comparisonCellInverse, hA],
          norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hposA]
      have hIB_norm :
          ‖P5Core.comparisonCellInverse ν block true h ξ
              (cell h (selectedProduct ν block true u))‖ =
            (selectedCellMass ν block true h
              (cell h (selectedProduct ν block true u)))⁻¹ := by
        rw [show P5Core.comparisonCellInverse ν block true h ξ
              (cell h (selectedProduct ν block true u)) =
              (selectedCellMass ν block true h
                (cell h (selectedProduct ν block true u)) : ℂ)⁻¹ by
            simp [P5Core.comparisonCellInverse, hB],
          norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hposB]
      have hKA := selectedKernel_diag_norm_ge_inverse ν block false Q h ξ
        (selectedProduct ν block false u) hQ hξ hA
      have hKB := selectedKernel_diag_norm_ge_inverse ν block true Q h ξ
        (selectedProduct ν block true u) hQ hξ hB
      have hIA :
          ‖P5Core.comparisonCellInverse ν block false h ξ
              (cell h (selectedProduct ν block false u))‖ ≤
            ‖selectedKernel ν block false Q h ξ
              (selectedProduct ν block false u) (selectedProduct ν block false u)‖ := by
        rw [hIA_norm]
        exact hKA
      have hIB :
          ‖P5Core.comparisonCellInverse ν block true h ξ
              (cell h (selectedProduct ν block true u))‖ ≤
            ‖selectedKernel ν block true Q h ξ
              (selectedProduct ν block true u) (selectedProduct ν block true u)‖ := by
        rw [hIB_norm]
        exact hKB
      calc
        _ = ‖P5Core.comparisonCellInverse ν block false h ξ
                (cell h (selectedProduct ν block false u))‖ *
              ‖P5Core.comparisonCellInverse ν block true h ξ
                (cell h (selectedProduct ν block true u))‖ := norm_mul _ _
        _ ≤ ‖selectedKernel ν block false Q h ξ
                (selectedProduct ν block false u) (selectedProduct ν block false u)‖ *
              ‖selectedKernel ν block true Q h ξ
                (selectedProduct ν block true u) (selectedProduct ν block true u)‖ :=
          mul_le_mul hIA hIB (norm_nonneg _) (norm_nonneg _)
        _ = ‖P5Core.comparisonSign ν *
              selectedKernel ν block false Q h ξ
                (selectedProduct ν block false u) (selectedProduct ν block false u) *
              selectedKernel ν block true Q h ξ
                (selectedProduct ν block true u) (selectedProduct ν block true u)‖ := by
          rw [norm_mul, norm_mul, P5Core.comparisonSign_norm]
          ring
        _ = ‖ν.coefficient (extendAux a₀ u) (extendAux a₀ u) u‖ := by
          rw [← hcoeff]
        _ ≤ P5Core.patternCost ν :=
          P5Core.coefficient_norm_le_patternCost ν _ _ _
    · have hzero : P5Core.comparisonCellInverse ν block true h ξ
          (cell h (selectedProduct ν block true u)) = 0 := by
        simp [P5Core.comparisonCellInverse, hB]
      rw [hzero]
      simp only [mul_zero, norm_zero]
      exact P5Core.patternCost_nonneg ν
  · have hzero : P5Core.comparisonCellInverse ν block false h ξ
        (cell h (selectedProduct ν block false u)) = 0 := by
      simp [P5Core.comparisonCellInverse, hA]
    rw [hzero]
    simp only [zero_mul, norm_zero]
    exact P5Core.patternCost_nonneg ν

end Erdos821.P5Cell
