import Erdos821.P4Probe.Family
import Erdos821.P4Char.Basic

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma selectedKernel_bound {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (Q : ℕ) (h ξ : ℝ)
    (hξ : 0 < ξ) (D X : ℕ) :
    ‖selectedKernel ν block side Q h ξ D X‖ ≤ (Q : ℝ) ^ 2 / ξ := by
  let v := selectedCellMass ν block side h (Blueprint.Analytic.cell h X)
  have hs : ‖∑ χ ∈ Blueprint.Analytic.primitiveCharacters Q,
      star (Blueprint.Analytic.charValue χ D) * Blueprint.Analytic.charValue χ X‖ ≤
      (Q : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ χ ∈ Blueprint.Analytic.primitiveCharacters Q,
          ‖star (Blueprint.Analytic.charValue χ D) * Blueprint.Analytic.charValue χ X‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _χ ∈ Blueprint.Analytic.primitiveCharacters Q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul, norm_star]
        simpa using mul_le_mul (Erdos821.P4Char.norm_part Q χ D)
          (Erdos821.P4Char.norm_part Q χ X) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ ≤ (Q : ℝ) ^ 2 := by
        simpa using (Nat.cast_le (α := ℝ)).mpr (Erdos821.P4Char.count_part Q)
  unfold selectedKernel
  dsimp only
  split_ifs with hc
  · have hv : 0 < v := hξ.trans_le hc.2
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hv]
    calc
      _ ≤ v⁻¹ * (Q : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hv.le)
      _ ≤ ξ⁻¹ * (Q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (inv_le_inv₀ hv hξ |>.mpr hc.2) (sq_nonneg _)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

lemma signedPattern_bound {P : PrimeGroups} {J ell m : ℕ} (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ) (hξ : 0 < ξ)
    (c : ProbeChoice P m block) (a b : P.BigLabels (J + ell)) (u : P.BigAux J) :
    ‖(signedPattern hj block Q h ξ c).coefficient a b u‖ ≤
      ((Q : ℝ) ^ 2 / ξ) ^ 2 := by
  dsimp [signedPattern]
  rw [norm_mul, norm_mul, norm_neg, norm_pow]
  norm_num only [norm_neg, norm_one, one_pow, one_mul]
  have hb : 0 ≤ (Q : ℝ) ^ 2 / ξ := by positivity
  simpa [pow_two] using mul_le_mul
    (selectedKernel_bound (choiceBase hj c.val) block false Q h ξ hξ _ _)
    (selectedKernel_bound (choiceBase hj c.val) block true Q h ξ hξ _ _)
    (norm_nonneg _) hb

lemma probeChoice_card_le (P : PrimeGroups) (m : ℕ) (block : P.BigGroup → Bool) :
    Fintype.card (ProbeChoice P m block) ≤ 2 ^ (m * Fintype.card P.BigGroup) := by
  calc
    _ ≤ Fintype.card (P.BigGroup → Finset (Fin m)) := Fintype.card_subtype_le _
    _ = _ := by simp [Fintype.card_pi, ← pow_mul]

lemma probeFamily_count_le (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hj : m ≤ J) (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ) :
    (probeFamily F P J m hj block Q h ξ).count ≤
      2 ^ (m * Fintype.card P.BigGroup) + 1 := by
  simpa [probeFamily, Fintype.card_option] using
    Nat.add_le_add_right (probeChoice_card_le P m block) 1

lemma sSup_range_le_nonneg {α : Type*} (f : α → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a, f a ≤ C) : sSup (Set.range f) ≤ C := by
  rcases (Set.range f).eq_empty_or_nonempty with he | hn
  · simp [he, hC]
  · exact csSup_le hn (by rintro _ ⟨a, rfl⟩; exact hf a)

lemma probeFamily_patternMass_le (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hj : m ≤ J) (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ) (hξ : 0 < ξ) :
    ((probeFamily F P J m hj block Q h ξ).model 1 0).patternMass ≤
      ((2 : ℝ) ^ (m * Fintype.card P.BigGroup) + 1) *
        max 1 (((Q : ℝ) ^ 2 / ξ) ^ 2) := by
  let C : ℝ := max 1 (((Q : ℝ) ^ 2 / ξ) ^ 2)
  have hC : 0 ≤ C := le_trans (by norm_num) (le_max_left ..)
  have hp (v : Fin (probeFamily F P J m hj block Q h ξ).count)
      (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
      ‖((probeFamily F P J m hj block Q h ξ).pattern v).coefficient a b u‖ ≤ C := by
    dsimp [probeFamily]
    split
    · simp only [rawPattern, norm_one]
      exact le_max_left ..
    · exact (signedPattern_bound hj block Q h ξ hξ _ a b u).trans (le_max_right ..)
  calc
    _ ≤ ∑ _v : Fin (probeFamily F P J m hj block Q h ξ).count, C := by
      apply Finset.sum_le_sum
      intro v _
      exact sSup_range_le_nonneg _ C hC (fun z => hp v z.1 z.2.1 z.2.2)
    _ = ((probeFamily F P J m hj block Q h ξ).count : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast probeFamily_count_le F P J m hj block Q h ξ) hC

end
end Erdos821.P4Probe
