import Mathlib

/-! Abstract three-range integral estimate (paper §4, completion): on a time
range, a product of four continuous functions is controlled by
(i) smallness of the second factor off finitely many unit intervals,
(ii) smallness of the third factor at large times on those intervals, and
(iii) smallness of the first factor at low times. -/

noncomputable section
open MeasureTheory

namespace Erdos821.P5Marked

theorem setIntegral_indicator_Icc_le {h : ℝ → ℝ} (hh : Continuous h) (hnn : ∀ s, 0 ≤ h s)
    (a b c d : ℝ) (hab : a ≤ b) :
    ∫ s in Set.Icc c d, (Set.Icc a b).indicator h s ≤ ∫ s in a..b, h s := by
  rw [setIntegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_mono_set
  · exact (hh.integrableOn_Icc)
  · exact Filter.Eventually.of_forall (fun s => hnn s)
  · exact Filter.Eventually.of_forall Set.inter_subset_right

theorem three_range_integral
    (F1 F2 F3 F4 : ℝ → ℂ) (hc1 : Continuous F1) (hc2 : Continuous F2)
    (hc3 : Continuous F3) (hc4 : Continuous F4)
    (T0 T1 θ ε1 ε3 M4 Q3 Q14 : ℝ) (occ : Finset ℤ)
    (hT0 : 0 ≤ T0) (hT1 : 0 ≤ T1) (hθ : 0 ≤ θ) (hε3 : 0 ≤ ε3)
    (hoff : ∀ s, |s| ≤ T1 → (∀ j ∈ occ, s ∉ Set.Icc (j : ℝ) (j + 1)) → ‖F2 s‖ ≤ θ)
    (h2 : ∀ s, ‖F2 s‖ ≤ 1) (h3 : ∀ s, ‖F3 s‖ ≤ 1) (h4 : ∀ s, ‖F4 s‖ ≤ M4)
    (h3hi : ∀ s, T0 ≤ |s| → |s| ≤ T1 → ‖F3 s‖ ≤ ε3)
    (h1lo : ∀ s, |s| ≤ T0 → ‖F1 s‖ ≤ ε1)
    (hQ3 : ∫ s in (-T1)..T1, ‖F1 s * F3 s * F4 s‖ ^ 2 ≤ Q3)
    (hQ14 : ∑ j ∈ occ, ∫ s in (j : ℝ)..(j + 1), ‖F1 s * F4 s‖ ^ 2 ≤ Q14) :
    ∫ s in (-T1)..T1, ‖F1 s * F2 s * F3 s * F4 s‖ ^ 2 ≤
      θ ^ 2 * Q3 + ε3 ^ 2 * Q14 + 2 * T0 * (ε1 ^ 2 * M4 ^ 2) := by
  have hM4 : 0 ≤ M4 := (norm_nonneg _).trans (h4 0)
  set cA : ℝ := ε1 ^ 2 * M4 ^ 2 with hcA
  have hcA0 : 0 ≤ cA := by positivity
  let gA : ℝ → ℝ := (Set.Icc (-T0) T0).indicator (fun _ => cA)
  let h14 : ℝ → ℝ := fun s => ‖F1 s * F4 s‖ ^ 2
  let gB : ℝ → ℝ := fun s => ε3 ^ 2 * ∑ j ∈ occ, (Set.Icc (j : ℝ) (j + 1)).indicator h14 s
  let gC : ℝ → ℝ := fun s => θ ^ 2 * ‖F1 s * F3 s * F4 s‖ ^ 2
  let f : ℝ → ℝ := fun s => ‖F1 s * F2 s * F3 s * F4 s‖ ^ 2
  have hh14c : Continuous h14 := by fun_prop
  have hh14nn : ∀ s, 0 ≤ h14 s := fun s => by positivity
  have hgAnn : ∀ s, 0 ≤ gA s := fun s => by
    simp only [gA, Set.indicator]; split_ifs <;> positivity
  have hgBnn : ∀ s, 0 ≤ gB s := fun s => by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro j _
    simp only [Set.indicator]; split_ifs
    · exact hh14nn s
    · exact le_refl 0
  have hgCnn : ∀ s, 0 ≤ gC s := fun s => by positivity
  -- pointwise domination on the range
  have hpt : ∀ s ∈ Set.Icc (-T1) T1, f s ≤ gA s + gB s + gC s := by
    intro s hs
    have hsT1 : |s| ≤ T1 := abs_le.mpr ⟨hs.1, hs.2⟩
    have hf : f s = ‖F1 s‖ ^ 2 * ‖F2 s‖ ^ 2 * ‖F3 s‖ ^ 2 * ‖F4 s‖ ^ 2 := by
      simp only [f, norm_mul]; ring
    have n1 := norm_nonneg (F1 s); have n2 := norm_nonneg (F2 s)
    have n3 := norm_nonneg (F3 s); have n4 := norm_nonneg (F4 s)
    have h2s := h2 s; have h3s := h3 s; have h4s := h4 s
    by_cases hlo : |s| ≤ T0
    · have hA : gA s = cA :=
        Set.indicator_of_mem (show s ∈ Set.Icc (-T0) T0 from abs_le.mp hlo) _
      have h1s := h1lo s hlo
      have : f s ≤ cA := by
        rw [hf, hcA]
        have e1 : ‖F1 s‖ ^ 2 ≤ ε1 ^ 2 := pow_le_pow_left₀ n1 h1s 2
        have e2 : ‖F2 s‖ ^ 2 ≤ 1 := by nlinarith
        have e3 : ‖F3 s‖ ^ 2 ≤ 1 := by nlinarith
        have e4 : ‖F4 s‖ ^ 2 ≤ M4 ^ 2 := pow_le_pow_left₀ n4 h4s 2
        calc ‖F1 s‖ ^ 2 * ‖F2 s‖ ^ 2 * ‖F3 s‖ ^ 2 * ‖F4 s‖ ^ 2
            ≤ ε1 ^ 2 * 1 * 1 * M4 ^ 2 := by gcongr
          _ = ε1 ^ 2 * M4 ^ 2 := by ring
      linarith [hgBnn s, hgCnn s]
    · rw [not_le] at hlo
      by_cases hocc : ∃ j ∈ occ, s ∈ Set.Icc (j : ℝ) (j + 1)
      · obtain ⟨j, hj, hsj⟩ := hocc
        have h3e := h3hi s hlo.le hsT1
        have hB : ε3 ^ 2 * h14 s ≤ gB s := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (Set.Icc (j : ℝ) (j + 1)).indicator h14 s = h14 s :=
            Set.indicator_of_mem hsj _
          rw [← this]
          apply Finset.single_le_sum (f := fun j : ℤ =>
            (Set.Icc (j : ℝ) (j + 1)).indicator h14 s) _ hj
          intro i _
          simp only [Set.indicator]; split_ifs
          · exact hh14nn s
          · exact le_refl 0
        have : f s ≤ ε3 ^ 2 * h14 s := by
          rw [hf]
          simp only [h14, norm_mul]
          have e2 : ‖F2 s‖ ^ 2 ≤ 1 := by nlinarith
          have e3 : ‖F3 s‖ ^ 2 ≤ ε3 ^ 2 := pow_le_pow_left₀ n3 h3e 2
          calc ‖F1 s‖ ^ 2 * ‖F2 s‖ ^ 2 * ‖F3 s‖ ^ 2 * ‖F4 s‖ ^ 2
              ≤ ‖F1 s‖ ^ 2 * 1 * ε3 ^ 2 * ‖F4 s‖ ^ 2 := by gcongr
            _ = ε3 ^ 2 * (‖F1 s‖ * ‖F4 s‖) ^ 2 := by ring
        linarith [hgAnn s, hgCnn s]
      · simp only [not_exists, not_and] at hocc
        have h2θ := hoff s hsT1 hocc
        have : f s ≤ gC s := by
          rw [hf]
          simp only [gC, norm_mul]
          have e2 : ‖F2 s‖ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ n2 h2θ 2
          calc ‖F1 s‖ ^ 2 * ‖F2 s‖ ^ 2 * ‖F3 s‖ ^ 2 * ‖F4 s‖ ^ 2
              ≤ ‖F1 s‖ ^ 2 * θ ^ 2 * ‖F3 s‖ ^ 2 * ‖F4 s‖ ^ 2 := by gcongr
            _ = θ ^ 2 * (‖F1 s‖ * ‖F3 s‖ * ‖F4 s‖) ^ 2 := by ring
        linarith [hgAnn s, hgBnn s]
  -- integrability
  have hT : -T1 ≤ T1 := by linarith
  have hfc : Continuous f := by fun_prop
  have hgAi : IntegrableOn gA (Set.Icc (-T1) T1) :=
    (continuous_const.integrableOn_Icc).indicator measurableSet_Icc
  have hgBi : IntegrableOn gB (Set.Icc (-T1) T1) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j _
    exact (hh14c.integrableOn_Icc).indicator measurableSet_Icc
  have hgCc : Continuous gC := by fun_prop
  have hgCi : IntegrableOn gC (Set.Icc (-T1) T1) := hgCc.integrableOn_Icc
  have hconv : ∀ g : ℝ → ℝ, ∫ s in (-T1)..T1, g s = ∫ s in Set.Icc (-T1) T1, g s := by
    intro g
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
  have hmain : ∫ s in Set.Icc (-T1) T1, f s ≤ ∫ s in Set.Icc (-T1) T1, (gA s + gB s + gC s) :=
    setIntegral_mono_on hfc.integrableOn_Icc ((hgAi.add hgBi).add hgCi) measurableSet_Icc hpt
  have hsplit : ∫ s in Set.Icc (-T1) T1, (gA s + gB s + gC s) =
      (∫ s in Set.Icc (-T1) T1, gA s) + (∫ s in Set.Icc (-T1) T1, gB s) +
        ∫ s in Set.Icc (-T1) T1, gC s := by
    have hAB : IntegrableOn (fun s => gA s + gB s) (Set.Icc (-T1) T1) := hgAi.add hgBi
    rw [integral_add hAB hgCi, integral_add hgAi hgBi]
  rw [hsplit] at hmain
  have hA : ∫ s in Set.Icc (-T1) T1, gA s ≤ 2 * T0 * cA := by
    simp only [gA]
    rw [setIntegral_indicator measurableSet_Icc]
    calc ∫ s in Set.Icc (-T1) T1 ∩ Set.Icc (-T0) T0, cA
        ≤ ∫ s in Set.Icc (-T0) T0, cA := by
          apply setIntegral_mono_set (continuous_const.integrableOn_Icc)
            (Filter.Eventually.of_forall (fun _ => hcA0))
            (Filter.Eventually.of_forall Set.inter_subset_right)
      _ = 2 * T0 * cA := by
          rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
          ring
  have hB : ∫ s in Set.Icc (-T1) T1, gB s ≤ ε3 ^ 2 * Q14 := by
    simp only [gB]
    rw [integral_const_mul, integral_finsetSum]
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine le_trans (Finset.sum_le_sum fun j _ => ?_) hQ14
      exact setIntegral_indicator_Icc_le hh14c hh14nn _ _ _ _ (by linarith)
    · intro j _
      exact (hh14c.integrableOn_Icc).indicator measurableSet_Icc
  have hC : ∫ s in Set.Icc (-T1) T1, gC s ≤ θ ^ 2 * Q3 := by
    simp only [gC]
    rw [integral_const_mul, ← hconv]
    exact mul_le_mul_of_nonneg_left hQ3 (by positivity)
  rw [hconv]
  change ∫ s in Set.Icc (-T1) T1, f s ≤ _
  linarith

end Erdos821.P5Marked
