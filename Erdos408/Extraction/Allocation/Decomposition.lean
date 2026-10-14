import Erdos408.Extraction.Defs

/-!
# The decomposition of the proxy sum

The proxy sum is `∑_w F(w) A(w + 1)`, with `|F| ≤ B_d` and `F = 0` off the
cutoff support. Inserting `1 = S + Φ_fail` (success and failure
probabilities) and `A = G - (G - A)`, `G = min(G, Λ) + (G - min(G, Λ))`, gives

  `|∑ F A| ≤ |∑ F min(G, Λ) S| + B_d Λ⁻¹ ∑ G² + B_d ∑_{bad} G + B_d ∑_{near} A Φ_fail`,

where `G - A` is supported on the candidate-square multiples ("bad") and
`G - min(G, Λ) ≤ G² / Λ`. The bad sum is bounded by Cauchy–Schwarz, and the
candidate-square multiples are counted directly.
-/

namespace Erdos408

open Finset

/-- The decomposition inequality. -/
theorem abs_sum_le_of_decomp {W : Finset ℕ} {F Aw Gt S Fl : ℕ → ℝ} {Λ Bd : ℝ}
    (Pbad Pnear : ℕ → Prop) [DecidablePred Pbad] [DecidablePred Pnear] (hBd : 0 ≤ Bd)
    (hΛ : 0 < Λ) (hF : ∀ w ∈ W, |F w| ≤ Bd) (hFz : ∀ w ∈ W, ¬ Pnear w → F w = 0)
    (hA : ∀ w ∈ W, 0 ≤ Aw w ∧ Aw w ≤ Gt w) (hAeq : ∀ w ∈ W, ¬ Pbad w → Aw w = Gt w)
    (hS : ∀ w ∈ W, 0 ≤ S w ∧ S w ≤ 1) (hSF : ∀ w ∈ W, S w + Fl w = 1)
    (hFl : ∀ w ∈ W, 0 ≤ Fl w) :
    |∑ w ∈ W, F w * Aw w| ≤ |∑ w ∈ W, F w * min (Gt w) Λ * S w| +
      Bd * (∑ w ∈ W, Gt w ^ 2) / Λ + Bd * ∑ w ∈ W with Pbad w, Gt w +
        Bd * ∑ w ∈ W with Pnear w, Aw w * Fl w := by
  have hsplit : ∑ w ∈ W, F w * Aw w = ∑ w ∈ W, F w * min (Gt w) Λ * S w +
      (∑ w ∈ W, F w * (Gt w - min (Gt w) Λ) * S w - ∑ w ∈ W, F w * (Gt w - Aw w) * S w +
        ∑ w ∈ W, F w * Aw w * Fl w) := by
    rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun w hw => ?_
    have := hSF w hw
    have : Fl w = 1 - S w := by linarith
    rw [this]
    ring
  have hG : ∀ w ∈ W, 0 ≤ Gt w := fun w hw => (hA w hw).1.trans (hA w hw).2
  have hBd' : ∀ w ∈ W, |F w| * |S w| ≤ Bd := fun w hw => by
    rw [abs_of_nonneg (hS w hw).1]
    have := hF w hw
    have := hS w hw
    nlinarith [abs_nonneg (F w)]
  -- the clipping error: `G - min(G, Λ) ≤ G² / Λ`
  have h1 : |∑ w ∈ W, F w * (Gt w - min (Gt w) Λ) * S w| ≤ Bd * (∑ w ∈ W, Gt w ^ 2) / Λ := by
    rw [mul_div_assoc, sum_div, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w hw => ?_)
    have hm : 0 ≤ Gt w - min (Gt w) Λ := sub_nonneg.2 (min_le_left _ _)
    have hq : Gt w - min (Gt w) Λ ≤ Gt w ^ 2 / Λ := by
      rcases le_total (Gt w) Λ with h | h
      · rw [min_eq_left h, sub_self]
        positivity
      · rw [min_eq_right h, le_div_iff₀ hΛ]
        nlinarith [hG w hw]
    rw [abs_mul, abs_mul, abs_of_nonneg hm]
    calc |F w| * (Gt w - min (Gt w) Λ) * |S w| = |F w| * |S w| * (Gt w - min (Gt w) Λ) := by
          ring
      _ ≤ Bd * (Gt w ^ 2 / Λ) := mul_le_mul (hBd' w hw) hq hm hBd
  -- the candidate-square error: `G - A` vanishes off the bad set
  have h2 : |∑ w ∈ W, F w * (Gt w - Aw w) * S w| ≤ Bd * ∑ w ∈ W with Pbad w, Gt w := by
    rw [sum_filter, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w hw => ?_)
    by_cases hb : Pbad w
    · simp only [hb, ↓reduceIte]
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 (hA w hw).2)]
      calc |F w| * (Gt w - Aw w) * |S w| = |F w| * |S w| * (Gt w - Aw w) := by ring
        _ ≤ Bd * Gt w := mul_le_mul (hBd' w hw) (by linarith [(hA w hw).1])
            (sub_nonneg.2 (hA w hw).2) hBd
    · simp only [hb, ↓reduceIte]
      rw [hAeq w hw hb, sub_self, mul_zero, zero_mul, abs_zero, mul_zero]
  -- the failure term vanishes off the cutoff support
  have h3 : |∑ w ∈ W, F w * Aw w * Fl w| ≤ Bd * ∑ w ∈ W with Pnear w, Aw w * Fl w := by
    rw [sum_filter, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w hw => ?_)
    by_cases hb : Pnear w
    · simp only [hb, ↓reduceIte]
      rw [abs_mul, abs_mul, abs_of_nonneg (hA w hw).1, abs_of_nonneg (hFl w hw), mul_assoc]
      exact mul_le_mul_of_nonneg_right (hF w hw) (mul_nonneg (hA w hw).1 (hFl w hw))
    · simp only [hb, ↓reduceIte]
      rw [hFz w hw hb, zero_mul, zero_mul, abs_zero, mul_zero]
  rw [hsplit]
  calc _ ≤ |∑ w ∈ W, F w * min (Gt w) Λ * S w| +
        (|∑ w ∈ W, F w * (Gt w - min (Gt w) Λ) * S w| +
          |∑ w ∈ W, F w * (Gt w - Aw w) * S w| + |∑ w ∈ W, F w * Aw w * Fl w|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by linarith

/-- Cauchy–Schwarz on a subset: `∑_{w ∈ s, P w} f ≤ √(#{P} ∑_s f²)`. -/
lemma sum_filter_le_sqrt {s : Finset ℕ} {f : ℕ → ℝ} (P : ℕ → Prop) [DecidablePred P] :
    ∑ w ∈ s with P w, f w ≤ Real.sqrt ((s.filter P).card * ∑ w ∈ s, f w ^ 2) := by
  refine Real.le_sqrt_of_sq_le ?_
  calc (∑ w ∈ s with P w, f w) ^ 2 = (∑ w ∈ s with P w, 1 * f w) ^ 2 := by simp
    _ ≤ (∑ w ∈ s with P w, (1 : ℝ) ^ 2) * ∑ w ∈ s with P w, f w ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (s.filter P).card * ∑ w ∈ s, f w ^ 2 := by
        rw [one_pow, sum_const, nsmul_eq_mul, mul_one]
        exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun w _ _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- The number of `w ∈ [1, M]` with `p² ∣ w + 1` for some `p ∈ S` is at most
`∑_{p ∈ S} (M + 1) / p²`. -/
lemma card_filter_sq_dvd_le (S : Finset ℕ) (M : ℕ) :
    (((Icc 1 M).filter fun w => ∃ p ∈ S, p * p ∣ w + 1).card : ℝ) ≤
      ∑ p ∈ S, ((M : ℝ) + 1) / (p * p) := by
  have hsub : (Icc 1 M).filter (fun w => ∃ p ∈ S, p * p ∣ w + 1) ⊆
      S.biUnion fun p => (Icc 1 M).filter fun w => p * p ∣ w + 1 := by
    intro w hw
    obtain ⟨hw, p, hp, hdvd⟩ := mem_filter.1 hw
    exact mem_biUnion.2 ⟨p, hp, mem_filter.2 ⟨hw, hdvd⟩⟩
  refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
  push_cast
  refine sum_le_sum fun p _ => ?_
  -- shift `w ↦ w + 1` into `(0, M + 1]`
  have hcard : ((Icc 1 M).filter fun w => p * p ∣ w + 1).card ≤ (M + 1) / (p * p) := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div]
    refine card_le_card_of_injOn (· + 1) (fun w hw => ?_) fun a _ b _ h => by simpa using h
    obtain ⟨hw, hdvd⟩ := mem_filter.1 (mem_coe.1 hw)
    rw [mem_Icc] at hw
    exact mem_coe.2 (mem_filter.2 ⟨mem_Ioc.2 ⟨Nat.succ_pos w, Nat.succ_le_succ hw.2⟩, hdvd⟩)
  calc (((Icc 1 M).filter fun w => p * p ∣ w + 1).card : ℝ) ≤ ((M + 1) / (p * p) : ℕ) := by
        exact_mod_cast hcard
    _ ≤ ((M : ℝ) + 1) / (p * p) := by
        have := Nat.cast_div_le (α := ℝ) (m := M + 1) (n := p * p)
        push_cast at this
        exact this

end Erdos408
