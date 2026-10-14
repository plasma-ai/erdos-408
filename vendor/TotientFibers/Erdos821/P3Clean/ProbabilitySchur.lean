import Erdos821.S2.CountableSchur

/-! Schur control by a finite mixture of reversible probability transition laws. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

theorem normBound_probability_mixture {α δ : Type*} [Fintype α] [Fintype δ]
    (mass : α → ℝ) (R : δ → α → α → ℝ) (amplitude : δ → ℝ) (K : α → α → ℂ)
    (hm : ∀ a, 0 ≤ mass a) (hR : ∀ d a b, 0 ≤ R d a b)
    (ha : ∀ d, 0 ≤ amplitude d)
    (hrow : ∀ d a, (∑ b, R d a b) = 1)
    (hrev : ∀ d a b, mass a * R d a b = mass b * R d b a)
    (hK : ∀ a b, ‖K a b‖ ≤ ∑ d, amplitude d * R d a b) :
    NormBound mass K (∑ d, amplitude d) := by
  have hC : 0 ≤ ∑ d, amplitude d := Finset.sum_nonneg (fun d _ => ha d)
  have hb := finite_support_schur mass (fun _ => 1) K
    (∑ d, amplitude d) (∑ d, amplitude d) hm (fun _ => zero_lt_one) hC hC
  have hr (a : α) (t : Finset α) : ∑ b ∈ t, ‖K a b‖ * (1 : ℝ) ≤ (∑ d, amplitude d) * 1 := by
    simp only [mul_one]
    calc
      _ ≤ ∑ b ∈ t, ∑ d, amplitude d * R d a b := Finset.sum_le_sum (fun b _ => hK a b)
      _ ≤ ∑ b, ∑ d, amplitude d * R d a b :=
        Finset.sum_le_univ_sum_of_nonneg (fun b => Finset.sum_nonneg (fun d _ => mul_nonneg (ha d) (hR d a b)))
      _ = _ := by rw [Finset.sum_comm]; simp only [← Finset.mul_sum, hrow, mul_one]
  have hc (b : α) (s : Finset α) :
      ∑ a ∈ s, mass a * ‖K a b‖ * 1 ≤ (∑ d, amplitude d) * mass b * 1 := by
    simp only [mul_one]
    calc
      _ ≤ ∑ a ∈ s, mass a * ∑ d, amplitude d * R d a b :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hK a b) (hm a))
      _ ≤ ∑ a, mass a * ∑ d, amplitude d * R d a b :=
        Finset.sum_le_univ_sum_of_nonneg (fun a => mul_nonneg (hm a)
          (Finset.sum_nonneg (fun d _ => mul_nonneg (ha d) (hR d a b))))
      _ = ∑ d, amplitude d * (mass b * ∑ a, R d b a) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro a _
        calc
          _ = amplitude d * (mass a * R d a b) := by ring
          _ = _ := by rw [hrev]
      _ = _ := by simp only [hrow, mul_one, Finset.sum_mul]
  simpa only [Real.sqrt_mul_self hC] using hb hr hc


end Erdos821.P3Clean
