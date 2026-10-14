import Erdos821.P5.WeightedLog

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- A log-phase progression may begin just below its natural scale. That
piece contains at most one integer, with reciprocal mass at most `1/(q*N)`. -/
theorem weighted_log_phase_extended_of_task (hlog : LogPhaseSumTask) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (N lo hi u : ℝ) (q a : ℕ),
        0 < N → x ^ (τ / 2) ≤ N → N - 1 ≤ lo → lo ≤ hi → hi ≤ 2 * N →
        1 ≤ q → a < q → (q : ℝ) * N ≤ q * lo + a →
        1 ≤ |u| → |u| ≤ x ^ (2 : ℕ) →
        ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
          mellin (q * (y : ℝ) + a) u / ((q * (y : ℝ) + a : ℝ) : ℂ)‖ ≤
            (K / q) * (|u|⁻¹ + N ^ (-δ)) + ((q : ℝ) * N)⁻¹ := by
  classical
  obtain ⟨δ, K, hδ, hK, hevent⟩ := weighted_log_phase_of_task hlog τ hτ
  refine ⟨δ, K, hδ, hK, hevent.mono ?_⟩
  intro x hx N lo hi u q a hNpos hN hlo hlohi hhi hq haq hbase hu hux
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hqN : 0 < (q : ℝ) * N := mul_pos hqpos hNpos
  let s := Finset.Icc ⌈lo⌉ ⌊hi⌋
  let f : ℤ → ℂ := fun y =>
    mellin (q * (y : ℝ) + a) u / ((q * (y : ℝ) + a : ℝ) : ℂ)
  let p : ℤ → Prop := fun y => N ≤ (y : ℝ)
  have hs (y : ℤ) (hy : y ∈ s) : lo ≤ (y : ℝ) ∧ (y : ℝ) ≤ hi := by
    exact ⟨Int.ceil_le.mp (Finset.mem_Icc.mp hy).1, Int.le_floor.mp (Finset.mem_Icc.mp hy).2⟩
  have hhighset : s.filter p = Finset.Icc ⌈max lo N⌉ ⌊hi⌋ := by
    ext y
    simp only [s, p, Finset.mem_filter, Finset.mem_Icc, Int.ceil_le, Int.le_floor, max_le_iff]
    tauto
  have hhigh : ‖∑ y ∈ s.filter p, f y‖ ≤ (K / q) * (|u|⁻¹ + N ^ (-δ)) := by
    rw [hhighset]
    by_cases hvalid : max lo N ≤ hi
    · exact hx N (max lo N) hi u q a hNpos hN (le_max_right _ _) hvalid hhi hq haq hu hux
    · have hempty : Finset.Icc ⌈max lo N⌉ ⌊hi⌋ = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have hylo := Int.ceil_le.mp (Finset.mem_Icc.mp hy).1
        have hyhi := Int.le_floor.mp (Finset.mem_Icc.mp hy).2
        exact hvalid (hylo.trans hyhi)
      rw [hempty, Finset.sum_empty, norm_zero]
      positivity
  have hlowcard : (s.filter (fun y => ¬p y)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro y hy z hz
    have hylo := hlo.trans (hs y (Finset.mem_filter.mp hy).1).1
    have hzlo := hlo.trans (hs z (Finset.mem_filter.mp hz).1).1
    have hyhi : (y : ℝ) < N := lt_of_not_ge (Finset.mem_filter.mp hy).2
    have hzhi : (z : ℝ) < N := lt_of_not_ge (Finset.mem_filter.mp hz).2
    have hyz : (y : ℝ) < (z : ℝ) + 1 := by linarith
    have hzy : (z : ℝ) < (y : ℝ) + 1 := by linarith
    have hyz' : y < z + 1 := by exact_mod_cast hyz
    have hzy' : z < y + 1 := by exact_mod_cast hzy
    omega
  have hterm (y : ℤ) (hy : y ∈ s) : ‖f y‖ ≤ ((q : ℝ) * N)⁻¹ := by
    have hden : (q : ℝ) * N ≤ q * (y : ℝ) + a :=
      hbase.trans (by gcongr; exact (hs y hy).1)
    have hdenpos : 0 < (q : ℝ) * y + a := hqN.trans_le hden
    dsimp [f]
    rw [norm_div, norm_mellin, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenpos]
    simpa only [one_div] using one_div_le_one_div_of_le hqN hden
  have hlow : ‖∑ y ∈ s.filter (fun y => ¬p y), f y‖ ≤ ((q : ℝ) * N)⁻¹ := by
    calc
      _ ≤ ∑ y ∈ s.filter (fun y => ¬p y), ‖f y‖ := norm_sum_le _ _
      _ ≤ ∑ _y ∈ s.filter (fun y => ¬p y), ((q : ℝ) * N)⁻¹ :=
        Finset.sum_le_sum (fun y hy => hterm y (Finset.mem_filter.mp hy).1)
      _ = ((s.filter (fun y => ¬p y)).card : ℝ) * ((q : ℝ) * N)⁻¹ := by simp
      _ ≤ 1 * ((q : ℝ) * N)⁻¹ := by gcongr; exact_mod_cast hlowcard
      _ = _ := one_mul _
  have hsplit : (∑ y ∈ s, f y) = (∑ y ∈ s.filter p, f y) +
      ∑ y ∈ s.filter (fun y => ¬p y), f y := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : N ≤ (y : ℝ) <;> simp [p, h]
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hhigh hlow)

end Erdos821.P5Core
