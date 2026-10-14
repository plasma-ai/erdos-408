import Erdos821.P5.PartialSummation
import Erdos821.P5.Tasks
import Erdos821.Classical.DerivativeTests

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The log-phase task supplies the normalized cancellation on each character
class. The factor `1/q` is retained for summing the classes later. -/
theorem weighted_log_phase_of_task (hlog : LogPhaseSumTask) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (N lo hi u : ℝ) (q a : ℕ),
        0 < N → x ^ (τ / 2) ≤ N → N ≤ lo → lo ≤ hi → hi ≤ 2 * N →
        1 ≤ q → a < q → 1 ≤ |u| → |u| ≤ x ^ (2 : ℕ) →
        ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
          mellin (q * (y : ℝ) + a) u / ((q * (y : ℝ) + a : ℝ) : ℂ)‖ ≤
            (K / q) * (|u|⁻¹ + N ^ (-δ)) := by
  obtain ⟨δ, K, hδ, hK, hevent⟩ := hlog Blueprint.DerivativeTests_proof τ hτ
  refine ⟨δ, K, hδ, hK, hevent.mono ?_⟩
  intro x hx N lo hi u q a hNpos hN hloN hlohi hhi hq haq hu hux
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  let E := |u|⁻¹ + N ^ (-δ)
  let H := K * N * E
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hden : (q : ℝ) * N ≤ (a : ℝ) + q * (⌈lo⌉ : ℤ) := by
    have hloceil : lo ≤ ((⌈lo⌉ : ℤ) : ℝ) := Int.le_ceil lo
    have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    have hmul := mul_le_mul_of_nonneg_left (hloN.trans hloceil) hqpos.le
    linarith
  have hdenpos : 0 < (a : ℝ) + q * (⌈lo⌉ : ℤ) := (mul_pos hqpos hNpos).trans_le hden
  have hpref (c : ℤ) (hc₁ : ⌈lo⌉ ≤ c) (hc₂ : c ≤ ⌊hi⌋) :
      ‖∑ y ∈ Finset.Icc ⌈lo⌉ c, mellin (q * (y : ℝ) + a) u‖ ≤ H := by
    have hlo_c : lo ≤ (c : ℝ) := Int.ceil_le.mp hc₁
    have hc_hi : (c : ℝ) ≤ hi := Int.le_floor.mp hc₂
    have hc_2N : (c : ℝ) ≤ 2 * N := hc_hi.trans hhi
    simpa only [Int.floor_intCast] using
      hx N lo (c : ℝ) u q a hN hloN hlo_c hc_2N hq haq hu hux
  have hweighted := integer_reciprocal_weight_sum_bound ⌈lo⌉ ⌊hi⌋ (a : ℝ) (q : ℝ) H
    (fun y => mellin (q * (y : ℝ) + a) u) hdenpos hqpos.le hH hpref
  calc
    _ = ‖∑ y ∈ Finset.Icc ⌈lo⌉ ⌊hi⌋,
        mellin (q * (y : ℝ) + a) u / (((a : ℝ) + q * (y : ℝ) : ℝ) : ℂ)‖ := by
      simp only [add_comm]
    _ ≤ H / ((a : ℝ) + q * (⌈lo⌉ : ℤ)) := hweighted
    _ ≤ H / ((q : ℝ) * N) :=
      div_le_div_of_nonneg_left hH (mul_pos hqpos hNpos) hden
    _ = (K / q) * (|u|⁻¹ + N ^ (-δ)) := by
      dsimp [H, E]
      field_simp

end Erdos821.P5Core
