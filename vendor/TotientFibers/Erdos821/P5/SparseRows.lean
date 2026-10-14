import Erdos821.P5.HarmonicRows
import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Cardinality slack absorbs the square-root error of the Gram kernel. -/
theorem sparse_card_sqrt_le (Y U : ℝ) (E : Finset ℤ) (hY : 1 ≤ Y)
    (hU : Y ^ (0.6 : ℝ) ≤ U) (hE : (E.card : ℝ) ≤ Y ^ (0.05 : ℝ)) :
    (E.card : ℝ) * Real.sqrt Y ≤ U := by
  have hYpos : 0 < Y := by linarith
  calc
    _ ≤ Y ^ (0.05 : ℝ) * Real.sqrt Y :=
      mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg _)
    _ = Y ^ ((0.05 : ℝ) + 1 / 2) := by rw [Real.sqrt_eq_rpow, Real.rpow_add hYpos]
    _ ≤ Y ^ (0.6 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
    _ ≤ U := hU

/-- The full-interval Gram estimate has logarithmic row sums for samples in integer cells. -/
theorem sparse_gram_rows (K Y U : ℝ) (E : Finset ℤ) (t : ℤ → ℝ)
    (hK : 0 < K) (hY : Real.exp 1 ≤ Y) (hU : Y ^ (0.6 : ℝ) ≤ U)
    (hcard : (E.card : ℝ) ≤ Y ^ (0.05 : ℝ))
    (hE : ∀ j ∈ E, |(j : ℝ)| ≤ Y)
    (hcell : ∀ j ∈ E, (j : ℝ) ≤ t j ∧ t j ≤ (j : ℝ) + 1)
    (hgram : ∀ z : ℝ, |z| ≤ 4 * Y →
      ‖dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) z‖ ≤
        K * (U / (1 + |z|) + Real.sqrt (4 * Y))) :
    ∀ j ∈ E, ∑ k ∈ E,
      ‖dp (Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊) (fun _ => 1) (t j - t k)‖ ≤
        20 * K * U * Real.log (2 * Y) := by
  have hY1 : 1 ≤ Y := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    exact h.trans hY
  have hYpos : 0 < Y := by linarith
  have hU1 : 1 ≤ U := (Real.one_le_rpow hY1 (by norm_num : (0 : ℝ) ≤ 0.6)).trans hU
  have hUpos : 0 < U := by linarith
  have hlogY : 1 ≤ Real.log Y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hY
  have hlog : 1 ≤ Real.log (2 * Y) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne']
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]
  have htime (j : ℤ) (hj : j ∈ E) : |t j| ≤ Y + 1 := by
    obtain ⟨hjlo, hjhi⟩ := abs_le.mp (hE j hj)
    apply abs_le.mpr
    constructor <;> linarith [(hcell j hj).1, (hcell j hj).2]
  have hdiff (j k : ℤ) (hj : j ∈ E) (hk : k ∈ E) : |t j - t k| ≤ 4 * Y := by
    have h := abs_add_le (t j) (-(t k))
    rw [abs_neg] at h
    change |t j - t k| ≤ |t j| + |t k| at h
    linarith [htime j hj, htime k hk]
  have hsqrt : Real.sqrt (4 * Y) = 2 * Real.sqrt Y := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hsmall := sparse_card_sqrt_le Y U E hY1 hU hcard
  intro j hj
  have hrecip : (∑ k ∈ E, 1 / (1 + |t j - t k|)) ≤ 16 * Real.log (2 * Y) := by
    calc
      _ ≤ ∑ k ∈ E, 2 / (1 + |(j : ℝ) - k|) := Finset.sum_le_sum
        (fun k hk => reciprocal_cell_distance j k t (hcell j hj) (hcell k hk))
      _ = 2 * ∑ k ∈ E, 1 / (1 + |(j : ℝ) - k|) := by
        simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (integer_harmonic_row_log E j Y hY (hE j hj) hE)
          (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith only [h]
  have hrecipU := mul_le_mul_of_nonneg_left hrecip hUpos.le
  have hsmall4 : (E.card : ℝ) * Real.sqrt (4 * Y) ≤ 2 * U := by
    rw [hsqrt]
    nlinarith only [hsmall]
  calc
    _ ≤ ∑ k ∈ E, K * (U / (1 + |t j - t k|) + Real.sqrt (4 * Y)) :=
      Finset.sum_le_sum (fun k hk => hgram _ (hdiff j k hj hk))
    _ = K * (U * (∑ k ∈ E, 1 / (1 + |t j - t k|)) +
        (E.card : ℝ) * Real.sqrt (4 * Y)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
    _ ≤ K * (16 * U * Real.log (2 * Y) + 2 * U) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hrecipU, hsmall4]) hK.le
    _ ≤ _ := by
      have hscale := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * U by positivity)
      have h : 16 * U * Real.log (2 * Y) + 2 * U ≤ 20 * U * Real.log (2 * Y) := by
        nlinarith only [hscale, hUpos]
      have h' := mul_le_mul_of_nonneg_left h hK.le
      convert h' using 1 <;> ring

end Erdos821.P5Core
