import Erdos821.P5MarkedEnergy.BoxIdentity
import Erdos821.P5MarkedEnergy.Weights

/-! Weighted mean values of box polynomials. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked
open Blueprint.Analytic

def boxF (f1 f2 f3 f4 : ℕ → ℂ) : Fin 4 → ℕ → ℂ := ![f1, f2, f3, f4]
def boxI (β : Q4) : Fin 4 → ℕ := ![β.1, β.2.1, β.2.2.1, β.2.2.2]

theorem sum_boxI (β : Q4) : ∑ j, boxI β j = bsize β := by
  simp [boxI, Fin.sum_univ_four, bsize]

theorem boxPoly_eq_dp (f1 f2 f3 f4 : ℕ → ℂ) (β : Q4) (τ : ℝ) :
    boxPoly f1 f2 f3 f4 β τ =
      dp (Finset.Icc 1 (2 ^ (bsize β + 4))) (coll (boxF f1 f2 f3 f4) (boxI β)) τ := by
  have h := prod_hpoly_eq (boxF f1 f2 f3 f4) (boxI β) τ
  rw [Fin.prod_univ_four, sum_boxI] at h
  rw [← h]
  simp [boxPoly, boxF, boxI]

theorem continuous_boxPoly (f1 f2 f3 f4 : ℕ → ℂ) (β : Q4) : Continuous (boxPoly f1 f2 f3 f4 β) := by
  unfold boxPoly
  exact (((continuous_hpoly _ _).mul (continuous_hpoly _ _)).mul (continuous_hpoly _ _)).mul
    (continuous_hpoly _ _)

theorem norm_boxPoly_le (f1 f2 f3 f4 : ℕ → ℂ) (β : Q4) (B1 B2 B3 B4 : ℝ)
    (h1 : ∀ m ∈ dyad β.1, ‖f1 m‖ ≤ B1) (h2 : ∀ m ∈ dyad β.2.1, ‖f2 m‖ ≤ B2)
    (h3 : ∀ m ∈ dyad β.2.2.1, ‖f3 m‖ ≤ B3) (h4 : ∀ m ∈ dyad β.2.2.2, ‖f4 m‖ ≤ B4) (τ : ℝ) :
    ‖boxPoly f1 f2 f3 f4 β τ‖ ≤ B1 * B2 * B3 * B4 := by
  unfold boxPoly
  rw [norm_mul, norm_mul, norm_mul]
  have e1 := norm_hpoly_le f1 _ B1 h1 τ
  have e2 := norm_hpoly_le f2 _ B2 h2 τ
  have e3 := norm_hpoly_le f3 _ B3 h3 τ
  have e4 := norm_hpoly_le f4 _ B4 h4 τ
  have n2 := norm_nonneg (hpoly f2 β.2.1 τ)
  have n3 := norm_nonneg (hpoly f3 β.2.2.1 τ)
  have n4 := norm_nonneg (hpoly f4 β.2.2.2 τ)
  have b1 : 0 ≤ B1 := (norm_nonneg _).trans e1
  have b2 : 0 ≤ B2 := n2.trans e2
  have b3 : 0 ≤ B3 := n3.trans e3
  gcongr

/-- Weighted mean value of a box polynomial, uniform in the shift. -/
theorem box_wmv : ∃ K c : ℝ, 0 < K ∧ 0 ≤ c ∧
    ∀ (f1 f2 f3 f4 : ℕ → ℂ) (β : Q4) (B1 B2 B3 B4 h c' : ℝ),
      0 ≤ B1 → 0 ≤ B2 → 0 ≤ B3 → 0 ≤ B4 →
      (∀ m ∈ dyad β.1, ‖f1 m‖ ≤ B1) → (∀ m ∈ dyad β.2.1, ‖f2 m‖ ≤ B2) →
      (∀ m ∈ dyad β.2.2.1, ‖f3 m‖ ≤ B3) → (∀ m ∈ dyad β.2.2.2, ‖f4 m‖ ≤ B4) → 0 < h →
      Integrable (fun t => wt h t * ‖boxPoly f1 f2 f3 f4 β (t + c')‖ ^ 2) ∧
      ∫ t, wt h t * ‖boxPoly f1 f2 f3 f4 β (t + c')‖ ^ 2 ≤
        K * (1 / h + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) *
          ((B1 * B2 * B3 * B4) ^ 2 * Real.log (2 * 2 ^ (bsize β + 4)) ^ c / 2 ^ bsize β) := by
  obtain ⟨KW, hKW, hW⟩ := weighted_mean_value
  obtain ⟨c, K4, hc, hK4, hcoll⟩ := sqNorm_coll_le 4
  refine ⟨KW * K4, c, by positivity, hc, ?_⟩
  intro f1 f2 f3 f4 β B1 B2 B3 B4 h c' hB1 hB2 hB3 hB4 h1 h2 h3 h4 hh
  have hsq := hcoll (boxF f1 f2 f3 f4) (boxI β) ![B1, B2, B3, B4]
    (fun j => by fin_cases j <;> simp [hB1, hB2, hB3, hB4])
    (fun j => by fin_cases j <;> simpa [boxF, boxI] using ‹_›)
  rw [Fin.prod_univ_four, sum_boxI] at hsq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons] at hsq
  have hw := hW (2 ^ (bsize β + 4)) (coll (boxF f1 f2 f3 f4) (boxI β)) h c' hh
  simp_rw [boxPoly_eq_dp]
  refine ⟨hw.1, hw.2.trans ?_⟩
  push_cast
  have hpos : 0 ≤ (1 / h + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) := by
    have : 0 ≤ Real.log (2 * 2 ^ (bsize β + 4)) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ 2 ^ (bsize β + 4) := one_le_pow₀ (by norm_num)
      linarith)
    positivity
  calc KW * (1 / h + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) *
        sqNorm (Finset.Icc 1 (2 ^ (bsize β + 4))) (coll (boxF f1 f2 f3 f4) (boxI β))
      ≤ KW * (1 / h + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) *
        (K4 * (B1 * B2 * B3 * B4) ^ 2 * Real.log (2 * 2 ^ (bsize β + 4)) ^ c / 2 ^ bsize β) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

end Erdos821.P5Marked
