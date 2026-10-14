import Erdos821.P5.EndpointBounds
import Erdos821.P5.GroupFreeBounds
import Erdos821.P5.ProgressionIntervals
import Erdos821.Classical.DivisorMoments

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem divisor_fourth_count_nonneg_exponent :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧ ∀ Y : ℝ, 1 ≤ Y →
      (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ 4) ≤
        K * Y * Real.log (2 * Y) ^ c := by
  obtain ⟨c₀, K, hK, hm⟩ := Blueprint.DivisorMoments_proof 4
  let c := max c₀ 0
  let M := max 1 (Real.log 2 ^ c₀)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  refine ⟨c, K * M, le_max_right _ _, mul_pos hK hMpos, ?_⟩
  intro Y hY
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 * Y) := Real.log_le_log (by norm_num) (by linarith)
  have hlogpos : 0 < Real.log (2 * Y) := hlog2.trans_le hlog
  have hpow : Real.log (2 * Y) ^ c₀ ≤ M * Real.log (2 * Y) ^ c := by
    by_cases hc : 0 ≤ c₀
    · have heq : c = c₀ := max_eq_left hc
      rw [heq]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hlogpos.le _) hM1
    · have hc₀ : c₀ ≤ 0 := le_of_not_ge hc
      have heq : c = 0 := max_eq_right hc₀
      rw [heq, Real.rpow_zero, mul_one]
      exact (Real.rpow_le_rpow_of_nonpos hlog2 hlog hc₀).trans (le_max_right _ _)
  calc
    _ ≤ K * Y * Real.log (2 * Y) ^ c₀ := (hm Y hY).2
    _ ≤ K * Y * (M * Real.log (2 * Y) ^ c) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- The endpoint square sum on multiples of a supported physical-list product.
Both the logarithmic exponent and constant are independent of that product. -/
theorem endpoint_square_sum_multiples :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
      ∀ (G : PrimeGroups) (x C τ η X : ℝ) (E : Endpoint) (D : ℕ),
        1 ≤ L x → EndpointBound x C τ η E → 1 ≤ D → (D : ℝ) ≤ X →
        D.primeFactors ⊆ Finset.univ.biUnion G.primes →
        (∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (fun n => D ∣ n),
          ‖endpoint G x E n‖ ^ 2) ≤
            K * (X / D) * L x ^ (4 * C) * Real.log (4 * X / D) ^ c := by
  classical
  obtain ⟨c, K, hc, hK, hm⟩ := divisor_fourth_count_nonneg_exponent
  refine ⟨c, 2 * K, hc, by positivity, ?_⟩
  intro G x C τ η X E D hL hE hD hDX hprimes
  have hDpos : 0 < D := by omega
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hXpos : 0 < X := hDR.trans_le hDX
  have hU1 : 1 ≤ X / (D : ℝ) := (le_div_iff₀ hDR).mpr (by simpa using hDX)
  let Y := 2 * X / D
  let I := Finset.Icc ⌈X / (D : ℝ)⌉₊ ⌊Y⌋₊
  have hY1 : 1 ≤ Y := by dsimp [Y]; rw [mul_div_assoc]; linarith
  have hv1 (v : ℕ) (hv : v ∈ I) : 1 ≤ v := by
    have h := hU1.trans (Nat.le_of_ceil_le (Finset.mem_Icc.mp hv).1)
    exact_mod_cast h
  have hI : I ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
    intro v hv
    exact Finset.mem_Icc.mpr ⟨hv1 v hv, (Finset.mem_Icc.mp hv).2⟩
  rw [sum_interval_multiples X (2 * X) D _ hXpos.le (by linarith) hDpos]
  calc
    _ ≤ ∑ v ∈ I, L x ^ (4 * C) * (v.divisors.card : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro v hv
      apply (endpoint_norm_sq_le G x C τ η E hL hE (D * v)).trans
      have hcard := groupFreePart_divisors_card_le G D v hDpos.ne' (by have := hv1 v hv; omega) hprimes
      gcongr
    _ = L x ^ (4 * C) * ∑ v ∈ I, (v.divisors.card : ℝ) ^ 4 := by rw [Finset.mul_sum]
    _ ≤ L x ^ (4 * C) * ∑ v ∈ Finset.Icc 1 ⌊Y⌋₊, (v.divisors.card : ℝ) ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith : 0 ≤ L x) _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hI (by intros; positivity)
    _ ≤ L x ^ (4 * C) * (K * Y * Real.log (2 * Y) ^ c) :=
      mul_le_mul_of_nonneg_left (hm Y hY1) (Real.rpow_nonneg (by linarith : 0 ≤ L x) _)
    _ = _ := by
      have hlog : 2 * Y = 4 * X / D := by dsimp [Y]; ring
      rw [hlog]
      dsimp [Y]
      ring

end Erdos821.P5Core
