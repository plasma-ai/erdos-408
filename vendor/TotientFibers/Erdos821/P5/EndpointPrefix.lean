import Erdos821.P5.EndpointMean

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Prefix version of the supported-multiples moment bound. It also covers
the positive shifted endpoint, whose range need not be one dyad. -/
theorem endpoint_square_sum_prefix_multiples :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
      ∀ (G : PrimeGroups) (x C τ η Y : ℝ) (E : Endpoint) (D : ℕ),
        1 ≤ L x → EndpointBound x C τ η E → 1 ≤ D → (D : ℝ) ≤ Y →
        D.primeFactors ⊆ Finset.univ.biUnion G.primes →
        (∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => D ∣ n),
          ‖endpoint G x E n‖ ^ 2) ≤
            K * (Y / D) * L x ^ (4 * C) * Real.log (2 * Y / D) ^ c := by
  classical
  obtain ⟨c, K, hc, hK, hm⟩ := divisor_fourth_count_nonneg_exponent
  refine ⟨c, K, hc, hK, ?_⟩
  intro G x C τ η Y E D hL hE hD hDY hprimes
  have hDpos : 0 < D := by omega
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hDR1 : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  have hY1 : 1 ≤ Y := hDR1.trans hDY
  have hU1 : 1 ≤ Y / (D : ℝ) := (le_div_iff₀ hDR).mpr (by simpa using hDY)
  let I := Finset.Icc ⌈1 / (D : ℝ)⌉₊ ⌊Y / (D : ℝ)⌋₊
  have hv1 (v : ℕ) (hv : v ∈ I) : 1 ≤ v := by
    have h : (0 : ℝ) < v := (div_pos (by norm_num : (0 : ℝ) < 1) hDR).trans_le
      (Nat.le_of_ceil_le (Finset.mem_Icc.mp hv).1)
    have : 0 < v := by exact_mod_cast h
    omega
  have hI : I ⊆ Finset.Icc 1 ⌊Y / (D : ℝ)⌋₊ := by
    intro v hv
    exact Finset.mem_Icc.mpr ⟨hv1 v hv, (Finset.mem_Icc.mp hv).2⟩
  have hreindex := sum_interval_multiples 1 Y D (fun n => ‖endpoint G x E n‖ ^ 2)
    (by norm_num) hY1 hDpos
  simp only [Nat.ceil_one] at hreindex
  rw [hreindex]
  calc
    _ ≤ ∑ v ∈ I, L x ^ (4 * C) * (v.divisors.card : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro v hv
      apply (endpoint_norm_sq_le G x C τ η E hL hE (D * v)).trans
      have hcard := groupFreePart_divisors_card_le G D v hDpos.ne'
        (by have := hv1 v hv; omega) hprimes
      gcongr
    _ = L x ^ (4 * C) * ∑ v ∈ I, (v.divisors.card : ℝ) ^ 4 := by
      rw [Finset.mul_sum]
    _ ≤ L x ^ (4 * C) * ∑ v ∈ Finset.Icc 1 ⌊Y / (D : ℝ)⌋₊,
        (v.divisors.card : ℝ) ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith : 0 ≤ L x) _)
      exact Finset.sum_le_sum_of_subset_of_nonneg hI (by intros; positivity)
    _ ≤ L x ^ (4 * C) * (K * (Y / D) * Real.log (2 * (Y / D)) ^ c) :=
      mul_le_mul_of_nonneg_left (hm (Y / D) hU1)
        (Real.rpow_nonneg (by linarith : 0 ≤ L x) _)
    _ = _ := by rw [mul_div_assoc]; ring

end Erdos821.P5Core
