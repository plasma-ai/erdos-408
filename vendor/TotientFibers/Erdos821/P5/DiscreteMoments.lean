import Erdos821.P5.Moments
import Erdos821.Classical.DirichletMean

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem nat_mul_log_nonneg (N : ℕ) : 0 ≤ (N : ℝ) * Real.log (2 * N) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))

/-- P1's discrete mean square applies to every prime-polynomial power with the same K. -/
theorem discrete_prime_polynomial_moment
    (hm : Blueprint.MeanSquares := Erdos821.Classical.blueprint_meanSquares) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset ℕ) (b : ℕ → ℂ) (j : ℕ)
      (lo hi : ℝ) (E : Finset ℝ),
      (∀ p ∈ s, p.Prime) → lo ≤ hi →
      (∀ t ∈ E, lo ≤ t ∧ t ≤ hi) →
      (∀ t ∈ E, ∀ u ∈ E, t ≠ u → 1 ≤ |t - u|) →
      (∑ t ∈ E, ‖primePolynomial s b t‖ ^ (2 * j)) ≤
        K * (hi - lo + 1 + ((s.sup id) ^ j : ℕ) *
          Real.log (2 * ((s.sup id) ^ j : ℕ))) *
          Real.log (2 * ((s.sup id) ^ j : ℕ)) ^ 2 *
          Nat.factorial j * (∑ p ∈ s, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) ^ j := by
  obtain ⟨K, hK, hmean⟩ := hm
  refine ⟨K, hK, ?_⟩
  intro s b j lo hi E hprime hI hE hsep
  have h := (hmean ((s.sup id) ^ j) (primePowerCoefficient s b j) lo hi hI).2 E hE hsep
  have hmoment := prime_polynomial_moment s b j hprime (Finset.Icc 1 ((s.sup id) ^ j))
  have hfactor : 0 ≤ K * (hi - lo + 1 + ((s.sup id) ^ j : ℕ) *
      Real.log (2 * ((s.sup id) ^ j : ℕ))) *
      Real.log (2 * ((s.sup id) ^ j : ℕ)) ^ 2 := by
    apply mul_nonneg
    · apply mul_nonneg hK.le
      have := nat_mul_log_nonneg ((s.sup id) ^ j)
      linarith
    · positivity
  calc
    _ = ∑ t ∈ E, ‖dp (Finset.Icc 1 ((s.sup id) ^ j))
        (primePowerCoefficient s b j) t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [prime_polynomial_power s b j hprime, norm_pow, ← pow_mul, Nat.mul_comm j 2]
    _ ≤ _ := h
    _ ≤ _ := by
      have hbnd := mul_le_mul_of_nonneg_left hmoment hfactor
      simpa only [sqNorm, mul_assoc] using hbnd

end Erdos821.P5Core
