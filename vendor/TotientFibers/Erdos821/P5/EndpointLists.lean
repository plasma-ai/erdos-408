import Erdos821.P5.EndpointMean

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- Sum physical-list endpoint moments using their harmonic mass. Repeated
products of different lists are retained; no injectivity of D is needed. -/
theorem endpoint_square_sum_lists :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
      ∀ (G : PrimeGroups) (x C τ η X : ℝ) (E : Endpoint),
        1 ≤ L x → EndpointBound x C τ η E → 1 ≤ X →
        ∀ {ι : Type*} (s : Finset ι) (D : ι → ℕ) (w : ι → ℝ),
          (∀ i ∈ s, 1 ≤ D i ∧ (D i : ℝ) ≤ X ∧
            (D i).primeFactors ⊆ Finset.univ.biUnion G.primes) →
          (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i / D i) ≤ 1 →
          (∑ i ∈ s, w i * ∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (fun n => D i ∣ n),
            ‖endpoint G x E n‖ ^ 2) ≤
              K * X * L x ^ (4 * C) * Real.log (4 * X) ^ c := by
  classical
  obtain ⟨c, K, hc, hK, hm⟩ := endpoint_square_sum_multiples
  refine ⟨c, K, hc, hK, ?_⟩
  intro G x C τ η X E hL hE hX ι s D w hD hw hmass
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L x := by linarith
  have hlogX : 0 < Real.log (4 * X) := Real.log_pos (by linarith)
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ n ∈ (Finset.Icc ⌈X⌉₊ ⌊2 * X⌋₊).filter (fun n => D i ∣ n),
        ‖endpoint G x E n‖ ^ 2) ≤
          K * (X / D i) * L x ^ (4 * C) * Real.log (4 * X) ^ c := by
    obtain ⟨hDi, hDiX, hpr⟩ := hD i hi
    have hDR : 1 ≤ (D i : ℝ) := by exact_mod_cast hDi
    have hDpos : 0 < (D i : ℝ) := by linarith
    have harg : 1 < 4 * X / D i := (lt_div_iff₀ hDpos).mpr (by nlinarith)
    have hlogpos : 0 < Real.log (4 * X / D i) := Real.log_pos harg
    have hlogle : Real.log (4 * X / D i) ≤ Real.log (4 * X) :=
      Real.log_le_log (by positivity) (div_le_self (by positivity : 0 ≤ 4 * X) hDR)
    have hpow := Real.rpow_le_rpow hlogpos.le hlogle hc
    apply (hm G x C τ η X E (D i) hL hE hDi hDiX hpr).trans
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  let R := K * X * L x ^ (4 * C) * Real.log (4 * X) ^ c
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    _ ≤ ∑ i ∈ s, w i * (K * (X / D i) * L x ^ (4 * C) * Real.log (4 * X) ^ c) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hrow i hi) (hw i hi))
    _ = R * ∑ i ∈ s, w i / D i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [R]
      ring
    _ ≤ R * 1 := mul_le_mul_of_nonneg_left hmass hR
    _ = _ := mul_one _

end Erdos821.P5Core
