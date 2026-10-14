import Erdos821.P5.EndpointPrefix
import Erdos821.P5.SharedLists

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem endpoint_square_sum_le_of_injective {ι : Type*} (s : Finset ι)
    (v : ι → ℕ) (hv : Set.InjOn v s) (G : PrimeGroups) (x Y : ℝ)
    (E : Endpoint) (D : ℕ)
    (hs : ∀ i ∈ s, 1 ≤ v i ∧ (v i : ℝ) ≤ Y ∧ D ∣ v i) :
    (∑ i ∈ s, ‖endpoint G x E (v i)‖ ^ 2) ≤
      ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => D ∣ n), ‖endpoint G x E n‖ ^ 2 := by
  classical
  have heq : (∑ n ∈ s.image v, ‖endpoint G x E n‖ ^ 2) =
      ∑ i ∈ s, ‖endpoint G x E (v i)‖ ^ 2 := Finset.sum_image hv
  rw [← heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
  intro n hn
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hvi, hviY, hDvi⟩ := hs i hi
  have hY : 0 ≤ Y := (Nat.cast_nonneg (v i)).trans hviY
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hvi, (Nat.le_floor_iff hY).mpr hviY⟩, hDvi⟩

/-- A free-prime collision costs its reciprocal in the normalized endpoint
pairing. The coefficient sequences are arbitrary under EndpointBound. -/
theorem endpoint_product_sum_multiples :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
      ∀ (G : PrimeGroups) (x C τ η X Y : ℝ) (E H : Endpoint) (D : ℕ),
        1 ≤ L x → EndpointBound x C τ η E → EndpointBound x C τ η H →
        0 < X → 1 ≤ D → (D : ℝ) ≤ Y →
        D.primeFactors ⊆ Finset.univ.biUnion G.primes →
        ∀ {ι : Type*} (s : Finset ι) (u v : ι → ℕ),
          Set.InjOn u s → Set.InjOn v s →
          (∀ i ∈ s, X ≤ (u i : ℝ)) →
          (∀ i ∈ s, 1 ≤ u i ∧ (u i : ℝ) ≤ Y ∧ D ∣ u i ∧
            1 ≤ v i ∧ (v i : ℝ) ≤ Y ∧ D ∣ v i) →
          (∑ i ∈ s, ‖endpoint G x E (u i)‖ * ‖endpoint G x H (v i)‖ / (u i : ℝ)) ≤
            (K * (Y / D) * L x ^ (4 * C) * Real.log (2 * Y / D) ^ c) / X := by
  classical
  obtain ⟨c, K, hc, hK, hm⟩ := endpoint_square_sum_prefix_multiples
  refine ⟨c, K, hc, hK, ?_⟩
  intro G x C τ η X Y E H D hL hE hH hX hD hDY hprimes ι s u v hu hv hlo hs
  let R := K * (Y / D) * L x ^ (4 * C) * Real.log (2 * Y / D) ^ c
  have hEu : (∑ i ∈ s, ‖endpoint G x E (u i)‖ ^ 2) ≤ R := by
    exact (endpoint_square_sum_le_of_injective s u hu G x Y E D
      (fun i hi => ⟨(hs i hi).1, (hs i hi).2.1, (hs i hi).2.2.1⟩)).trans
        (hm G x C τ η Y E D hL hE hD hDY hprimes)
  have hHv : (∑ i ∈ s, ‖endpoint G x H (v i)‖ ^ 2) ≤ R := by
    exact (endpoint_square_sum_le_of_injective s v hv G x Y H D
      (fun i hi => (hs i hi).2.2.2)).trans
        (hm G x C τ η Y H D hL hH hD hDY hprimes)
  have hR : 0 ≤ R := (Finset.sum_nonneg (fun i hi => sq_nonneg _)).trans hEu
  have hCS : (∑ i ∈ s, ‖endpoint G x E (u i)‖ * ‖endpoint G x H (v i)‖) ≤ R := by
    calc
      _ ≤ Real.sqrt (∑ i ∈ s, ‖endpoint G x E (u i)‖ ^ 2) *
          Real.sqrt (∑ i ∈ s, ‖endpoint G x H (v i)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt s _ _
      _ ≤ Real.sqrt R * Real.sqrt R :=
        mul_le_mul (Real.sqrt_le_sqrt hEu) (Real.sqrt_le_sqrt hHv)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = R := Real.mul_self_sqrt hR
  calc
    _ ≤ (∑ i ∈ s, ‖endpoint G x E (u i)‖ * ‖endpoint G x H (v i)‖) / X := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i hi =>
        div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hX (hlo i hi))
    _ ≤ R / X := div_le_div_of_nonneg_right hCS hX.le

end Erdos821.P5Core
