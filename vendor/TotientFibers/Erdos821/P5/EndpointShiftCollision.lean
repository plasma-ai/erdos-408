import Erdos821.P5.EndpointCollision

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem shifted_toNat_injOn (s : Finset ℕ) (h : ℤ)
    (hs : ∀ n ∈ s, 0 ≤ (n : ℤ) + h) :
    Set.InjOn (fun n : ℕ => ((n : ℤ) + h).toNat) s := by
  intro n hn r hr heq
  have heqZ := congrArg (fun z : ℕ => (z : ℤ)) heq
  rw [Int.toNat_of_nonneg (hs n hn), Int.toNat_of_nonneg (hs r hr)] at heqZ
  omega

/-- The collision average on the actual positive signed shift. Both endpoint
ranges are bounded by Y, so a single divisor-moment constant applies. -/
theorem endpoint_shift_sum_free_multiples :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
      ∀ (G : PrimeGroups) (x C τ η X Y : ℝ) (E H : Endpoint) (p D : ℕ) (k : ℤ),
        1 ≤ L x → EndpointBound x C τ η E → EndpointBound x C τ η H →
        0 < X → 1 ≤ p → (p : ℝ) ≤ Y → p ∣ D →
        p.primeFactors ⊆ Finset.univ.biUnion G.primes →
        ∀ s : Finset ℕ,
          (∀ n ∈ s, X ≤ (n : ℝ)) →
          (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ Y ∧ p ∣ n ∧
            0 < (n : ℤ) + k * (D : ℤ) ∧
            ((n : ℤ) + k * (D : ℤ)).toNat ≤ Y) →
          (∑ n ∈ s, ‖endpoint G x E n‖ *
            ‖endpoint G x H ((n : ℤ) + k * (D : ℤ)).toNat‖ / (n : ℝ)) ≤
            (K * (Y / p) * L x ^ (4 * C) * Real.log (2 * Y / p) ^ c) / X := by
  obtain ⟨c, K, hc, hK, hm⟩ := endpoint_product_sum_multiples
  refine ⟨c, K, hc, hK, ?_⟩
  intro G x C τ η X Y E H p D k hL hE hH hX hp hpY hpD hprimes s hlo hs
  let v : ℕ → ℕ := fun n => ((n : ℤ) + k * (D : ℤ)).toNat
  apply hm G x C τ η X Y E H p hL hE hH hX hp hpY hprimes s id v
  · exact Function.injective_id.injOn
  · exact shifted_toNat_injOn s _ (fun n hn => (hs n hn).2.2.2.1.le)
  · exact hlo
  · intro n hn
    obtain ⟨hn1, hnY, hpn, hpos, hvY⟩ := hs n hn
    have hvZ : (v n : ℤ) = (n : ℤ) + k * (D : ℤ) :=
      Int.toNat_of_nonneg hpos.le
    have hv1 : 1 ≤ v n := by
      have hvpos : (0 : ℤ) < (v n : ℤ) := hvZ.symm ▸ hpos
      have : 0 < v n := by exact_mod_cast hvpos
      omega
    have hpv : p ∣ v n :=
      (dvd_shift_iff p D n (v n) k hpD hvZ).mp hpn
    exact ⟨hn1, hnY, hpn, hv1, hvY, hpv⟩

end Erdos821.P5Core
