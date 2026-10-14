import Erdos821.P5.GroupFreeBounds

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem primeFactors_prod_supported {ι : Type*} (s : Finset ι) (f : ι → ℕ) (Q : Finset ℕ) :
    (∀ i ∈ s, 0 < f i) → (∀ i ∈ s, (f i).primeFactors ⊆ Q) →
      (∏ i ∈ s, f i).primeFactors ⊆ Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hp hf
    have hsp (j : ι) (hj : j ∈ s) := hp j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Nat.primeFactors_mul
      (hp i (Finset.mem_insert_self _ _)).ne' (Finset.prod_pos hsp).ne']
    exact Finset.union_subset (hf i (Finset.mem_insert_self _ _))
      (ih hsp (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Multiplication by a positive integer supported on group primes leaves the
complete outside-group prime-power part unchanged. No square-freeness is needed. -/
theorem groupFreePart_mul_supported (G : PrimeGroups) (D n : ℕ) (hD : D ≠ 0)
    (hprime : D.primeFactors ⊆ Finset.univ.biUnion G.primes) :
    groupFreePart G (D * n) = groupFreePart G n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  let Q := Finset.univ.biUnion G.primes
  have hset : (D * n).primeFactors \ Q = n.primeFactors \ Q := by
    rw [Nat.primeFactors_mul hD hn]
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hpD | hpn, hpQ⟩
      · exact (hpQ (hprime hpD)).elim
      · exact ⟨hpn, hpQ⟩
    · rintro ⟨hpn, hpQ⟩
      exact ⟨Or.inr hpn, hpQ⟩
  unfold groupFreePart
  change (∏ p ∈ (D * n).primeFactors \ Q, p ^ (D * n).factorization p) =
    ∏ p ∈ n.primeFactors \ Q, p ^ n.factorization p
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  have hpD : p ∉ D.primeFactors := fun h => (Finset.mem_sdiff.mp hp).2 (hprime h)
  have hzero : D.factorization p = 0 := by
    rw [← Nat.support_factorization] at hpD
    simpa only [Finsupp.mem_support_iff, not_not] using hpD
  rw [Nat.factorization_mul hD hn, Finsupp.add_apply, hzero, zero_add]

theorem endpoint_mul_supported (G : PrimeGroups) (x : ℝ) (E : Endpoint) (D n : ℕ)
    (hD : D ≠ 0) (hprime : D.primeFactors ⊆ Finset.univ.biUnion G.primes) :
    endpoint G x E (D * n) = endpoint G x E n := by
  unfold endpoint
  rw [groupFreePart_mul_supported G D n hD hprime]

end Erdos821.P5Core
