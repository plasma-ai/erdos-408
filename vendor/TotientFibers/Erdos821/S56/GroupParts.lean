import Erdos821.S56.BlueprintInvariant

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def groupPart (G : PrimeGroups) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors ∩ groupPrimes G, p ^ n.factorization p

theorem groupPart_mul_freePart (G : PrimeGroups) (n : ℕ) (hn : 0 < n) :
    groupPart G n * groupFreePart G n = n := by
  have hd : Disjoint (n.primeFactors ∩ groupPrimes G) (n.primeFactors \ groupPrimes G) := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    exact (Finset.mem_sdiff.mp hp').2 (Finset.mem_inter.mp hp).2
  have hu : n.primeFactors ∩ groupPrimes G ∪ (n.primeFactors \ groupPrimes G) =
      n.primeFactors := by ext p; simp; tauto
  change (∏ p ∈ n.primeFactors ∩ groupPrimes G, p ^ n.factorization p) *
    (∏ p ∈ n.primeFactors \ groupPrimes G, p ^ n.factorization p) = n
  rw [← Finset.prod_union hd, hu]
  exact (Nat.prod_primeFactors_pow_factorization hn.ne').symm

theorem groupFreePart_pos (G : PrimeGroups) (n : ℕ) : 0 < groupFreePart G n := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1) _

theorem groupPart_pos (G : PrimeGroups) (n : ℕ) : 0 < groupPart G n := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.pos_of_mem_primeFactors (Finset.mem_inter.mp hp).1) _

theorem groupFreePart_dvd (G : PrimeGroups) (n : ℕ) (hn : 0 < n) :
    groupFreePart G n ∣ n := by
  refine ⟨groupPart G n, ?_⟩
  simpa [mul_comm] using (groupPart_mul_freePart G n hn).symm

theorem groupFreePart_groupFree (G : PrimeGroups) (n : ℕ) :
    GroupFree G (groupFreePart G n) := by
  intro p hp
  obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
  have hpprime := G.prime g p hpg
  apply hpprime.prime.not_dvd_finsetProd
  intro q hq hdiv
  have hqprime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
  have heq : p = q := Nat.prime_eq_prime_of_dvd_pow hpprime hqprime hdiv
  exact (Finset.mem_sdiff.mp hq).2 (heq ▸ hp)

theorem groupFreePart_eq_self (G : PrimeGroups) (n : ℕ) (hn : 0 < n)
    (hfree : GroupFree G n) : groupFreePart G n = n := by
  have hp : groupFreePart G 1 = 1 := by simp [groupFreePart]
  simpa [hp] using groupFreePart_mul G n 1 hn (by norm_num) hfree


end Erdos821.S56Core
