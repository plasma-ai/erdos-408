import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem groupFreePart_pos (G : PrimeGroups) (n : ℕ) : 0 < groupFreePart G n := by
  unfold groupFreePart
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).pos _

theorem groupFreePart_dvd (G : PrimeGroups) (n : ℕ) : groupFreePart G n ∣ n := by
  by_cases hn : n = 0
  · subst n
    exact dvd_zero _
  have h := Finset.prod_dvd_prod_of_subset
    (n.primeFactors \ Finset.univ.biUnion G.primes) n.primeFactors
    (fun p => p ^ n.factorization p) Finset.sdiff_subset
  rw [← Nat.prod_primeFactors_pow_factorization hn] at h
  exact h

/-- Removing the complete group-prime part leaves a factor coprime to every
positive integer supported on group primes. -/
theorem groupFreePart_coprime (G : PrimeGroups) (n D : ℕ) (hD : D ≠ 0)
    (hprime : D.primeFactors ⊆ Finset.univ.biUnion G.primes) :
    Nat.Coprime (groupFreePart G n) D := by
  unfold groupFreePart
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hpf := (Finset.mem_sdiff.mp hp).1
  have hpprime := Nat.prime_of_mem_primeFactors hpf
  apply (Nat.Coprime.pow_left _)
  apply hpprime.coprime_iff_not_dvd.mpr
  intro hpd
  exact (Finset.mem_sdiff.mp hp).2 (hprime (Nat.mem_primeFactors.mpr ⟨hpprime, hpd, hD⟩))

theorem groupFreePart_dvd_residual (G : PrimeGroups) (D v : ℕ) (hD : D ≠ 0)
    (hprime : D.primeFactors ⊆ Finset.univ.biUnion G.primes) :
    groupFreePart G (D * v) ∣ v :=
  (groupFreePart_coprime G (D * v) D hD hprime).dvd_mul_left.mp (groupFreePart_dvd G (D * v))

theorem groupFreePart_divisors_card_le (G : PrimeGroups) (D v : ℕ) (hD : D ≠ 0)
    (hv : v ≠ 0) (hprime : D.primeFactors ⊆ Finset.univ.biUnion G.primes) :
    (groupFreePart G (D * v)).divisors.card ≤ v.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hv (groupFreePart_dvd_residual G D v hD hprime))

end Erdos821.P5Core
