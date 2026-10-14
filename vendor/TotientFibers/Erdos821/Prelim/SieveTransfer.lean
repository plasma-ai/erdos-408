import Mathlib
import Erdos821.Blueprint.Sieve

/-!
# Sieve transfer: finset prime sets ↔ squarefree divisors (`lem:sieve`)

For `S.primes` (all `Nat.Prime`), `s ↦ ∏ s` maps finsets `s ⊆ S.primes` to
squarefree `d` with `d.primeFactors ⊆ S.primes`, and `d ↦ d.primeFactors`
is the inverse (via `Nat.prod_primeFactors_of_squarefree`). This bridges
`Prelim.BlockSieve`/`SieveExpectation` (finsets) with `Blueprint.Sieve`
(`ℕ` divisors, `products`, `polynomial`, `remainderSum`).
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- A prime is squarefree. -/
theorem prime_squarefree {p : ℕ} (hp : p.Prime) : Squarefree p := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hx hxx
  have hxdvd : x ∣ p := dvd_trans (dvd_mul_right x x) hxx
  have heq : x = p := (Nat.prime_dvd_prime_iff_eq hx hp).mp hxdvd
  rw [heq] at hxx
  have hle : p * p ≤ p := Nat.le_of_dvd hp.pos hxx
  have hp2 : 2 ≤ p := hp.two_le
  nlinarith

/-- A prime does not divide a product of other distinct primes. -/
theorem prime_not_dvd_prod {s : Finset ℕ} {q : ℕ}
    (hq : q.Prime) (hs : ∀ p ∈ s, p.Prime) (hqout : q ∉ s) :
    ¬ q ∣ ∏ p ∈ s, p := by
  intro hdvd
  have hqPrime : Prime q := Nat.prime_iff.mp hq
  have hex : ∃ p ∈ s, q ∣ p := by
    have h := (Prime.dvd_finsetProd_iff hqPrime (fun p => p)).mp hdvd
    simpa using h
  obtain ⟨p, hpmem, hqp⟩ := hex
  have hp : p.Prime := hs p hpmem
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  subst heq
  exact hqout hpmem

/-- Product of distinct primes is squarefree. -/
theorem prod_primes_squarefree (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert q s₀ has ih =>
    have hq : q.Prime := hs q (Finset.mem_insert_self q s₀)
    have hs₀ : ∀ p ∈ s₀, p.Prime := fun p hp =>
      hs p (Finset.mem_insert_of_mem hp)
    have ihSq := ih hs₀
    have hqSq := prime_squarefree hq
    have hcop : Nat.Coprime q (∏ p ∈ s₀, p) := by
      rw [hq.coprime_iff_not_dvd]
      exact prime_not_dvd_prod hq hs₀ has
    have hiff : Squarefree (q * ∏ p ∈ s₀, p) ↔
        Nat.Coprime q (∏ p ∈ s₀, p) ∧ Squarefree q ∧
          Squarefree (∏ p ∈ s₀, p) :=
      Nat.squarefree_mul_iff
    -- `Squarefree (q * ∏ s₀) ↔ ...`; rewrite `∏ insert` as `q * ∏`
    have hprod : ∏ p ∈ insert q s₀, p = q * ∏ p ∈ s₀, p :=
      Finset.prod_insert has
    rw [hprod]
    exact hiff.mpr ⟨hcop, hqSq, ihSq⟩

/-- Prime factors of a product of distinct primes recover the set. -/
theorem primeFactors_prod_eq (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : (∏ p ∈ s, p).primeFactors = s := by
  have hprod_ne : ∏ p ∈ s, p ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hpmem
    have hp := hs p hpmem
    exact hp.ne_zero
  ext q
  constructor
  · intro hqmem
    have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqdvd : q ∣ ∏ p ∈ s, p := Nat.dvd_of_mem_primeFactors hqmem
    have hqGen : Prime q := Nat.prime_iff.mp hqPrime
    have hex : ∃ p ∈ s, q ∣ p := by
      have h := (Prime.dvd_finsetProd_iff hqGen (fun p => p)).mp hqdvd
      simpa using h
    obtain ⟨p, hpmem, hqp⟩ := hex
    have hp : p.Prime := hs p hpmem
    have heq : q = p := (Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hqp
    subst heq
    exact hpmem
  · intro hqmem
    have hq : q.Prime := hs q hqmem
    have hqdvd : q ∣ ∏ p ∈ s, p := Finset.dvd_prod_of_mem _ hqmem
    exact hq.mem_primeFactors hqdvd hprod_ne

end PrelimLemmas
end Erdos821
