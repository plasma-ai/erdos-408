import Erdos821.Blueprint.TypeII

noncomputable section
open scoped BigOperators

namespace Erdos821.S56Core
open Erdos821.Blueprint Erdos821.Blueprint.Analytic

def groupPrimes (G : PrimeGroups) : Finset ℕ := Finset.univ.biUnion G.primes

def GroupFree (G : PrimeGroups) (e : ℕ) : Prop :=
  ∀ p ∈ groupPrimes G, ¬p ∣ e

private theorem factorization_zero_of_not_mem (n p : ℕ) (hp : p ∉ n.primeFactors) :
    n.factorization p = 0 := by
  exact Finsupp.notMem_support_iff.mp hp

/-- Extending a prime-factor product only inserts factors of exponent zero. -/
private theorem factorization_product_extend (n : ℕ) (hn : n ≠ 0)
    (s : Finset ℕ) (hs : n.primeFactors ⊆ s) :
    (∏ p ∈ s, p ^ n.factorization p) = n := by
  calc
    _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      symm
      apply Finset.prod_subset hs
      intro p _ hp
      rw [factorization_zero_of_not_mem n p hp, pow_zero]
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

/-- Multiplication by a group-free factor preserves the literal blueprint
outside part, including arbitrary prime-power multiplicities. -/
theorem groupFreePart_mul (G : PrimeGroups) (e h : ℕ)
    (he : 0 < e) (hh : 0 < h) (hfree : GroupFree G e) :
    groupFreePart G (e * h) = e * groupFreePart G h := by
  classical
  let s := (e * h).primeFactors \ groupPrimes G
  have hes : e.primeFactors ⊆ s := by
    intro p hp
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · rw [Nat.primeFactors_mul he.ne' hh.ne']
      exact Finset.mem_union_left _ hp
    · intro hpg
      exact hfree p hpg (Nat.dvd_of_mem_primeFactors hp)
  have hhs : h.primeFactors \ groupPrimes G ⊆ s := by
    intro p hp
    obtain ⟨hph, hpg⟩ := Finset.mem_sdiff.mp hp
    apply Finset.mem_sdiff.mpr
    rw [Nat.primeFactors_mul he.ne' hh.ne']
    exact ⟨Finset.mem_union_right _ hph, hpg⟩
  change (∏ p ∈ s, p ^ (e * h).factorization p) =
    e * ∏ p ∈ h.primeFactors \ groupPrimes G, p ^ h.factorization p
  simp_rw [Nat.factorization_mul he.ne' hh.ne', Finsupp.add_apply, pow_add]
  rw [Finset.prod_mul_distrib, factorization_product_extend e he.ne' s hes]
  congr 1
  symm
  apply Finset.prod_subset hhs
  intro p hp hpnot
  have hpn : p ∉ h.primeFactors := by
    intro hph
    exact hpnot (Finset.mem_sdiff.mpr ⟨hph, (Finset.mem_sdiff.mp hp).2⟩)
  rw [factorization_zero_of_not_mem h p hpn, pow_zero]

theorem omegaGroup_mul (G : PrimeGroups) (e h : ℕ) (hfree : GroupFree G e)
    (g : Fin G.size) : omegaGroup G g (e * h) = omegaGroup G g h := by
  classical
  unfold omegaGroup
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hdvd⟩
    have hpg : p ∈ groupPrimes G := Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hp⟩
    exact ⟨hp, ((G.prime g p hp).dvd_mul.mp hdvd).resolve_left (hfree p hpg)⟩
  · rintro ⟨hp, hdvd⟩
    exact ⟨hp, dvd_mul_of_dvd_right hdvd e⟩

theorem markWeight_mul (G : PrimeGroups) (e h : ℕ) (hfree : GroupFree G e)
    (q : ℝ) (t : Fin G.size → ℕ) :
    markWeight G q t (e * h) = markWeight G q t h := by
  have hω : omega G (e * h) = omega G h := by
    unfold omega
    exact Finset.sum_congr rfl (fun g _ => omegaGroup_mul G e h hfree g)
  simp_rw [markWeight, hω, omegaGroup_mul G e h hfree]


end Erdos821.S56Core
