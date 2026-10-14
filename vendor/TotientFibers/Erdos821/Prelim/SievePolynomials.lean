import Erdos821.Prelim.SieveBounds

/-!
# Coefficient certificates for the block-sieve polynomials

Index the prime-set supports by their squarefree products. Both polynomials
have the same sign on their common support, so their difference also has
coefficients of absolute value at most one.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821.PrelimLemmas

def sieveCoefficient (T : Finset (Finset ℕ)) (d : ℕ) : ℝ :=
  if d ∈ T.image (fun s => ∏ p ∈ s, p) then (-1 : ℝ) ^ d.primeFactors.card else 0

theorem sieveCoefficient_abs_le (T : Finset (Finset ℕ)) (d : ℕ) :
    |sieveCoefficient T d| ≤ 1 := by
  unfold sieveCoefficient
  split_ifs <;> simp

theorem sieveCoefficient_sub_abs_le (T Q : Finset (Finset ℕ)) (hTQ : T ⊆ Q)
    (d : ℕ) : |sieveCoefficient T d - sieveCoefficient Q d| ≤ 1 := by
  have himage : T.image (fun s => ∏ p ∈ s, p) ⊆
      Q.image (fun s => ∏ p ∈ s, p) := Finset.image_subset_image hTQ
  by_cases hdT : d ∈ T.image (fun s => ∏ p ∈ s, p)
  · simp [sieveCoefficient, hdT, himage hdT]
  · by_cases hdQ : d ∈ Q.image (fun s => ∏ p ∈ s, p) <;>
      simp [sieveCoefficient, hdT, hdQ]

theorem sieveCoefficient_zero (α : Type) (S : Blueprint.SieveData α)
    (T : Finset (Finset ℕ)) (D : ℝ)
    (hlevel : T.image (fun s => ∏ p ∈ s, p) ⊆ S.products D)
    (d : ℕ) (hd : d ∉ S.products D) : sieveCoefficient T d = 0 := by
  have hout : d ∉ T.image (fun s => ∏ p ∈ s, p) := fun hm => hd (hlevel hm)
  simp [sieveCoefficient, hout]

/-- Reindex a supported polynomial through its prime-set support. -/
theorem sieveCoefficient_polynomial_eq (α : Type) (S : Blueprint.SieveData α)
    (T : Finset (Finset ℕ)) (D : ℝ)
    (hT : ∀ s ∈ T, s ⊆ S.primes)
    (hlevel : T.image (fun s => ∏ p ∈ s, p) ⊆ S.products D) (a : α) :
    S.polynomial D (sieveCoefficient T) a =
      ∑ s ∈ T.filter (· ⊆ badFinset α S a), (-1 : ℝ) ^ s.card := by
  have hpf : ∀ s ∈ T, (∏ p ∈ s, p).primeFactors = s :=
    fun s hs => primeFactors_prod_eq s (fun p hp => S.prime p (hT s hs hp))
  have hinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) ↑T := by
    intro s hs t ht heq
    have h := congrArg Nat.primeFactors heq
    simpa only [hpf s hs, hpf t ht] using h
  have hrestrict : (∑ d ∈ T.image (fun s => ∏ p ∈ s, p),
      sieveCoefficient T d * S.monomial d a) = S.polynomial D (sieveCoefficient T) a := by
    apply Finset.sum_subset hlevel
    intro d _ hd
    simp [sieveCoefficient, hd]
  rw [← hrestrict, Finset.sum_image hinj, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  have hmem : (∏ p ∈ s, p) ∈ T.image (fun s => ∏ p ∈ s, p) :=
    Finset.mem_image_of_mem _ hs
  have hiff : (∀ p ∈ s, S.bad p a) ↔ s ⊆ badFinset α S a := by
    constructor
    · intro hb p hp
      exact Finset.mem_filter.mpr ⟨hT s hs hp, hb p hp⟩
    · intro hb p hp
      exact (Finset.mem_filter.mp (hb hp)).2
  simp only [sieveCoefficient, if_pos hmem, hpf s hs, Blueprint.SieveData.monomial,
    hiff]
  split_ifs <;> simp

def upperPrimeSupport (α : Type) (S : Blueprint.SieveData α)
    (z : ℝ) (N h : ℕ) : Finset (Finset ℕ) :=
  Prelim.BlockSieve.SieveSupport ((Finset.range N).biUnion (Block α S z))
    (Finset.range N) (Block α S z) (fun j => (j + 1) * h)

def lowerPrimeSupport (α : Type) (S : Blueprint.SieveData α)
    (z : ℝ) (N h : ℕ) : Finset (Finset ℕ) :=
  SupportV ((Finset.range N).biUnion (Block α S z))
    (Finset.range N) (Block α S z) (fun j => (j + 1) * h)

theorem upper_polynomial_eq (α : Type) (S : Blueprint.SieveData α)
    (z η C : ℝ) (hdb : S.densityBounds z η C) (N : ℕ) (hN : Zscale z N < 2)
    (h : ℕ) (a : α) :
    S.polynomial (z ^ (4 * h + 2)) (sieveCoefficient (upperPrimeSupport α S z N h)) a =
      Prelim.BlockSieve.Uval (Finset.range N) (Block α S z)
        (fun j => (j + 1) * h) (badFinset α S a) := by
  rw [sieveCoefficient_polynomial_eq α S (upperPrimeSupport α S z N h)
    (z ^ (4 * h + 2))
    (fun s hs => support_subset_primes α S z N h s hs)
    (support_image_subset α S z hdb.1 N h _ rfl)]
  exact (Uval_eq_support_sum α S z hdb.1 N hN η C hdb h a).symm

theorem lower_polynomial_eq (α : Type) (S : Blueprint.SieveData α)
    (z η C : ℝ) (hdb : S.densityBounds z η C) (N : ℕ) (hN : Zscale z N < 2)
    (h : ℕ) (he : Even h) (a : α) :
    S.polynomial (z ^ (4 * h + 2)) (sieveCoefficient (lowerPrimeSupport α S z N h)) a =
      Prelim.BlockSieve.Vval (Finset.range N) (Block α S z)
        (fun j => (j + 1) * h) (badFinset α S a) := by
  rw [sieveCoefficient_polynomial_eq α S (lowerPrimeSupport α S z N h)
    (z ^ (4 * h + 2))
    (fun s hs => supportV_subset_primes α S z N h s hs)
    (supportV_image_subset α S z hdb.1 N h _ rfl)]
  exact (Vval_eq_supportV_sum α S z hdb.1 N hN η C hdb h he a).symm

/-- Exact coefficient, support and pointwise certificates of `eq:sieve-polynomials`. -/
theorem exists_sieve_polynomials (α : Type) (S : Blueprint.SieveData α)
    (z η C : ℝ) (hdb : S.densityBounds z η C) (h : ℕ) (he : Even h) :
    ∃ u v : ℕ → ℝ,
      (∀ d, |u d| ≤ 1 ∧ |v d| ≤ 1 ∧ |u d - v d| ≤ 1) ∧
      (∀ d, d ∉ S.products (z ^ (4 * h + 2)) → u d = 0 ∧ v d = 0) ∧
      ∀ a ∈ S.objects,
        let D := z ^ (4 * h + 2)
        let I : ℝ := if ∀ p ∈ S.primes, ¬ S.bad p a then 1 else 0
        S.polynomial D v a ≤ I ∧ I ≤ S.polynomial D u a ∧
          0 ≤ S.polynomial D u a ∧
          S.polynomial D u a - I ≤ S.polynomial D (fun d => u d - v d) a := by
  obtain ⟨N, hN⟩ := exists_Zscale_lt_two hdb.1
  let T := upperPrimeSupport α S z N h
  let Q := lowerPrimeSupport α S z N h
  have hTQ : T ⊆ Q := Finset.subset_union_left
  have hlevelT : T.image (fun s => ∏ p ∈ s, p) ⊆ S.products (z ^ (4 * h + 2)) :=
    support_image_subset α S z hdb.1 N h _ rfl
  have hlevelQ : Q.image (fun s => ∏ p ∈ s, p) ⊆ S.products (z ^ (4 * h + 2)) :=
    supportV_image_subset α S z hdb.1 N h _ rfl
  refine ⟨sieveCoefficient T, sieveCoefficient Q, ?_, ?_, ?_⟩
  · intro d
    exact ⟨sieveCoefficient_abs_le T d, sieveCoefficient_abs_le Q d,
      sieveCoefficient_sub_abs_le T Q hTQ d⟩
  · intro d hd
    exact ⟨sieveCoefficient_zero α S T _ hlevelT d hd,
      sieveCoefficient_zero α S Q _ hlevelQ d hd⟩
  · intro a _
    have hU := upper_polynomial_eq α S z η C hdb N hN h a
    have hV := lower_polynomial_eq α S z η C hdb N hN h he a
    have hdiff : S.polynomial (z ^ (4 * h + 2))
        (fun d => sieveCoefficient T d - sieveCoefficient Q d) a =
        S.polynomial (z ^ (4 * h + 2)) (sieveCoefficient T) a -
          S.polynomial (z ^ (4 * h + 2)) (sieveCoefficient Q) a := by
      simp only [Blueprint.SieveData.polynomial, sub_mul, Finset.sum_sub_distrib]
    have hiff : badFinset α S a = ∅ ↔ ∀ p ∈ S.primes, ¬ S.bad p a := by
      unfold badFinset
      exact Finset.filter_eq_empty_iff
    have hcov := badFinset_covered α S z hdb.1 N hN η C hdb a
    have heJ : ∀ j ∈ Finset.range N, Even ((j + 1) * h) := fun j _ => he.mul_left _
    dsimp only
    rw [hdiff, hU, hV]
    simp only [← hiff]
    exact ⟨Prelim.BlockSieve.Vval_le_avoid _ _ _ _ hcov heJ,
      Prelim.BlockSieve.Uval_ge_avoid _ _ _ _ hcov heJ,
      Prelim.BlockSieve.Uval_nonneg _ _ _ _ heJ,
      Prelim.BlockSieve.overcount_le_sub _ _ _ _ hcov heJ⟩

end Erdos821.PrelimLemmas
