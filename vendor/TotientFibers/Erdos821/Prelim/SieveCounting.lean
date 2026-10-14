import Mathlib
import Erdos821.Prelim.BlockSieve
import Erdos821.Prelim.SieveGeometry
import Erdos821.Prelim.SieveExpectation
import Erdos821.Prelim.SieveProduct
import Erdos821.Prelim.SieveTransfer
import Erdos821.Prelim.SieveLevel
import Erdos821.Blueprint.Sieve

/-!
# Sieve counting, upper part (`lem:sieve`, `eq:block-sieve`)

For `S : SieveData`, `z > 1`, `Jmax` with `Z_Jmax < 2`, `J = range Jmax`,
`B j = Block S z j`, `e j = (j+1)*h` (`h` even), `g = S.density`:
`sifted ≤ ∑ weight·Uval ≤ X·∏S + remainderSum`, where `∏S = ∏ blockExpS`
(`support_weighted_sum_eq`) and the remainder is bounded via transfer
(`primeFactors_prod_eq`, `prod_primes_squarefree`) + level
(`support_level_le`) so the support image lies in `S.products D`
(`D = z^{4h+2}`).
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Finset
namespace Erdos821
namespace PrelimLemmas

/-- Bad prime set of an object. -/
def badFinset (α : Type) (S : Erdos821.Blueprint.SieveData α) (a : α) : Finset ℕ :=
  S.primes.filter (fun p => S.bad p a)

/-- `badFinset` is the filter; membership. -/
theorem mem_badFinset (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (a : α) (p : ℕ) :
    p ∈ badFinset α S a ↔ p ∈ S.primes ∧ S.bad p a := by
  simp [badFinset]

/-- Covering: every bad prime lies in some block. -/
theorem badFinset_covered (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C) (a : α) :
    badFinset α S a ⊆ (Finset.range Jmax).biUnion (fun j => Block α S z j) := by
  intro p hp
  have hpmem : p ∈ S.primes := (Finset.mem_filter.mp hp).1
  have hple : (p : ℝ) ≤ z := (hdb.2.2.1 p hpmem).1
  obtain ⟨j, hjJ, hjB⟩ := Block_cover α S z hz Jmax hJ p hpmem hple
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjJ, hjB⟩

/-- Sifted indicator equals `badFinset = ∅` indicator. -/
theorem sifted_term_eq (α : Type) (S : Erdos821.Blueprint.SieveData α) (a : α) :
    (if ∀ p ∈ S.primes, ¬ S.bad p a then S.weight a else 0)
      = S.weight a * (if badFinset α S a = ∅ then (1 : ℝ) else 0) := by
  by_cases h : ∀ p ∈ S.primes, ¬ S.bad p a
  · have hempty : badFinset α S a = ∅ := by
      unfold badFinset
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      exact h p hp
    have hif : (if badFinset α S a = ∅ then (1 : ℝ) else 0) = 1 :=
      if_pos hempty
    rw [if_pos h, hif, mul_one]
  · have hne : badFinset α S a ≠ ∅ := by
      intro hempty
      apply h
      intro p hp
      have : p ∉ badFinset α S a := hempty ▸ Finset.notMem_empty p
      simp [badFinset] at this
      exact this hp
    have hif : (if badFinset α S a = ∅ then (1 : ℝ) else 0) = 0 :=
      if_neg hne
    rw [if_neg h, hif, mul_zero]

/-- Pointwise upper: sifted term `≤ weight·Uval`. -/
theorem sifted_term_le_Uval (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (he : Even h) (a : α) (ha : a ∈ S.objects) :
    (if ∀ p ∈ S.primes, ¬ S.bad p a then S.weight a else 0)
      ≤ S.weight a * Prelim.BlockSieve.Uval (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a) := by
  rw [sifted_term_eq]
  have hcov := badFinset_covered α S z hz Jmax hJ η C hdb a
  have heJ : ∀ j ∈ Finset.range Jmax, Even ((j + 1) * h) :=
    fun j _ => he.mul_left _
  have hUI := Prelim.BlockSieve.Uval_ge_avoid (Finset.range Jmax)
    (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a) hcov heJ
  have hw := S.nonneg a ha
  by_cases hempty : badFinset α S a = ∅
  · have hif : (if badFinset α S a = ∅ then (1 : ℝ) else 0) = 1 :=
      if_pos hempty
    have hUI1 : (1 : ℝ) ≤ Prelim.BlockSieve.Uval (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a) := by
      have h2 := hUI
      rw [hif] at h2
      exact h2
    have hgoal : S.weight a * (if badFinset α S a = ∅ then (1 : ℝ) else 0)
        = S.weight a * 1 := by rw [hif]
    rw [hgoal]
    exact mul_le_mul_of_nonneg_left hUI1 hw
  · have hif : (if badFinset α S a = ∅ then (1 : ℝ) else 0) = 0 :=
      if_neg hempty
    have hgoal : S.weight a * (if badFinset α S a = ∅ then (1 : ℝ) else 0)
        = 0 := by rw [hif, mul_zero]
    rw [hgoal]
    exact mul_nonneg hw (Prelim.BlockSieve.Uval_nonneg _ _ _ _ heJ)

/-- Global upper: `sifted ≤ ∑ weight·Uval`. -/
theorem sifted_le_sum_Uval (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (he : Even h) :
    S.sifted ≤ ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Uval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a) := by
  unfold Erdos821.Blueprint.SieveData.sifted
  apply Finset.sum_le_sum
  intro a ha
  exact sifted_term_le_Uval α S z hz Jmax hJ η C hdb h he a ha

/-- `Uval` equals the real signed support sum (cast of `sieveSupport_sum_eq`). -/
theorem Uval_eq_support_sum (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (a : α) :
    Prelim.BlockSieve.Uval (Finset.range Jmax)
      (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
      = ∑ s ∈ (Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).filter
        (· ⊆ badFinset α S a), (-1 : ℝ) ^ s.card := by
  have hcov := badFinset_covered α S z hz Jmax hJ η C hdb a
  have hdisj : ∀ j₁ ∈ Finset.range Jmax, ∀ j₂ ∈ Finset.range Jmax, j₁ ≠ j₂ →
      Disjoint (Block α S z j₁) (Block α S z j₂) := by
    intro j₁ _ j₂ _ hne
    exact Block_disjoint α S z hz hne
  have hint := Prelim.BlockSieve.sieveSupport_sum_eq
    ((Finset.range Jmax).biUnion (fun j => Block α S z j))
    (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)
    (badFinset α S a) hcov hcov hdisj
  have hUval_cast : Prelim.BlockSieve.Uval (Finset.range Jmax)
      (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
      = ((∏ j ∈ Finset.range Jmax,
        Prelim.SieveCalculus.blockUpper ((j + 1) * h)
          ((badFinset α S a ∩ Block α S z j).card) : ℤ) : ℝ) := by
    unfold Prelim.BlockSieve.Uval Prelim.BlockSieve.blkU
    rw [Int.cast_prod]
  have hsum_cast : (∑ s ∈ (Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).filter
      (· ⊆ badFinset α S a), (-1 : ℝ) ^ s.card)
      = ((∑ s ∈ (Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).filter
        (· ⊆ badFinset α S a), (-1 : ℤ) ^ s.card : ℤ) : ℝ) := by
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hUval_cast, hsum_cast, hint]

/-- Blocks cover primes: `J.biUnion B ⊆ primes`. -/
theorem biUnion_subset_primes (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax : ℕ) :
    (Finset.range Jmax).biUnion (fun j => Block α S z j) ⊆ S.primes := by
  intro p hp
  rw [Finset.mem_biUnion] at hp
  obtain ⟨j, _, hjB⟩ := hp
  exact Block_subset α S z j hjB

/-- Support sets consist of primes. -/
theorem support_subset_primes (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    s ⊆ S.primes :=
  ((Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hs).1.trans
    (biUnion_subset_primes α S z Jmax)

/-- Support sets have prime elements. -/
theorem support_prime (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h))
    (p : ℕ) (hp : p ∈ s) : p.Prime :=
  S.prime p (support_subset_primes α S z Jmax h s hs hp)

/-- `∏ s` recovers `s` as prime factors. -/
theorem support_prod_primeFactors (α : Type)
    (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    (∏ q ∈ s, q).primeFactors = s :=
  primeFactors_prod_eq s (fun p hp => support_prime α S z Jmax h s hs p hp)

/-- Monomial at `∏ s` equals the subset indicator. -/
theorem monomial_eq_subset (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h))
    (a : α) :
    S.monomial (∏ q ∈ s, q) a
      = (if s ⊆ badFinset α S a then (1 : ℝ) else 0) := by
  have hpf := support_prod_primeFactors α S z Jmax h s hs
  unfold Erdos821.Blueprint.SieveData.monomial
  have hequiv : (∀ p ∈ (∏ q ∈ s, q).primeFactors, S.bad p a)
      ↔ s ⊆ badFinset α S a := by
    constructor
    · intro hall p hpmem
      have hmem : p ∈ (∏ q ∈ s, q).primeFactors := hpf.symm ▸ hpmem
      have hbad := hall p hmem
      rw [mem_badFinset]
      exact ⟨support_subset_primes α S z Jmax h s hs hpmem, hbad⟩
    · intro hsub p hpmem
      have hmem : p ∈ s := hpf ▸ hpmem
      have hmem2 := hsub hmem
      exact (mem_badFinset α S a p).mp hmem2 |>.2
  simp only [hequiv]

/-- Density at `∏ s` factorizes. -/
theorem g_prod_eq (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    S.g (∏ q ∈ s, q) = ∏ p ∈ s, S.density p := by
  unfold Erdos821.Blueprint.SieveData.g
  rw [support_prod_primeFactors α S z Jmax h s hs]

/-- Weighted upper sum as a double sum (interchange preparation). -/
theorem sum_Uval_eq_double (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C) (h : ℕ) :
    ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Uval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a)
    = ∑ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
      ∑ a ∈ S.objects,
        (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0) := by
  have hUval : ∀ a ∈ S.objects,
      S.weight a * Prelim.BlockSieve.Uval (Finset.range Jmax)
        (fun j => Block α S z j) (fun j => (j + 1) * h) (badFinset α S a)
      = ∑ s ∈ Prelim.BlockSieve.SieveSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0) := by
    intro a _
    rw [Uval_eq_support_sum α S z hz Jmax hJ η C hdb h a, Finset.mul_sum]
    exact Finset.sum_filter (fun s => s ⊆ badFinset α S a)
      (fun s => S.weight a * (-1 : ℝ) ^ s.card)
  have hstep : ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Uval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a)
      = ∑ a ∈ S.objects, ∑ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0) :=
    Finset.sum_congr rfl (fun a ha => hUval a ha)
  rw [hstep]
  exact Finset.sum_comm

/-- Inner sum equals `(-1)^{|s|}·(X·g + r)`. -/
theorem inner_sum_eq (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) (s : Finset ℕ)
    (hs : s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) :
    ∑ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
    = (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q) + S.remainder (∏ q ∈ s, q)) := by
  have hmon : ∀ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a else 0)
      = S.weight a * S.monomial (∏ q ∈ s, q) a := by
    intro a _
    rw [monomial_eq_subset α S z Jmax h s hs a]
    by_cases hsub : s ⊆ badFinset α S a <;> simp [hsub]
  have hG : ∀ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
      = (-1 : ℝ) ^ s.card * (if s ⊆ badFinset α S a then S.weight a else 0) := by
    intro a _
    by_cases hsub : s ⊆ badFinset α S a <;> simp [hsub, mul_comm]
  have hsum1 : ∑ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
      = (-1 : ℝ) ^ s.card * ∑ a ∈ S.objects,
        (if s ⊆ badFinset α S a then S.weight a else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact hG a ha
  have hsum2 : ∑ a ∈ S.objects,
      (if s ⊆ badFinset α S a then S.weight a else 0)
      = ∑ a ∈ S.objects, S.weight a * S.monomial (∏ q ∈ s, q) a := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hmon a ha
  have hsum3 : ∑ a ∈ S.objects, S.weight a * S.monomial (∏ q ∈ s, q) a
      = S.X * S.g (∏ q ∈ s, q) + S.remainder (∏ q ∈ s, q) := by
    have hdef : S.remainder (∏ q ∈ s, q)
        = (∑ a ∈ S.objects, S.weight a * S.monomial (∏ q ∈ s, q) a)
          - S.X * S.g (∏ q ∈ s, q) := rfl
    linarith
  rw [hsum1, hsum2, hsum3]

/-- Support product map is injective on prime sets. -/
theorem support_prod_injOn (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (Jmax h : ℕ) :
    Set.InjOn (fun s : Finset ℕ => ∏ q ∈ s, q)
      ↑(Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)) := by
  intro s hs t ht heq
  have hs' := support_prod_primeFactors α S z Jmax h s
    (Finset.mem_coe.mp hs)
  have ht' := support_prod_primeFactors α S z Jmax h t
    (Finset.mem_coe.mp ht)
  have heq' : (∏ q ∈ s, q) = (∏ q ∈ t, q) := heq
  calc s = (∏ q ∈ s, q).primeFactors := hs'.symm
    _ = (∏ q ∈ t, q).primeFactors := by rw [heq']
    _ = t := ht'

/-- Support image lies in `products D` (`D = z^{4h+2}`). -/
theorem support_image_subset (α : Type) (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax h : ℕ)
    (D : ℝ) (hD : D = z ^ (4 * h + 2 : ℕ)) :
    (Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).image
      (fun s : Finset ℕ => ∏ q ∈ s, q)
    ⊆ S.products D := by
  intro d hd
  rw [Finset.mem_image] at hd
  obtain ⟨s, hs, rfl⟩ := hd
  have hsq := prod_primes_squarefree s
    (fun p hp => support_prime α S z Jmax h s hs p hp)
  have hpf := support_prod_primeFactors α S z Jmax h s hs
  have hprimes : (∏ q ∈ s, q).primeFactors ⊆ S.primes := by
    rw [hpf]
    exact support_subset_primes α S z Jmax h s hs
  have hz0 : (0 : ℝ) < z := lt_trans one_pos hz
  have hDpos : (0 : ℝ) < D := by rw [hD]; positivity
  have hlevel : ((∏ q ∈ s, q : ℕ) : ℝ) ≤ D := by
    have hle := support_level_le α S z hz h Jmax s hs
    have hcast : ((∏ q ∈ s, q : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := Nat.cast_prod _ _
    rw [hcast, hD]
    exact hle
  have hd1 : 1 ≤ ∏ q ∈ s, q := by
    apply Finset.one_le_prod
    intro p hp
    exact (support_prime α S z Jmax h s hs p hp).pos
  have hdle : ∏ q ∈ s, q ≤ ⌊D⌋₊ :=
    Nat.le_floor hlevel
  unfold Erdos821.Blueprint.SieveData.products
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hd1, hdle⟩, hsq, hprimes⟩

/-- Upper counting: `sifted ≤ X·∏S + remainderSum`. -/
theorem sifted_le_main_add_remainder (α : Type)
    (S : Erdos821.Blueprint.SieveData α)
    (z : ℝ) (hz : 1 < z) (Jmax : ℕ) (hJ : Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C)
    (h : ℕ) (he : Even h) :
    S.sifted ≤ S.X * (∏ j ∈ Finset.range Jmax,
        blockExpS (Block α S z j) S.density ((j + 1) * h))
      + S.remainderSum (z ^ (4 * h + 2 : ℕ)) := by
  have hsupp_le := sifted_le_sum_Uval α S z hz Jmax hJ η C hdb h he
  have hdouble := sum_Uval_eq_double α S z hz Jmax hJ η C hdb h
  -- rewrite `∑ w·Uval` as `∑_s ∑_a`
  have hsupp : Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)
      = Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h) := rfl
  -- main term via weighted support sum
  have hmain : ∑ s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
      (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
      = S.X * (∏ j ∈ Finset.range Jmax,
        blockExpS (Block α S z j) S.density ((j + 1) * h)) := by
    have hweighted := support_weighted_sum_eq (Finset.range Jmax)
      (fun j => Block α S z j) (fun j => (j + 1) * h) S.density
      (fun j₁ _ j₂ _ hne => Block_disjoint α S z hz hne)
    have hg : ∀ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        S.g (∏ q ∈ s, q) = ∏ p ∈ s, S.density p := by
      intro s hs
      exact g_prod_eq α S z Jmax h s hs
    have hsum_eq : ∑ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
        = S.X * ∑ s ∈ Prelim.BlockSieve.SieveSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          ((-1 : ℝ) ^ s.card * ∏ p ∈ s, S.density p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hg s hs]
      ring
    rw [hsum_eq, ← hweighted]
  -- combine inner sums
  have hcombine : ∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Uval
      (Finset.range Jmax) (fun j => Block α S z j)
      (fun j => (j + 1) * h) (badFinset α S a)
      = S.X * (∏ j ∈ Finset.range Jmax,
        blockExpS (Block α S z j) S.density ((j + 1) * h))
        + ∑ s ∈ Prelim.BlockSieve.SieveSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q) := by
    rw [hdouble]
    have hinner : ∀ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        ∑ a ∈ S.objects,
          (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
        = (-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
          + (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q) := by
      intro s hs
      have h1 := inner_sum_eq α S z Jmax h s hs
      rw [h1, mul_add]
    have h1 : ∑ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        ∑ a ∈ S.objects,
          (if s ⊆ badFinset α S a then S.weight a * (-1 : ℝ) ^ s.card else 0)
        = ∑ s ∈ Prelim.BlockSieve.SieveSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          ((-1 : ℝ) ^ s.card * (S.X * S.g (∏ q ∈ s, q))
            + (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q)) :=
      Finset.sum_congr rfl (fun s hs => hinner s hs)
    rw [h1, Finset.sum_add_distrib, hmain]
  -- remainder part `≤ remainderSum`
  have hrem_le : ∑ s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range Jmax).biUnion (fun j => Block α S z j))
      (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
      (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q)
      ≤ S.remainderSum (z ^ (4 * h + 2 : ℕ)) := by
    have hterm : ∀ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q)
        ≤ |S.remainder (∏ q ∈ s, q)| := by
      intro s _
      rcases neg_one_pow_eq_or (R := ℝ) s.card with h1 | h1
      · rw [h1, one_mul]
        exact le_abs_self _
      · rw [h1, neg_one_mul]
        exact neg_le_abs _
    have hsum_abs : ∑ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        (-1 : ℝ) ^ s.card * S.remainder (∏ q ∈ s, q)
        ≤ ∑ s ∈ Prelim.BlockSieve.SieveSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
          |S.remainder (∏ q ∈ s, q)| := by
      apply Finset.sum_le_sum
      intro s hs
      exact hterm s hs
    have himage_eq : ∑ s ∈ Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h),
        |S.remainder (∏ q ∈ s, q)|
        = ∑ d ∈ (Prelim.BlockSieve.SieveSupport
          ((Finset.range Jmax).biUnion (fun j => Block α S z j))
          (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).image
          (fun s : Finset ℕ => ∏ q ∈ s, q),
          |S.remainder d| := by
      rw [Finset.sum_image]
      intro s hs t ht heq
      exact support_prod_injOn α S z Jmax h
        (Finset.mem_coe.mpr hs) (Finset.mem_coe.mpr ht) heq
    have hsub := support_image_subset α S z hz Jmax h
      (z ^ (4 * h + 2 : ℕ)) rfl
    have hle_image : ∑ d ∈ (Prelim.BlockSieve.SieveSupport
        ((Finset.range Jmax).biUnion (fun j => Block α S z j))
        (Finset.range Jmax) (fun j => Block α S z j) (fun j => (j + 1) * h)).image
        (fun s : Finset ℕ => ∏ q ∈ s, q), |S.remainder d|
        ≤ ∑ d ∈ S.products (z ^ (4 * h + 2 : ℕ)), |S.remainder d| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro d _ _
      exact abs_nonneg _
    have hremainder : S.remainderSum (z ^ (4 * h + 2 : ℕ))
        = ∑ d ∈ S.products (z ^ (4 * h + 2 : ℕ)), |S.remainder d| := rfl
    linarith [hsum_abs, himage_eq, hle_image, hremainder]
  linarith [hsupp_le, hcombine, hrem_le]

end PrelimLemmas
end Erdos821
