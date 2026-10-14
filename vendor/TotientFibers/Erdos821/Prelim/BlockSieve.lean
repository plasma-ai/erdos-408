import Mathlib
import Erdos821.Prelim.SieveCalculus

/-!
# Block sieve, pointwise assembly (`lem:sieve`, "more precisely" part)

This file assembles the block polynomials of `lem:sieve` in
`01-preliminaries.tex` at the pointwise (evaluation) level, on top of the
identities in `SieveCalculus`.

Setup: finitely many blocks `B j` of sieve primes (`J : Finset ιb`), even
truncation degrees `e j`, and for each object the finset `bad` of its bad
primes covered by the blocks. With `t_j = |(bad ∩ B j)|`:
* `blkU j = U_j(t_j)` (one-block inclusion–exclusion value),
* `blkI j = 1_{t_j = 0}` (block avoidance),
* `blkE j = C(t_j, e_j + 1)` (degree-`e_j+1` error),
* `Uval = ∏ blkU`, `Vval = Uval - ∑ blkE_j ∏_{k≠j} blkU_k`.

We prove the paper's pointwise claims: `V ≤ 1_{no bad} ≤ U`, `U ≥ 0`,
and that the overcount `U - 1_{no bad}` is dominated by the pointwise
nonnegative `U - V`.

The expanded coefficient/support/level bounds (`|λ_d| ≤ 1` on squarefree
`d ≤ z^{4h+2}`), the expectation estimates (`a_j`, `e_j`, `R_h ≪ e^{-h}`),
the counting conclusion `eq:block-sieve`, and the rough-integer corollary
follow next, using `Mertens` for the density products.
-/

namespace Erdos821
namespace Prelim
namespace BlockSieve

open Finset

variable {ιb : Type*} [DecidableEq ιb]

/-- One-block inclusion–exclusion value at the bad count of the block. -/
def blkU (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (j : ιb) : ℝ :=
  ((SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) : ℤ) : ℝ)

/-- One-block avoidance indicator. -/
def blkI (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (j : ιb) : ℝ :=
  if bad ∩ B j = ∅ then 1 else 0

/-- One-block degree-`(e_j+1)` error value. -/
def blkE (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (j : ιb) : ℝ :=
  (((bad ∩ B j).card.choose (e j + 1) : ℕ) : ℝ)

/-- Upper polynomial value: product of block values. -/
def Uval (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) : ℝ :=
  ∏ j ∈ J, blkU J B e bad j

/-- Lower polynomial value: upper minus the correction sum. -/
def Vval (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) : ℝ :=
  Uval J B e bad - ∑ j ∈ J, blkE J B e bad j * ∏ k ∈ J.erase j, blkU J B e bad k

theorem blkU_nonneg (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (he : ∀ j ∈ J, Even (e j)) {j : ιb} (hj : j ∈ J) :
    0 ≤ blkU J B e bad j := by
  by_cases hempty : bad ∩ B j = ∅
  · have ht0 : (bad ∩ B j).card = 0 := Finset.card_eq_zero.mpr hempty
    have gU : blkU J B e bad j
        = ((SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) : ℤ) : ℝ) := rfl
    rw [gU, ht0, SieveCalculus.blockUpper_zero, Int.cast_one]
    exact zero_le_one
  · have ht1 : 1 ≤ (bad ∩ B j).card := Nat.pos_of_ne_zero (fun hcon =>
      hempty (Finset.card_eq_zero.mp hcon))
    have h := SieveCalculus.blockUpper_nonneg_of_even (e j) _ (he j hj) ht1
    have gU : blkU J B e bad j
        = ((SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) : ℤ) : ℝ) := rfl
    rw [gU]
    exact_mod_cast h

theorem blkI_nonneg (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) {j : ιb} : 0 ≤ blkI J B e bad j := by
  simp only [blkI]
  split_ifs <;> norm_num

theorem blkI_le_blkU (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (he : ∀ j ∈ J, Even (e j)) {j : ιb} (hj : j ∈ J) :
    blkI J B e bad j ≤ blkU J B e bad j := by
  by_cases hempty : bad ∩ B j = ∅
  · have ht0 : (bad ∩ B j).card = 0 := Finset.card_eq_zero.mpr hempty
    have gU : blkU J B e bad j
        = ((SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) : ℤ) : ℝ) := rfl
    have gI : blkI J B e bad j = 1 := by simp only [blkI, if_pos hempty]
    rw [gU, gI, ht0, SieveCalculus.blockUpper_zero, Int.cast_one]
  · have gI : blkI J B e bad j = 0 := by simp only [blkI, if_neg hempty]
    rw [gI]
    exact blkU_nonneg J B e bad he hj

theorem blkU_sub_blkI_le_blkE (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (he : ∀ j ∈ J, Even (e j)) {j : ιb} (hj : j ∈ J) :
    blkU J B e bad j - blkI J B e bad j ≤ blkE J B e bad j := by
  by_cases hempty : bad ∩ B j = ∅
  · have ht0 : (bad ∩ B j).card = 0 := Finset.card_eq_zero.mpr hempty
    have gU : blkU J B e bad j
        = ((SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) : ℤ) : ℝ) := rfl
    have gI : blkI J B e bad j = 1 := by simp only [blkI, if_pos hempty]
    have gE : blkE J B e bad j
        = ((((bad ∩ B j).card.choose (e j + 1) : ℕ)) : ℝ) := rfl
    rw [gU, gI, gE, ht0, SieveCalculus.blockUpper_zero, Int.cast_one, sub_self]
    exact Nat.cast_nonneg _
  · have htne : (bad ∩ B j).card ≠ 0 := fun hcon =>
      hempty (Finset.card_eq_zero.mp hcon)
    have ht1 : 1 ≤ (bad ∩ B j).card := Nat.pos_of_ne_zero htne
    have gU : blkU J B e bad j
        = ((SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) : ℤ) : ℝ) := rfl
    have gI : blkI J B e bad j = 0 := by simp only [blkI, if_neg hempty]
    have gE : blkE J B e bad j
        = ((((bad ∩ B j).card.choose (e j + 1) : ℕ)) : ℝ) := rfl
    rw [gU, gI, gE, sub_zero]
    have h := SieveCalculus.blockUpper_sub_indicator_le_error (e j)
      ((bad ∩ B j).card) (he j hj)
    rw [if_neg htne, sub_zero] at h
    exact_mod_cast h

/-- The product of block avoidances is the global avoidance indicator
(needs every bad prime to live in some block). -/
theorem prod_blkI_eq_avoid (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (hcov : bad ⊆ J.biUnion B) :
    ∏ j ∈ J, blkI J B e bad j = (if bad = ∅ then (1 : ℝ) else 0) := by
  by_cases hb : bad = ∅
  · simp only [if_pos hb]
    apply Finset.prod_eq_one
    intro j _
    simp only [blkI]
    simp [hb]
  · simp only [if_neg hb]
    obtain ⟨p, hpb⟩ := Finset.nonempty_iff_ne_empty.mpr hb
    have hcovp := hcov hpb
    rw [Finset.mem_biUnion] at hcovp
    obtain ⟨j, hjJ, hjB⟩ := hcovp
    apply Finset.prod_eq_zero hjJ
    have hne : ¬ bad ∩ B j = ∅ := by
      intro hcon
      have hmem : p ∈ bad ∩ B j := Finset.mem_inter.mpr ⟨hpb, hjB⟩
      rw [hcon] at hmem
      exact Finset.notMem_empty p hmem
    simp only [blkI, if_neg hne]

/-- The paper's `1_{no bad} ≤ U`: the upper value dominates avoidance. -/
theorem Uval_ge_avoid (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (hcov : bad ⊆ J.biUnion B)
    (he : ∀ j ∈ J, Even (e j)) :
    (if bad = ∅ then (1 : ℝ) else 0) ≤ Uval J B e bad := by
  have hle := SieveCalculus.prod_le_prod_of_nonneg_le J (blkI J B e bad)
    (blkU J B e bad) (fun j _ => blkI_nonneg J B e bad)
    (fun j hj => blkI_le_blkU J B e bad he hj)
  rw [prod_blkI_eq_avoid J B e bad hcov] at hle
  show (if bad = ∅ then (1 : ℝ) else 0) ≤ ∏ j ∈ J, blkU J B e bad j
  exact hle

/-- The paper's `U ≥ 0`. -/
theorem Uval_nonneg (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (he : ∀ j ∈ J, Even (e j)) : 0 ≤ Uval J B e bad :=
  Finset.prod_nonneg (fun j hj => blkU_nonneg J B e bad he hj)

/-- The paper's `V ≤ 1_{no bad}`: the lower value is below avoidance,
by the telescoping inequality. -/
theorem Vval_le_avoid (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (hcov : bad ⊆ J.biUnion B)
    (he : ∀ j ∈ J, Even (e j)) :
    Vval J B e bad ≤ (if bad = ∅ then (1 : ℝ) else 0) := by
  have htele := SieveCalculus.prod_telescope_le J (blkI J B e bad)
    (blkU J B e bad) (blkE J B e bad)
    (fun j _ => blkI_nonneg J B e bad)
    (fun j hj => blkI_le_blkU J B e bad he hj)
    (fun j hj => blkU_sub_blkI_le_blkE J B e bad he hj)
  have hprod := prod_blkI_eq_avoid J B e bad hcov
  have hV : Vval J B e bad
      = ∏ j ∈ J, blkU J B e bad j
        - ∑ j ∈ J, blkE J B e bad j * ∏ k ∈ J.erase j, blkU J B e bad k := rfl
  rw [hV]
  rw [hprod] at htele
  linarith

/-- The overcount `U - 1_{no bad}` is dominated by `U - V`. -/
theorem overcount_le_sub (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (hcov : bad ⊆ J.biUnion B)
    (he : ∀ j ∈ J, Even (e j)) :
    Uval J B e bad - (if bad = ∅ then (1 : ℝ) else 0)
      ≤ Uval J B e bad - Vval J B e bad := by
  have h := Vval_le_avoid J B e bad hcov he
  linarith

/-- The paper's pointwise nonnegativity of `U - V`. -/
theorem Uval_sub_Vval_nonneg (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ) (bad : Finset ℕ) (he : ∀ j ∈ J, Even (e j)) :
    0 ≤ Uval J B e bad - Vval J B e bad := by
  have hV : Uval J B e bad - Vval J B e bad
      = ∑ j ∈ J, blkE J B e bad j * ∏ k ∈ J.erase j, blkU J B e bad k := by
    show Uval J B e bad
        - (Uval J B e bad
          - ∑ j ∈ J, blkE J B e bad j * ∏ k ∈ J.erase j, blkU J B e bad k)
        = ∑ j ∈ J, blkE J B e bad j * ∏ k ∈ J.erase j, blkU J B e bad k
    rw [sub_sub_cancel]
  rw [hV]
  apply Finset.sum_nonneg
  intro j hj
  have hE0 : 0 ≤ blkE J B e bad j := by
    simp only [blkE]
    exact Nat.cast_nonneg _
  have hP0 : 0 ≤ ∏ k ∈ J.erase j, blkU J B e bad k := by
    apply Finset.prod_nonneg
    intro k hk
    exact blkU_nonneg J B e bad he (Finset.mem_of_mem_erase hk)
  exact mul_nonneg hE0 hP0

/-! ## Sieve support, coefficients, and level -/

/-- Sieve support: squarefree indices (as prime sets) within ambient `P`
respecting per-block degree caps. Each `d` here carries coefficient
`(-1)^{|d|}` in the upper polynomial (`eq:sieve-polynomials`). -/
def SieveSupport (P : Finset ℕ) (J : Finset ιb) (B : ιb → Finset ℕ)
    (e : ιb → ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun d => ∀ j ∈ J, (d ∩ B j).card ≤ e j)

theorem mem_sieveSupport (P : Finset ℕ) (J : Finset ιb) (B : ιb → Finset ℕ)
    (e : ιb → ℕ) (d : Finset ℕ) :
    d ∈ SieveSupport P J B e ↔ d ⊆ P ∧ ∀ j ∈ J, (d ∩ B j).card ≤ e j := by
  simp only [SieveSupport, Finset.mem_filter, Finset.mem_powerset]

/-- Block subset sum: summing `(-1)^{|u|}` over subsets of `T` of size at
most `e` gives the one-block value `blockUpper e |T|`. Via
`Finset.sum_powerset_apply_card` (grouping by cardinality) and Mertens-free
range restriction. -/
theorem blockSubsetSum_eq (e : ℕ) (T : Finset ℕ) :
    (∑ u ∈ T.powerset.filter (fun u => u.card ≤ e), (-1 : ℤ) ^ (u.card))
      = SieveCalculus.blockUpper e (T.card) := by
  have hif : (∑ u ∈ T.powerset.filter (fun u => u.card ≤ e), (-1 : ℤ) ^ (u.card))
      = ∑ u ∈ T.powerset, (if u.card ≤ e then (-1 : ℤ) ^ (u.card) else 0) := by
    rw [Finset.sum_filter]
  rw [hif]
  refine (Finset.sum_powerset_apply_card
    (fun m : ℕ => if m ≤ e then (-1 : ℤ) ^ m else 0)).trans ?_
  unfold SieveCalculus.blockUpper
  by_cases hle : e ≤ T.card
  · have hsub : Finset.range (e + 1) ⊆ Finset.range (T.card + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hvan : ∀ x ∈ Finset.range (T.card + 1), x ∉ Finset.range (e + 1) →
        T.card.choose x • (if x ≤ e then (-1 : ℤ) ^ x else 0) = 0 := by
      intro x _ hx
      have hxe : ¬ x ≤ e := by
        intro hle2
        exact hx (Finset.mem_range.mpr (Nat.lt_succ_of_le hle2))
      rw [if_neg hxe, smul_zero]
    rw [← Finset.sum_subset hsub hvan]
    apply Finset.sum_congr rfl
    intro m hm
    have hme : m ≤ e := by
      have hmr := Finset.mem_range.mp hm
      omega
    rw [if_pos hme, nsmul_eq_mul, mul_comm]
  · have hlt : T.card < e := by omega
    have hsub : Finset.range (T.card + 1) ⊆ Finset.range (e + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hvan : ∀ x ∈ Finset.range (e + 1), x ∉ Finset.range (T.card + 1) →
        T.card.choose x • (if x ≤ e then (-1 : ℤ) ^ x else 0) = 0 := by
      intro x _ hx
      have hxT : T.card < x := by
        have hnx : ¬ x < T.card + 1 := fun hlt => hx (Finset.mem_range.mpr hlt)
        omega
      simp only [Nat.choose_eq_zero_of_lt hxT, zero_smul]
    rw [Finset.sum_subset hsub hvan]
    apply Finset.sum_congr rfl
    intro m hm
    have hme : m ≤ e := by
      have hmr := Finset.mem_range.mp hm
      omega
    rw [if_pos hme, nsmul_eq_mul, mul_comm]

/-- Sieve coefficients have absolute value one (paper: "absolute
coefficients at most one"). -/
theorem sieve_coeff_abs_eq_one (d : Finset ℕ) :
    |(-1 : ℤ) ^ (d.card)| = 1 := by
  rcases neg_one_pow_eq_or ℤ d.card with h | h <;> simp [h]

/-- Level bound: a constrained index has product at most the per-block cap
powers (`z^{4h+2}` in the paper follows from the geometric block choice).
Needs the index covered by the blocks and the blocks disjoint. -/
theorem sieve_prod_le (J : Finset ιb) (B : ιb → Finset ℕ) (e : ιb → ℕ)
    (Z : ιb → ℕ) (d : Finset ℕ)
    (hcon : ∀ j ∈ J, ((d ∩ B j).card) ≤ e j)
    (hsub : d ⊆ J.biUnion B)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂))
    (hcaps : ∀ j ∈ J, ∀ p ∈ B j, p ≤ Z j)
    (hZ1 : ∀ j ∈ J, 1 ≤ Z j) :
    ∏ p ∈ d, p ≤ ∏ j ∈ J, Z j ^ (e j) := by
  have hdecomp : J.biUnion (fun j => d ∩ B j) = d := by
    apply le_antisymm
    · intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨j, _, hj⟩ := hp
      exact (Finset.mem_inter.mp hj).1
    · intro p hp
      have hpp := hsub hp
      rw [Finset.mem_biUnion] at hpp ⊢
      obtain ⟨j, hjJ, hjB⟩ := hpp
      exact ⟨j, hjJ, Finset.mem_inter.mpr ⟨hp, hjB⟩⟩
  have hdisj' : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ →
      Disjoint (d ∩ B j₁) (d ∩ B j₂) := by
    intro j₁ h1 j₂ h2 hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have hb1 := (Finset.mem_inter.mp hp1).2
    have hb2 := (Finset.mem_inter.mp hp2).2
    exact (Finset.disjoint_left.mp (hdisj j₁ h1 j₂ h2 hne)) hb1 hb2
  have hPD : Set.PairwiseDisjoint (↑J) (fun j => d ∩ B j) := by
    intro j₁ hj₁ j₂ hj₂ hne
    rw [Finset.mem_coe] at hj₁ hj₂
    exact hdisj' j₁ hj₁ j₂ hj₂ hne
  have hinner : ∀ j ∈ J, ∏ p ∈ d ∩ B j, p ≤ Z j ^ ((d ∩ B j).card) := by
    intro j hj
    calc ∏ p ∈ d ∩ B j, p ≤ ∏ _p ∈ d ∩ B j, Z j :=
          Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _)
            (fun p hp => hcaps j hj p ((Finset.mem_inter.mp hp).2))
      _ = Z j ^ ((d ∩ B j).card) := Finset.prod_const _
  calc ∏ p ∈ d, p = ∏ j ∈ J, ∏ p ∈ d ∩ B j, p := by
        conv_lhs => rw [← hdecomp]
        rw [Finset.prod_biUnion hPD]
    _ ≤ ∏ j ∈ J, Z j ^ (e j) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact Finset.prod_nonneg (fun p _ => Nat.zero_le _)
        · intro j hj
          calc ∏ p ∈ d ∩ B j, p ≤ Z j ^ ((d ∩ B j).card) := hinner j hj
            _ ≤ Z j ^ (e j) :=
                Nat.pow_le_pow_right (by have h := hZ1 j hj; omega) (hcon j hj)

/-- Level bound on the support: every supported index satisfies the
product cap (with ambient covered by the blocks). -/
theorem sieveSupport_prod_le (P : Finset ℕ) (J : Finset ιb) (B : ιb → Finset ℕ)
    (e : ιb → ℕ) (Z : ιb → ℕ) (d : Finset ℕ)
    (hd : d ∈ SieveSupport P J B e) (hP : P ⊆ J.biUnion B)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂))
    (hcaps : ∀ j ∈ J, ∀ p ∈ B j, p ≤ Z j)
    (hZ1 : ∀ j ∈ J, 1 ≤ Z j) :
    ∏ p ∈ d, p ≤ ∏ j ∈ J, Z j ^ (e j) := by
  have hdm := (mem_sieveSupport P J B e d).mp hd
  exact sieve_prod_le J B e Z d hdm.2 (hdm.1.trans hP) hdisj hcaps hZ1

/-- Disjointness gives contradictions from double membership (avoids
chained `disjoint_left.mp` applications through strict-implicit binders). -/
theorem disjoint_mem_false {s t : Finset ℕ} (h : Disjoint s t) {p : ℕ}
    (hps : p ∈ s) (hpt : p ∈ t) : False := by
  have hempty : s ∩ t = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h
  have hmem : p ∈ s ∩ t := Finset.mem_inter.mpr ⟨hps, hpt⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty p hmem

/-- Subset-sum bridge: the upper value equals the signed sum over the
support (`eq:sieve-polynomials`, upper part). Needs disjoint blocks and
the bad set covered by them. Proved by induction on the block set,
splitting indices as `d = (d ∩ B a) ∪ (d \ B a)`; the one-block factor
is `blockSubsetSum_eq`. -/
theorem sieveSupport_sum_eq (P : Finset ℕ) (J : Finset ιb) (B : ιb → Finset ℕ)
    (e : ιb → ℕ) (bad : Finset ℕ)
    (hbad : bad ⊆ P) (hbadcov : bad ⊆ J.biUnion B)
    (hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂)) :
    (∑ d ∈ (SieveSupport P J B e).filter (· ⊆ bad), (-1 : ℤ) ^ (d.card))
      = ∏ j ∈ J, SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) := by
  revert bad hbad hbadcov hdisj
  induction J using Finset.induction with
  | empty =>
    intro bad hbad hbadcov hdisj
    have hbad0 : bad = ∅ := Finset.subset_empty.mp (by simpa using hbadcov)
    subst hbad0
    have hset : (SieveSupport P ∅ B e).filter (· ⊆ (∅ : Finset ℕ)) = {∅} := by
      ext d
      constructor
      · intro hd
        rw [Finset.mem_filter] at hd
        have hd0 : d = ∅ := Finset.subset_empty.mp hd.2
        rw [hd0]
        exact Finset.mem_singleton_self ∅
      · intro hd
        have hd0 : d = ∅ := Finset.mem_singleton.mp hd
        subst hd0
        rw [Finset.mem_filter, mem_sieveSupport]
        exact ⟨⟨Finset.empty_subset _, fun j hj =>
          absurd hj (Finset.notMem_empty j)⟩, Finset.empty_subset _⟩
    rw [hset, Finset.sum_singleton, Finset.card_empty, pow_zero,
      Finset.prod_empty]
  | @insert a s has ih =>
    intro bad hbad hbadcov hdisj
    have hbad' : bad \ B a ⊆ P := Finset.Subset.trans Finset.sdiff_subset hbad
    have hcov' : bad \ B a ⊆ s.biUnion B := by
      intro p hp
      have hpmem : p ∈ bad := (Finset.mem_sdiff.mp hp).1
      have hpnot : p ∉ B a := (Finset.mem_sdiff.mp hp).2
      have hcovp := hbadcov hpmem
      rw [Finset.mem_biUnion] at hcovp ⊢
      obtain ⟨j, hjJ, hjB⟩ := hcovp
      rw [Finset.mem_insert] at hjJ
      cases hjJ with
      | inl hja =>
        subst hja
        exact absurd hjB hpnot
      | inr hjs => exact ⟨j, hjs, hjB⟩
    have hdisj' : ∀ j₁ ∈ s, ∀ j₂ ∈ s, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂) :=
      fun j₁ h1 j₂ h2 hne =>
        hdisj j₁ (Finset.mem_insert_of_mem h1) j₂ (Finset.mem_insert_of_mem h2)
          hne
    have ih' := ih (bad \ B a) hbad' hcov' hdisj'
    have hinter_eq : ∀ j ∈ s, (bad \ B a) ∩ B j = bad ∩ B j := by
      intro j hj
      have hdisjaj : Disjoint (B a) (B j) :=
        hdisj a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
          (fun heq => has (heq.symm ▸ hj))
      ext p
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hpb, -⟩, hpj⟩
        exact ⟨hpb, hpj⟩
      · rintro ⟨hpb, hpj⟩
        refine ⟨⟨hpb, ?_⟩, hpj⟩
        intro hpa
        exact False.elim (disjoint_mem_false hdisjaj hpa hpj)
    have ih'' : (∑ d ∈ (SieveSupport P s B e).filter (· ⊆ bad \ B a),
          (-1 : ℤ) ^ (d.card))
        = ∏ j ∈ s, SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) := by
      rw [ih']
      apply Finset.prod_congr rfl
      intro j hj
      rw [hinter_eq j hj]
    have ha_side : (∑ u ∈ (bad ∩ B a).powerset.filter (fun u => u.card ≤ e a),
          (-1 : ℤ) ^ (u.card))
        = SieveCalculus.blockUpper (e a) ((bad ∩ B a).card) :=
      blockSubsetSum_eq (e a) (bad ∩ B a)
    have hprod : (∏ j ∈ insert a s,
          SieveCalculus.blockUpper (e j) ((bad ∩ B j).card))
        = SieveCalculus.blockUpper (e a) ((bad ∩ B a).card)
          * ∏ j ∈ s, SieveCalculus.blockUpper (e j) ((bad ∩ B j).card) := by
      rw [Finset.prod_insert has]
    have hdecomp : ((SieveSupport P (insert a s) B e).filter (· ⊆ bad))
        = ((((bad ∩ B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
            ((SieveSupport P s B e).filter (· ⊆ bad \ B a))).image
            (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)) := by
      ext d
      simp only [Finset.mem_image]
      constructor
      · intro hd
        rw [Finset.mem_filter] at hd
        obtain ⟨hdsup, hdsub⟩ := hd
        rw [mem_sieveSupport] at hdsup
        obtain ⟨hdP, hcon⟩ := hdsup
        have huP : d ∩ B a ∈ (bad ∩ B a).powerset :=
          Finset.mem_powerset.mpr
            (Finset.inter_subset_inter hdsub (fun p hp => hp))
        have huC : (d ∩ B a).card ≤ e a :=
          hcon a (Finset.mem_insert_self a s)
        have hvP : d \ B a ∈ SieveSupport P s B e := by
          rw [mem_sieveSupport]
          refine ⟨Finset.Subset.trans Finset.sdiff_subset hdP, fun j hj => ?_⟩
          have hdisjaj : Disjoint (B a) (B j) :=
            hdisj a (Finset.mem_insert_self a s) j
              (Finset.mem_insert_of_mem hj) (fun heq => has (heq.symm ▸ hj))
          have hinter : (d \ B a) ∩ B j = d ∩ B j := by
            ext p
            simp only [Finset.mem_inter, Finset.mem_sdiff]
            constructor
            · rintro ⟨⟨hpd, -⟩, hpj⟩
              exact ⟨hpd, hpj⟩
            · rintro ⟨hpd, hpj⟩
              refine ⟨⟨hpd, ?_⟩, hpj⟩
              intro hpa
              exact False.elim (disjoint_mem_false hdisjaj hpa hpj)
          rw [hinter]
          exact hcon j (Finset.mem_insert_of_mem hj)
        have hvsub : d \ B a ⊆ bad \ B a := by
          intro p hp
          rw [Finset.mem_sdiff] at hp ⊢
          exact ⟨hdsub hp.1, hp.2⟩
        have hunion : d ∩ B a ∪ d \ B a = d := by
          ext p
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          tauto
        exact ⟨(d ∩ B a, d \ B a),
          Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨huP, huC⟩,
            Finset.mem_filter.mpr ⟨hvP, hvsub⟩⟩,
          by show d ∩ B a ∪ d \ B a = d; exact hunion⟩
      · intro hd
        obtain ⟨uv, huv, heq⟩ := hd
        rw [Finset.mem_product] at huv
        obtain ⟨huU, huV⟩ := huv
        have heq' : uv.1 ∪ uv.2 = d := heq
        subst d
        rw [Finset.mem_filter] at huU huV
        obtain ⟨huUp, huC⟩ := huU
        obtain ⟨huVsup, huVsub⟩ := huV
        rw [mem_sieveSupport] at huVsup
        obtain ⟨huVP, huVcon⟩ := huVsup
        have huUsub : uv.1 ⊆ bad ∩ B a := Finset.mem_powerset.mp huUp
        have huB : uv.1 ⊆ B a :=
          Finset.Subset.trans huUsub Finset.inter_subset_right
        have hvD : Disjoint uv.2 (B a) :=
          Finset.disjoint_left.mpr (fun p hpv =>
            (Finset.mem_sdiff.mp (huVsub hpv)).2)
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [mem_sieveSupport]
          refine ⟨?_, ?_⟩
          · -- uv.1 ∪ uv.2 ⊆ P
            intro p hp
            rw [Finset.mem_union] at hp
            cases hp with
            | inl hpu => exact hbad (huUsub.trans Finset.inter_subset_left hpu)
            | inr hpv => exact huVP hpv
          · intro j hj
            rw [Finset.mem_insert] at hj
            cases hj with
            | inl hja =>
              subst j
              have hinter_a : (uv.1 ∪ uv.2) ∩ B a = uv.1 := by
                ext p
                simp only [Finset.mem_inter, Finset.mem_union]
                constructor
                · rintro ⟨hp | hp, hpa⟩
                  · exact hp
                  · exact False.elim (disjoint_mem_false hvD hp hpa)
                · intro hp
                  exact ⟨Or.inl hp, huB hp⟩
              rw [hinter_a]
              exact huC
            | inr hjs =>
              have hdisjaj : Disjoint (B a) (B j) :=
                hdisj a (Finset.mem_insert_self a s) j
                  (Finset.mem_insert_of_mem hjs)
                  (fun heq => has (heq.symm ▸ hjs))
              have hinter_j : (uv.1 ∪ uv.2) ∩ B j = uv.2 ∩ B j := by
                ext p
                simp only [Finset.mem_inter, Finset.mem_union]
                constructor
                · rintro ⟨hp | hp, hpj⟩
                  · exact False.elim
                      (disjoint_mem_false hdisjaj (huB hp) hpj)
                  · exact ⟨hp, hpj⟩
                · rintro ⟨hpv, hpj⟩
                  exact ⟨Or.inr hpv, hpj⟩
              rw [hinter_j]
              exact huVcon j hjs
        · intro p hp
          rw [Finset.mem_union] at hp
          cases hp with
          | inl hpu =>
            exact huUsub.trans Finset.inter_subset_left hpu
          | inr hpv =>
            exact huVsub.trans Finset.sdiff_subset hpv
    have hinj : Set.InjOn (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)
        ↑(((bad ∩ B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
          ((SieveSupport P s B e).filter (· ⊆ bad \ B a))) := by
      intro uv huv uv' huv' heq
      have heq' : uv.1 ∪ uv.2 = uv'.1 ∪ uv'.2 := heq
      obtain ⟨hu1, hu2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv)
      obtain ⟨hu1', hu2'⟩ := Finset.mem_product.mp (Finset.mem_coe.mp huv')
      have huB : uv.1 ⊆ B a := by
        have hsub : uv.1 ⊆ bad ∩ B a :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hu1).1
        exact Finset.Subset.trans hsub Finset.inter_subset_right
      have huB' : uv'.1 ⊆ B a := by
        have hsub : uv'.1 ⊆ bad ∩ B a :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hu1').1
        exact Finset.Subset.trans hsub Finset.inter_subset_right
      have hvD : Disjoint uv.2 (B a) := by
        have hsub : uv.2 ⊆ bad \ B a :=
          (Finset.mem_filter.mp hu2).2
        exact Finset.disjoint_left.mpr (fun p hp =>
          (Finset.mem_sdiff.mp (hsub hp)).2)
      have hvD' : Disjoint uv'.2 (B a) := by
        have hsub : uv'.2 ⊆ bad \ B a :=
          (Finset.mem_filter.mp hu2').2
        exact Finset.disjoint_left.mpr (fun p hp =>
          (Finset.mem_sdiff.mp (hsub hp)).2)
      have rec1 : uv.1 = (uv.1 ∪ uv.2) ∩ B a := by
        ext p
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · intro hp
          exact ⟨Or.inl hp, huB hp⟩
        · rintro ⟨hp | hp, hpa⟩
          · exact hp
          · exact False.elim (disjoint_mem_false hvD hp hpa)
      have rec1' : uv'.1 = (uv'.1 ∪ uv'.2) ∩ B a := by
        ext p
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · intro hp
          exact ⟨Or.inl hp, huB' hp⟩
        · rintro ⟨hp | hp, hpa⟩
          · exact hp
          · exact False.elim (disjoint_mem_false hvD' hp hpa)
      have rec2 : uv.2 = (uv.1 ∪ uv.2) \ B a := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro hp
          exact ⟨Or.inr hp, fun h => disjoint_mem_false hvD hp h⟩
        · rintro ⟨hp | hp, hnb⟩
          · exact absurd (huB hp) hnb
          · exact hp
      have rec2' : uv'.2 = (uv'.1 ∪ uv'.2) \ B a := by
        ext p
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro hp
          exact ⟨Or.inr hp, fun h => disjoint_mem_false hvD' hp h⟩
        · rintro ⟨hp | hp, hnb⟩
          · exact absurd (huB' hp) hnb
          · exact hp
      have e1 : uv.1 = uv'.1 := by rw [rec1, rec1', heq']
      have e2 : uv.2 = uv'.2 := by rw [rec2, rec2', heq']
      exact Prod.ext e1 e2
    have himg : (∑ d ∈ ((((bad ∩ B a).powerset.filter
            (fun u => u.card ≤ e a)) ×ˢ
            ((SieveSupport P s B e).filter (· ⊆ bad \ B a))).image
            (fun uv : Finset ℕ × Finset ℕ => uv.1 ∪ uv.2)),
          (-1 : ℤ) ^ (d.card))
        = ∑ uv ∈ ((bad ∩ B a).powerset.filter (fun u => u.card ≤ e a)) ×ˢ
          ((SieveSupport P s B e).filter (· ⊆ bad \ B a)),
          (-1 : ℤ) ^ ((uv.1 ∪ uv.2).card) :=
      Finset.sum_image hinj
    have hdouble : (∑ uv ∈ ((bad ∩ B a).powerset.filter
            (fun u => u.card ≤ e a)) ×ˢ
            ((SieveSupport P s B e).filter (· ⊆ bad \ B a)),
          (-1 : ℤ) ^ ((uv.1 ∪ uv.2).card))
        = (∑ u ∈ (bad ∩ B a).powerset.filter (fun u => u.card ≤ e a),
            (-1 : ℤ) ^ (u.card))
          * (∑ v ∈ (SieveSupport P s B e).filter (· ⊆ bad \ B a),
            (-1 : ℤ) ^ (v.card)) := by
      have eprod : (∑ uv ∈ ((bad ∩ B a).powerset.filter
              (fun u => u.card ≤ e a)) ×ˢ
              ((SieveSupport P s B e).filter (· ⊆ bad \ B a)),
            (-1 : ℤ) ^ ((uv.1 ∪ uv.2).card))
          = ∑ u ∈ (bad ∩ B a).powerset.filter (fun u => u.card ≤ e a),
            ∑ v ∈ (SieveSupport P s B e).filter (· ⊆ bad \ B a),
            (-1 : ℤ) ^ ((u ∪ v).card) :=
        Finset.sum_product _ _ _
      have emul : (∑ u ∈ (bad ∩ B a).powerset.filter (fun u => u.card ≤ e a),
            (-1 : ℤ) ^ (u.card))
          * (∑ v ∈ (SieveSupport P s B e).filter (· ⊆ bad \ B a),
            (-1 : ℤ) ^ (v.card))
          = ∑ u ∈ (bad ∩ B a).powerset.filter (fun u => u.card ≤ e a),
            ∑ v ∈ (SieveSupport P s B e).filter (· ⊆ bad \ B a),
            (-1 : ℤ) ^ (u.card) * (-1 : ℤ) ^ (v.card) :=
        Finset.sum_mul_sum _ _ _ _
      rw [eprod, emul]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have huB : u ⊆ B a := by
        have hsub : u ⊆ bad ∩ B a :=
          Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
        exact Finset.Subset.trans hsub Finset.inter_subset_right
      have hvD : Disjoint v (B a) := by
        have hsub : v ⊆ bad \ B a := (Finset.mem_filter.mp hv).2
        exact Finset.disjoint_left.mpr (fun p hp =>
          (Finset.mem_sdiff.mp (hsub hp)).2)
      have hdisjuv : Disjoint u v :=
        Finset.disjoint_left.mpr (fun p hpu hpv =>
          disjoint_mem_false hvD hpv (huB hpu))
      rw [Finset.card_union_of_disjoint hdisjuv, pow_add]
    rw [hdecomp, himg, hdouble, ha_side, ih'', hprod.symm]

end BlockSieve
end Prelim
end Erdos821
