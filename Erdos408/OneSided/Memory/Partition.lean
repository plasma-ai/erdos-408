import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum

/-!
# The partition identity for distinct births

PD `mem:partition-identity` and `mem:rank-coefficients` (`blueprint/one_sided_type_ii.md`
§13, M10). Let `β : α → Option ℕ` assign to each birth address its prime, or `none` if the
address is not performed. A block `C` is *realized* when every address of `C` is performed
with one common prime. Then the indicator that the performed values are distinct is
`∑_𝒞 ∏_{C ∈ 𝒞} (-1)^{|C| - 1} (|C| - 1)! [C realized]`, over collections `𝒞` of pairwise
disjoint blocks of size at least two. The coefficient mass at rank
`r(𝒞) = ∑_C (|C| - 1)` is at most `|α|^{2r}`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The performed values of `β` are pairwise distinct. -/
def BirthsDistinct (β : α → Option ℕ) : Prop :=
  ∀ a a' p, β a = some p → β a' = some p → a = a'

/-- The block `C` is realized: every address of `C` is performed, all with one prime. -/
def BlockRealized (β : α → Option ℕ) (C : Finset α) : Prop :=
  ∃ p, ∀ a ∈ C, β a = some p

open scoped Classical in
/-- The collections of pairwise disjoint blocks of size at least two. -/
def blockSystems (α : Type*) [Fintype α] [DecidableEq α] : Finset (Finset (Finset α)) :=
  univ.filter fun 𝒞 => (𝒞 : Set (Finset α)).PairwiseDisjoint id ∧ ∀ C ∈ 𝒞, 2 ≤ #C

/-- The rank `r(𝒞) = ∑_{C ∈ 𝒞} (|C| - 1)` of a block system. -/
def blockRank (𝒞 : Finset (Finset α)) : ℕ := ∑ C ∈ 𝒞, (#C - 1)

/-- The coefficient `∏_{C ∈ 𝒞} (-1)^{|C| - 1} (|C| - 1)!` of a block system. -/
def blockCoef (𝒞 : Finset (Finset α)) : ℤ := ∏ C ∈ 𝒞, (-1) ^ (#C - 1) * (#C - 1).factorial

/-! ### Block systems inside a set of addresses -/

open scoped Classical in
/-- The block systems whose blocks all lie in `S`. -/
private def blockSystemsIn (S : Finset α) : Finset (Finset (Finset α)) :=
  (blockSystems α).filter fun 𝒞 => ∀ C ∈ 𝒞, C ⊆ S

/-- Membership in `blockSystemsIn S`. -/
private theorem mem_blockSystemsIn {S : Finset α} {𝒞 : Finset (Finset α)} :
    𝒞 ∈ blockSystemsIn S ↔
      (𝒞 : Set (Finset α)).PairwiseDisjoint id ∧ ∀ C ∈ 𝒞, 2 ≤ #C ∧ C ⊆ S := by
  simp only [blockSystemsIn, blockSystems, mem_filter, mem_univ, true_and, and_assoc]
  constructor
  · rintro ⟨hd, h2, hS⟩
    exact ⟨hd, fun C hC => ⟨h2 C hC, hS C hC⟩⟩
  · rintro ⟨hd, h⟩
    exact ⟨hd, fun C hC => (h C hC).1, fun C hC => (h C hC).2⟩

/-- Every block system lies in `univ`. -/
private theorem blockSystemsIn_univ : blockSystemsIn (univ : Finset α) = blockSystems α :=
  filter_true_of_mem fun _ _ C _ => subset_univ C

/-- The only block system inside `∅` is the empty one. -/
private theorem blockSystemsIn_empty : blockSystemsIn (∅ : Finset α) = {∅} := by
  ext 𝒞
  rw [mem_blockSystemsIn, mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    refine eq_empty_of_forall_notMem fun C hC => ?_
    have h2 := (h C hC).1
    rw [subset_empty.1 (h C hC).2, card_empty] at h2
    omega
  · rintro rfl
    simp

/-- A block system inside `T \ B` has no block through an address outside `T`. -/
private theorem insert_notMem_of_mem_blockSystemsIn {a : α} {T B B' : Finset α}
    {𝒞 : Finset (Finset α)} (ha : a ∉ T) (h𝒞 : 𝒞 ∈ blockSystemsIn (T \ B)) :
    insert a B' ∉ 𝒞 := fun h =>
  ha (mem_sdiff.1 (((mem_blockSystemsIn.1 h𝒞).2 _ h).2 (mem_insert_self a B'))).1

/-- Splitting the block systems inside `insert a T` by the block through `a`: either no block
contains `a`, or that block is `insert a B` for a nonempty `B ⊆ T` and the other blocks form a
block system inside `T \ B`. -/
private theorem sum_blockSystemsIn_insert {M : Type*} [AddCommMonoid M] {a : α} {T : Finset α}
    (ha : a ∉ T) (Φ : Finset (Finset α) → M) :
    ∑ 𝒞 ∈ blockSystemsIn (insert a T), Φ 𝒞 =
      ∑ 𝒞 ∈ blockSystemsIn T, Φ 𝒞 +
        ∑ B ∈ T.powerset.filter (·.Nonempty),
          ∑ 𝒞 ∈ blockSystemsIn (T \ B), Φ (insert (insert a B) 𝒞) := by
  rw [← sum_filter_not_add_sum_filter _ fun 𝒞 => ∃ C ∈ 𝒞, a ∈ C]
  congr 1
  · refine sum_congr ?_ fun _ _ => rfl
    ext 𝒞
    simp only [mem_filter, mem_blockSystemsIn, not_exists, not_and]
    constructor
    · rintro ⟨⟨hd, h⟩, haC⟩
      exact ⟨hd, fun C hC =>
        ⟨(h C hC).1, (subset_insert_iff_of_notMem (haC C hC)).1 (h C hC).2⟩⟩
    · rintro ⟨hd, h⟩
      exact ⟨⟨hd, fun C hC => ⟨(h C hC).1, (h C hC).2.trans (subset_insert a T)⟩⟩,
        fun C hC haC => ha ((h C hC).2 haC)⟩
  · rw [sum_sigma']
    symm
    refine sum_bij (fun x _ => insert (insert a x.1) x.2) ?_ ?_ ?_ fun _ _ => rfl
    · rintro ⟨B, 𝒞⟩ hx
      simp only [mem_sigma, mem_filter, mem_powerset] at hx
      obtain ⟨⟨hBT, hB⟩, h𝒞⟩ := hx
      obtain ⟨hd, h⟩ := mem_blockSystemsIn.1 h𝒞
      have haB : a ∉ B := fun h => ha (hBT h)
      refine mem_filter.2 ⟨mem_blockSystemsIn.2 ⟨?_, ?_⟩,
        insert a B, mem_insert_self _ _, mem_insert_self _ _⟩
      · rw [coe_insert]
        refine hd.insert fun C hC _ => ?_
        have hCT := (h C hC).2
        show Disjoint (insert a B) C
        exact disjoint_insert_left.2
          ⟨fun h => ha (mem_sdiff.1 (hCT h)).1, disjoint_sdiff.mono_right hCT⟩
      · refine (forall_mem_insert _ _ _).2 ⟨⟨?_, insert_subset_insert a hBT⟩, fun C hC =>
          ⟨(h C hC).1, (h C hC).2.trans (sdiff_subset.trans (subset_insert a T))⟩⟩
        rw [card_insert_of_notMem haB]
        have := hB.card_pos
        omega
    · rintro ⟨B₁, 𝒞₁⟩ hx₁ ⟨B₂, 𝒞₂⟩ hx₂ h
      dsimp only at h
      simp only [mem_sigma, mem_filter, mem_powerset] at hx₁ hx₂
      have h𝒞₁ := insert_notMem_of_mem_blockSystemsIn (B' := B₁) ha hx₁.2
      have h𝒞₂ := insert_notMem_of_mem_blockSystemsIn (B' := B₂) ha hx₂.2
      have hB : insert a B₁ = insert a B₂ := by
        have h₁ := mem_insert_self (insert a B₁) 𝒞₁
        rw [h, mem_insert] at h₁
        exact h₁.resolve_right (insert_notMem_of_mem_blockSystemsIn ha hx₂.2)
      obtain rfl : B₁ = B₂ :=
        calc B₁ = (insert a B₁).erase a := (erase_insert fun h => ha (hx₁.1.1 h)).symm
          _ = (insert a B₂).erase a := by rw [hB]
          _ = B₂ := erase_insert fun h => ha (hx₂.1.1 h)
      obtain rfl : 𝒞₁ = 𝒞₂ :=
        calc 𝒞₁ = (insert (insert a B₁) 𝒞₁).erase (insert a B₁) := (erase_insert h𝒞₁).symm
          _ = (insert (insert a B₁) 𝒞₂).erase (insert a B₁) := by rw [h]
          _ = 𝒞₂ := erase_insert h𝒞₂
      rfl
    · intro 𝒞 h𝒞
      obtain ⟨h𝒞S, C, hC, haC⟩ := mem_filter.1 h𝒞
      obtain ⟨hd, h⟩ := mem_blockSystemsIn.1 h𝒞S
      refine ⟨⟨C.erase a, 𝒞.erase C⟩, ?_, ?_⟩
      · simp only [mem_sigma, mem_filter, mem_powerset]
        refine ⟨⟨subset_insert_iff.1 (h C hC).2, ?_⟩, mem_blockSystemsIn.2
          ⟨hd.subset (coe_subset.2 (erase_subset C 𝒞)), fun C' hC' => ?_⟩⟩
        · rw [← card_pos, card_erase_of_mem haC]
          have := (h C hC).1
          omega
        · obtain ⟨hne, hC'⟩ := mem_erase.1 hC'
          have hdisj : Disjoint C' C := hd hC' hC hne
          refine ⟨(h C' hC').1, subset_sdiff.2 ⟨?_, hdisj.mono_right (erase_subset a C)⟩⟩
          exact (subset_insert_iff_of_notMem (disjoint_right.1 hdisj haC)).1 (h C' hC').2
      · dsimp only
        rw [insert_erase haC, insert_erase hC]

/-! ### Distinctness on a set of addresses -/

/-- The performed values of `β` on `S` are pairwise distinct. -/
private def DistinctOn (β : α → Option ℕ) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ a' ∈ S, ∀ p, β a = some p → β a' = some p → a = a'

omit [Fintype α] [DecidableEq α] in
/-- Distinctness passes to subsets. -/
private theorem DistinctOn.mono {β : α → Option ℕ} {S S' : Finset α} (h : DistinctOn β S)
    (hS : S' ⊆ S) : DistinctOn β S' :=
  fun a ha a' ha' p hp hp' => h a (hS ha) a' (hS ha') p hp hp'

omit [Fintype α] in
/-- For `B` inside the class `P` of addresses of `T` performed with the prime `p`,
distinctness on `T \ B` is distinctness away from `P` with at most one survivor of `P`. -/
private theorem distinctOn_sdiff_iff {β : α → Option ℕ} {T P B : Finset α} {p : ℕ}
    (hP : P = T.filter (β · = some p)) (hB : B ⊆ P) :
    DistinctOn β (T \ B) ↔ DistinctOn β (T \ P) ∧ #(P \ B) ≤ 1 := by
  subst hP
  constructor
  · intro h
    refine ⟨h.mono (sdiff_subset_sdiff subset_rfl hB), card_le_one.2 fun x hx x' hx' => ?_⟩
    simp only [mem_sdiff, mem_filter] at hx hx'
    exact h x (mem_sdiff.2 ⟨hx.1.1, hx.2⟩) x' (mem_sdiff.2 ⟨hx'.1.1, hx'.2⟩) p hx.1.2 hx'.1.2
  · rintro ⟨hd, hc⟩ x hx x' hx' q hq hq'
    simp only [mem_sdiff] at hx hx'
    by_cases hxp : β x = some p
    · have hqp : q = p := Option.some_inj.1 (hq.symm.trans hxp)
      rw [hqp] at hq hq'
      exact card_le_one.1 hc x (mem_sdiff.2 ⟨mem_filter.2 ⟨hx.1, hq⟩, hx.2⟩)
        x' (mem_sdiff.2 ⟨mem_filter.2 ⟨hx'.1, hq'⟩, hx'.2⟩)
    · have hx'p : β x' ≠ some p := fun h => hxp (hq.trans (hq'.symm.trans h))
      exact hd x (mem_sdiff.2 ⟨hx.1, fun h => hxp (mem_filter.1 h).2⟩)
        x' (mem_sdiff.2 ⟨hx'.1, fun h => hx'p (mem_filter.1 h).2⟩) q hq hq'

omit [Fintype α] in
/-- Adding an address `a` performed with the prime `p`: distinctness on `insert a T` is
distinctness away from the class `P` of `p` in `T`, with `P` empty. -/
private theorem distinctOn_insert_iff {β : α → Option ℕ} {a : α} {T P : Finset α} {p : ℕ}
    (hβ : β a = some p) (ha : a ∉ T) (hP : P = T.filter (β · = some p)) :
    DistinctOn β (insert a T) ↔ DistinctOn β (T \ P) ∧ #P = 0 := by
  subst hP
  constructor
  · intro h
    refine ⟨h.mono (sdiff_subset.trans (subset_insert a T)), card_eq_zero.2 ?_⟩
    refine filter_eq_empty_iff.2 fun x hx hxp => ?_
    exact ha (h x (mem_insert_of_mem hx) a (mem_insert_self a T) p hxp hβ ▸ hx)
  · rintro ⟨hd, hc⟩
    have hT : ∀ x ∈ T, β x ≠ some p := fun x hx => filter_eq_empty_iff.1 (card_eq_zero.1 hc) hx
    rw [card_eq_zero.1 hc, sdiff_empty] at hd
    intro x hx x' hx' q hq hq'
    rcases mem_insert.1 hx with rfl | hxT <;> rcases mem_insert.1 hx' with rfl | hxT'
    · rfl
    · exact absurd (hq'.trans (hq.symm.trans hβ)) (hT x' hxT')
    · exact absurd (hq.trans (hq'.symm.trans hβ)) (hT x hxT)
    · exact hd x hxT x' hxT' q hq hq'

omit [Fintype α] [DecidableEq α] in
/-- The alternating factorial sum over the nonempty `B ⊆ P` with `|P \ B| ≤ 1` turns
`[|P| ≤ 1]` into `[|P| = 0]`. -/
private theorem indicator_card_eq_zero (P : Finset α) :
    (if #P = 0 then 1 else 0 : ℤ) = (if #P ≤ 1 then 1 else 0) +
      ∑ B ∈ P.powerset.filter (·.Nonempty),
        (-1) ^ #B * ((#B).factorial : ℤ) * if #P - #B ≤ 1 then 1 else 0 := by
  rw [sum_filter]
  simp_rw [← card_pos]
  have h := sum_powerset_apply_card (x := P) fun k =>
    if 0 < k then (-1) ^ k * (k.factorial : ℤ) * (if #P - k ≤ 1 then 1 else 0) else 0
  rw [h]
  generalize #P = m
  match m with
  | 0 => simp
  | 1 => simp [sum_range_succ]
  | j + 2 =>
    rw [sum_range_succ, sum_range_succ, sum_eq_zero fun k hk => ?_]
    · have h₁ : (j + 2).choose (j + 1) = j + 2 := Nat.choose_succ_self_right (j + 1)
      have h₂ : j + 2 - (j + 1) = 1 := by omega
      have h₃ : ((j + 2).factorial : ℤ) = (j + 2) * (j + 1).factorial := by
        push_cast [Nat.factorial_succ]
        ring
      simp only [h₁, h₂, h₃, Nat.choose_self, Nat.sub_self, nsmul_eq_mul]
      simp
      ring
    · have : ¬j + 2 - k ≤ 1 := by
        have := mem_range.1 hk
        omega
      simp [this]

open scoped Classical in
/-- The signed weight `(-1)^{|C| - 1} (|C| - 1)! [C realized]` of a block. -/
private def blockWeight (β : α → Option ℕ) (C : Finset α) : ℤ :=
  (-1) ^ (#C - 1) * (#C - 1).factorial * if BlockRealized β C then 1 else 0

omit [Fintype α] in
open scoped Classical in
/-- Distinctness satisfies the recursion of `sum_blockSystemsIn_insert` with the weights
`blockWeight`. -/
private theorem distinctOn_insert_indicator (β : α → Option ℕ) {a : α} {T : Finset α}
    (ha : a ∉ T) :
    (if DistinctOn β (insert a T) then 1 else 0 : ℤ) =
      (if DistinctOn β T then 1 else 0) +
        ∑ B ∈ T.powerset.filter (·.Nonempty),
          blockWeight β (insert a B) * if DistinctOn β (T \ B) then 1 else 0 := by
  cases hβ : β a with
  | none =>
    have hw : ∀ B, blockWeight β (insert a B) = 0 := fun B => by
      have : ¬BlockRealized β (insert a B) := fun ⟨p, hp⟩ => by
        have := hp a (mem_insert_self a B)
        rw [hβ] at this
        cases this
      simp only [blockWeight, this, ↓reduceIte, mul_zero]
    have hD : DistinctOn β (insert a T) ↔ DistinctOn β T := by
      refine ⟨fun h => h.mono (subset_insert a T), fun h x hx x' hx' p hp hp' => ?_⟩
      rcases mem_insert.1 hx with rfl | hxT
      · rw [hβ] at hp
        cases hp
      rcases mem_insert.1 hx' with rfl | hxT'
      · rw [hβ] at hp'
        cases hp'
      exact h x hxT x' hxT' p hp hp'
    simp only [hD, hw, zero_mul, sum_const_zero, add_zero]
  | some p =>
    obtain ⟨P, hP⟩ : ∃ P, P = T.filter (β · = some p) := ⟨_, rfl⟩
    have hPT : P ⊆ T := hP ▸ filter_subset _ _
    have hw : ∀ B ⊆ T, blockWeight β (insert a B) =
        (-1) ^ #B * ((#B).factorial : ℤ) * if B ⊆ P then 1 else 0 := fun B hB => by
      have hR : BlockRealized β (insert a B) ↔ B ⊆ P := by
        subst hP
        constructor
        · rintro ⟨q, hq⟩ x hx
          have hqp : q = p := by
            have := hq a (mem_insert_self a B)
            rw [hβ] at this
            exact (Option.some_inj.1 this).symm
          exact mem_filter.2 ⟨hB hx, hqp ▸ hq x (mem_insert_of_mem hx)⟩
        · intro h
          exact ⟨p, (forall_mem_insert _ _ _).2 ⟨hβ, fun x hx => (mem_filter.1 (h hx)).2⟩⟩
      rw [blockWeight, card_insert_of_notMem fun h => ha (hB h), Nat.add_sub_cancel]
      by_cases h : B ⊆ P <;> simp [h, hR]
    have hsub : P.powerset.filter (·.Nonempty) ⊆ T.powerset.filter (·.Nonempty) :=
      filter_subset_filter _ (powerset_mono.2 hPT)
    have hzero : ∀ B ∈ T.powerset.filter (·.Nonempty), B ∉ P.powerset.filter (·.Nonempty) →
        blockWeight β (insert a B) * (if DistinctOn β (T \ B) then 1 else 0) = 0 := by
      intro B hB hB'
      simp only [mem_filter, mem_powerset] at hB hB'
      have : ¬B ⊆ P := fun h => hB' ⟨h, hB.2⟩
      rw [hw B hB.1]
      simp [this]
    rw [← sum_subset hsub hzero]
    have hT := distinctOn_sdiff_iff hP (empty_subset _)
    rw [sdiff_empty, sdiff_empty] at hT
    by_cases hd : DistinctOn β (T \ P)
    · have hB : ∀ B ∈ P.powerset.filter (·.Nonempty),
          blockWeight β (insert a B) * (if DistinctOn β (T \ B) then 1 else 0) =
            (-1) ^ #B * ((#B).factorial : ℤ) * if #P - #B ≤ 1 then 1 else 0 := by
        intro B hB
        have hBP : B ⊆ P := mem_powerset.1 (mem_filter.1 hB).1
        rw [hw B (hBP.trans hPT), distinctOn_sdiff_iff hP hBP, card_sdiff_of_subset hBP]
        simp [hBP, hd]
      rw [distinctOn_insert_iff hβ ha hP, hT, sum_congr rfl hB]
      simp only [hd, true_and]
      exact indicator_card_eq_zero P
    · have hB : ∀ B ∈ P.powerset.filter (·.Nonempty),
          blockWeight β (insert a B) * (if DistinctOn β (T \ B) then 1 else 0) = 0 := by
        intro B hB
        rw [distinctOn_sdiff_iff hP (mem_powerset.1 (mem_filter.1 hB).1)]
        simp [hd]
      rw [distinctOn_insert_iff hβ ha hP, hT, sum_congr rfl hB]
      simp [hd]

open scoped Classical in
/-- The partition identity on a set `S` of addresses. -/
private theorem distinctOn_indicator_eq (β : α → Option ℕ) (S : Finset α) :
    (if DistinctOn β S then 1 else 0 : ℤ) =
      ∑ 𝒞 ∈ blockSystemsIn S, ∏ C ∈ 𝒞, blockWeight β C := by
  induction S using Finset.strongInduction with
  | H S ih =>
    obtain rfl | ⟨a, haS⟩ := S.eq_empty_or_nonempty
    · rw [blockSystemsIn_empty, sum_singleton, prod_empty]
      simp [DistinctOn]
    obtain ⟨T, ha, rfl⟩ : ∃ T, a ∉ T ∧ insert a T = S :=
      ⟨S.erase a, notMem_erase a S, insert_erase haS⟩
    rw [sum_blockSystemsIn_insert ha, distinctOn_insert_indicator β ha, ih T (ssubset_insert ha)]
    congr 1
    refine sum_congr rfl fun B _ => ?_
    rw [ih _ (sdiff_subset.trans_ssubset (ssubset_insert ha)), mul_sum]
    refine sum_congr rfl fun 𝒞 h𝒞 => ?_
    rw [prod_insert (insert_notMem_of_mem_blockSystemsIn ha h𝒞)]

/-! ### Rank coefficients -/

/-- The coefficient mass `∑ ∏_{C ∈ 𝒞} (|C| - 1)!` of the block systems of rank `r` inside
`S`. -/
private def rankMass (r : ℕ) (S : Finset α) : ℕ :=
  ∑ 𝒞 ∈ blockSystemsIn S, if blockRank 𝒞 = r then ∏ C ∈ 𝒞, (#C - 1).factorial else 0

/-- The arithmetic step of the rank bound:
`n^{2r} + ∑_{1 ≤ k ≤ r} C(n, k) k! n^{2(r - k)} ≤ (n + 1)^{2r}`. -/
private theorem rank_step_le (n r : ℕ) :
    n ^ (2 * r) + ∑ k ∈ range (n + 1), n.choose k •
        (if 0 < k ∧ k ≤ r then k.factorial * n ^ (2 * (r - k)) else 0) ≤
      (n + 1) ^ (2 * r) := by
  calc n ^ (2 * r) + ∑ k ∈ range (n + 1), n.choose k •
          (if 0 < k ∧ k ≤ r then k.factorial * n ^ (2 * (r - k)) else 0)
      ≤ n ^ (2 * r) + ∑ k ∈ range (n + 1), if 0 < k ∧ k ≤ r then n ^ (2 * r - k) else 0 := by
        gcongr with k
        split_ifs with hk
        · rw [nsmul_eq_mul, Nat.cast_id, ← mul_assoc, mul_comm (n.choose k),
            ← Nat.descFactorial_eq_factorial_mul_choose]
          calc n.descFactorial k * n ^ (2 * (r - k)) ≤ n ^ k * n ^ (2 * (r - k)) :=
                Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow n k)
            _ = n ^ (2 * r - k) := by
                rw [← pow_add]
                congr 1
                omega
        · simp
    _ ≤ n ^ (2 * r) + ∑ k ∈ range (r + 1), if 0 < k ∧ k ≤ r then n ^ (2 * r - k) else 0 := by
        refine Nat.add_le_add_left ?_ _
        rw [← sum_filter_of_ne (p := (· ≤ r)) fun k _ hk => ?_]
        · exact sum_le_sum_of_subset fun k hk => mem_range.2 (by
            have := (mem_filter.1 hk).2
            omega)
        · by_contra h
          simp_all
    _ = ∑ k ∈ range (r + 1), n ^ (2 * r - k) := by
        rw [sum_range_succ' _ r, sum_range_succ' _ r]
        simp only [lt_self_iff_false, false_and, ↓reduceIte, add_zero, Nat.sub_zero]
        rw [add_comm]
        congr 1
        refine sum_congr rfl fun k hk => ?_
        have : 0 < k + 1 ∧ k + 1 ≤ r := ⟨k.succ_pos, mem_range.1 hk⟩
        simp only [this, and_self, ↓reduceIte]
    _ ≤ ∑ k ∈ range (r + 1), n ^ (2 * r - k) * (2 * r).choose k :=
        sum_le_sum fun k hk =>
          Nat.le_mul_of_pos_right _ (Nat.choose_pos (by have := mem_range.1 hk; omega))
    _ ≤ ∑ k ∈ range (2 * r + 1), n ^ (2 * r - k) * (2 * r).choose k :=
        sum_le_sum_of_subset (range_subset_range.2 (by omega))
    _ = (n + 1) ^ (2 * r) := by
        rw [add_comm n 1, add_pow]
        simp only [one_pow, one_mul, Nat.cast_id]

/-- The rank bound on a set `S` of addresses. -/
private theorem rankMass_le (r : ℕ) (S : Finset α) : rankMass r S ≤ #S ^ (2 * r) := by
  induction S using Finset.strongInduction generalizing r with
  | H S ih =>
    obtain rfl | ⟨a, haS⟩ := S.eq_empty_or_nonempty
    · rw [rankMass, blockSystemsIn_empty, sum_singleton, card_empty]
      rcases r with _ | r <;> simp [blockRank]
    obtain ⟨T, ha, rfl⟩ : ∃ T, a ∉ T ∧ insert a T = S :=
      ⟨S.erase a, notMem_erase a S, insert_erase haS⟩
    have hB : ∀ B ∈ T.powerset.filter (·.Nonempty),
        ∑ 𝒞 ∈ blockSystemsIn (T \ B), (if blockRank (insert (insert a B) 𝒞) = r then
            ∏ C ∈ insert (insert a B) 𝒞, (#C - 1).factorial else 0) ≤
          if 0 < #B ∧ #B ≤ r then (#B).factorial * #T ^ (2 * (r - #B)) else 0 := by
      intro B hB
      obtain ⟨hBT, hBne⟩ := mem_filter.1 hB
      have haB : a ∉ B := fun h => ha (mem_powerset.1 hBT h)
      have hcard : #(insert a B) - 1 = #B := by
        rw [card_insert_of_notMem haB, Nat.add_sub_cancel]
      have h𝒞 : ∀ 𝒞 ∈ blockSystemsIn (T \ B),
          (if blockRank (insert (insert a B) 𝒞) = r then
            ∏ C ∈ insert (insert a B) 𝒞, (#C - 1).factorial else 0) =
          (#B).factorial *
            if blockRank 𝒞 = r - #B ∧ #B ≤ r then ∏ C ∈ 𝒞, (#C - 1).factorial else 0 := by
        intro 𝒞 h𝒞
        have hX := insert_notMem_of_mem_blockSystemsIn (B' := B) ha h𝒞
        rw [blockRank, blockRank, sum_insert hX, prod_insert hX, hcard, mul_ite, mul_zero]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [sum_congr rfl h𝒞, ← mul_sum]
      by_cases hr : #B ≤ r
      · have h0 : 0 < #B ∧ #B ≤ r := ⟨hBne.card_pos, hr⟩
        simp only [hr, and_true, h0, and_self, ↓reduceIte]
        gcongr
        exact (ih _ (sdiff_subset.trans_ssubset (ssubset_insert ha)) (r - #B)).trans
          (Nat.pow_le_pow_left (card_le_card sdiff_subset) _)
      · simp [hr]
    rw [rankMass, sum_blockSystemsIn_insert ha, card_insert_of_notMem ha]
    calc _ ≤ #T ^ (2 * r) + ∑ B ∈ T.powerset.filter (·.Nonempty),
            (if 0 < #B ∧ #B ≤ r then (#B).factorial * #T ^ (2 * (r - #B)) else 0) :=
          add_le_add (ih T (ssubset_insert ha) r) (sum_le_sum hB)
      _ ≤ #T ^ (2 * r) + ∑ B ∈ T.powerset,
            (if 0 < #B ∧ #B ≤ r then (#B).factorial * #T ^ (2 * (r - #B)) else 0) := by
          gcongr
          exact filter_subset _ _
      _ = #T ^ (2 * r) + ∑ k ∈ range (#T + 1), (#T).choose k •
            (if 0 < k ∧ k ≤ r then k.factorial * #T ^ (2 * (r - k)) else 0) := by
          rw [sum_powerset_apply_card
            (fun k => if 0 < k ∧ k ≤ r then k.factorial * #T ^ (2 * (r - k)) else 0)]
      _ ≤ (#T + 1) ^ (2 * r) := rank_step_le _ r

open scoped Classical in
/-- **The partition identity**: the indicator of distinct performed values is the signed sum
over block systems of their realization indicators. -/
theorem birthsDistinct_indicator_eq (β : α → Option ℕ) :
    (if BirthsDistinct β then 1 else 0 : ℤ) =
      ∑ 𝒞 ∈ blockSystems α, blockCoef 𝒞 * ∏ C ∈ 𝒞, if BlockRealized β C then 1 else 0 := by
  have h := distinctOn_indicator_eq β univ
  have hD : DistinctOn β univ ↔ BirthsDistinct β := by
    simp [DistinctOn, BirthsDistinct]
  rw [blockSystemsIn_univ, hD] at h
  rw [h]
  refine sum_congr rfl fun 𝒞 _ => ?_
  rw [blockCoef, ← prod_mul_distrib]
  rfl

/-- **The rank coefficients**: the block systems of rank `r` have total coefficient mass at
most `|α|^{2r}`. -/
theorem sum_abs_blockCoef_le (r : ℕ) :
    ∑ 𝒞 ∈ (blockSystems α).filter (fun 𝒞 => blockRank 𝒞 = r), |blockCoef 𝒞| ≤
      (Fintype.card α : ℤ) ^ (2 * r) := by
  have h := rankMass_le r (univ : Finset α)
  rw [rankMass, blockSystemsIn_univ, ← sum_filter, card_univ] at h
  calc ∑ 𝒞 ∈ (blockSystems α).filter (fun 𝒞 => blockRank 𝒞 = r), |blockCoef 𝒞|
      = ((∑ 𝒞 ∈ (blockSystems α).filter (fun 𝒞 => blockRank 𝒞 = r),
          ∏ C ∈ 𝒞, (#C - 1).factorial : ℕ) : ℤ) := by
        push_cast
        refine sum_congr rfl fun 𝒞 _ => ?_
        rw [blockCoef, abs_prod]
        refine prod_congr rfl fun C _ => ?_
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    _ ≤ (Fintype.card α : ℤ) ^ (2 * r) := by exact_mod_cast h

end Erdos408.OneSided
