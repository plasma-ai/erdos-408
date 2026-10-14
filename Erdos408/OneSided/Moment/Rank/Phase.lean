import Erdos408.OneSided.Memory.Partition
import Mathlib.Data.Finset.Pairwise
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Local phases for a block system

PD `mem:local-phases` (`blueprint/one_sided_type_ii.md` §13, M10, low rank), with a finite
Fourier average in place of the circle integral. Fix a block system `𝒞` with addresses
`U = ⋃ 𝒞`, and choose in each block a pivot. Then
`[C realized] = ∏_{a ∈ C} [β_a performed and β_a = β_{piv a}]`. For values below `P`, with
`ζ = e(1/P)`,
`[p = p'] = P⁻¹ ∑_{k < P} ζ^{k (p + (P - 1) p')}`.

Expanding the product over the addresses gives an average over frequency vectors `κ` of
products `∏_a ψ_κ(a, β_a)` of *local* phases: each depends on one address and its value only
(`exists_blockPhase`). The phase of an address outside `U` is `1`, and every phase has
modulus at most one. The pivot collects the frequencies of its block, so its phase is
`ζ^{p e_κ(a)}` with `e_κ(a) = κ_a + (P - 1) ∑_{piv a' = a} κ_{a'}`.

A rank-`r` system has at most `2r` addresses (`card_biUnion_le_two_mul_blockRank`).
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The Fourier average -/

/-- The root of unity `ζ = e(1/P)`. -/
def unitRoot (P : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / P)

/-- `ζ` has modulus one. -/
theorem norm_unitRoot {P : ℕ} (hP : 0 < P) : ‖unitRoot P‖ = 1 :=
  (Complex.isPrimitiveRoot_exp P hP.ne').norm'_eq_one hP.ne'

/-- For `p, p' < P`, `P` divides `p + (P - 1) p'` exactly when `p = p'`. -/
theorem dvd_add_mul_iff {P p p' : ℕ} (hP : 0 < P) (hp : p < P) (hp' : p' < P) :
    P ∣ p + (P - 1) * p' ↔ p = p' := by
  obtain ⟨P, rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · intro h
    -- `p ≡ p + (P + 1) p' = (p + P p') + p' ≡ p'`
    have h₁ : p % (P + 1) = (p + P * p' + p') % (P + 1) := by
      rw [show p + P * p' + p' = p + (P + 1) * p' by ring, Nat.add_mul_mod_self_left]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h, zero_add, Nat.mod_mod] at h₁
    rwa [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hp'] at h₁
  · rintro rfl
    exact ⟨p, by ring⟩

/-- The Fourier factor `ζ^{k (p + (P - 1) p')}` of a pair of values, zero unless both are
performed. -/
def fourierFactor (P k : ℕ) : Option ℕ → Option ℕ → ℂ
  | some p, some p' => unitRoot P ^ (k * (p + (P - 1) * p'))
  | _, _ => 0

/-- **The Fourier average**: for values below `P`, the average of the Fourier factors over
`k < P` is the indicator that both values are performed and equal. -/
theorem fourierFactor_average {P : ℕ} (hP : 0 < P) {o o' : Option ℕ}
    (ho : ∀ p, o = some p → p < P) (ho' : ∀ p, o' = some p → p < P) :
    (P : ℂ)⁻¹ * ∑ k ∈ range P, fourierFactor P k o o' = if o ≠ none ∧ o = o' then 1 else 0 := by
  have hP' : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  rcases o with _ | p
  · simp [fourierFactor]
  rcases o' with _ | p'
  · simp [fourierFactor]
  have hζ : IsPrimitiveRoot (unitRoot P) P := Complex.isPrimitiveRoot_exp P hP.ne'
  set m := p + (P - 1) * p'
  have hsum : ∑ k ∈ range P, fourierFactor P k (some p) (some p') =
      ∑ k ∈ range P, (unitRoot P ^ m) ^ k :=
    sum_congr rfl fun k _ => by
      simp only [fourierFactor, ← pow_mul]
      rw [mul_comm]
  rw [hsum]
  by_cases hm : P ∣ m
  · -- `ζ^m = 1`: the average is `1`
    have h1 : unitRoot P ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).2 hm
    have hpp : p = p' := (dvd_add_mul_iff hP (ho p rfl) (ho' p' rfl)).1 hm
    simp [h1, hpp, hP']
  · -- `ζ^m ≠ 1` is a `P`-th root of unity: the geometric sum vanishes
    have h1 : unitRoot P ^ m ≠ 1 := fun h => hm ((hζ.pow_eq_one_iff_dvd m).1 h)
    have hpp : p ≠ p' := fun h => hm ((dvd_add_mul_iff hP (ho p rfl) (ho' p' rfl)).2 h)
    have hP1 : (unitRoot P ^ m) ^ P = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, hP1, sub_self, zero_div, mul_zero]
    simp [hpp]

/-! ### Pivots -/

/-- A block system has a pivot map: on each block it is constant, with its value in the
block. -/
theorem exists_pivot {𝒞 : Finset (Finset α)} (h𝒞 : 𝒞 ∈ blockSystems α) :
    ∃ piv : α → α, ∀ C ∈ 𝒞, ∀ a ∈ C, piv a ∈ C ∧ ∀ a' ∈ C, piv a' = piv a := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨id, fun C _ a _ => (IsEmpty.false a).elim⟩
  obtain ⟨-, hdisj, hcard⟩ := mem_filter.1 h𝒞
  have hrep : ∀ C ∈ 𝒞, ∃ c, c ∈ C := fun C hC =>
    card_pos.1 (by have := hcard C hC; omega)
  choose! rep hrep using hrep
  have hblk : ∀ a ∈ 𝒞.biUnion id, ∃ C ∈ 𝒞, a ∈ C := fun a ha => by
    simpa using mem_biUnion.1 ha
  choose! blk hblk using hblk
  -- the block of an address of `C` is `C`, by disjointness
  have key : ∀ C ∈ 𝒞, ∀ a ∈ C, blk a = C := fun C hC a ha =>
    have h := hblk a (mem_biUnion.2 ⟨C, hC, ha⟩)
    Set.PairwiseDisjoint.elim_finset hdisj h.1 hC a h.2 ha
  refine ⟨fun a => rep (blk a), fun C hC a ha => ⟨?_, fun a' ha' => ?_⟩⟩
  · show rep (blk a) ∈ C
    rw [key C hC a ha]
    exact hrep C hC
  · simp only [key C hC a ha, key C hC a' ha']

open scoped Classical in
/-- With a pivot map, a block is realized when each of its addresses is performed with the
value of its pivot. -/
theorem prod_blockRealized_eq {𝒞 : Finset (Finset α)} (h𝒞 : 𝒞 ∈ blockSystems α)
    {piv : α → α} (hpiv : ∀ C ∈ 𝒞, ∀ a ∈ C, piv a ∈ C ∧ ∀ a' ∈ C, piv a' = piv a)
    (β : α → Option ℕ) :
    (∏ C ∈ 𝒞, if BlockRealized β C then 1 else 0 : ℂ) =
      ∏ a ∈ 𝒞.biUnion id, if β a ≠ none ∧ β a = β (piv a) then 1 else 0 := by
  obtain ⟨-, hdisj, hcard⟩ := mem_filter.1 h𝒞
  rw [prod_biUnion hdisj]
  refine prod_congr rfl fun C hC => ?_
  obtain ⟨c, hc⟩ : ∃ c, c ∈ C := card_pos.1 (by have := hcard C hC; omega)
  have hiff : BlockRealized β C ↔ ∀ a ∈ C, β a ≠ none ∧ β a = β (piv a) := by
    constructor
    · rintro ⟨p, hp⟩ a ha
      exact ⟨by simp [hp a ha], by rw [hp a ha, hp _ (hpiv C hC a ha).1]⟩
    · intro h
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 (h c hc).1
      -- `β a = β (piv a) = β (piv c) = β c = p`
      refine ⟨p, fun a ha => ?_⟩
      rw [(h a ha).2, (hpiv C hC c hc).2 a ha, ← (h c hc).2, hp]
  simp only [prod_boole, id]
  by_cases h : BlockRealized β C
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (hiff.1 h))]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false (mt hiff.2 h))]

/-! ### The local phases -/

/-- The local phase of the address `a`, for the frequency vector `κ` and the pivot map `piv`
on the addresses `U`: `ζ^{p e_κ(a)}` on a performed value `p`, with
`e_κ(a) = κ_a + (P - 1) ∑_{a' ∈ U, piv a' = a} κ_{a'}`; zero on `none`; and `1` off `U`. -/
def blockPhase (P : ℕ) (U : Finset α) (piv : α → α) (κ : α → ℕ) (a : α) : Option ℕ → ℂ :=
  if a ∈ U then fun o =>
    o.elim 0 fun p => unitRoot P ^ (p * (κ a + (P - 1) * ∑ a' ∈ U with piv a' = a, κ a'))
  else fun _ => 1

omit [Fintype α] in
/-- The local phases have modulus at most one. -/
theorem norm_blockPhase_le {P : ℕ} (hP : 0 < P) (U : Finset α) (piv : α → α) (κ : α → ℕ)
    (a : α) (o : Option ℕ) : ‖blockPhase P U piv κ a o‖ ≤ 1 := by
  unfold blockPhase
  split_ifs
  · rcases o with _ | p
    · simp
    · simp [norm_pow, norm_unitRoot hP]
  · simp

/-- For a frequency vector `κ`, the product of the Fourier factors of the pairs
`(β_a, β_{piv a})`, `a ∈ U`, is the product of the local phases: the pivot collects the
frequencies of its block. -/
theorem prod_fourierFactor_eq (P : ℕ) {U : Finset α} {piv : α → α}
    (hpiv : ∀ a ∈ U, piv a ∈ U) (κ : α → ℕ) (β : α → Option ℕ) :
    ∏ a, (if a ∈ U then fourierFactor P (κ a) (β a) (β (piv a)) else 1) =
      ∏ a, blockPhase P U piv κ a (β a) := by
  by_cases hperf : ∀ a ∈ U, ∃ p, β a = some p
  · choose! val hval using hperf
    -- both sides are `ζ` to a power: the pairs `(a, piv a)` regroup by pivot
    have hL : ∀ a, (if a ∈ U then fourierFactor P (κ a) (β a) (β (piv a)) else 1) =
        if a ∈ U then unitRoot P ^ (κ a * (val a + (P - 1) * val (piv a))) else 1 := by
      intro a
      split_ifs with ha
      · rw [hval a ha, hval _ (hpiv a ha)]
        rfl
      · rfl
    have hR : ∀ a, blockPhase P U piv κ a (β a) =
        if a ∈ U then
          unitRoot P ^ (val a * (κ a + (P - 1) * ∑ a' ∈ U with piv a' = a, κ a'))
        else 1 := by
      intro a
      unfold blockPhase
      split_ifs with ha
      · rw [hval a ha]
        rfl
      · rfl
    simp only [hL, hR, Fintype.prod_ite_mem, prod_pow_eq_pow_sum]
    congr 1
    -- `∑_{a ∈ U} κ_a val(piv a) = ∑_{a ∈ U} val a ∑_{piv a' = a} κ_{a'}`
    have hfib : ∑ a ∈ U, val a * ∑ a' ∈ U with piv a' = a, κ a' =
        ∑ a ∈ U, κ a * val (piv a) := by
      rw [← sum_fiberwise_of_maps_to hpiv (fun a => κ a * val (piv a))]
      refine sum_congr rfl fun a _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun a' ha' => ?_
      rw [(mem_filter.1 ha').2, mul_comm]
    have e₁ : ∑ a ∈ U, κ a * (val a + (P - 1) * val (piv a)) =
        ∑ a ∈ U, κ a * val a + (P - 1) * ∑ a ∈ U, κ a * val (piv a) := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    have e₂ : ∑ a ∈ U, val a * (κ a + (P - 1) * ∑ a' ∈ U with piv a' = a, κ a') =
        ∑ a ∈ U, κ a * val a + (P - 1) * ∑ a ∈ U, val a * ∑ a' ∈ U with piv a' = a, κ a' := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    rw [e₁, e₂, hfib]
  · -- an unperformed address of `U` kills both sides
    push Not at hperf
    obtain ⟨a, ha, hnone⟩ := hperf
    have hβ : β a = none := by
      rcases h : β a with _ | p
      · rfl
      · exact (hnone p h).elim
    rw [prod_eq_zero (mem_univ a) (by simp [ha, hβ, fourierFactor]),
      prod_eq_zero (mem_univ a) (by simp [blockPhase, ha, hβ])]

open scoped Classical in
/-- **The local phases of a block system**: for `P` larger than every performed value, the
realization indicator of a block system is the average over frequency vectors `κ < P` of a
product of local phases `ψ_κ(a, β_a)`, each of modulus at most one and equal to `1` off the
addresses of the blocks. -/
theorem exists_blockPhase {𝒞 : Finset (Finset α)} (h𝒞 : 𝒞 ∈ blockSystems α) {P : ℕ}
    (hP : 0 < P) :
    ∃ ψ : (α → ℕ) → α → Option ℕ → ℂ,
      (∀ κ a o, ‖ψ κ a o‖ ≤ 1) ∧
      (∀ κ a, a ∉ 𝒞.biUnion id → ψ κ a = fun _ => 1) ∧
      ∀ β : α → Option ℕ, (∀ a p, β a = some p → p < P) →
        (∏ C ∈ 𝒞, if BlockRealized β C then 1 else 0 : ℂ) =
          ((P : ℂ) ^ Fintype.card α)⁻¹ *
            ∑ κ ∈ Fintype.piFinset fun _ : α => range P, ∏ a, ψ κ a (β a) := by
  obtain ⟨piv, hpiv⟩ := exists_pivot h𝒞
  set U := 𝒞.biUnion id with hU
  have hpivU : ∀ a ∈ U, piv a ∈ U := fun a ha => by
    obtain ⟨C, hC, haC⟩ := mem_biUnion.1 ha
    exact mem_biUnion.2 ⟨C, hC, (hpiv C hC a haC).1⟩
  refine ⟨blockPhase P U piv, norm_blockPhase_le hP U piv, fun κ a ha => by
    simp [blockPhase, ha], fun β hβ => ?_⟩
  have hP' : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hb : ∀ a, ∀ p, β a = some p → p < P := hβ
  rw [prod_blockRealized_eq h𝒞 hpiv β]
  calc ∏ a ∈ U, (if β a ≠ none ∧ β a = β (piv a) then 1 else 0 : ℂ)
      = ∏ a, ((P : ℂ)⁻¹ * ∑ k ∈ range P,
          if a ∈ U then fourierFactor P k (β a) (β (piv a)) else 1) := by
        rw [← Fintype.prod_ite_mem]
        refine prod_congr rfl fun a _ => ?_
        by_cases ha : a ∈ U
        · simp only [ha, ↓reduceIte]
          rw [fourierFactor_average hP (hb a) (hb (piv a))]
        · simp [ha, hP']
    _ = ((P : ℂ) ^ Fintype.card α)⁻¹ * ∑ κ ∈ Fintype.piFinset fun _ : α => range P,
          ∏ a, (if a ∈ U then fourierFactor P (κ a) (β a) (β (piv a)) else 1) := by
        rw [prod_mul_distrib, prod_const, card_univ, inv_pow,
          prod_univ_sum (fun _ => range P)
            (fun a k => if a ∈ U then fourierFactor P k (β a) (β (piv a)) else 1)]
    _ = ((P : ℂ) ^ Fintype.card α)⁻¹ * ∑ κ ∈ Fintype.piFinset fun _ : α => range P,
          ∏ a, blockPhase P U piv κ a (β a) := by
        congr 1
        exact sum_congr rfl fun κ _ => prod_fourierFactor_eq P hpivU κ β

/-! ### Rank and addresses -/

/-- A block system of rank `r` has at most `2r` addresses: each block has `|C| ≤ 2(|C| - 1)`. -/
theorem card_biUnion_le_two_mul_blockRank {𝒞 : Finset (Finset α)}
    (h𝒞 : 𝒞 ∈ blockSystems α) : #(𝒞.biUnion id) ≤ 2 * blockRank 𝒞 := by
  classical
  obtain ⟨-, hdisj, hcard⟩ := mem_filter.1 h𝒞
  rw [card_biUnion hdisj, blockRank, mul_sum]
  exact sum_le_sum fun C hC => by
    have := hcard C hC
    simp only [id]
    omega

/-- The rank of a block system is at most the number of addresses. -/
theorem blockRank_le_card {𝒞 : Finset (Finset α)} (h𝒞 : 𝒞 ∈ blockSystems α) :
    blockRank 𝒞 ≤ Fintype.card α := by
  classical
  obtain ⟨-, hdisj, -⟩ := mem_filter.1 h𝒞
  calc blockRank 𝒞 ≤ #(𝒞.biUnion id) := by
        rw [card_biUnion hdisj, blockRank]
        exact sum_le_sum fun C _ => Nat.sub_le _ _
    _ ≤ Fintype.card α := card_le_univ _

end Erdos408.OneSided
