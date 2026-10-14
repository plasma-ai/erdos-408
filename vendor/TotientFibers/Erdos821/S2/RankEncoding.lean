import Erdos821.S2.CycleSigns

/-! A rank-r permutation is encoded by r pairs of transposed addresses. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

lemma adjacent_swaps_product {α : Type*} [DecidableEq α] (l : List α) :
    ((l.zip l.tail).map (fun p => Equiv.swap p.1 p.2)).prod = l.formPerm := by
  have hz (l₁ l₂ : List α) :
      ((l₁.zip l₂).map (fun p => Equiv.swap p.1 p.2)) = List.zipWith Equiv.swap l₁ l₂ := by
    induction l₁ generalizing l₂ with
    | nil => simp
    | cons x xs ih =>
      cases l₂ with
      | nil => simp
      | cons y ys => simp [ih]
  exact congrArg List.prod (hz l l.tail)

lemma adjacent_pairs_length {α : Type*} (l : List α) :
    (l.zip l.tail).length = l.length - 1 := by
  simp only [List.length_zip, List.length_tail, Nat.min_eq_right (Nat.sub_le _ _)]

lemma cycleRank_sum {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    birthRank (cycleBirthBlocks σ) =
      ∑ c ∈ σ.cycleFactorsFinset, (c.support.card - 1) := by
  unfold birthRank cycleBirthBlocks
  rw [Finset.sum_image (cycleFactors_support_injective σ)]

lemma cycleRank_mul_disjoint {a : ℕ} {σ τ : Equiv.Perm (Fin a)}
    (h : σ.Disjoint τ) :
    birthRank (cycleBirthBlocks (σ * τ)) =
      birthRank (cycleBirthBlocks σ) + birthRank (cycleBirthBlocks τ) := by
  rw [cycleRank_sum, h.cycleFactorsFinset_mul_eq_union,
    Finset.sum_union h.disjoint_cycleFactorsFinset, ← cycleRank_sum, ← cycleRank_sum]

/-- A cycle contributes one swap pair for every address except its anchor. -/
theorem exists_rank_swap_pairs {a : ℕ} (σ : Equiv.Perm (Fin a)) :
    ∃ l : List (Fin a × Fin a),
      l.length = birthRank (cycleBirthBlocks σ) ∧
      (l.map (fun p => Equiv.swap p.1 p.2)).prod = σ := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one =>
    refine ⟨[], ?_, rfl⟩
    simp [birthRank, cycleBirthBlocks]
  | base_cycles σ hσ =>
    have hcy := hσ
    obtain ⟨x, hx, _⟩ := hσ
    refine ⟨(σ.toList x).zip (σ.toList x).tail, ?_, ?_⟩
    · rw [adjacent_pairs_length, Equiv.Perm.length_toList, hcy.cycleOf_eq hx]
      simp [birthRank, cycleBirthBlocks, hcy.cycleFactorsFinset_eq_singleton]
    · rw [adjacent_swaps_product, Equiv.Perm.formPerm_toList, hcy.cycleOf_eq hx]
  | induction_disjoint σ τ hd _ ihσ ihτ =>
    obtain ⟨l, hl, hp⟩ := ihσ
    obtain ⟨l', hl', hp'⟩ := ihτ
    refine ⟨l ++ l', ?_, ?_⟩
    · simp only [List.length_append, hl, hl', cycleRank_mul_disjoint hd]
    · rw [List.map_append, List.prod_append, hp, hp']

def rankPermutations (a r : ℕ) : Finset (Equiv.Perm (Fin a)) :=
  Finset.univ.filter (fun σ => birthRank (cycleBirthBlocks σ) = r)

def rankSwapList {a r : ℕ} (σ : rankPermutations a r) : List (Fin a × Fin a) :=
  Classical.choose (exists_rank_swap_pairs σ.val)

lemma rankSwapList_properties {a r : ℕ} (σ : rankPermutations a r) :
    (rankSwapList σ).length = r ∧
      ((rankSwapList σ).map (fun p => Equiv.swap p.1 p.2)).prod = σ.val := by
  have hp := Classical.choose_spec (exists_rank_swap_pairs σ.val)
  exact ⟨hp.1.trans (Finset.mem_filter.mp σ.property).2, hp.2⟩

def swapPairCode {a r : ℕ} (σ : rankPermutations a r) : Fin r → Fin a × Fin a :=
  fun i => (rankSwapList σ).get ⟨i.val, by rw [(rankSwapList_properties σ).1]; exact i.isLt⟩

theorem swapPairCode_injective {a r : ℕ} :
    Function.Injective (@swapPairCode a r) := by
  intro σ τ h
  have hl : rankSwapList σ = rankSwapList τ := by
    apply List.ext_getElem
    · rw [(rankSwapList_properties σ).1, (rankSwapList_properties τ).1]
    · intro i hi hi'
      have hir : i < r := by rw [← (rankSwapList_properties σ).1]; exact hi
      have he := congrArg (fun f : Fin r → Fin a × Fin a => f ⟨i, hir⟩) h
      simpa only [swapPairCode, List.get_eq_getElem] using he
  apply Subtype.ext
  calc
    σ.val = ((rankSwapList σ).map (fun p => Equiv.swap p.1 p.2)).prod :=
      (rankSwapList_properties σ).2.symm
    _ = ((rankSwapList τ).map (fun p => Equiv.swap p.1 p.2)).prod := by rw [hl]
    _ = τ.val := (rankSwapList_properties τ).2

/-- At most a^(2r) permutations have equality rank r. -/
theorem rankPermutations_card_le (a r : ℕ) :
    (rankPermutations a r).card ≤ a ^ (2 * r) := by
  calc
    (rankPermutations a r).card = Fintype.card (rankPermutations a r) := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Fin r → Fin a × Fin a) := Fintype.card_le_of_injective _ swapPairCode_injective
    _ = a ^ (2 * r) := by
      rw [Fintype.card_pi_const, Fintype.card_prod, Fintype.card_fin]
      rw [← pow_two, ← pow_mul]


end Erdos821.S2
