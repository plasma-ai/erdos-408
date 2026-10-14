module

public import Erdos408.TwoSided.Graph.Restore.Eventually

/-!
# The stripped correlations of the raw and the comparison patterns

The stripped correlation `stripSum` of a pattern `(C, K)` is, for the two kinds of pattern of
`GraphTransference`'s family (`blueprint/two_sided_correlation.md` §4.3):

* the raw correlation `twoSidedSum` for the raw pattern (`C = ∅`, `K = 1`), since then
  `D_C = 1`, `t_g = 1` and `W₁ = markedListWeight P q₀ (unsharedSlots ∅) 1` (one prime per
  group: `∑_ℓ 1 = ∏_g ω_g`), once the cutoff support `w ≤ κ x` lies below `x²`
  (`stripSum_raw_eq`);
* `β` times the stripped comparison correlation for a comparison pattern, whose kernel
  factors as `β φ(D_A) φ'(D_B) ψ'(X_B) ψ(X_A)` (`stripSum_comparison_eq`).

Both kernels depend only on the unshared parts of the lists (`pad_invariant_*`).
-/

@[expose] public section

namespace Erdos408.TwoSided

namespace Restore

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ}

/-! ### The raw pattern -/

omit [Fintype ι] [DecidableEq ι] in
/-- The raw pattern has the final slot only. -/
lemma unsharedSlots_empty (g : ι) :
    unsharedSlots (fun _ => (∅ : Finset (Fin J))) g = {Fin.last J} := by
  simp [unsharedSlots]

/-- The only auxiliary labels of the raw pattern are `1`. -/
lemma auxLabels_empty (P : ι → Finset ℕ) :
    auxLabels P (fun _ => (∅ : Finset (Fin J))) = {fun _ _ => 1} := by
  ext a
  simp only [auxLabels, Fintype.mem_piFinset, notMem_empty, ite_false, mem_singleton,
    funext_iff]

/-- The represented lists of the raw pattern: one prime of each group. -/
lemma card_slotLists_empty (P : ι → Finset ℕ) (n : ℕ) :
    (slotLists P (unsharedSlots (fun _ => (∅ : Finset (Fin J)))) n).card =
      ∏ g, primeCount (P g) n := by
  have h : slotLists P (unsharedSlots (fun _ => (∅ : Finset (Fin J)))) n =
      Fintype.piFinset fun g => Fintype.piFinset fun j : Fin (J + 1) =>
        if j = Fin.last J then (P g).filter (· ∣ n) else {1} := by
    ext l
    simp only [slotLists, unsharedSlots_empty, mem_filter, Fintype.mem_piFinset,
      mem_singleton, coe_singleton, Set.injOn_singleton, true_and, forall_eq]
    constructor
    · rintro ⟨h₁, h₂⟩ g j
      have := h₁ g j
      split_ifs at this ⊢ with hj
      · subst hj
        exact mem_filter.2 ⟨this, h₂ g⟩
      · exact this
    · intro h
      refine ⟨fun g j => ?_, fun g => ?_⟩
      · have := h g j
        split_ifs at this ⊢ with hj
        · exact (mem_filter.1 this).1
        · exact this
      · have := h g (Fin.last J)
        rw [ite_eq_left rfl] at this
        exact (mem_filter.1 this).2
  rw [h, Fintype.card_piFinset]
  refine prod_congr rfl fun g _ => ?_
  rw [Fintype.card_piFinset, Fintype.prod_eq_single (Fin.last J) fun j hj => by simp [hj]]
  simp [primeCount]

/-- `W₁ = q₀^{ω - s} ∏_g ω_g / V_g` is the stripped damping times the number of represented
lists of the raw pattern. -/
lemma markedWeight_eq_listDamping_mul (P : ι → Finset ℕ) (q₀ : ℝ) (n : ℕ) :
    markedWeight Finset.univ q₀ P n =
      listDamping P q₀ (fun _ => (∅ : Finset (Fin J))) n *
        (slotLists P (unsharedSlots (fun _ => (∅ : Finset (Fin J)))) n).card := by
  rw [card_slotLists_empty]
  unfold markedWeight listDamping groupPrimeCount
  simp only [unsharedSlots_empty, card_singleton, Nat.cast_one, sum_const, card_univ,
    pow_one, nsmul_eq_mul, mul_one]
  push_cast
  rw [mul_assoc]
  congr 1
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun g _ => by ring

/-- **The raw pattern.** Its stripped correlation is the raw correlation, once `κ x ≤ x²`. -/
lemma stripSum_raw_eq {x q₀ κ : ℝ} (hx : 0 < x) (hκx : κ * x ≤ x ^ 2) (P : ι → Finset ℕ)
    (F G : ℕ → ℝ) {Ψ : ℝ → ℝ} (hsupp : ∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) :
    stripSum x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ =
      ((∑ w ∈ Icc 1 ⌊κ * x⌋₊, Ψ (w / x) / w * F w * G (w + 1) *
        markedWeight Finset.univ q₀ P w * markedWeight Finset.univ q₀ P (w + 1) : ℝ) : ℂ) := by
  unfold stripSum
  rw [auxLabels_empty, sum_singleton]
  have hμ : labelMass P (fun _ => (∅ : Finset (Fin J))) (fun _ _ => 1) = 1 := by
    simp [labelMass]
  have hD : slotProduct (fun _ => (∅ : Finset (Fin J))) (fun (_ : ι) (_ : Fin J) => 1) = 1 := by
    simp [slotProduct]
  rw [hμ, hD, Complex.ofReal_one, one_mul, Complex.ofReal_sum]
  symm
  refine sum_subset (Icc_subset_Icc le_rfl (Nat.floor_le_floor hκx)) (fun w hw hw' => ?_)
    |>.trans (sum_congr rfl fun w _ => ?_)
  · have hlt : ⌊κ * x⌋₊ < w := by
      by_contra h
      exact hw' (mem_Icc.2 ⟨(mem_Icc.1 hw).1, not_lt.1 h⟩)
    have hw0 : (0 : ℝ) < w := by
      have := (mem_Icc.1 hw).1
      exact_mod_cast (show 0 < w by omega)
    have hwx : κ < w / x := by
      rw [lt_div_iff₀ hx]
      rcases le_or_gt 0 (κ * x) with hκ0 | hκ0
      · exact (Nat.floor_lt hκ0).1 hlt
      · linarith
    have hψ : Ψ (w / x) = 0 := by
      by_contra h
      linarith [(hsupp _ h).2]
    rw [hψ]
    simp
  · rw [markedWeight_eq_listDamping_mul P q₀ w, markedWeight_eq_listDamping_mul P q₀ (w + 1)]
    simp only [Nat.cast_one, mul_one, sum_const, nsmul_eq_mul]
    push_cast
    ring

omit [Fintype ι] [DecidableEq ι] in
/-- The raw kernel depends only on the unshared parts. -/
lemma pad_invariant_one (p p' : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) :
    (fun _ _ _ => (1 : ℂ)) p p' a =
      (fun _ _ _ => (1 : ℂ)) (pad (fun _ => (∅ : Finset (Fin J))) p)
        (pad (fun _ => (∅ : Finset (Fin J))) p') a :=
  rfl

/-! ### The comparison patterns -/

/-- **The comparison patterns.** With the kernel `β φ(D_A) φ'(D_B) ψ(X_A) ψ'(X_B)`, the stripped
correlation is `β` times the stripped comparison correlation. -/
lemma stripSum_comparison_eq (x q₀ : ℝ) (P : ι → Finset ℕ) (A B : ι → Finset (Fin J))
    (β : ℂ) (φ φ' ψ ψ' : ℕ → ℂ) (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) :
    stripSum x q₀ P (fun h => A h ∪ B h)
        (fun p p' a => β * φ (slotProduct A a) * φ' (slotProduct B a) *
          ψ (slotProduct A fun h i => p' h i.castSucc) *
          ψ' (slotProduct B fun h i => p h i.castSucc)) F G Ψ =
      β * strippedComparison x q₀ P A B φ φ' ψ ψ' F G Ψ := by
  unfold stripSum strippedComparison markedListWeight
  dsimp only
  have key : ∀ (a : ι → Fin J → ℕ) (S S' : Finset (ι → Fin (J + 1) → ℕ)),
      ∑ l ∈ S, ∑ l' ∈ S', β * φ (slotProduct A a) * φ' (slotProduct B a) *
          ψ (slotProduct A fun h i => l' h i.castSucc) *
          ψ' (slotProduct B fun h i => l h i.castSucc) =
        β * φ (slotProduct A a) * φ' (slotProduct B a) *
          ((∑ l ∈ S, ψ' (slotProduct B fun h i => l h i.castSucc)) *
            ∑ l' ∈ S', ψ (slotProduct A fun h i => l' h i.castSucc)) := by
    intro a S S'
    rw [sum_mul_sum, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun l' _ => by ring
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [key]
  unfold listDamping labelMass
  push_cast
  ring

omit [DecidableEq ι] in
/-- The comparison kernel depends only on the unshared parts: it reads the source labels in
`B ⊆ C` and the target labels in `A ⊆ C`. -/
lemma pad_invariant_comparison (A B : ι → Finset (Fin J)) (β : ℂ) (φ φ' ψ ψ' : ℕ → ℂ)
    (p p' : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) :
    β * φ (slotProduct A a) * φ' (slotProduct B a) *
        ψ (slotProduct A fun h i => p' h i.castSucc) *
        ψ' (slotProduct B fun h i => p h i.castSucc) =
      β * φ (slotProduct A a) * φ' (slotProduct B a) *
        ψ (slotProduct A fun h i => pad (fun h => A h ∪ B h) p' h i.castSucc) *
        ψ' (slotProduct B fun h i => pad (fun h => A h ∪ B h) p h i.castSucc) := by
  have hA : (slotProduct A fun h i => p' h i.castSucc) =
      slotProduct A fun h i => pad (fun h => A h ∪ B h) p' h i.castSucc := by
    unfold slotProduct
    refine prod_congr rfl fun h _ => prod_congr rfl fun i hi => ?_
    exact (ite_eq_left (castSucc_mem_unsharedSlots.2 (mem_union_left _ hi))).symm
  have hB : (slotProduct B fun h i => p h i.castSucc) =
      slotProduct B fun h i => pad (fun h => A h ∪ B h) p h i.castSucc := by
    unfold slotProduct
    refine prod_congr rfl fun h _ => prod_congr rfl fun i hi => ?_
    exact (ite_eq_left (castSucc_mem_unsharedSlots.2 (mem_union_right _ hi))).symm
  rw [hA, hB]

end Restore

end Erdos408.TwoSided
