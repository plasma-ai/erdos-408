import Erdos821.S2.HistoryBirths

/-! Distinct birth histories have bounded memory independently of ghost batches. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem multiset_card_sum {α ι : Type*} (s : Finset ι) (f : ι → Multiset α) :
    (∑ i ∈ s, f i).card = ∑ i ∈ s, (f i).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Multiset.card_add]

theorem group_prime_mem_all (g : P.Group) (p : P.Prime g) : p.val ∈ P.allPrimes :=
  Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, p.property⟩

/-- A bounded multiset over a finite alphabet is the image of a bounded
ordered-list representation. This keeps diagonal multiplicities. -/
theorem bounded_multiset_finite (α : Type*) [Finite α] (B : ℕ) :
    Finite {z : Multiset α // z.card ≤ B} := by
  classical
  let mk : (Σ b : Fin (B + 1), Fin b.val → α) → {z : Multiset α // z.card ≤ B} :=
    fun v => ⟨(List.ofFn v.2 : Multiset α), by simpa using Nat.le_of_lt_succ v.1.isLt⟩
  apply Finite.of_surjective mk
  intro z
  let v : List.Vector α z.val.card := ⟨z.val.toList, Multiset.length_toList z.val⟩
  refine ⟨⟨⟨z.val.card, Nat.lt_succ_of_le z.property⟩, v.get⟩, ?_⟩
  apply Subtype.ext
  change (List.ofFn v.get : Multiset α) = z.val
  rw [← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  exact Multiset.coe_toList z.val

abbrev BoundedMemoryState (P : PrimeGroups) (M B : ℕ) :=
  {s : P.MemoryState M // P.memorySize s ≤ B}

theorem bounded_memoryState_finite (P : PrimeGroups) (M B : ℕ) :
    Finite (BoundedMemoryState P M B) := by
  classical
  letI (g : P.BigGroup) : Finite {z : P.Memory g.val // z.card ≤ B} :=
    bounded_multiset_finite (P.Particle g.val) B
  let enc : BoundedMemoryState P M B →
      P.SmallResidues × P.Labels M × ((g : P.BigGroup) → {z : P.Memory g.val // z.card ≤ B}) :=
    fun s => (s.val.1, s.val.2.1, fun g => ⟨s.val.2.2 g, by
      have hg : (s.val.2.2 g).card ≤ P.memorySize s.val := by
        unfold PrimeGroups.memorySize
        exact Finset.single_le_sum (f := fun h => (s.val.2.2 h).card)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
      exact hg.trans s.property⟩)
  apply Finite.of_injective enc
  intro s t he
  apply Subtype.ext
  have hy : s.val.1 = t.val.1 := congrArg (fun z => z.1) he
  have ha : s.val.2.1 = t.val.2.1 := congrArg (fun z => z.2.1) he
  have hz : s.val.2.2 = t.val.2.2 := by
    funext g
    exact congrArg (fun z => (z.2.2 g).val) he
  exact Prod.ext hy (Prod.ext ha hz)

abbrev BoundedHistoryData (A : Model F P J m) (n B : ℕ) :=
  Σ before : Fin (n + 1) → BoundedMemoryState P (J + F.ell) B,
    Σ after : Fin (n + 1) → BoundedMemoryState P (J + F.ell) B,
      ((i : Fin (n + 1)) → GhostChoice (before i).val (after i).val) ×
        ((i : Fin n) → EdgeChoice A (after i.castSucc).val)

theorem truncated_history_finite (A : Model F P J m) (n B : ℕ) :
    Finite {H : MemoryHistory A n // H.Truncated B} := by
  classical
  letI : Finite (BoundedMemoryState P (J + F.ell) B) := bounded_memoryState_finite P _ B
  letI : Fintype (BoundedMemoryState P (J + F.ell) B) := Fintype.ofFinite _
  letI (s t : P.MemoryState (J + F.ell)) : Fintype (GhostChoice s t) := inferInstance
  letI (s : P.MemoryState (J + F.ell)) : Fintype (EdgeChoice A s) := inferInstance
  letI : Fintype (BoundedHistoryData A n B) := by
    unfold BoundedHistoryData
    infer_instance
  let mk : BoundedHistoryData A n B → {H : MemoryHistory A n // H.Truncated B} :=
    fun d => ⟨⟨(fun i => (d.1 i).val), (fun i => (d.2.1 i).val), d.2.2.1, d.2.2.2⟩,
      fun i => ⟨(d.1 i).property, (d.2.1 i).property⟩⟩
  apply Finite.of_surjective mk
  intro H
  refine ⟨⟨(fun i => ⟨H.val.before i, (H.property i).1⟩),
    (fun i => ⟨H.val.after i, (H.property i).2⟩), H.val.ghost, H.val.edge⟩, ?_⟩
  apply Subtype.ext
  rfl

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

theorem ghostBirthValues_card (i : Fin (n + 1)) : (H.ghostBirthValues i).card = ghostBirthCount (H.ghost i) := by
  simp [ghostBirthValues, multiset_card_sum, ghostBirthCount]

theorem totalGhostBirths_le_card : H.totalGhostBirths ≤ H.birthValues.card := by
  simp only [birthValues, Multiset.card_add, multiset_card_sum, H.ghostBirthValues_card, totalGhostBirths]
  omega

theorem birthValues_subset_allprimes : H.birthValues ⊆ P.allPrimes.val := by
  intro p hp
  simp only [birthValues, Multiset.mem_add] at hp
  rcases hp with (hp | hp) | hp
  · simp only [initialBirthValues, Multiset.mem_sum, Finset.mem_univ, true_and,
      Multiset.mem_singleton] at hp
    obtain ⟨g, i, rfl⟩ := hp
    exact group_prime_mem_all g.val ((H.before 0).2.1 g.val i)
  · simp only [Multiset.mem_sum, Finset.mem_univ, true_and, ghostBirthValues,
      Multiset.mem_singleton] at hp
    obtain ⟨i, g, h, rfl⟩ := hp
    exact group_prime_mem_all g.val ((H.ghost i).2.2 g h)
  · simp only [Multiset.mem_sum, Finset.mem_univ, true_and, freshBirthValues,
      Multiset.mem_singleton] at hp
    obtain ⟨i, g, h, _, rfl⟩ := hp
    exact group_prime_mem_all g.val ((permuteActive (H.edge i).2.1 (H.before i.succ)).2.1 g.val h)

theorem birthValues_card_le (hH : H.DistinctBirths) : H.birthValues.card ≤ P.allPrimes.card := by
  have he : H.birthValues ≤ P.allPrimes.val :=
    (Multiset.le_iff_subset hH).mpr H.birthValues_subset_allprimes
  exact Multiset.card_le_card he

/-- This bound makes the exact distinct-history sum a finite object.
Actual finiteness of the history index type is proved separately. -/
theorem distinct_truncated (hH : H.Valid) (hd : H.DistinctBirths) :
    H.Truncated (P.allPrimes.card + n * ((J + F.ell) * Fintype.card P.BigGroup)) := by
  intro i
  have hb := H.size_le_births_stores hH i
  have ht := H.totalGhostBirths_le_card.trans (H.birthValues_card_le hd)
  have hi : i.val ≤ n := by omega
  have hc := Nat.mul_le_mul_right ((J + F.ell) * Fintype.card P.BigGroup) hi
  constructor <;> omega

theorem valid_distinct_finite (A : Model F P J m) (n : ℕ) :
    Finite {H : MemoryHistory A n // H.Valid ∧ H.DistinctBirths} := by
  classical
  let B := P.allPrimes.card + n * ((J + F.ell) * Fintype.card P.BigGroup)
  letI := truncated_history_finite A n B
  let enc : {H : MemoryHistory A n // H.Valid ∧ H.DistinctBirths} →
      {H : MemoryHistory A n // H.Truncated B} :=
    fun H => ⟨H.val, H.val.distinct_truncated H.property.1 H.property.2⟩
  apply Finite.of_injective enc
  intro H K he
  apply Subtype.ext
  exact congrArg (fun z : {H : MemoryHistory A n // H.Truncated B} => z.val) he

end MemoryHistory

theorem distinct_history_hasFiniteSupport {β : Type*} [Zero β]
    (A : Model F P J m) (n : ℕ) (f : MemoryHistory A n → β) :
    Function.HasFiniteSupport (fun H => if H.Valid ∧ H.DistinctBirths then f H else 0) := by
  letI : Finite {H : MemoryHistory A n // H.Valid ∧ H.DistinctBirths} :=
    MemoryHistory.valid_distinct_finite A n
  have hf : Set.Finite {H : MemoryHistory A n | H.Valid ∧ H.DistinctBirths} :=
    @Set.toFinite (MemoryHistory A n) {H | H.Valid ∧ H.DistinctBirths}
      (MemoryHistory.valid_distinct_finite A n)
  apply hf.subset
  intro H hH
  change (if H.Valid ∧ H.DistinctBirths then f H else 0) ≠ 0 at hH
  by_contra hn
  exact hH (ite_eq_right hn)

theorem distinctMemoryExpression_summable (A : Model F P J m) (n : ℕ) (rho theta : ℝ) :
    Summable (fun H : MemoryHistory A n => if H.Valid ∧ H.DistinctBirths then H.Weight rho theta else 0) :=
  summable_of_hasFiniteSupport (distinct_history_hasFiniteSupport A n (fun H => H.Weight rho theta))

theorem distinctMemoryExpression_abs_summable (A : Model F P J m) (n : ℕ) (rho theta : ℝ) :
    Summable (fun H : MemoryHistory A n => if H.Valid ∧ H.DistinctBirths then ‖H.Weight rho theta‖ else 0) :=
  summable_of_hasFiniteSupport (distinct_history_hasFiniteSupport A n (fun H => ‖H.Weight rho theta‖))

abbrev ValidDistinctHistory (A : Model F P J m) (n : ℕ) :=
  {H : MemoryHistory A n // H.Valid ∧ H.DistinctBirths}

instance (A : Model F P J m) (n : ℕ) : Finite (ValidDistinctHistory A n) :=
  MemoryHistory.valid_distinct_finite A n

instance (A : Model F P J m) (n : ℕ) : Fintype (ValidDistinctHistory A n) := Fintype.ofFinite _

theorem distinctMemoryExpression_eq_finite_sum (A : Model F P J m) (n : ℕ) (rho theta : ℝ) :
    distinctMemoryExpression A n rho theta = ∑ H : ValidDistinctHistory A n, H.val.Weight rho theta := by
  have hs : Function.support (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.DistinctBirths then H.Weight rho theta else 0) ⊆
      {H | H.Valid ∧ H.DistinctBirths} := by
    intro H hH
    change (if H.Valid ∧ H.DistinctBirths then H.Weight rho theta else 0) ≠ 0 at hH
    by_contra hn
    exact hH (ite_eq_right hn)
  unfold distinctMemoryExpression
  rw [← tsum_subtype_eq_of_support_subset hs]
  change (∑' H : ValidDistinctHistory A n,
    if H.val.Valid ∧ H.val.DistinctBirths then H.val.Weight rho theta else 0) = _
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro H _
  exact ite_eq_left H.property


end Erdos821.S2Core
