import Erdos821.S2.MemoryHistory

/-! Cardinal accounting for old indices, stores and original ghost births. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem zeroBirthBatch_card {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g) :
    (zeroBirthBatch p).card = b := by
  simp [zeroBirthBatch]

theorem ghostChoiceValid_memory_card {M : ℕ} {s t : P.MemoryState M}
    (c : GhostChoice s t) (hc : ghostChoiceValid c) (g : P.BigGroup) :
    (t.2.2 g).card = (s.2.2 g).card - (c.1 g).card + (c.2.1 g).val := by
  have he := congrArg Multiset.card (hc g).2
  simp only [Multiset.card_add, deleteMemoryIndices_card, zeroBirthBatch_card] at he
  exact he.symm

theorem ghostChoiceValid_size_le {M : ℕ} {s t : P.MemoryState M}
    (c : GhostChoice s t) (hc : ghostChoiceValid c) :
    P.memorySize t ≤ P.memorySize s + ghostBirthCount c := by
  simp only [PrimeGroups.memorySize, ghostBirthCount, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro g _
  have he := ghostChoiceValid_memory_card c hc g
  omega

theorem edgeChoiceValid_size_le (A : Model F P J m) {n : ℕ} (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (hc : edgeChoiceValid A .all i s t c) :
    P.memorySize t ≤ P.memorySize s + (J + F.ell) * Fintype.card P.BigGroup := by
  have hg := rawEdgeValid_memory_card A (A.pattern c.2.2.1) (edgeForward i)
    c.2.2.2.1 (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 hc.1
  simp only [PrimeGroups.memorySize]
  calc
    _ ≤ ∑ g : P.BigGroup, ((s.2.2 g).card + (J + F.ell)) := by
      apply Finset.sum_le_sum
      intro g _
      have he := hg g
      simp only [permuteActive] at he
      have hstore := Finset.card_le_univ (c.2.2.2.2.1 g)
      simp only [Fintype.card_fin] at hstore
      omega
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

/-- A generic finite recurrence accounts for each ghost increment exactly once. -/
theorem finite_growth_bound (n C : ℕ) (before after births : Fin (n + 1) → ℕ)
    (hzero : before 0 = 0)
    (hghost : ∀ i, after i ≤ before i + births i)
    (hedge : ∀ i : Fin n, before i.succ ≤ after i.castSucc + C) :
    ∀ i, before i ≤ (∑ j : Fin (n + 1), if j.val < i.val then births j else 0) + i.val * C ∧
      after i ≤ (∑ j : Fin (n + 1), if j.val ≤ i.val then births j else 0) + i.val * C := by
  have prefix_step (i : Fin (n + 1)) :
      (∑ j : Fin (n + 1), if j.val ≤ i.val then births j else 0) =
        (∑ j : Fin (n + 1), if j.val < i.val then births j else 0) + births i := by
    calc
      _ = ∑ j : Fin (n + 1), ((if j.val < i.val then births j else 0) +
          (if j = i then births i else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = i
        · subst j; simp
        · have hv : j.val ≠ i.val := fun hv => h (Fin.ext hv)
          by_cases hl : j.val < i.val
          · simp [hl, h, Nat.le_of_lt hl]
          · have hle : ¬ j.val ≤ i.val := by omega
            simp [hl, h, hle]
      _ = _ := by simp [Finset.sum_add_distrib]
  intro i
  induction i using Fin.induction with
  | zero =>
      constructor
      · simp [hzero]
      · simpa [prefix_step, hzero] using hghost 0
  | succ i ih =>
      have hp : (∑ j : Fin (n + 1), if j.val < i.succ.val then births j else 0) =
          ∑ j : Fin (n + 1), if j.val ≤ i.castSucc.val then births j else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff]
      have hb : before i.succ ≤
          (∑ j : Fin (n + 1), if j.val < i.succ.val then births j else 0) + i.succ.val * C := by
        calc
          _ ≤ after i.castSucc + C := hedge i
          _ ≤ ((∑ j : Fin (n + 1), if j.val ≤ i.castSucc.val then births j else 0) +
              i.castSucc.val * C) + C := Nat.add_le_add_right ih.2 C
          _ = _ := by
            rw [hp]
            simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_mul, Nat.one_mul]
            omega
      exact ⟨hb, by rw [prefix_step]; have hg := hghost i.succ; omega⟩

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

/-- Even the coarser bound M stores per edge is enough for the memory tail:
M is fixed before x tends to infinity. -/
theorem size_le_births_stores (hH : H.Valid) (i : Fin (n + 1)) :
    P.memorySize (H.before i) ≤ H.totalGhostBirths + i.val * ((J + F.ell) * Fintype.card P.BigGroup) ∧
    P.memorySize (H.after i) ≤ H.totalGhostBirths + i.val * ((J + F.ell) * Fintype.card P.BigGroup) := by
  have hz : P.memorySize (H.before 0) = 0 := by
    simp [PrimeGroups.memorySize, hH.1]
  have hg (i : Fin (n + 1)) := ghostChoiceValid_size_le (H.ghost i) (hH.2.2.1 i).2.2
  have he (i : Fin n) := edgeChoiceValid_size_le A i (H.after i.castSucc)
    (H.before i.succ) (H.edge i) (hH.2.2.2 i)
  have hr := finite_growth_bound n ((J + F.ell) * Fintype.card P.BigGroup)
    (fun i => P.memorySize (H.before i)) (fun i => P.memorySize (H.after i))
    (fun i => ghostBirthCount (H.ghost i)) hz hg he i
  constructor
  · apply hr.1.trans
    apply Nat.add_le_add_right
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> omega
  · apply hr.2.trans
    apply Nat.add_le_add_right
    apply Finset.sum_le_sum
    intro j _
    split_ifs <;> omega

theorem ghostBatch_le (B : ℕ) (hH : H.Truncated B) (i : Fin (n + 1)) (g : P.BigGroup) :
    ((H.ghost i).2.1 g).val ≤ B := by
  have hb := ((H.ghost i).2.1 g).isLt
  have hg : ((H.after i).2.2 g).card ≤ P.memorySize (H.after i) := by
    unfold PrimeGroups.memorySize
    exact Finset.single_le_sum (f := fun h : P.BigGroup => ((H.after i).2.2 h).card)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
  have hsize := (hH i).2
  omega

/-- Every path omitted by a cutoff needs a corresponding number of original
 ghost births, beyond the fixed total capacity of stores. -/
theorem tail_requires_births (B : ℕ) (hH : H.Valid) (htail : ¬ H.Truncated B) :
    B < H.totalGhostBirths + n * ((J + F.ell) * Fintype.card P.BigGroup) := by
  by_contra h
  apply htail
  intro i
  have hi : i.val ≤ n := by omega
  have hc := Nat.mul_le_mul_right ((J + F.ell) * Fintype.card P.BigGroup) hi
  have hg := H.size_le_births_stores hH i
  constructor <;> omega

end MemoryHistory


end Erdos821.S2Core
