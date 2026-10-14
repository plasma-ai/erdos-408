import Erdos821.P3Adj.Factor
import Erdos821.P3Adj.Basic
import Erdos821.P3Adj.Weight

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph hiding GhostChoice absoluteMemoryGhostKernel absoluteScaledMemoryGhostKernel deleteMemoryIndices ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEntry memoryGhostKernel zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core

variable {P : PrimeGroups} {g : P.BigGroup} (s u : P.Memory g.val)

def isZeroParticle (v : P.Particle g.val) : Prop := v.2 = 0

instance : DecidablePred (isZeroParticle (P := P) (g := g)) := fun v =>
  inferInstanceAs (Decidable (v.2 = 0))

def Sv (s : P.Memory g.val) (v : P.Particle g.val) : Finset (Fin s.card) :=
  Finset.univ.filter (fun i => memoryEntry s i = v)

lemma Sv_card (s : P.Memory g.val) (v : P.Particle g.val) :
    (Sv (P := P) (g := g) s v).card = s.count v := by
  unfold Sv
  exact (count_eq_card_filter s v).symm

lemma Sv_disjoint (s : P.Memory g.val) (v w : P.Particle g.val) (hvw : v ≠ w) :
    Disjoint (Sv (P := P) (g := g) s v) (Sv (P := P) (g := g) s w) := by
  unfold Sv
  apply Finset.disjoint_filter.mpr
  intro i _ hiv hiw
  exact hvw (hiv.symm.trans hiw)

lemma filter_sdiff_eq (A : Finset (Fin s.card)) (v : P.Particle g.val) :
    ((Finset.univ \ A).filter (fun i => memoryEntry s i = v))
    = ((Sv (P := P) (g := g) s v) \ A) := by
  unfold Sv
  ext i
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

lemma delete_count_Sv (A : Finset (Fin s.card)) (v : P.Particle g.val) :
    (deleteMemoryIndices s A).count v = (((Sv (P := P) (g := g) s v) \ A).card) := by
  rw [delete_count_eq s A v, filter_sdiff_eq s A v]

/-- Every index lies in its own value block. -/
lemma mem_Sv_self (i : Fin s.card) :
    i ∈ Sv (P := P) (g := g) s (memoryEntry s i) := by
  unfold Sv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The value blocks cover all indices. -/
lemma biUnion_Sv : Finset.univ.biUnion (fun v => Sv (P := P) (g := g) s v) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨memoryEntry s i, mem_Sv_self s i⟩

/-- Any deleted set splits across value blocks. -/
lemma A_eq_biUnion (A : Finset (Fin s.card)) :
    A = Finset.univ.biUnion (fun v => (Sv (P := P) (g := g) s v) ∩ A) := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_inter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    exact ⟨memoryEntry s i, mem_Sv_self s i, hi⟩
  · rintro ⟨v, _, hiA⟩
    exact hiA

/-- Zero blocks lie inside zero indices; nonzero blocks are disjoint from them. -/
lemma Sv_subset_zero (v : P.Particle g.val) (hv : isZeroParticle (P := P) (g := g) v) :
    Sv (P := P) (g := g) s v ⊆ zeroMemoryIndices s := by
  unfold Sv zeroMemoryIndices isZeroParticle at *
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rw [hi]
  exact hv

lemma Sv_disjoint_zero (v : P.Particle g.val) (hv : ¬ isZeroParticle (P := P) (g := g) v) :
    Disjoint (Sv (P := P) (g := g) s v) (zeroMemoryIndices s) := by
  unfold Sv zeroMemoryIndices isZeroParticle at *
  apply Finset.disjoint_filter.mpr
  intro i _ hiv hzero
  apply hv
  rw [← hiv]
  exact hzero

/-- Deletion fiber: deleted index sets giving surviving `u`. -/
def fiberA : Finset (Finset (Fin s.card)) :=
  Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices s ∧ deleteMemoryIndices s A = u)

/-- Nonzero preservation needed for nonempty fiber. -/
def nonzeroPreserved : Prop :=
  ∀ v : P.Particle g.val, ¬ isZeroParticle v → u.count v = s.count v

/-- Fiber implies prescribed intersection sizes. -/
lemma fiber_imp_inter_card (A : Finset (Fin s.card))
    (hA : A ∈ fiberA (P := P) (g := g) s u) (v : P.Particle g.val) :
    ((Sv (P := P) (g := g) s v) ∩ A).card = s.count v - u.count v := by
  have hmem : A ⊆ zeroMemoryIndices s ∧ deleteMemoryIndices s A = u := by
    simpa only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and] using hA
  have hcount : (deleteMemoryIndices s A).count v = u.count v := by
    rw [hmem.2]
  rw [delete_count_Sv s A v] at hcount
  have hSv : (Sv (P := P) (g := g) s v).card = s.count v := Sv_card s v
  have hsdiff : (((Sv (P := P) (g := g) s v) \ A).card)
      = (Sv (P := P) (g := g) s v).card - (A ∩ (Sv (P := P) (g := g) s v)).card := by
    rw [Finset.card_sdiff]
  have hcomm : (A ∩ (Sv (P := P) (g := g) s v)).card
      = ((Sv (P := P) (g := g) s v) ∩ A).card := by
    rw [Finset.inter_comm]
  have hle : ((Sv (P := P) (g := g) s v) ∩ A).card ≤ s.count v := by
    rw [← hSv]
    exact Finset.card_le_card Finset.inter_subset_left
  omega

/-- Deletion is always a submultiset. -/
lemma delete_le (A : Finset (Fin s.card)) : deleteMemoryIndices s A ≤ s := by
  rw [Multiset.le_iff_count]
  intro v
  rw [delete_count_Sv s A v]
  have hsub : ((Sv (P := P) (g := g) s v) \ A) ⊆ (Sv (P := P) (g := g) s v) :=
    Finset.sdiff_subset
  have hcard := Finset.card_le_card hsub
  rw [Sv_card s v] at hcard
  exact hcard

/-- Fiber implies validity (nonzero preserved and submultiset). -/
lemma fiber_imp_valid (A : Finset (Fin s.card)) (hA : A ∈ fiberA (P := P) (g := g) s u) :
    nonzeroPreserved (P := P) (g := g) s u ∧ u ≤ s := by
  have hmem : A ⊆ zeroMemoryIndices s ∧ deleteMemoryIndices s A = u := by
    simpa only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and] using hA
  constructor
  · intro v hv
    have hdisj := Sv_disjoint_zero (P := P) (g := g) s v hv
    have hinter : ((Sv (P := P) (g := g) s v) ∩ A) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      rw [Finset.mem_inter] at hi
      have hiS := hi.1
      have hiA := hi.2
      have hiZ := hmem.1 hiA
      have hnot : i ∉ zeroMemoryIndices s := by
        have hdisj' : Disjoint (Sv (P := P) (g := g) s v) (zeroMemoryIndices s) := hdisj
        rw [Finset.disjoint_left] at hdisj'
        exact hdisj' hiS
      exact hnot hiZ
    have hinter_card : ((Sv (P := P) (g := g) s v) ∩ A).card = 0 := by
      rw [hinter, Finset.card_empty]
    have hinter_size := fiber_imp_inter_card (P := P) (g := g) s u A hA v
    rw [hinter_card] at hinter_size
    have hle : u.count v ≤ s.count v := by
      have hle' : (deleteMemoryIndices s A).count v ≤ s.count v := by
        have hle'' := delete_le (P := P) (g := g) s A
        rw [Multiset.le_iff_count] at hle''
        exact hle'' v
      rw [hmem.2] at hle'
      exact hle'
    omega
  · rw [← hmem.2]
    exact delete_le s A

lemma fiberA_card :
    (fiberA (P := P) (g := g) s u).card =
    if nonzeroPreserved (P := P) (g := g) s u ∧ u ≤ s then
      ∏ v : P.Particle g.val, Nat.choose (s.count v) (u.count v)
    else 0 := by
  by_cases hvalid : nonzeroPreserved (P := P) (g := g) s u ∧ u ≤ s
  · rw [if_pos hvalid]
    obtain ⟨hpres, hle⟩ := hvalid
    have hcount_le : ∀ v : P.Particle g.val, u.count v ≤ s.count v := by
      rw [← Multiset.le_iff_count]
      exact hle
    let k : P.Particle g.val → ℕ := fun v => s.count v - u.count v
    let t : ∀ v : P.Particle g.val, Finset (Finset (Fin s.card)) :=
      fun v => Finset.powersetCard (k v) (Sv (P := P) (g := g) s v)
    let Pf : Finset (∀ v : P.Particle g.val, Finset (Fin s.card)) :=
      Fintype.piFinset t
    -- Forward map lands in piFinset
    have hfw_mem : ∀ A ∈ fiberA (P := P) (g := g) s u,
        (fun v => (Sv (P := P) (g := g) s v) ∩ A) ∈ Pf := by
      intro A hA
      simp only [Pf, t, Fintype.mem_piFinset, Finset.mem_powersetCard]
      intro v
      constructor
      · exact Finset.inter_subset_left
      · exact fiber_imp_inter_card (P := P) (g := g) s u A hA v
    have hfw_inj : ∀ A1 ∈ fiberA (P := P) (g := g) s u,
        ∀ A2 ∈ fiberA (P := P) (g := g) s u,
        (fun v => (Sv (P := P) (g := g) s v) ∩ A1)
        = (fun v => (Sv (P := P) (g := g) s v) ∩ A2) → A1 = A2 := by
      intro A1 _ A2 _ heq
      have h1 := A_eq_biUnion (P := P) (g := g) s A1
      have h2 := A_eq_biUnion (P := P) (g := g) s A2
      have h12 : Finset.univ.biUnion (fun v => (Sv (P := P) (g := g) s v) ∩ A1)
          = Finset.univ.biUnion (fun v => (Sv (P := P) (g := g) s v) ∩ A2) := by
        rw [heq]
      rw [h1, h2, h12]
    have hfw_surj : ∀ D ∈ Pf, ∃ A, ∃ (_ : A ∈ fiberA (P := P) (g := g) s u),
        (fun v => (Sv (P := P) (g := g) s v) ∩ A) = D := by
      intro D hD
      have hDmem : ∀ v, D v ⊆ Sv (P := P) (g := g) s v ∧ (D v).card = k v := by
        intro v
        have hv : D v ∈ t v := by
          have hmem : D ∈ Pf := hD
          simp only [Pf, t, Fintype.mem_piFinset] at hmem
          exact hmem v
        simp only [t, k, Finset.mem_powersetCard] at hv
        exact hv
      let A0 : Finset (Fin s.card) := Finset.univ.biUnion D
      have hA0_mem : A0 ∈ fiberA (P := P) (g := g) s u := by
        have hA0_sub : A0 ⊆ zeroMemoryIndices s := by
          unfold A0
          apply Finset.biUnion_subset.mpr
          intro v _
          by_cases hvz : isZeroParticle (P := P) (g := g) v
          · exact Finset.Subset.trans (hDmem v).1 (Sv_subset_zero (P := P) (g := g) s v hvz)
          · have hk0 : k v = 0 := by
              simp only [k]
              have hpresv := hpres v hvz
              omega
            have hcard0 : (D v).card = 0 := by
              have hcard := (hDmem v).2
              simp only [k] at hcard ⊢
              -- hcard : card = s.count - u.count, with preserved equality gives 0?
              have hpresv := hpres v hvz
              omega
            have hempty : D v = ∅ := Finset.card_eq_zero.mp hcard0
            rw [hempty]
            exact Finset.empty_subset _
        have hA0_del : deleteMemoryIndices s A0 = u := by
          apply Multiset.ext.mpr
          intro v
          rw [delete_count_Sv s A0 v]
          have hinter : ((Sv (P := P) (g := g) s v) ∩ A0) = D v := by
            apply Finset.ext
            intro x
            simp only [Finset.mem_inter]
            constructor
            · rintro ⟨hxS, hxU⟩
              rw [Finset.mem_biUnion] at hxU
              obtain ⟨w, _, hxDw⟩ := hxU
              have hxSw : x ∈ Sv (P := P) (g := g) s w := (hDmem w).1 hxDw
              by_cases hvw : v = w
              · subst hvw
                exact hxDw
              · have hdisj := Sv_disjoint (P := P) (g := g) s v w hvw
                have hcontra : False := by
                  rw [Finset.disjoint_left] at hdisj
                  exact hdisj hxS hxSw
                exact False.elim hcontra
            · intro hxD
              have hxS : x ∈ Sv (P := P) (g := g) s v := (hDmem v).1 hxD
              have hxU : x ∈ Finset.univ.biUnion D := by
                rw [Finset.mem_biUnion]
                exact ⟨v, Finset.mem_univ v, hxD⟩
              exact ⟨hxS, hxU⟩
          have hcardD : (D v).card = k v := (hDmem v).2
          have hSv : (Sv (P := P) (g := g) s v).card = s.count v := Sv_card s v
          have hsdiff : (((Sv (P := P) (g := g) s v) \ A0).card)
              = (Sv (P := P) (g := g) s v).card - ((Sv (P := P) (g := g) s v) ∩ A0).card := by
            have h := Finset.card_sdiff (s := A0) (t := Sv (P := P) (g := g) s v)
            -- card_sdiff : (t \ s).card = t.card - (s ∩ t).card, need comm?
            simp only [Finset.inter_comm] at h ⊢
            exact h
          rw [hsdiff, hinter, hcardD, hSv]
          simp only [k]
          have hle_v := hcount_le v
          omega
        simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hA0_sub, hA0_del⟩
      have hA0_eq : (fun v => (Sv (P := P) (g := g) s v) ∩ A0) = D := by
        apply funext
        intro v
        apply Finset.ext
        intro x
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hxS, hxU⟩
          rw [Finset.mem_biUnion] at hxU
          obtain ⟨w, _, hxDw⟩ := hxU
          have hxSw : x ∈ Sv (P := P) (g := g) s w := (hDmem w).1 hxDw
          by_cases hvw : v = w
          · subst hvw
            exact hxDw
          · have hdisj := Sv_disjoint (P := P) (g := g) s v w hvw
            have hcontra : False := by
              rw [Finset.disjoint_left] at hdisj
              exact hdisj hxS hxSw
            exact False.elim hcontra
        · intro hxD
          have hxS : x ∈ Sv (P := P) (g := g) s v := (hDmem v).1 hxD
          have hxU : x ∈ Finset.univ.biUnion D := by
            rw [Finset.mem_biUnion]
            exact ⟨v, Finset.mem_univ v, hxD⟩
          exact ⟨hxS, hxU⟩
      exact ⟨A0, hA0_mem, hA0_eq⟩
    have hbij := Finset.card_bij (fun A _ => (fun v => (Sv (P := P) (g := g) s v) ∩ A))
      hfw_mem hfw_inj hfw_surj
    rw [hbij]
    simp only [Pf, t, k, Fintype.card_piFinset, Finset.card_powersetCard, Sv_card]
    apply Finset.prod_congr rfl
    intro v _
    rw [Nat.choose_symm (hcount_le v)]
  · rw [if_neg hvalid]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro A hA
    exact hvalid (fiber_imp_valid s u A hA)


end Erdos821.P3Adj
