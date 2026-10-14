import Erdos821.P3Adj.Factor
import Erdos821.P3Adj.Basic

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph hiding GhostChoice absoluteMemoryGhostKernel absoluteScaledMemoryGhostKernel deleteMemoryIndices ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEntry memoryGhostKernel zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core

variable {P : PrimeGroups} {g : P.BigGroup} {b : ℕ} (m : P.Memory g.val)

/-- Birth fiber: ordered prime batches giving multiset `m`. -/
def fiberP (m : P.Memory g.val) (b : ℕ) : Finset (Fin b → P.Prime g.val) :=
  Finset.univ.filter (fun p => zeroBirthBatch (P := P) (g := g.val) p = m)

/-- Birth multiset must be zero-only and card-correct. -/
def birthValid (m : P.Memory g.val) (b : ℕ) : Prop :=
  m.card = b ∧ ∀ v : P.Particle g.val, v.2 ≠ 0 → m.count v = 0

/-- Every element of a zero-only multiset has zero residue. -/
lemma zero_of_mem_of_valid {m : P.Memory g.val} {b : ℕ}
    (hvalid : birthValid (P := P) (g := g) m b) {v : P.Particle g.val}
    (hv : v ∈ m) : v.2 = 0 := by
  by_contra hne
  have hpos : 0 < m.count v := Multiset.count_pos.mpr hv
  have hz := hvalid.2 v hne
  omega

/-- A zero particle is determined by its prime. -/
lemma zero_mk_eq {v : P.Particle g.val} (hv : v.2 = 0) :
    ((⟨v.1, 0⟩ : P.Particle g.val)) = v := by
  rw [← hv]

lemma fiberP_card :
    (fiberP (P := P) (g := g) m b).card =
    if birthValid (P := P) (g := g) m b then
      b.factorial / ∏ v : P.Particle g.val, (m.count v).factorial
    else 0 := by
  induction b generalizing m with
  | zero =>
    simp only [fiberP]
    by_cases h : birthValid (P := P) (g := g) m 0
    · rw [if_pos h]
      have hcard : m.card = 0 := h.1
      have hm0 : m = 0 := Multiset.card_eq_zero.mp hcard
      rw [hm0]
      have hof : ∀ p : Fin 0 → P.Prime g.val,
          zeroBirthBatch (P := P) (g := g.val) p = 0 := by
        intro p
        unfold zeroBirthBatch
        rw [List.ofFn_zero]
        rfl
      have hfilter : Finset.univ.filter (fun p : Fin 0 → P.Prime g.val =>
          zeroBirthBatch (P := P) (g := g.val) p = 0) = Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hof p
      rw [hfilter]
      simp
    · rw [if_neg h]
      by_cases hcard : m.card = 0
      · have hm0 : m = 0 := Multiset.card_eq_zero.mp hcard
        rw [hm0] at h
        have hzero : ∀ v : P.Particle g.val, v.2 ≠ 0 → (0 : P.Memory g.val).count v = 0 := by
          intro v _
          exact Multiset.count_zero v
        exact absurd ⟨by simp, hzero⟩ h
      · have hne : ∀ p : Fin 0 → P.Prime g.val,
            ¬ (zeroBirthBatch (P := P) (g := g.val) p = m) := by
          intro p hp
          have hc : (zeroBirthBatch (P := P) (g := g.val) p).card = 0 := birth_card p
          rw [hp] at hc
          exact hcard hc
        have hempty : Finset.univ.filter (fun p : Fin 0 → P.Prime g.val =>
            zeroBirthBatch (P := P) (g := g.val) p = m) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact hne p hp
        rw [hempty, Finset.card_empty]
  | succ b ih =>
    simp only [fiberP]
    by_cases h : birthValid (P := P) (g := g) m (b + 1)
    · rw [if_pos h]
      obtain ⟨hcard, hzero⟩ := h
      -- Head particle of a valid batch lies in m.toFinset
      have hhead : ∀ p : Fin (b + 1) → P.Prime g.val,
          zeroBirthBatch (P := P) (g := g.val) p = m →
          ((⟨p 0, 0⟩ : P.Particle g.val)) ∈ m.toFinset := by
        intro p hp
        have hmem_list : (⟨p 0, 0⟩ : P.Particle g.val) ∈
            List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g.val)) := by
          have hof : List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g.val))
              = (⟨p 0, 0⟩ : P.Particle g.val) ::
                List.ofFn (fun i : Fin b => (⟨p i.succ, 0⟩ : P.Particle g.val)) := by
            conv_lhs => rw [List.ofFn_succ]
          rw [hof]
          exact List.mem_cons_self
        have hmem_multi : (⟨p 0, 0⟩ : P.Particle g.val) ∈
            (zeroBirthBatch (P := P) (g := g.val) p) := by
          unfold zeroBirthBatch
          simpa using hmem_list
        rw [hp] at hmem_multi
        exact Multiset.mem_toFinset.mpr hmem_multi
      -- Tail batch gives the erased multiset
      have htail : ∀ (v : P.Particle g.val) (p : Fin (b + 1) → P.Prime g.val),
          ((⟨p 0, 0⟩ : P.Particle g.val)) = v →
          zeroBirthBatch (P := P) (g := g.val) p = m →
          zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v := by
        intro v p hv hp
        have hof : List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g.val))
            = (⟨p 0, 0⟩ : P.Particle g.val) ::
              List.ofFn (fun i : Fin b => (⟨p i.succ, 0⟩ : P.Particle g.val)) := by
          conv_lhs => rw [List.ofFn_succ]
        have hcoe : (zeroBirthBatch (P := P) (g := g.val) p)
            = (⟨p 0, 0⟩ : P.Particle g.val) ::ₘ
              (zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ)) := by
          unfold zeroBirthBatch
          rw [hof, Multiset.cons_coe]
        rw [hcoe] at hp
        rw [hv] at hp
        have hv_mem : v ∈ m := by
          have hmem : v ∈ v ::ₘ
              (zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ)) :=
            Multiset.mem_cons_self v _
          rw [hp] at hmem
          exact hmem
        have herase : v ::ₘ (m.erase v) = m := Multiset.cons_erase hv_mem
        have hcons : v ::ₘ (zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ))
            = v ::ₘ (m.erase v) := by
          have hmp_eq1 : v ::ₘ
              (zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ)) = m := by
            exact hp
          exact hmp_eq1.trans herase.symm
        exact (Multiset.cons_inj_right v).mp hcons
      -- Fiber splits by head particle; sum head fibers via IH
      have hsplit : Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
          zeroBirthBatch (P := P) (g := g.val) p = m)
          = m.toFinset.biUnion (fun v =>
            Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
              ((⟨p 0, 0⟩ : P.Particle g.val)) = v ∧
              zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v)) := by
        apply Finset.ext
        intro p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Multiset.mem_toFinset]
        constructor
        · intro hp
          have hv_mem : ((⟨p 0, 0⟩ : P.Particle g.val)) ∈ m := by
            have hmem_list : (⟨p 0, 0⟩ : P.Particle g.val) ∈
                List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g.val)) := by
              have hof : List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g.val))
                  = (⟨p 0, 0⟩ : P.Particle g.val) ::
                    List.ofFn (fun i : Fin b => (⟨p i.succ, 0⟩ : P.Particle g.val)) := by
                conv_lhs => rw [List.ofFn_succ]
              rw [hof]
              exact List.mem_cons_self
            have hmem_multi : (⟨p 0, 0⟩ : P.Particle g.val) ∈
                (zeroBirthBatch (P := P) (g := g.val) p) := by
              unfold zeroBirthBatch
              simpa using hmem_list
            rw [hp] at hmem_multi
            exact hmem_multi
          exact ⟨(⟨p 0, 0⟩ : P.Particle g.val), hv_mem, rfl,
            htail _ p rfl hp⟩
        · rintro ⟨v, hv_mem, hv_eq, htail_eq⟩
          have hof : List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g.val))
              = (⟨p 0, 0⟩ : P.Particle g.val) ::
                List.ofFn (fun i : Fin b => (⟨p i.succ, 0⟩ : P.Particle g.val)) := by
            conv_lhs => rw [List.ofFn_succ]
          have hcoe : (zeroBirthBatch (P := P) (g := g.val) p)
              = (⟨p 0, 0⟩ : P.Particle g.val) ::ₘ
                (zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ)) := by
            unfold zeroBirthBatch
            rw [hof, Multiset.cons_coe]
          rw [hcoe, hv_eq, htail_eq]
          exact Multiset.cons_erase hv_mem
      rw [hsplit]
      -- Disjoint head fibers; sum via IH
      have hdisj : ∀ v ∈ m.toFinset, ∀ w ∈ m.toFinset, v ≠ w →
          Disjoint (Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            ((⟨p 0, 0⟩ : P.Particle g.val)) = v ∧
            zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v))
          (Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            ((⟨p 0, 0⟩ : P.Particle g.val)) = w ∧
            zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase w)) := by
        intro v _ w _ hvw
        apply Finset.disjoint_filter.mpr
        intro p _ hpa hpb
        exact hvw (hpa.1.symm.trans hpb.1)
      have hcard_sum : (m.toFinset.biUnion (fun v =>
          Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            ((⟨p 0, 0⟩ : P.Particle g.val)) = v ∧
            zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v))).card
          = ∑ v ∈ m.toFinset,
            (Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
              ((⟨p 0, 0⟩ : P.Particle g.val)) = v ∧
              zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v)).card := by
        apply Finset.card_biUnion
        intro v hv w hw hvw
        exact hdisj v (Finset.mem_coe.mp hv) w (Finset.mem_coe.mp hw) hvw
      -- Erased multisets stay zero-only with card b
      have herase_valid : ∀ v ∈ m.toFinset, birthValid (P := P) (g := g) (m.erase v) b := by
        intro v hv
        have hv_mem : v ∈ m := Multiset.mem_toFinset.mp hv
        have hcard_erase : (m.erase v).card = b := by
          have hcard : (m.erase v).card + 1 = m.card :=
            Multiset.card_erase_add_one hv_mem
          omega
        refine ⟨hcard_erase, fun w hw => ?_⟩
        have hle : (m.erase v).count w ≤ m.count w :=
          Multiset.count_le_of_le w (Multiset.erase_le v m)
        have hz := hzero w hw
        omega
      have hhead_card : ∀ v ∈ m.toFinset,
          (Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            ((⟨p 0, 0⟩ : P.Particle g.val)) = v ∧
            zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v)).card
          = (fiberP (P := P) (g := g) (m.erase v) b).card := by
        intro v hv
        apply Finset.card_bij (fun p _ => (fun i : Fin b => p i.succ))
        · intro p hp
          simp only [fiberP, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact hp.2
        · intro p1 hp1 p2 hp2 heq
          have h0_1 : ((⟨p1 0, 0⟩ : P.Particle g.val)) = v :=
            (Finset.mem_filter.mp hp1).2.1
          have h0_2 : ((⟨p2 0, 0⟩ : P.Particle g.val)) = v :=
            (Finset.mem_filter.mp hp2).2.1
          have hfst : p1 0 = p2 0 := by
            have e1 : p1 0 = ((((⟨p1 0, 0⟩ : P.Particle g.val))) : P.Particle g.val).1 := rfl
            have e2 : p2 0 = ((((⟨p2 0, 0⟩ : P.Particle g.val))) : P.Particle g.val).1 := rfl
            rw [e1, e2, h0_1, h0_2]
          have htail_eq : (fun i : Fin b => p1 i.succ) = (fun i : Fin b => p2 i.succ) := heq
          have hp1_eq : p1 = Fin.cons (p1 0) (fun i : Fin b => p1 i.succ) := by
            exact (Fin.cons_self_tail p1).symm
          have hp2_eq : p2 = Fin.cons (p2 0) (fun i : Fin b => p2 i.succ) := by
            exact (Fin.cons_self_tail p2).symm
          have hhead_eq : p1 0 = p2 0 := hfst
          rw [hhead_eq, htail_eq] at hp1_eq
          rw [hp1_eq]
          exact hp2_eq.symm
        · intro p' hp'
          simp only [fiberP, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
          -- prime head from particle v
          have hv_mem : v ∈ m := Multiset.mem_toFinset.mp hv
          have hv_zero : v.2 = 0 := zero_of_mem_of_valid ⟨hcard, hzero⟩ hv_mem
          have hmk : ((⟨v.1, 0⟩ : P.Particle g.val)) = v := by
            have e : v = ⟨v.1, v.2⟩ := rfl
            rw [hv_zero] at e
            exact e.symm
          have hfun_eq : (fun i : Fin b => (Fin.cons (α := fun _ => P.Prime g.val) v.1 p') i.succ)
              = p' := by
            apply funext
            intro i
            exact Fin.cons_succ (α := fun _ => P.Prime g.val) v.1 p' i
          have hhead : ((⟨(Fin.cons (α := fun _ => P.Prime g.val) v.1 p') 0, 0⟩ : P.Particle g.val))
              = v := by
            rw [Fin.cons_zero (α := fun _ => P.Prime g.val) v.1 p']
            exact hmk
          have htail : zeroBirthBatch (P := P) (g := g.val)
              (fun i : Fin b => (Fin.cons (α := fun _ => P.Prime g.val) v.1 p') i.succ)
              = m.erase v := by
            rw [hfun_eq]
            exact hp'
          exact ⟨Fin.cons (α := fun _ => P.Prime g.val) v.1 p',
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              ⟨hhead, htail⟩⟩, hfun_eq⟩
      have hsum_eq : (m.toFinset.biUnion (fun v =>
          Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            ((⟨p 0, 0⟩ : P.Particle g.val)) = v ∧
            zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v))).card
          = ∑ v ∈ m.toFinset, (fiberP (P := P) (g := g) (m.erase v) b).card := by
        rw [hcard_sum]
        apply Finset.sum_congr rfl
        intro v hv
        exact hhead_card v hv
      have hrest_eq : ∀ v ∈ m.toFinset,
          (fiberP (P := P) (g := g) (m.erase v) b).card
          = b.factorial / ∏ w : P.Particle g.val, ((m.erase v).count w).factorial := by
        intro v hv
        have hih := ih (m.erase v)
        rw [if_pos (herase_valid v hv)] at hih
        exact hih
      have hsum_rw : (m.toFinset.biUnion (fun v =>
          Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            ((⟨p 0, 0⟩ : P.Particle g.val)) = v ∧
            zeroBirthBatch (P := P) (g := g.val) (fun i : Fin b => p i.succ) = m.erase v))).card
          = ∑ v ∈ m.toFinset, (b.factorial / ∏ w : P.Particle g.val, ((m.erase v).count w).factorial) := by
        rw [hsum_eq]
        apply Finset.sum_congr rfl
        intro v hv
        exact hrest_eq v hv
      rw [hsum_rw]
      have hcount_sum : ∑ v ∈ m.toFinset, m.count v = b + 1 := by
        rw [Multiset.toFinset_sum_count_eq, hcard]
      have hDpos : 0 < ∏ w : P.Particle g.val, (m.count w).factorial :=
        Finset.prod_pos fun w _ => Nat.factorial_pos _
      have hsum_univ : ∑ w ∈ (Finset.univ : Finset (P.Particle g.val)), m.count w = b + 1 := by
        rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a), hcard]
      have hDvd : (∏ w : P.Particle g.val, (m.count w).factorial) ∣ (b + 1).factorial := by
        have h1 := Nat.prod_factorial_dvd_factorial_sum (Finset.univ : Finset (P.Particle g.val))
          (fun w => m.count w)
        rwa [hsum_univ] at h1
      have hterm : ∀ v ∈ m.toFinset,
          (∏ w : P.Particle g.val, (m.count w).factorial)
            * (b.factorial / ∏ w : P.Particle g.val, ((m.erase v).count w).factorial)
          = (m.count v) * b.factorial := by
        intro v hv
        have hv_mem : v ∈ m := Multiset.mem_toFinset.mp hv
        have hcpos : 0 < m.count v := Multiset.count_pos.mpr hv_mem
        have hcard_erase : (m.erase v).card = b := by
          have hcard2 : (m.erase v).card + 1 = m.card :=
            Multiset.card_erase_add_one hv_mem
          omega
        have hsum_v : ∑ w ∈ (Finset.univ : Finset (P.Particle g.val)), (m.erase v).count w = b := by
          rw [Multiset.sum_count_eq_card (fun a_ _ => Finset.mem_univ a_), hcard_erase]
        have hDvd_v : (∏ w : P.Particle g.val, ((m.erase v).count w).factorial) ∣ b.factorial := by
          have h1 := Nat.prod_factorial_dvd_factorial_sum (Finset.univ : Finset (P.Particle g.val))
            (fun w => (m.erase v).count w)
          rwa [hsum_v] at h1
        have hce : ((m.erase v).count v) + 1 = m.count v := by
          have h1 := Multiset.count_erase_self v m
          omega
        have hfact : (m.count v).factorial
            = m.count v * (((m.erase v).count v).factorial) := by
          rw [← hce]
          exact Nat.factorial_succ _
        have hR_eq : (∏ w ∈ Finset.univ.erase v, (m.count w).factorial)
            = ∏ w ∈ Finset.univ.erase v, (((m.erase v).count w).factorial) := by
          apply Finset.prod_congr rfl
          intro w hw
          have hne : w ≠ v := Finset.ne_of_mem_erase hw
          rw [(Multiset.count_erase_of_ne hne m).symm]
        have hD_eq : (∏ w : P.Particle g.val, (m.count w).factorial)
            = m.count v * ∏ w : P.Particle g.val, (((m.erase v).count w).factorial) := by
          have h1 := Finset.mul_prod_erase (Finset.univ : Finset (P.Particle g.val))
            (fun w => (m.count w).factorial) (Finset.mem_univ v)
          have h2 := Finset.mul_prod_erase (Finset.univ : Finset (P.Particle g.val))
            (fun w => ((m.erase v).count w).factorial) (Finset.mem_univ v)
          rw [← h1, ← h2, hR_eq, hfact]
          ring
        calc (∏ w : P.Particle g.val, (m.count w).factorial)
              * (b.factorial / ∏ w : P.Particle g.val, (((m.erase v).count w).factorial))
            = m.count v * ((∏ w : P.Particle g.val, (((m.erase v).count w).factorial))
              * (b.factorial / ∏ w : P.Particle g.val, (((m.erase v).count w).factorial))) := by
              rw [hD_eq]; ring
          _ = m.count v * b.factorial := by
              rw [Nat.mul_div_cancel' hDvd_v]
      have hmul : (∏ w : P.Particle g.val, (m.count w).factorial)
          * (∑ v ∈ m.toFinset, (b.factorial / ∏ w : P.Particle g.val, ((m.erase v).count w).factorial))
          = (b + 1).factorial := by
        rw [Finset.mul_sum]
        have hcongr : (∑ v ∈ m.toFinset, (∏ w : P.Particle g.val, (m.count w).factorial)
            * (b.factorial / ∏ w : P.Particle g.val, ((m.erase v).count w).factorial))
            = ∑ v ∈ m.toFinset, (m.count v) * b.factorial := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hterm v hv
        rw [hcongr, ← Finset.sum_mul, hcount_sum]
        exact (Nat.factorial_succ b).symm
      have hfin : (∏ w : P.Particle g.val, (m.count w).factorial)
          * ((b + 1).factorial / ∏ w : P.Particle g.val, (m.count w).factorial)
          = (b + 1).factorial :=
        Nat.mul_div_cancel' hDvd
      have hcancel := hmul.trans hfin.symm
      exact mul_left_cancel₀ (ne_of_gt hDpos) hcancel
    · rw [if_neg h]
      by_cases hcard : m.card = b + 1
      · have hzero_neg : ¬ ∀ v : P.Particle g.val, v.2 ≠ 0 → m.count v = 0 := by
          intro hzero'
          exact h ⟨hcard, hzero'⟩
        push_neg at hzero_neg
        obtain ⟨v, hv1, hv2⟩ := hzero_neg
        have hpos : 0 < m.count v := Nat.pos_of_ne_zero hv2
        have hmem : v ∈ m := Multiset.count_pos.mp hpos
        have hne : ∀ p : Fin (b + 1) → P.Prime g.val,
            ¬ (zeroBirthBatch (P := P) (g := g.val) p = m) := by
          intro p hp
          have hmem_birth : v ∈ zeroBirthBatch (P := P) (g := g.val) p := by
            rw [hp]
            exact hmem
          unfold zeroBirthBatch at hmem_birth
          rw [Multiset.mem_coe] at hmem_birth
          rw [List.mem_ofFn'] at hmem_birth
          obtain ⟨i, hi⟩ := hmem_birth
          cases v with
          | mk q r =>
            have h1 : p i = q := congrArg Sigma.fst hi
            subst h1
            exact hv1 (eq_of_heq (Sigma.mk.inj_iff.mp hi).2).symm
        have hempty : Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            zeroBirthBatch (P := P) (g := g.val) p = m) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact hne p hp
        rw [hempty, Finset.card_empty]
      · have hne : ∀ p : Fin (b + 1) → P.Prime g.val,
          ¬ (zeroBirthBatch (P := P) (g := g.val) p = m) := by
          intro p hp
          have hcard_p : (zeroBirthBatch (P := P) (g := g.val) p).card = b + 1 := birth_card p
          rw [hp] at hcard_p
          exact hcard hcard_p
        have hempty : Finset.univ.filter (fun p : Fin (b + 1) → P.Prime g.val =>
            zeroBirthBatch (P := P) (g := g.val) p = m) = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact hne p hp
        rw [hempty, Finset.card_empty]

end Erdos821.P3Adj
