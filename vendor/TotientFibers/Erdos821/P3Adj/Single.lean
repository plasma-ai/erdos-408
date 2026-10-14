import Erdos821.P3Adj.Factor
import Erdos821.P3Adj.Basic
import Erdos821.P3Adj.Weight
import Erdos821.P3Adj.FiberA
import Erdos821.P3Adj.FiberP

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph hiding GhostChoice absoluteMemoryGhostKernel absoluteScaledMemoryGhostKernel deleteMemoryIndices ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEntry memoryGhostKernel zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData} {J n : ℕ} {rho d : ℝ} {i : Fin (n + 1)}
variable {g : P.BigGroup} {s0 t0 : P.Memory g.val}

/-- Per-group reversal factor: `(d * V) ^ (card t - card s)` as in `ghostReversalFactor`. -/
def singleReversal (P : PrimeGroups) (d : ℝ) (g : P.BigGroup)
    (s0 t0 : P.Memory g.val) : ℝ :=
  (d * P.V g.val) ^ (((t0.card : ℤ) - (s0.card : ℤ)))

/-- Group Fock mass is positive under positivity hypotheses. -/
lemma groupMemoryMass_pos (F : FixedData) (n : ℕ) (g : P.Group)
    (z : P.Memory g) (hV : 0 < P.V g)
    (hbase : ∀ q : P.Prime g, 0 < baselinePrime F n q.val) :
    0 < P.groupMemoryMass F n g z := by
  unfold PrimeGroups.groupMemoryMass
  apply div_pos
  · have hmap : ∀ a ∈ z.map (fun u => tiltedMu F P n g u.1), 0 < a := by
      intro a ha
      rw [Multiset.mem_map] at ha
      obtain ⟨u, _, rfl⟩ := ha
      exact tiltedMu_pos hV (hbase u.1)
    exact Multiset.prod_pos hmap
  · apply Finset.prod_pos
    intro u _
    exact Nat.cast_pos.mpr (Nat.factorial_pos _)

lemma groupMemoryMass_ne_zero (F : FixedData) (n : ℕ) (g : P.Group)
    (z : P.Memory g) (hV : 0 < P.V g)
    (hbase : ∀ q : P.Prime g, 0 < baselinePrime F n q.val) :
    P.groupMemoryMass F n g z ≠ 0 :=
  ne_of_gt (groupMemoryMass_pos F n g z hV hbase)

/-- A birth batch contains only zero-residue particles. -/
lemma birth_batch_zero {b : ℕ} (p : Fin b → P.Prime g.val)
    (v : P.Particle g.val) (hv : v.2 ≠ 0) :
    (zeroBirthBatch (P := P) (g := g.val) p).count v = 0 := by
  rw [Multiset.count_eq_zero_of_notMem]
  intro hmem
  unfold zeroBirthBatch at hmem
  rw [Multiset.mem_coe] at hmem
  rw [List.mem_ofFn'] at hmem
  obtain ⟨k, hk⟩ := hmem
  cases v with
  | mk q r =>
    have h1 : p k = q := congrArg Sigma.fst hk
    subst h1
    exact hv (eq_of_heq (Sigma.mk.inj_iff.mp hk).2).symm

/-- Deletion along zero indices preserves nonzero counts. -/
lemma delete_preserves_nonzero (s : P.Memory g.val) (A : Finset (Fin s.card))
    (hA : A ⊆ zeroMemoryIndices s) (v : P.Particle g.val)
    (hv : ¬ isZeroParticle (P := P) (g := g) v) :
    (deleteMemoryIndices s A).count v = s.count v := by
  rw [delete_count_Sv s A v]
  have hdisj := Sv_disjoint_zero (P := P) (g := g) s v hv
  have hinter : ((Sv (P := P) (g := g) s v) ∩ A) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro k hk
    rw [Finset.mem_inter] at hk
    have hkS := hk.1
    have hkA := hk.2
    have hkZ := hA hkA
    have hnot : k ∉ zeroMemoryIndices s := by
      rw [Finset.disjoint_left] at hdisj
      exact hdisj hkS
    exact hnot hkZ
  have hdisjA : Disjoint (Sv (P := P) (g := g) s v) A :=
    hdisj.mono_right hA
  have hsdiff : ((Sv (P := P) (g := g) s v) \ A) = Sv (P := P) (g := g) s v :=
    Finset.sdiff_eq_self_of_disjoint hdisjA
  rw [hsdiff, Sv_card s v]

/-- A valid single transition preserves all nonzero counts. -/
lemma singleValid_preserves_nonzero {A : Finset (Fin s0.card)} {b : Fin (t0.card + 1)}
    {p : Fin b.val → P.Prime g.val}
    (hvalid : singleValid (P := P) (g := g) s0 t0 A b p)
    (v : P.Particle g.val) (hv : ¬ isZeroParticle (P := P) (g := g) v) :
    s0.count v = t0.count v := by
  obtain ⟨hsub, heq⟩ := hvalid
  have hdel : (deleteMemoryIndices s0 A).count v = s0.count v :=
    delete_preserves_nonzero s0 A hsub v hv
  have hbirth : (zeroBirthBatch (P := P) (g := g.val) p).count v = 0 := by
    unfold isZeroParticle at hv
    exact birth_batch_zero p v hv
  have hcount : (deleteMemoryIndices s0 A + zeroBirthBatch (P := P) (g := g.val) p).count v =
      t0.count v := congrArg (fun m => Multiset.count v m) heq
  have hadd : (deleteMemoryIndices s0 A + zeroBirthBatch (P := P) (g := g.val) p).count v =
      (deleteMemoryIndices s0 A).count v + (zeroBirthBatch (P := P) (g := g.val) p).count v :=
    Multiset.count_add _ _ _
  omega

/-- If source and target disagree on a nonzero count, no choice is valid. -/
lemma singleValid_false_of_mismatch {A : Finset (Fin s0.card)} {b : Fin (t0.card + 1)}
    {p : Fin b.val → P.Prime g.val}
    (hmis : ∃ v : P.Particle g.val, ¬ isZeroParticle v ∧ s0.count v ≠ t0.count v)
    (hvalid : singleValid (P := P) (g := g) s0 t0 A b p) : False := by
  obtain ⟨v, hvz, hne⟩ := hmis
  exact hne (singleValid_preserves_nonzero hvalid v hvz)

/-- Single kernel vanishes on nonzero mismatch. -/
lemma singleKernel_eq_zero_of_mismatch
    (hmis : ∃ v : P.Particle g.val, ¬ isZeroParticle v ∧ s0.count v ≠ t0.count v)
    (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1)) :
    singleKernel F n rho d i g s0 t0 = 0 := by
  unfold singleKernel
  apply Finset.sum_eq_zero
  intro A _
  apply Finset.sum_eq_zero
  intro b _
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  intro hvalid
  exact singleValid_false_of_mismatch hmis hvalid

/-- Birth product depends only on the birth multiset. -/
lemma prodMu_batch_eq {b : ℕ} (p : Fin b → P.Prime g.val)
    (m : P.Memory g.val) (hm : zeroBirthBatch (P := P) (g := g.val) p = m) :
    (∏ h : Fin b, tiltedMu F P n g.val (p h)) =
      (m.map (fun u => tiltedMu F P n g.val u.1)).prod := by
  rw [← hm]
  unfold zeroBirthBatch
  rw [Multiset.map_coe, Multiset.prod_coe]
  have hmap : (List.ofFn (fun i => (⟨p i, 0⟩ : P.Particle g.val))).map
      (fun u => tiltedMu F P n g.val u.1)
      = List.ofFn (fun i => tiltedMu F P n g.val (p i)) := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, Fin.prod_ofFn]

/-- Deletion never exceeds the source. -/
lemma delete_le_mem (s : P.Memory g.val) (A : Finset (Fin s.card)) :
    deleteMemoryIndices s A ≤ s :=
  delete_le (P := P) (g := g) s A

/-- Source splits as survivor plus remainder. -/
lemma source_split (s u : P.Memory g.val) (hle : u ≤ s) :
    u + (s - u) = s := by
  rw [add_comm]
  exact Multiset.add_sub_cancel hle

/-- Mapped products split over survivor and remainder. -/
lemma map_prod_split (s u : P.Memory g.val) (hle : u ≤ s)
    (f : P.Particle g.val → ℝ) :
    (s.map f).prod = (u.map f).prod * ((s - u).map f).prod := by
  have h : s = u + (s - u) := by
    rw [add_comm]
    exact (Multiset.add_sub_cancel hle).symm
  conv_lhs => rw [h, Multiset.map_add, Multiset.prod_add]

/-- Cancellation for multiset addition via counts. -/
lemma add_cancel_left (u a b : P.Memory g.val) (h : u + a = u + b) : a = b := by
  apply Multiset.ext.mpr
  intro v
  have hc := congrArg (fun m => Multiset.count v m) h
  simp only [Multiset.count_add] at hc
  omega

/-- Surviving plus birth equals target iff birth is the difference. -/
lemma birth_eq_diff_iff (u t m : P.Memory g.val) (hle : u ≤ t) (hmd : m = t - u)
    (birth : P.Memory g.val) : u + birth = t ↔ birth = m := by
  have h2 : u + m = t := by
    rw [hmd, add_comm]
    exact Multiset.add_sub_cancel hle
  constructor
  · intro h
    have heq : u + birth = u + m := h.trans h2.symm
    exact add_cancel_left u birth m heq
  · intro h
    rw [h, h2]

/-- If survivor is not below target, no birth completes it. -/
lemma no_birth_of_not_le (u t birth : P.Memory g.val) (hle : ¬ u ≤ t)
    (h : u + birth = t) : False := by
  have hle2 : u ≤ t := by
    rw [← h]
    exact Multiset.le_add_right u birth
  exact hle hle2

/-- Sum over birth batches for fixed deletion and birth size, assuming deletion is
zero-contained and survivor lies below target. -/
lemma sum_p_eq (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (b : Fin (t0.card + 1))
    (hA_sub : A ⊆ zeroMemoryIndices s0)
    (hrho : 0 < rho) (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val)
    (hle_t : deleteMemoryIndices s0 A ≤ t0) :
    (∑ p : Fin b.val → P.Prime g.val,
      if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) =
    (((eta F n i / rho) ^ A.card *
      (visitQ F.q n i / rho ^ (2 : ℕ)) ^
        ((zeroMemoryIndices s0).card - A.card)) *
    ((((b.val.factorial : ℝ)⁻¹)) *
      ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val)) *
    ((((fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card : ℝ)) *
      (((t0 - deleteMemoryIndices s0 A).map
        (fun w => tiltedMu F P n g.val w.1)).prod))) := by
  have hvalid_iff : ∀ p : Fin b.val → P.Prime g.val,
      singleValid (P := P) (g := g) s0 t0 A b p ↔
        zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) := by
    intro p
    constructor
    · intro h
      have h2 : deleteMemoryIndices s0 A + zeroBirthBatch (P := P) (g := g.val) p = t0 := h.2
      exact (birth_eq_diff_iff _ t0 _ hle_t rfl _).mp h2
    · intro h
      have hbase_eq : deleteMemoryIndices s0 A + (t0 - deleteMemoryIndices s0 A) = t0 := by
        rw [add_comm]
        exact Multiset.add_sub_cancel hle_t
      have h2 : deleteMemoryIndices s0 A + zeroBirthBatch (P := P) (g := g.val) p = t0 := by
        rw [h]
        exact hbase_eq
      exact ⟨hA_sub, h2⟩
  have habs : ∀ p : Fin b.val → P.Prime g.val,
      |singleWeight F n rho i g s0 t0 A b p| =
      (eta F n i / rho) ^ A.card *
      (visitQ F.q n i / rho ^ (2 : ℕ)) ^
        ((zeroMemoryIndices s0).card - A.card) *
      ((b.val.factorial : ℝ)⁻¹) *
      (eta F n i * P.V g.val / rho) ^ b.val *
      ∏ h : Fin b.val, tiltedMu F P n g.val (p h) :=
    fun p => abs_singleWeight_eq F n rho hrho i g s0 t0 A b p hV hbase
  have hterm : ∀ p : Fin b.val → P.Prime g.val,
      (if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) =
      ((eta F n i / rho) ^ A.card *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices s0).card - A.card) *
        (((b.val.factorial : ℝ)⁻¹) *
          (eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val)) *
      (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
        ∏ h : Fin b.val, tiltedMu F P n g.val (p h)
      else 0) := by
    intro p
    by_cases h : zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A)
    · have hv : singleValid (P := P) (g := g) s0 t0 A b p := (hvalid_iff p).mpr h
      simp only [if_pos hv, if_pos h, habs p]
      ring
    · have hv : ¬ singleValid (P := P) (g := g) s0 t0 A b p := fun hvv => h ((hvalid_iff p).mp hvv)
      simp only [if_neg hv, if_neg h]
      ring
  have hconst : ∀ p : Fin b.val → P.Prime g.val,
      (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
        ∏ h : Fin b.val, tiltedMu F P n g.val (p h)
      else 0) =
      (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
        ((t0 - deleteMemoryIndices s0 A).map (fun w => tiltedMu F P n g.val w.1)).prod
      else 0) := by
    intro p
    by_cases h : zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A)
    · simp only [if_pos h]
      exact prodMu_batch_eq (F := F) (n := n) p _ h
    · simp only [if_neg h]
  have hsum_congr : (∑ p : Fin b.val → P.Prime g.val,
      (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
        ∏ h : Fin b.val, tiltedMu F P n g.val (p h)
      else 0)) =
      (∑ p : Fin b.val → P.Prime g.val,
      (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
        ((t0 - deleteMemoryIndices s0 A).map (fun w => tiltedMu F P n g.val w.1)).prod
      else 0)) :=
    Finset.sum_congr rfl (fun p _ => hconst p)
  have hsum : (∑ p : Fin b.val → P.Prime g.val,
      (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
        ((t0 - deleteMemoryIndices s0 A).map (fun w => tiltedMu F P n g.val w.1)).prod
      else 0)) =
      ((fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card : ℝ) *
        (((t0 - deleteMemoryIndices s0 A).map (fun w => tiltedMu F P n g.val w.1)).prod) := by
    have h1 : (∑ p : Fin b.val → P.Prime g.val,
        (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
          ((t0 - deleteMemoryIndices s0 A).map (fun w => tiltedMu F P n g.val w.1)).prod
        else 0)) =
        ∑ p ∈ fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val,
          ((t0 - deleteMemoryIndices s0 A).map (fun w => tiltedMu F P n g.val w.1)).prod :=
      (Finset.sum_filter _ _).symm
    rw [h1, Finset.sum_const, nsmul_eq_mul]
  calc (∑ p : Fin b.val → P.Prime g.val,
        if singleValid (P := P) (g := g) s0 t0 A b p then
          |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
        else 0)
      = ((eta F n i / rho) ^ A.card *
          (visitQ F.q n i / rho ^ (2 : ℕ)) ^
            ((zeroMemoryIndices s0).card - A.card) *
          (((b.val.factorial : ℝ)⁻¹) *
            (eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val)) *
        (∑ p : Fin b.val → P.Prime g.val,
          (if zeroBirthBatch (P := P) (g := g.val) p = (t0 - deleteMemoryIndices s0 A) then
            ∏ h : Fin b.val, tiltedMu F P n g.val (p h)
          else 0)) := by
        rw [Finset.sum_congr rfl (fun p _ => hterm p)]
        rw [Finset.mul_sum]
    _ = (((eta F n i / rho) ^ A.card *
          (visitQ F.q n i / rho ^ (2 : ℕ)) ^
            ((zeroMemoryIndices s0).card - A.card)) *
        ((((b.val.factorial : ℝ)⁻¹)) *
          ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val)) *
        ((((fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card : ℝ)) *
          (((t0 - deleteMemoryIndices s0 A).map
            (fun w => tiltedMu F P n g.val w.1)).prod))) := by
        rw [hsum_congr, hsum]
        ring

/-- Factorial product for birth multiset is positive. -/
lemma birthDenom_pos (m : P.Memory g.val) :
    0 < ∏ v : P.Particle g.val, ((m.count v).factorial : ℝ) :=
  Finset.prod_pos fun v _ => Nat.cast_pos.mpr (Nat.factorial_pos _)

lemma birthDenom_ne_zero (m : P.Memory g.val) :
    (∏ v : P.Particle g.val, ((m.count v).factorial : ℝ)) ≠ 0 :=
  ne_of_gt (birthDenom_pos m)

/-- BirthValid first component is card equality. -/
lemma birthValid_card {m : P.Memory g.val} {b : ℕ}
    (h : birthValid (P := P) (g := g) m b) : m.card = b := h.1

/-- Multinomial divisibility for a valid birth multiset. -/
lemma birth_dvd (m : P.Memory g.val) (b : ℕ)
    (hvalid : birthValid (P := P) (g := g) m b) :
    (∏ v : P.Particle g.val, (m.count v).factorial) ∣ b.factorial := by
  have hsum : ∑ v ∈ (Finset.univ : Finset (P.Particle g.val)), m.count v = b := by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact hvalid.1
  have h1 := Nat.prod_factorial_dvd_factorial_sum (Finset.univ : Finset (P.Particle g.val))
    (fun v => m.count v)
  rwa [hsum] at h1

/-- Real form of the birth fiber cancellation. -/
lemma birth_fiber_real (m : P.Memory g.val) (b : ℕ)
    (hvalid : birthValid (P := P) (g := g) m b) :
    (((b.factorial : ℝ))⁻¹) * (((fiberP (P := P) (g := g) m b).card : ℝ)) =
      (((∏ v : P.Particle g.val, ((m.count v).factorial : ℝ)))⁻¹) := by
  have hcard_eq : (fiberP (P := P) (g := g) m b).card =
      (if birthValid (P := P) (g := g) m b then
        b.factorial / ∏ v : P.Particle g.val, (m.count v).factorial
      else 0) := fiberP_card (P := P) (g := g) (b := b) m
  rw [if_pos hvalid] at hcard_eq
  have hdvd := birth_dvd m b hvalid
  have hDpos : 0 < (∏ v : P.Particle g.val, (m.count v).factorial : ℕ) :=
    Finset.prod_pos fun v _ => Nat.factorial_pos _
  have hDne : ((∏ v : P.Particle g.val, ((m.count v).factorial : ℝ))) ≠ 0 :=
    birthDenom_ne_zero m
  have hbpos : (0 : ℝ) < (b.factorial : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos b)
  have hbne : (b.factorial : ℝ) ≠ 0 := ne_of_gt hbpos
  have hcast : ((((b.factorial / ∏ v : P.Particle g.val, (m.count v).factorial) : ℕ) : ℝ)) =
      (b.factorial : ℝ) / (((∏ v : P.Particle g.val, (m.count v).factorial) : ℕ) : ℝ) :=
    Nat.cast_div hdvd (by exact_mod_cast ne_of_gt hDpos)
  have hprod : ((((∏ v : P.Particle g.val, (m.count v).factorial) : ℕ) : ℝ)) =
      (∏ v : P.Particle g.val, ((m.count v).factorial : ℝ)) := by
    push_cast
    ring
  rw [hcard_eq, hcast, hprod]
  field_simp

/-- Card of birth difference is bounded by target. -/
lemma birthDiff_card_le (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (hle_t : deleteMemoryIndices s0 A ≤ t0) :
    (t0 - deleteMemoryIndices s0 A).card ≤ t0.card := by
  have hle : (t0 - deleteMemoryIndices s0 A) ≤ t0 :=
    Multiset.sub_le_self t0 (deleteMemoryIndices s0 A)
  exact Multiset.card_le_card hle

/-- Deletion card determines removed card. -/
lemma delete_card_eq (s : P.Memory g.val) (A : Finset (Fin s.card)) :
    (deleteMemoryIndices s A).card = s.card - A.card := by
  rw [delete_card s A]
  have huniv : (Finset.univ : Finset (Fin s.card)).card = s.card := by
    rw [Finset.card_univ, Fintype.card_fin]
  have h1 : (A ∩ (Finset.univ : Finset (Fin s.card))).card = A.card := by
    rw [Finset.inter_univ]
  have hsdiff : ((Finset.univ : Finset (Fin s.card)) \ A).card =
      (Finset.univ : Finset (Fin s.card)).card - (A ∩ (Finset.univ : Finset (Fin s.card))).card :=
    Finset.card_sdiff
  rw [hsdiff, h1, huniv]

/-- Removed card from survivor card. -/
lemma removed_card_eq (s : P.Memory g.val) (A : Finset (Fin s.card)) :
    A.card = s.card - (deleteMemoryIndices s A).card := by
  have hdel := delete_card_eq s A
  have hAle : A.card ≤ s.card := by
    have huniv : (Finset.univ : Finset (Fin s.card)).card = s.card := by
      rw [Finset.card_univ, Fintype.card_fin]
    have hle := Finset.card_le_card (Finset.subset_univ A)
    rwa [huniv] at hle
  omega

/-- Per-survivor term for the single-group kernel. -/
def perU_term (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 u : P.Memory g.val) : ℝ :=
  if hle_t : u ≤ t0 then
    if hvalid0 : birthValid (P := P) (g := g) (t0 - u) (t0 - u).card then
      ((eta F n i / rho) ^ (s0.card - u.card) *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices s0).card - (s0.card - u.card))) *
      (((eta F n i * P.V g.val / rho) ^ (t0 - u).card *
        d ^ (t0 - u).card) *
        ((((t0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod) *
          (((∏ v : P.Particle g.val,
            (((t0 - u).count v).factorial : ℝ)))⁻¹)))
    else 0
  else 0

/-- Vanishing of birth sum when survivor not below target. -/
lemma sum_p_eq_zero_of_not_le (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (b : Fin (t0.card + 1))
    (hA_sub : A ⊆ zeroMemoryIndices s0)
    (hle_t : ¬ deleteMemoryIndices s0 A ≤ t0) :
    (∑ p : Fin b.val → P.Prime g.val,
      if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  intro hvalid
  have h2 : deleteMemoryIndices s0 A + zeroBirthBatch (P := P) (g := g.val) p = t0 :=
    hvalid.2
  exact hle_t (by rw [← h2]; exact Multiset.le_add_right _ _)

/-- Vanishing when deletion not zero-contained. -/
lemma sum_p_eq_zero_of_not_sub (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (b : Fin (t0.card + 1))
    (hA_sub : ¬ A ⊆ zeroMemoryIndices s0) :
    (∑ p : Fin b.val → P.Prime g.val,
      if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  intro hvalid
  exact hA_sub hvalid.1

/-- Sum over birth sizes for fixed deletion, valid birth case. -/
lemma sum_b_valid (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (hA_sub : A ⊆ zeroMemoryIndices s0)
    (hrho : 0 < rho) (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val)
    (hle_t : deleteMemoryIndices s0 A ≤ t0)
    (hvalid0 : birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A)
      (t0 - deleteMemoryIndices s0 A).card) :
    (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
      if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) =
    ((eta F n i / rho) ^ A.card *
      (visitQ F.q n i / rho ^ (2 : ℕ)) ^
        ((zeroMemoryIndices s0).card - A.card)) *
    (((eta F n i * P.V g.val / rho) ^ (t0 - deleteMemoryIndices s0 A).card *
      d ^ (t0 - deleteMemoryIndices s0 A).card) *
      (((t0 - deleteMemoryIndices s0 A).map
        (fun w => tiltedMu F P n g.val w.1)).prod *
        (((∏ v : P.Particle g.val,
          (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹))) := by
  have hmcard_le : (t0 - deleteMemoryIndices s0 A).card ≤ t0.card :=
    birthDiff_card_le s0 t0 A hle_t
  let b0 : Fin (t0.card + 1) :=
    ⟨(t0 - deleteMemoryIndices s0 A).card, Nat.lt_succ_of_le hmcard_le⟩
  have hb0_val : b0.val = (t0 - deleteMemoryIndices s0 A).card := rfl
  have hS_b : ∀ b : Fin (t0.card + 1),
      (∑ p : Fin b.val → P.Prime g.val,
        if singleValid (P := P) (g := g) s0 t0 A b p then
          |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
        else 0) =
      ((eta F n i / rho) ^ A.card *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices s0).card - A.card)) *
      ((((b.val.factorial : ℝ)⁻¹) *
        ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val)) *
        ((((fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card : ℝ)) *
          (((t0 - deleteMemoryIndices s0 A).map
            (fun w => tiltedMu F P n g.val w.1)).prod))) := by
    intro b
    have h := sum_p_eq F n rho d i g s0 t0 A b hA_sub hrho hV hbase hle_t
    rw [h]
    ring
  have hT_b : ∀ b : Fin (t0.card + 1),
      ((((b.val.factorial : ℝ)⁻¹) *
        ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val)) *
        ((((fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card : ℝ)) *
          (((t0 - deleteMemoryIndices s0 A).map
            (fun w => tiltedMu F P n g.val w.1)).prod))) =
      ((((t0 - deleteMemoryIndices s0 A).map
        (fun w => tiltedMu F P n g.val w.1)).prod)) *
      (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
        ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val) *
          (((∏ v : P.Particle g.val,
            (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)
      else 0) := by
    intro b
    by_cases hvalid : birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val
    · have hfib := birth_fiber_real (P := P) (g := g)
        (t0 - deleteMemoryIndices s0 A) b.val hvalid
      simp only [if_pos hvalid]
      calc ((((b.val.factorial : ℝ)⁻¹) *
            ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val)) *
            ((((fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card : ℝ)) *
              (((t0 - deleteMemoryIndices s0 A).map
                (fun w => tiltedMu F P n g.val w.1)).prod)))
          = (((t0 - deleteMemoryIndices s0 A).map
              (fun w => tiltedMu F P n g.val w.1)).prod) *
            ((((b.val.factorial : ℝ)⁻¹) *
              (((fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card : ℝ))) *
              (((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val))) := by
              ring
        _ = (((t0 - deleteMemoryIndices s0 A).map
              (fun w => tiltedMu F P n g.val w.1)).prod) *
            (((((∏ v : P.Particle g.val,
              (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)) *
              (((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val))) := by
              rw [hfib]
        _ = _ := by ring
    · have hcard0 : (fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card = 0 := by
        have hcard_eq : (fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card =
            (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
              b.val.factorial / ∏ v : P.Particle g.val,
                ((t0 - deleteMemoryIndices s0 A).count v).factorial
            else 0) := fiberP_card (P := P) (g := g) (b := b.val) _
        rw [if_neg hvalid] at hcard_eq
        exact hcard_eq
      simp only [if_neg hvalid, hcard0, Nat.cast_zero, mul_zero, zero_mul]
  have hS_eq : ∀ b : Fin (t0.card + 1),
      (∑ p : Fin b.val → P.Prime g.val,
        if singleValid (P := P) (g := g) s0 t0 A b p then
          |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
        else 0) =
      (((eta F n i / rho) ^ A.card *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices s0).card - A.card)) *
        (((t0 - deleteMemoryIndices s0 A).map
          (fun w => tiltedMu F P n g.val w.1)).prod)) *
      (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
        ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val) *
          (((∏ v : P.Particle g.val,
            (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)
      else 0) := by
    intro b
    rw [hS_b b, hT_b b]
    ring
  have hsum_T : (∑ b : Fin (t0.card + 1),
      (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
        ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val) *
          (((∏ v : P.Particle g.val,
            (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)
      else 0)) =
      ((eta F n i * P.V g.val / rho) ^ (t0 - deleteMemoryIndices s0 A).card *
        d ^ (t0 - deleteMemoryIndices s0 A).card) *
        (((∏ v : P.Particle g.val,
          (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹) := by
    have hb0_mem : b0 ∈ (Finset.univ : Finset (Fin (t0.card + 1))) :=
      Finset.mem_univ b0
    have hvalid_b0 : birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b0.val := by
      rw [hb0_val]
      exact hvalid0
    have hsingle : ∀ b : Fin (t0.card + 1), b ≠ b0 →
        (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
          ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val) *
            (((∏ v : P.Particle g.val,
              (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)
        else 0) = 0 := by
      intro b hb
      have hne_val : b.val ≠ (t0 - deleteMemoryIndices s0 A).card := by
        intro heq
        apply hb
        apply Fin.ext
        rw [heq, hb0_val]
      have hnvalid : ¬ birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val := by
        intro hv
        exact hne_val hv.1.symm
      rw [if_neg hnvalid]
    have hsum_eq := Finset.sum_eq_single b0 (fun b _ hb => hsingle b hb)
      (fun hcon => absurd hb0_mem hcon)
    have hval_b0 : (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b0.val then
        ((eta F n i * P.V g.val / rho) ^ b0.val * d ^ b0.val) *
          (((∏ v : P.Particle g.val,
            (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)
      else 0) =
        ((eta F n i * P.V g.val / rho) ^ (t0 - deleteMemoryIndices s0 A).card *
          d ^ (t0 - deleteMemoryIndices s0 A).card) *
          (((∏ v : P.Particle g.val,
            (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹) := by
      rw [if_pos hvalid_b0, hb0_val]
    rw [hsum_eq]
    exact hval_b0
  calc (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
        if singleValid (P := P) (g := g) s0 t0 A b p then
          |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
        else 0)
      = (∑ b : Fin (t0.card + 1),
        ((((eta F n i / rho) ^ A.card *
          (visitQ F.q n i / rho ^ (2 : ℕ)) ^
            ((zeroMemoryIndices s0).card - A.card)) *
          (((t0 - deleteMemoryIndices s0 A).map
            (fun w => tiltedMu F P n g.val w.1)).prod)) *
        (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
          ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val) *
            (((∏ v : P.Particle g.val,
              (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)
        else 0))) := by
        apply Finset.sum_congr rfl
        intro b _
        exact hS_eq b
    _ = (((eta F n i / rho) ^ A.card *
          (visitQ F.q n i / rho ^ (2 : ℕ)) ^
            ((zeroMemoryIndices s0).card - A.card)) *
          (((t0 - deleteMemoryIndices s0 A).map
            (fun w => tiltedMu F P n g.val w.1)).prod)) *
        (∑ b : Fin (t0.card + 1),
          (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
            ((eta F n i * P.V g.val / rho) ^ b.val * d ^ b.val) *
              (((∏ v : P.Particle g.val,
                (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹)
          else 0)) := by
        rw [Finset.mul_sum]
    _ = _ := by
        rw [hsum_T]
        ring

/-- Sum over birth sizes vanishes for invalid birth difference. -/
lemma sum_b_invalid (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (hA_sub : A ⊆ zeroMemoryIndices s0)
    (hrho : 0 < rho) (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val)
    (hle_t : deleteMemoryIndices s0 A ≤ t0)
    (hinvalid : ¬ birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A)
      (t0 - deleteMemoryIndices s0 A).card) :
    (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
      if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hS := sum_p_eq F n rho d i g s0 t0 A b hA_sub hrho hV hbase hle_t
  have hnvalid_b : ¬ birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val := by
    intro hv
    apply hinvalid
    exact ⟨rfl, hv.2⟩
  have hcard0 : (fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card = 0 := by
    have hcard_eq : (fiberP (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val).card =
        (if birthValid (P := P) (g := g) (t0 - deleteMemoryIndices s0 A) b.val then
          b.val.factorial / ∏ v : P.Particle g.val,
            ((t0 - deleteMemoryIndices s0 A).count v).factorial
        else 0) := fiberP_card (P := P) (g := g) (b := b.val) _
    rw [if_neg hnvalid_b] at hcard_eq
    exact hcard_eq
  rw [hS]
  simp only [hcard0, Nat.cast_zero, mul_zero, zero_mul]

/-- Fixed-deletion sum equals per-survivor term. -/
lemma sum_A_eq_perU (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (hA_sub : A ⊆ zeroMemoryIndices s0)
    (hrho : 0 < rho) (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val) :
    (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
      if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) =
    perU_term F n rho d i g s0 t0 (deleteMemoryIndices s0 A) := by
  by_cases hle_t : deleteMemoryIndices s0 A ≤ t0
  · by_cases hvalid0 : birthValid (P := P) (g := g)
        (t0 - deleteMemoryIndices s0 A) (t0 - deleteMemoryIndices s0 A).card
    · have hsum := sum_b_valid F n rho d i g s0 t0 A hA_sub hrho hV hbase hle_t hvalid0
      have hcardA : A.card = s0.card - (deleteMemoryIndices s0 A).card :=
        removed_card_eq s0 A
      have hperU : perU_term F n rho d i g s0 t0 (deleteMemoryIndices s0 A) =
          ((eta F n i / rho) ^ A.card *
            (visitQ F.q n i / rho ^ (2 : ℕ)) ^
              ((zeroMemoryIndices s0).card - A.card)) *
          (((eta F n i * P.V g.val / rho) ^ (t0 - deleteMemoryIndices s0 A).card *
            d ^ (t0 - deleteMemoryIndices s0 A).card) *
            ((((t0 - deleteMemoryIndices s0 A).map
              (fun w => tiltedMu F P n g.val w.1)).prod) *
              (((∏ v : P.Particle g.val,
                (((t0 - deleteMemoryIndices s0 A).count v).factorial : ℝ)))⁻¹))) := by
        unfold perU_term
        rw [dif_pos hle_t, dif_pos hvalid0, hcardA]
      rw [hperU]
      exact hsum
    · have hsum0 := sum_b_invalid F n rho d i g s0 t0 A hA_sub hrho hV hbase hle_t hvalid0
      have hperU0 : perU_term F n rho d i g s0 t0 (deleteMemoryIndices s0 A) = 0 := by
        unfold perU_term
        rw [dif_pos hle_t, dif_neg hvalid0]
      rw [hperU0]
      exact hsum0
  · have hsum0 : (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
        if singleValid (P := P) (g := g) s0 t0 A b p then
          |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
        else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      exact sum_p_eq_zero_of_not_le F n rho d i g s0 t0 A b hA_sub hle_t
    have hperU0 : perU_term F n rho d i g s0 t0 (deleteMemoryIndices s0 A) = 0 := by
      unfold perU_term
      rw [dif_neg hle_t]
    rw [hperU0]
    exact hsum0

/-- Sum over deletions vanishes outside zero-contained sets. -/
lemma sum_A_zero_of_not_sub (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card))
    (hA_sub : ¬ A ⊆ zeroMemoryIndices s0) :
    (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
      if singleValid (P := P) (g := g) s0 t0 A b p then
        |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
      else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  exact sum_p_eq_zero_of_not_sub F n rho d i g s0 t0 A b hA_sub

/-- Zero-index count equals sum over zero particle counts. -/
lemma zeroCard_eq_sum (s : P.Memory g.val) :
    (zeroMemoryIndices s).card =
      ∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0),
        s.count v := by
  have hzero_eq : zeroMemoryIndices s =
      (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0)).biUnion
        (fun v => Sv (P := P) (g := g) s v) := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      have hk_mem : k ∈ Sv (P := P) (g := g) s (memoryEntry s k) :=
        mem_Sv_self s k
      have hz : (memoryEntry s k).2 = 0 := by
        unfold zeroMemoryIndices at hk
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact ⟨memoryEntry s k, hz, hk_mem⟩
    · rintro ⟨v, hv_zero, hkv⟩
      have hv_eq : memoryEntry s k = v := by
        unfold Sv at hkv
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hkv
      unfold zeroMemoryIndices
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hv_eq]
      exact hv_zero
  rw [hzero_eq]
  rw [Finset.card_biUnion (by
    intro v hv w hw hvw
    exact Sv_disjoint s v w hvw)]
  apply Finset.sum_congr rfl
  intro v _
  rw [Sv_card s v]

/-- Nonzero total equals total minus zero count. -/
lemma card_sub_zero_eq_sum_nonzero (s : P.Memory g.val) :
    s.card - (zeroMemoryIndices s).card =
      ∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 ≠ 0),
        s.count v := by
  have hsum_all : ∑ v ∈ (Finset.univ : Finset (P.Particle g.val)), s.count v = s.card := by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
  have hpart : (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0)) ∪
      (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)) =
      (Finset.univ : Finset (P.Particle g.val)) :=
    Finset.filter_union_filter_not_eq _ _
  have hdisj : Disjoint
      (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0))
      (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)) :=
    Finset.disjoint_filter_filter_not _ _ _
  have hsum_split : (∑ v ∈ (Finset.univ : Finset (P.Particle g.val)), s.count v) =
      (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0), s.count v) +
      (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0), s.count v) := by
    have h1 : (∑ v ∈ (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0)) ∪
        (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)), s.count v) =
        (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0), s.count v) +
        (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0), s.count v) :=
      Finset.sum_union hdisj
    rw [hpart] at h1
    exact h1
  have hZs := zeroCard_eq_sum s
  have hne_eq : (Finset.univ.filter (fun v : P.Particle g.val => v.2 ≠ 0)) =
      (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)) := by
    apply Finset.filter_congr
    intro v _
    simp only [ne_eq]
  rw [hne_eq]
  omega

/-- Nonzero totals agree when memories agree on nonzero counts. -/
lemma nonzero_totals_eq (s0 t0 : P.Memory g.val)
    (hagree : ∀ v : P.Particle g.val, ¬ isZeroParticle v → s0.count v = t0.count v) :
    s0.card - (zeroMemoryIndices s0).card =
      t0.card - (zeroMemoryIndices t0).card := by
  have hs := card_sub_zero_eq_sum_nonzero (P := P) (g := g) s0
  have ht := card_sub_zero_eq_sum_nonzero (P := P) (g := g) t0
  rw [hs, ht]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have hnz : ¬ isZeroParticle (P := P) (g := g) v := by
    unfold isZeroParticle
    exact hv
  exact hagree v hnz

/-- Single kernel as image sum over survivors. -/
lemma singleKernel_eq_image_sum (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 : P.Memory g.val)
    (hrho : 0 < rho) (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val) :
    singleKernel F n rho d i g s0 t0 =
    ∑ u ∈ Finset.image (fun A : Finset (Fin s0.card) => deleteMemoryIndices s0 A)
      (Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices s0)),
      ((fiberA (P := P) (g := g) s0 u).card : ℝ) *
        perU_term F n rho d i g s0 t0 u := by
  have hs : (Finset.univ.filter (fun A : Finset (Fin s0.card) => A ⊆ zeroMemoryIndices s0))
      ⊆ (Finset.univ : Finset (Finset (Fin s0.card))) :=
    Finset.filter_subset _ _
  have hS_eq : ∀ A : Finset (Fin s0.card),
      (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
        if singleValid (P := P) (g := g) s0 t0 A b p then
          |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
        else 0) =
      (if A ⊆ zeroMemoryIndices s0 then
        perU_term F n rho d i g s0 t0 (deleteMemoryIndices s0 A)
      else 0) := by
    intro A
    by_cases hsub : A ⊆ zeroMemoryIndices s0
    · rw [if_pos hsub]
      exact sum_A_eq_perU F n rho d i g s0 t0 A hsub hrho hV hbase
    · rw [if_neg hsub]
      exact sum_A_zero_of_not_sub F n rho d i g s0 t0 A hsub
  have hker : singleKernel F n rho d i g s0 t0 =
      ∑ A : Finset (Fin s0.card),
        (∑ b : Fin (t0.card + 1), ∑ p : Fin b.val → P.Prime g.val,
          if singleValid (P := P) (g := g) s0 t0 A b p then
            |singleWeight F n rho i g s0 t0 A b p| * d ^ b.val
          else 0) := by
    unfold singleKernel
    rfl
  rw [hker]
  rw [← Finset.sum_subset hs (fun x _ hx => by
    have hns : ¬ x ⊆ zeroMemoryIndices s0 := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] using hx
    rw [hS_eq x, if_neg hns])]
  -- Now sum over s = univ.filter subset, grouped by delete
  have hmaps : ∀ A ∈ Finset.univ.filter (fun A : Finset (Fin s0.card) => A ⊆ zeroMemoryIndices s0),
      (fun A : Finset (Fin s0.card) => deleteMemoryIndices s0 A) A ∈
        Finset.image (fun A : Finset (Fin s0.card) => deleteMemoryIndices s0 A)
          (Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices s0)) := by
    intro A hA
    exact Finset.mem_image_of_mem _ hA
  have hfib := Finset.sum_fiberwise_of_maps_to' hmaps
    (fun u : P.Memory g.val => perU_term F n rho d i g s0 t0 u)
  -- hfib : ∑ j ∈ image, ∑ i ∈ s with delete i = j, perU j = ∑ i ∈ s, perU (delete i)
  have hsum_s : (∑ A ∈ Finset.univ.filter (fun A : Finset (Fin s0.card) => A ⊆ zeroMemoryIndices s0),
      perU_term F n rho d i g s0 t0 (deleteMemoryIndices s0 A)) =
      ∑ u ∈ Finset.image (fun A : Finset (Fin s0.card) => deleteMemoryIndices s0 A)
        (Finset.univ.filter (fun A => A ⊆ zeroMemoryIndices s0)),
        ((fiberA (P := P) (g := g) s0 u).card : ℝ) *
          perU_term F n rho d i g s0 t0 u := by
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro u _
    have hfilter_eq : (Finset.univ.filter (fun A : Finset (Fin s0.card) => A ⊆ zeroMemoryIndices s0)).filter
        (fun A => deleteMemoryIndices s0 A = u) =
        fiberA (P := P) (g := g) s0 u := by
      unfold fiberA
      rw [Finset.filter_filter]
    rw [hfilter_eq, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum_s]
  apply Finset.sum_congr rfl
  intro A hA
  have hsub : A ⊆ zeroMemoryIndices s0 := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hA
  rw [hS_eq A, if_pos hsub]

/-- Real form of deletion fiber. -/
lemma fiberA_real (s u : P.Memory g.val)
    (hvalid : nonzeroPreserved (P := P) (g := g) s u ∧ u ≤ s) :
    (((fiberA (P := P) (g := g) s u).card : ℝ)) =
      (∏ v : P.Particle g.val, ((s.count v).factorial : ℝ)) /
      (∏ v : P.Particle g.val,
        (((u.count v).factorial : ℝ) * (((s.count v - u.count v).factorial : ℝ)))) := by
  have hcard : (fiberA (P := P) (g := g) s u).card =
      ∏ v : P.Particle g.val, Nat.choose (s.count v) (u.count v) := by
    have h := fiberA_card (P := P) (g := g) s u
    rw [if_pos hvalid] at h
    exact h
  have hchoose : ∀ v : P.Particle g.val,
      (((Nat.choose (s.count v) (u.count v) : ℕ)) : ℝ) =
        ((s.count v).factorial : ℝ) /
        (((u.count v).factorial : ℝ) * (((s.count v - u.count v).factorial : ℝ))) := by
    intro v
    have hle : u.count v ≤ s.count v :=
      Multiset.count_le_of_le v hvalid.2
    have hmul := Nat.choose_mul_factorial_mul_factorial hle
    have hUpos : (0 : ℝ) < ((u.count v).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hDpos : (0 : ℝ) < (((s.count v - u.count v).factorial : ℝ)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hDne : (((u.count v).factorial : ℝ) * (((s.count v - u.count v).factorial : ℝ))) ≠ 0 :=
      ne_of_gt (mul_pos hUpos hDpos)
    have hcast : ((((Nat.choose (s.count v) (u.count v)) : ℕ)) : ℝ) *
        ((((u.count v).factorial : ℝ)) * (((s.count v - u.count v).factorial : ℝ))) =
        (((s.count v).factorial : ℝ)) := by
      have hnat : Nat.choose (s.count v) (u.count v) * ((u.count v).factorial * (s.count v - u.count v).factorial) =
          (s.count v).factorial := by
        have h1 := hmul
        rw [mul_assoc] at h1
        exact h1
      exact_mod_cast hnat
    field_simp
    rw [← hcast]
    ring
  have hcast_prod : ((((∏ v : P.Particle g.val, Nat.choose (s.count v) (u.count v)) : ℕ)) : ℝ) =
      ∏ v : P.Particle g.val, ((((Nat.choose (s.count v) (u.count v) : ℕ))) : ℝ) := by
    push_cast
    ring
  rw [hcard, hcast_prod]
  rw [Finset.prod_congr rfl (fun v _ => hchoose v)]
  rw [Finset.prod_div_distrib]

/-- Damping exponents agree on valid survivors. -/
lemma Q_exp_eq (s0 t0 u : P.Memory g.val)
    (hagree_st : ∀ v : P.Particle g.val, ¬ isZeroParticle v → s0.count v = t0.count v)
    (hagree_u : ∀ v : P.Particle g.val, ¬ isZeroParticle v → u.count v = s0.count v)
    (hu_s : u ≤ s0) (hu_t : u ≤ t0) :
    (zeroMemoryIndices s0).card - (s0.card - u.card) =
      (zeroMemoryIndices t0).card - (t0.card - u.card) := by
  have hZs_le : (zeroMemoryIndices s0).card ≤ s0.card := by
    have hsub : zeroMemoryIndices s0 ⊆ (Finset.univ : Finset (Fin s0.card)) :=
      Finset.filter_subset _ _
    have huniv : (Finset.univ : Finset (Fin s0.card)).card = s0.card := by
      rw [Finset.card_univ, Fintype.card_fin]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq huniv)
  have hZt_le : (zeroMemoryIndices t0).card ≤ t0.card := by
    have hsub : zeroMemoryIndices t0 ⊆ (Finset.univ : Finset (Fin t0.card)) :=
      Finset.filter_subset _ _
    have huniv : (Finset.univ : Finset (Fin t0.card)).card = t0.card := by
      rw [Finset.card_univ, Fintype.card_fin]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq huniv)
  have hu_s_card : u.card ≤ s0.card := Multiset.card_le_card hu_s
  have hu_t_card : u.card ≤ t0.card := Multiset.card_le_card hu_t
  have hN_eq : s0.card - (zeroMemoryIndices s0).card =
      t0.card - (zeroMemoryIndices t0).card :=
    nonzero_totals_eq s0 t0 hagree_st
  -- D = s0 - u and M = t0 - u cards are s-u and t-u
  have hD_card : (s0 - u).card = s0.card - u.card := by
    have hadd : u.card + (s0 - u).card = s0.card := by
      have h : u + (s0 - u) = s0 := by
        rw [add_comm]
        exact Multiset.add_sub_cancel hu_s
      have hc := congrArg Multiset.card h
      simpa only [Multiset.card_add] using hc
    omega
  have hM_card : (t0 - u).card = t0.card - u.card := by
    have hadd : u.card + (t0 - u).card = t0.card := by
      have h : u + (t0 - u) = t0 := by
        rw [add_comm]
        exact Multiset.add_sub_cancel hu_t
      have hc := congrArg Multiset.card h
      simpa only [Multiset.card_add] using hc
    omega
  -- D and M are zero-only from agreement
  have hD_zero : ∀ v : P.Particle g.val, v.2 ≠ 0 → (s0 - u).count v = 0 := by
    intro v hv
    have hnz : ¬ isZeroParticle (P := P) (g := g) v := by
      unfold isZeroParticle
      exact hv
    have hs_eq := hagree_st v hnz
    have hu_eq := hagree_u v hnz
    have hcount : (s0 - u).count v = s0.count v - u.count v :=
      Multiset.count_sub v s0 u
    rw [hcount, hu_eq, hs_eq]
    -- s0.count - s0.count = 0? Since hu_eq : u.count = s0.count, hs_eq : s0.count = t0.count? Actually hu_eq : u.count = s0.count, so s0.count - u.count = 0
    omega
  have hM_zero : ∀ v : P.Particle g.val, v.2 ≠ 0 → (t0 - u).count v = 0 := by
    intro v hv
    have hnz : ¬ isZeroParticle (P := P) (g := g) v := by
      unfold isZeroParticle
      exact hv
    have hs_eq := hagree_st v hnz
    have hu_eq := hagree_u v hnz
    -- u.count = s0.count, s0.count = t0.count, so u.count = t0.count
    have hu_t_eq : u.count v = t0.count v := hu_eq.trans hs_eq
    have hcount : (t0 - u).count v = t0.count v - u.count v :=
      Multiset.count_sub v t0 u
    rw [hcount, hu_t_eq]
    omega
  -- D.card ≤ Zs and M.card ≤ Zt via zero sums
  have hD_le : (s0 - u).card ≤ (zeroMemoryIndices s0).card := by
    have hD_eq : (s0 - u).card =
        ∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0),
          (s0 - u).count v := by
      have hsum_all : ∑ v ∈ (Finset.univ : Finset (P.Particle g.val)), (s0 - u).count v =
          (s0 - u).card := by
        rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      have hsplit : (∑ v ∈ (Finset.univ : Finset (P.Particle g.val)), (s0 - u).count v) =
          (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0), (s0 - u).count v) +
          (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0), (s0 - u).count v) := by
        have hpart : (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0)) ∪
            (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)) =
            (Finset.univ : Finset (P.Particle g.val)) :=
          Finset.filter_union_filter_not_eq _ _
        have hdisj : Disjoint
            (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0))
            (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)) :=
          Finset.disjoint_filter_filter_not _ _ _
        have h1 : (∑ v ∈ (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0)) ∪
            (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)), (s0 - u).count v) =
            (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0), (s0 - u).count v) +
            (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0), (s0 - u).count v) :=
          Finset.sum_union hdisj
        rw [hpart] at h1
        exact h1
      have hnonzero_zero : (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0),
          (s0 - u).count v) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hD_zero v hv
      rw [hsum_all] at hsplit
      omega
    have hZs_eq := zeroCard_eq_sum (P := P) (g := g) s0
    rw [hD_eq, hZs_eq]
    apply Finset.sum_le_sum
    intro v _
    exact Multiset.count_le_of_le v (Multiset.sub_le_self s0 u)
  have hM_le : (t0 - u).card ≤ (zeroMemoryIndices t0).card := by
    have hM_eq : (t0 - u).card =
        ∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0),
          (t0 - u).count v := by
      have hsum_all : ∑ v ∈ (Finset.univ : Finset (P.Particle g.val)), (t0 - u).count v =
          (t0 - u).card := by
        rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      have hsplit : (∑ v ∈ (Finset.univ : Finset (P.Particle g.val)), (t0 - u).count v) =
          (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0), (t0 - u).count v) +
          (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0), (t0 - u).count v) := by
        have hpart : (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0)) ∪
            (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)) =
            (Finset.univ : Finset (P.Particle g.val)) :=
          Finset.filter_union_filter_not_eq _ _
        have hdisj : Disjoint
            (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0))
            (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)) :=
          Finset.disjoint_filter_filter_not _ _ _
        have h1 : (∑ v ∈ (Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0)) ∪
            (Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0)), (t0 - u).count v) =
            (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => v.2 = 0), (t0 - u).count v) +
            (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0), (t0 - u).count v) :=
          Finset.sum_union hdisj
        rw [hpart] at h1
        exact h1
      have hnonzero_zero : (∑ v ∈ Finset.univ.filter (fun v : P.Particle g.val => ¬ v.2 = 0),
          (t0 - u).count v) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hv2 : v.2 ≠ 0 := hv
        exact hM_zero v hv2
      rw [hsum_all] at hsplit
      omega
    have hZt_eq := zeroCard_eq_sum (P := P) (g := g) t0
    rw [hM_eq, hZt_eq]
    apply Finset.sum_le_sum
    intro v _
    exact Multiset.count_le_of_le v (Multiset.sub_le_self t0 u)
  -- Integer arithmetic: Zs-(s-u) = Zt-(t-u) from s-Zs = t-Zt
  have hN : s0.card - (zeroMemoryIndices s0).card =
      t0.card - (zeroMemoryIndices t0).card :=
    nonzero_totals_eq s0 t0 hagree_st
  have hDs : (s0 - u).card = s0.card - u.card := hD_card
  have hMt : (t0 - u).card = t0.card - u.card := hM_card
  -- Convert to integers
  have hint : ((zeroMemoryIndices s0).card : ℤ) - ((s0.card - u.card : ℕ) : ℤ) =
      ((zeroMemoryIndices t0).card : ℤ) - ((t0.card - u.card : ℕ) : ℤ) := by
    have h1 : (((s0.card - (zeroMemoryIndices s0).card : ℕ)) : ℤ) =
        (((t0.card - (zeroMemoryIndices t0).card : ℕ)) : ℤ) := by
      rw [hN]
    have hs_sub : (((s0.card - (zeroMemoryIndices s0).card : ℕ)) : ℤ) =
        (s0.card : ℤ) - ((zeroMemoryIndices s0).card : ℤ) := by
      apply Nat.cast_sub hZs_le
    have ht_sub : (((t0.card - (zeroMemoryIndices t0).card : ℕ)) : ℤ) =
        (t0.card : ℤ) - ((zeroMemoryIndices t0).card : ℤ) := by
      apply Nat.cast_sub hZt_le
    have hs_u : (((s0.card - u.card : ℕ)) : ℤ) = (s0.card : ℤ) - (u.card : ℤ) := by
      apply Nat.cast_sub hu_s_card
    have ht_u : (((t0.card - u.card : ℕ)) : ℤ) = (t0.card : ℤ) - (u.card : ℤ) := by
      apply Nat.cast_sub hu_t_card
    rw [hs_sub, ht_sub] at h1
    -- h1 : s - Zs = t - Zt as integers, want Zs-(s-u) = Zt-(t-u)
    have hDs_int : ((((s0 - u).card : ℕ)) : ℤ) = ((s0.card - u.card : ℕ) : ℤ) := by
      rw [hDs]
    have hMt_int : ((((t0 - u).card : ℕ)) : ℤ) = ((t0.card - u.card : ℕ) : ℤ) := by
      rw [hMt]
    -- Zs-(s-u) = Zs-s+u, Zt-(t-u) = Zt-t+u, and Zs-s = Zt-t from h1
    have hZs_s : ((zeroMemoryIndices s0).card : ℤ) - (s0.card : ℤ) =
        ((zeroMemoryIndices t0).card : ℤ) - (t0.card : ℤ) := by
      linarith
    calc ((zeroMemoryIndices s0).card : ℤ) - ((s0.card - u.card : ℕ) : ℤ)
          = (((zeroMemoryIndices s0).card : ℤ) - (s0.card : ℤ)) + (u.card : ℤ) := by
            rw [hs_u]
            ring
        _ = (((zeroMemoryIndices t0).card : ℤ) - (t0.card : ℤ)) + (u.card : ℤ) := by
            rw [hZs_s]
        _ = ((zeroMemoryIndices t0).card : ℤ) - ((t0.card - u.card : ℕ) : ℤ) := by
            rw [ht_u]
            ring
  -- Nat equality from integer equality, using true differences (D≤Zs, M≤Zt)
  have hZs_D : (s0.card - u.card) ≤ (zeroMemoryIndices s0).card := by
    rw [← hD_card]
    exact hD_le
  have hZt_M : (t0.card - u.card) ≤ (zeroMemoryIndices t0).card := by
    rw [← hM_card]
    exact hM_le
  have hcast_s : ((((zeroMemoryIndices s0).card - (s0.card - u.card) : ℕ)) : ℤ) =
      ((zeroMemoryIndices s0).card : ℤ) - ((s0.card - u.card : ℕ) : ℤ) := by
    apply Nat.cast_sub hZs_D
  have hcast_t : ((((zeroMemoryIndices t0).card - (t0.card - u.card) : ℕ)) : ℤ) =
      ((zeroMemoryIndices t0).card : ℤ) - ((t0.card - u.card : ℕ) : ℤ) := by
    apply Nat.cast_sub hZt_M
  have h_eq_int : ((((zeroMemoryIndices s0).card - (s0.card - u.card) : ℕ)) : ℤ) =
      ((((zeroMemoryIndices t0).card - (t0.card - u.card) : ℕ)) : ℤ) := by
    rw [hcast_s, hcast_t, hint]
  exact Nat.cast_injective h_eq_int

/-- Numerator products agree on valid survivors. -/
lemma num_eq (F : FixedData) (n : ℕ) (g : P.BigGroup)
    (s0 t0 u : P.Memory g.val) (hu_s : u ≤ s0) (hu_t : u ≤ t0) :
    ((s0.map (fun w => tiltedMu F P n g.val w.1)).prod *
      (((t0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod)) =
    ((t0.map (fun w => tiltedMu F P n g.val w.1)).prod *
      (((s0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod)) := by
  have hmult : s0 + (t0 - u) = t0 + (s0 - u) := by
    apply Multiset.ext.mpr
    intro v
    have hu_s_le : u.count v ≤ s0.count v :=
      Multiset.count_le_of_le v hu_s
    have hu_t_le : u.count v ≤ t0.count v :=
      Multiset.count_le_of_le v hu_t
    simp only [Multiset.count_add, Multiset.count_sub]
    omega
  have hmap : ((s0 + (t0 - u)).map (fun w => tiltedMu F P n g.val w.1)).prod =
      ((t0 + (s0 - u)).map (fun w => tiltedMu F P n g.val w.1)).prod := by
    rw [hmult]
  rw [Multiset.map_add, Multiset.map_add, Multiset.prod_add, Multiset.prod_add] at hmap
  exact hmap

/-- Group mass denominator over univ equals over toFinset. -/
lemma mass_denom_eq_univ (F : FixedData) (n : ℕ) (g : P.Group) (z : P.Memory g) :
    (∏ u ∈ z.toFinset, (((z.count u).factorial : ℝ))) =
      (∏ v : P.Particle g, (((z.count v).factorial : ℝ))) := by
  have hsub : z.toFinset ⊆ (Finset.univ : Finset (P.Particle g)) :=
    Finset.subset_univ _
  have hzero : ∀ v ∈ (Finset.univ : Finset (P.Particle g)), v ∉ z.toFinset →
      ((((z.count v).factorial : ℕ)) : ℝ) = 1 := by
    intro v _ hv
    have hmem : v ∉ z := by
      intro hm
      exact hv (Multiset.mem_toFinset.mpr hm)
    have hcount : z.count v = 0 :=
      Multiset.count_eq_zero_of_notMem hmem
    rw [hcount]
    simp
  have h := Finset.prod_subset hsub (fun v _ hv => hzero v (Finset.mem_univ v) hv)
  -- h : ∏ u ∈ toFinset, ... = ∏ v ∈ univ, ...? Actually prod_subset gives ∏ s = ∏ t when ...? Let's check direction: prod_subset (h : s ⊆ t) (hf : ∀ x ∈ t, x ∉ s → f x = 1) : ∏ x ∈ s, f x = ∏ x ∈ t, f x? Or opposite? Need to check: Finset.prod_subset : s ⊆ t → (∀ x ∈ t, x ∉ s → f x = 1) → ∏ x ∈ s, f x = ∏ x ∈ t, f x? Actually prod over smaller equals prod over larger when extra factors 1. Good. So h gives ∏ toFinset = ∏ univ. Good, which is exactly goal (LHS toFinset, RHS univ). Good.
  exact h

/-- Denominator products agree (up to commutativity). -/
lemma denom_eq (s0 t0 u : P.Memory g.val) :
    (∏ v : P.Particle g.val,
        (((u.count v).factorial : ℝ) * (((s0.count v - u.count v).factorial : ℝ)))) *
      (∏ v : P.Particle g.val, (((t0.count v - u.count v).factorial : ℝ))) =
      (∏ v : P.Particle g.val,
        (((u.count v).factorial : ℝ) * (((t0.count v - u.count v).factorial : ℝ)))) *
      (∏ v : P.Particle g.val, (((s0.count v - u.count v).factorial : ℝ))) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  ring

/-- Symmetric factor (skeleton). -/
lemma Sym_eq_skeleton (F : FixedData) (n : ℕ) (g : P.BigGroup)
    (s0 t0 u : P.Memory g.val) (hu_s : u ≤ s0) (hu_t : u ≤ t0) :
    ((s0.map (fun w => tiltedMu F P n g.val w.1)).prod /
      (∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) *
      (((∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) /
        (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((s0.count v - u.count v).factorial : ℝ)))))) *
      ((((t0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod) /
        (∏ v : P.Particle g.val, (((t0 - u).count v).factorial : ℝ)))) =
    ((t0.map (fun w => tiltedMu F P n g.val w.1)).prod /
      (∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) *
      (((∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) /
        (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((t0.count v - u.count v).factorial : ℝ)))))) *
      ((((s0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod) /
        (∏ v : P.Particle g.val, (((s0 - u).count v).factorial : ℝ)))) := by
  have hnum := num_eq F n g s0 t0 u hu_s hu_t
  have hMs_ne : (∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hMt_ne : (∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hU_D_ne : (∏ v : P.Particle g.val,
      (((u.count v).factorial : ℝ) * (((s0.count v - u.count v).factorial : ℝ)))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hU_M_ne : (∏ v : P.Particle g.val,
      (((u.count v).factorial : ℝ) * (((t0.count v - u.count v).factorial : ℝ)))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hD_m0_ne : (∏ v : P.Particle g.val, (((t0 - u).count v).factorial : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hD_D_ne : (∏ v : P.Particle g.val, (((s0 - u).count v).factorial : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hcount_D : ∀ v : P.Particle g.val, (s0 - u).count v = s0.count v - u.count v :=
    fun v => Multiset.count_sub v s0 u
  have hcount_M : ∀ v : P.Particle g.val, (t0 - u).count v = t0.count v - u.count v :=
    fun v => Multiset.count_sub v t0 u
  have hD_S_eq : (∏ v : P.Particle g.val, (((s0 - u).count v).factorial : ℝ)) =
      ∏ v : P.Particle g.val, (((s0.count v - u.count v).factorial : ℝ)) :=
    Finset.prod_congr rfl (fun v _ => by rw [hcount_D v])
  have hD_T_eq : (∏ v : P.Particle g.val, (((t0 - u).count v).factorial : ℝ)) =
      ∏ v : P.Particle g.val, (((t0.count v - u.count v).factorial : ℝ)) :=
    Finset.prod_congr rfl (fun v _ => by rw [hcount_M v])
  rw [hD_S_eq, hD_T_eq]
  have e1 : ((s0.map (fun w => tiltedMu F P n g.val w.1)).prod /
      (∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) *
      (((∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) /
        (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((s0.count v - u.count v).factorial : ℝ))))))) =
      (s0.map (fun w => tiltedMu F P n g.val w.1)).prod /
        (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((s0.count v - u.count v).factorial : ℝ)))) := by
    field_simp
  have e2 : ((t0.map (fun w => tiltedMu F P n g.val w.1)).prod /
      (∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) *
      (((∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) /
        (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((t0.count v - u.count v).factorial : ℝ))))))) =
      (t0.map (fun w => tiltedMu F P n g.val w.1)).prod /
        (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((t0.count v - u.count v).factorial : ℝ)))) := by
    field_simp
  rw [e1, e2, div_mul_div_comm, div_mul_div_comm]
  have hDen : (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((s0.count v - u.count v).factorial : ℝ)))) *
        (∏ v : P.Particle g.val, (((t0.count v - u.count v).factorial : ℝ))) =
      (∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((t0.count v - u.count v).factorial : ℝ)))) *
        (∏ v : P.Particle g.val, (((s0.count v - u.count v).factorial : ℝ))) :=
    denom_eq s0 t0 u
  -- Rewrite to common denominator form
  have hDen' : ((∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((s0.count v - u.count v).factorial : ℝ)))) *
        (∏ v : P.Particle g.val, (((t0.count v - u.count v).factorial : ℝ)))) =
      ((∏ v : P.Particle g.val,
          (((u.count v).factorial : ℝ) * (((t0.count v - u.count v).factorial : ℝ)))) *
        (∏ v : P.Particle g.val, (((s0.count v - u.count v).factorial : ℝ)))) := hDen
  rw [hDen', hnum]
/-- Coefficient ratio (skeleton). -/
lemma coeff_eq_skeleton (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 u : P.Memory g.val)
    (hrho : 0 < rho) (hV : 0 < P.V g.val) (hd : 0 < d)
    (hu_s : u ≤ s0) (hu_t : u ≤ t0)
    (hQeq : (zeroMemoryIndices s0).card - (s0.card - u.card) =
      (zeroMemoryIndices t0).card - (t0.card - u.card)) :
    ((eta F n i / rho) ^ (s0.card - u.card) *
      (visitQ F.q n i / rho ^ (2 : ℕ)) ^
        ((zeroMemoryIndices s0).card - (s0.card - u.card))) *
      (((eta F n i * P.V g.val / rho) ^ (t0 - u).card *
        d ^ (t0 - u).card)) =
      ((d * P.V g.val) ^ t0.card / ((d * P.V g.val) ^ s0.card)) *
      (((eta F n i / rho) ^ (t0.card - u.card) *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices t0).card - (t0.card - u.card))) *
        (((eta F n i * P.V g.val / rho) ^ (s0 - u).card *
          d ^ (s0 - u).card))) := by
  have hu_s_card : u.card ≤ s0.card := Multiset.card_le_card hu_s
  have hu_t_card : u.card ≤ t0.card := Multiset.card_le_card hu_t
  have hDs : (s0 - u).card = s0.card - u.card := by
    have hadd : u.card + (s0 - u).card = s0.card := by
      have h : u + (s0 - u) = s0 := by
        rw [add_comm]
        exact Multiset.add_sub_cancel hu_s
      have hc := congrArg Multiset.card h
      simpa only [Multiset.card_add] using hc
    omega
  have hMt : (t0 - u).card = t0.card - u.card := by
    have hadd : u.card + (t0 - u).card = t0.card := by
      have h : u + (t0 - u) = t0 := by
        rw [add_comm]
        exact Multiset.add_sub_cancel hu_t
      have hc := congrArg Multiset.card h
      simpa only [Multiset.card_add] using hc
    omega
  rw [hDs, hMt, hQeq]
  have hDV_pos : 0 < d * P.V g.val := mul_pos hd hV
  have hDV_ne : (d * P.V g.val) ≠ 0 := ne_of_gt hDV_pos
  have hDV_s_ne : ((d * P.V g.val) ^ s0.card) ≠ 0 := pow_ne_zero _ hDV_ne
  have hs_eq : u.card + (s0.card - u.card) = s0.card :=
    Nat.add_sub_cancel' hu_s_card
  have ht_eq : u.card + (t0.card - u.card) = t0.card :=
    Nat.add_sub_cancel' hu_t_card
  have hDV_s : (d * P.V g.val) ^ s0.card =
      (d * P.V g.val) ^ u.card * (d * P.V g.val) ^ (s0.card - u.card) := by
    rw [← pow_add, hs_eq]
  have hDV_t : (d * P.V g.val) ^ t0.card =
      (d * P.V g.val) ^ u.card * (d * P.V g.val) ^ (t0.card - u.card) := by
    rw [← pow_add, ht_eq]
  -- Combined birth constant C = (eta*V/rho)*d = (eta/rho)*(d*V)
  have hC_eq : (eta F n i / rho) * (d * P.V g.val) =
      (eta F n i * P.V g.val / rho) * d := by ring
  -- Main multiplied identity
  have hMain : (eta F n i / rho) ^ (s0.card - u.card) *
        ((eta F n i * P.V g.val / rho) ^ (t0.card - u.card) * d ^ (t0.card - u.card)) *
        (d * P.V g.val) ^ s0.card =
      (d * P.V g.val) ^ t0.card *
        ((eta F n i / rho) ^ (t0.card - u.card) *
          ((eta F n i * P.V g.val / rho) ^ (s0.card - u.card) * d ^ (s0.card - u.card))) := by
    rw [hDV_s, hDV_t]
    have hBd_s : (eta F n i * P.V g.val / rho) ^ (s0.card - u.card) * d ^ (s0.card - u.card) =
        ((eta F n i / rho) * (d * P.V g.val)) ^ (s0.card - u.card) := by
      rw [hC_eq, mul_pow]
    have hBd_t : (eta F n i * P.V g.val / rho) ^ (t0.card - u.card) * d ^ (t0.card - u.card) =
        ((eta F n i / rho) * (d * P.V g.val)) ^ (t0.card - u.card) := by
      rw [hC_eq, mul_pow]
    rw [hBd_s, hBd_t, mul_pow, mul_pow]
    ring
  -- Multiply by common Q power via linear combination
  have hMainQ : ((eta F n i / rho) ^ (s0.card - u.card) *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices t0).card - (t0.card - u.card)) *
        ((eta F n i * P.V g.val / rho) ^ (t0.card - u.card) * d ^ (t0.card - u.card))) *
        (d * P.V g.val) ^ s0.card =
      (d * P.V g.val) ^ t0.card *
        ((eta F n i / rho) ^ (t0.card - u.card) *
          (visitQ F.q n i / rho ^ (2 : ℕ)) ^
            ((zeroMemoryIndices t0).card - (t0.card - u.card)) *
          ((eta F n i * P.V g.val / rho) ^ (s0.card - u.card) * d ^ (s0.card - u.card))) := by
    linear_combination
      (visitQ F.q n i / rho ^ (2 : ℕ)) ^
        ((zeroMemoryIndices t0).card - (t0.card - u.card)) * hMain
  have hdiv : ((d * P.V g.val) ^ t0.card / ((d * P.V g.val) ^ s0.card)) *
        (((eta F n i / rho) ^ (t0.card - u.card) *
          (visitQ F.q n i / rho ^ (2 : ℕ)) ^
            ((zeroMemoryIndices t0).card - (t0.card - u.card))) *
          (((eta F n i * P.V g.val / rho) ^ (s0.card - u.card) *
            d ^ (s0.card - u.card)))) =
      ((d * P.V g.val) ^ t0.card *
        ((eta F n i / rho) ^ (t0.card - u.card) *
          (visitQ F.q n i / rho ^ (2 : ℕ)) ^
            ((zeroMemoryIndices t0).card - (t0.card - u.card)) *
          ((eta F n i * P.V g.val / rho) ^ (s0.card - u.card) * d ^ (s0.card - u.card)))) /
        ((d * P.V g.val) ^ s0.card) := by
    ring
  have hlhs : ((eta F n i / rho) ^ (s0.card - u.card) *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices t0).card - (t0.card - u.card))) *
        (((eta F n i * P.V g.val / rho) ^ (t0.card - u.card) *
          d ^ (t0.card - u.card))) =
      (eta F n i / rho) ^ (s0.card - u.card) *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^
          ((zeroMemoryIndices t0).card - (t0.card - u.card)) *
        ((eta F n i * P.V g.val / rho) ^ (t0.card - u.card) * d ^ (t0.card - u.card)) := by
    ring
  rw [hlhs, hdiv, eq_div_iff hDV_s_ne]
  linear_combination hMainQ

/-- Per-survivor mass identity. -/
lemma perU_mass_eq (F : FixedData) (n : ℕ) (rho d : ℝ) (i : Fin (n + 1))
    (g : P.BigGroup) (s0 t0 u : P.Memory g.val)
    (hrho : 0 < rho) (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val)
    (hd : 0 < d)
    (hagree_st : ∀ v : P.Particle g.val, ¬ isZeroParticle v → s0.count v = t0.count v) :
    P.groupMemoryMass F n g.val s0 * ((fiberA (P := P) (g := g) s0 u).card : ℝ) *
      perU_term F n rho d i g s0 t0 u =
      singleReversal P d g s0 t0 *
      (P.groupMemoryMass F n g.val t0 * ((fiberA (P := P) (g := g) t0 u).card : ℝ) *
        perU_term F n rho d i g t0 s0 u) := by
  by_cases hu_s : u ≤ s0
  · by_cases hu_t : u ≤ t0
    · by_cases hagree_u : nonzeroPreserved (P := P) (g := g) s0 u
      · -- Valid case: agreement + ≤both, both sides given by formulas
        have hagree_tu : nonzeroPreserved (P := P) (g := g) t0 u := fun v hv =>
          (hagree_u v hv).trans (hagree_st v hv)
        have hvalid_s : nonzeroPreserved (P := P) (g := g) s0 u ∧ u ≤ s0 :=
          ⟨hagree_u, hu_s⟩
        have hvalid_t : nonzeroPreserved (P := P) (g := g) t0 u ∧ u ≤ t0 :=
          ⟨hagree_tu, hu_t⟩
        have hfib_s := fiberA_real s0 u hvalid_s
        have hfib_t := fiberA_real t0 u hvalid_t
        have hfib_s' : ((fiberA (P := P) (g := g) s0 u).card : ℝ) =
            (∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) /
              ((∏ v : P.Particle g.val, (((u.count v).factorial : ℝ))) *
                (∏ v : P.Particle g.val, (((s0.count v - u.count v).factorial : ℝ)))) := by
          rw [hfib_s, Finset.prod_mul_distrib]
        have hfib_t' : ((fiberA (P := P) (g := g) t0 u).card : ℝ) =
            (∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) /
              ((∏ v : P.Particle g.val, (((u.count v).factorial : ℝ))) *
                (∏ v : P.Particle g.val, (((t0.count v - u.count v).factorial : ℝ)))) := by
          rw [hfib_t, Finset.prod_mul_distrib]
        have hbirth_Ms : birthValid (P := P) (g := g) (s0 - u) (s0 - u).card := by
          constructor
          · rfl
          · intro v hv
            have hnz : ¬ isZeroParticle (P := P) (g := g) v := by
              unfold isZeroParticle
              exact hv
            have hu_eq := hagree_u v hnz
            have hcount : (s0 - u).count v = s0.count v - u.count v :=
              Multiset.count_sub v s0 u
            rw [hcount, hu_eq, Nat.sub_self]
        have hbirth_Mt : birthValid (P := P) (g := g) (t0 - u) (t0 - u).card := by
          constructor
          · rfl
          · intro v hv
            have hnz : ¬ isZeroParticle (P := P) (g := g) v := by
              unfold isZeroParticle
              exact hv
            have hu_eq := hagree_tu v hnz
            have hcount : (t0 - u).count v = t0.count v - u.count v :=
              Multiset.count_sub v t0 u
            rw [hcount, hu_eq, Nat.sub_self]
        have hperU_fwd : perU_term F n rho d i g s0 t0 u =
            ((eta F n i / rho) ^ (s0.card - u.card) *
              (visitQ F.q n i / rho ^ (2 : ℕ)) ^
                ((zeroMemoryIndices s0).card - (s0.card - u.card))) *
            (((eta F n i * P.V g.val / rho) ^ (t0 - u).card *
              d ^ (t0 - u).card) *
              ((((t0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod) *
                (((∏ v : P.Particle g.val, (((t0 - u).count v).factorial : ℝ)))⁻¹))) := by
          unfold perU_term
          rw [dif_pos hu_t, dif_pos hbirth_Mt]
        have hperU_rev : perU_term F n rho d i g t0 s0 u =
            ((eta F n i / rho) ^ (t0.card - u.card) *
              (visitQ F.q n i / rho ^ (2 : ℕ)) ^
                ((zeroMemoryIndices t0).card - (t0.card - u.card))) *
            (((eta F n i * P.V g.val / rho) ^ (s0 - u).card *
              d ^ (s0 - u).card) *
              ((((s0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod) *
                (((∏ v : P.Particle g.val, (((s0 - u).count v).factorial : ℝ)))⁻¹))) := by
          unfold perU_term
          rw [dif_pos hu_s, dif_pos hbirth_Ms]
        have hQeq := Q_exp_eq s0 t0 u hagree_st hagree_u hu_s hu_t
        have hmass_s : P.groupMemoryMass F n g.val s0 =
            (s0.map (fun w => tiltedMu F P n g.val w.1)).prod /
              (∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) := by
          unfold PrimeGroups.groupMemoryMass
          rw [mass_denom_eq_univ F n _ _]
        have hmass_t : P.groupMemoryMass F n g.val t0 =
            (t0.map (fun w => tiltedMu F P n g.val w.1)).prod /
              (∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) := by
          unfold PrimeGroups.groupMemoryMass
          rw [mass_denom_eq_univ F n _ _]
        have hDV_ne : (d * P.V g.val) ≠ 0 := ne_of_gt (mul_pos hd hV)
        have hRev : singleReversal P d g s0 t0 =
            (d * P.V g.val) ^ t0.card / ((d * P.V g.val) ^ s0.card) := by
          unfold singleReversal
          rw [zpow_sub₀ hDV_ne, zpow_natCast, zpow_natCast]
        have hSym := Sym_eq_skeleton F n g s0 t0 u hu_s hu_t
        simp only [Finset.prod_mul_distrib] at hSym
        have hCoeff := coeff_eq_skeleton F n rho d i g s0 t0 u hrho hV hd hu_s hu_t hQeq
        rw [hmass_s, hmass_t, hfib_s', hfib_t', hperU_fwd, hperU_rev, hRev]
        have hLHS_factor :
            (s0.map (fun w => tiltedMu F P n g.val w.1)).prod /
              (∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) *
              ((∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) /
                ((∏ v : P.Particle g.val, (((u.count v).factorial : ℝ))) *
                  (∏ v : P.Particle g.val, (((s0.count v - u.count v).factorial : ℝ))))) *
              (((eta F n i / rho) ^ (s0.card - u.card) *
                (visitQ F.q n i / rho ^ (2 : ℕ)) ^
                  ((zeroMemoryIndices s0).card - (s0.card - u.card))) *
                (((eta F n i * P.V g.val / rho) ^ (t0 - u).card * d ^ (t0 - u).card) *
                  (((t0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod *
                    ((∏ v : P.Particle g.val, (((t0 - u).count v).factorial : ℝ)))⁻¹))) =
            (((s0.map (fun w => tiltedMu F P n g.val w.1)).prod /
              (∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) *
              (((∏ v : P.Particle g.val, (((s0.count v).factorial : ℝ))) /
                (((∏ v : P.Particle g.val, (((u.count v).factorial : ℝ))) *
                  (∏ v : P.Particle g.val, (((s0.count v - u.count v).factorial : ℝ))))))) *
              ((((t0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod) /
                (∏ v : P.Particle g.val, (((t0 - u).count v).factorial : ℝ)))) *
            (((eta F n i / rho) ^ (s0.card - u.card) *
              (visitQ F.q n i / rho ^ (2 : ℕ)) ^
                ((zeroMemoryIndices s0).card - (s0.card - u.card))) *
              (((eta F n i * P.V g.val / rho) ^ (t0 - u).card * d ^ (t0 - u).card)))) := by
          ring
        have hRHS_factor :
            (t0.map (fun w => tiltedMu F P n g.val w.1)).prod /
              (∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) *
              ((∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) /
                ((∏ v : P.Particle g.val, (((u.count v).factorial : ℝ))) *
                  (∏ v : P.Particle g.val, (((t0.count v - u.count v).factorial : ℝ))))) *
              (((eta F n i / rho) ^ (t0.card - u.card) *
                (visitQ F.q n i / rho ^ (2 : ℕ)) ^
                  ((zeroMemoryIndices t0).card - (t0.card - u.card))) *
                (((eta F n i * P.V g.val / rho) ^ (s0 - u).card * d ^ (s0 - u).card) *
                  (((s0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod *
                    ((∏ v : P.Particle g.val, (((s0 - u).count v).factorial : ℝ)))⁻¹))) =
            (((t0.map (fun w => tiltedMu F P n g.val w.1)).prod /
              (∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) *
              (((∏ v : P.Particle g.val, (((t0.count v).factorial : ℝ))) /
                (((∏ v : P.Particle g.val, (((u.count v).factorial : ℝ))) *
                  (∏ v : P.Particle g.val, (((t0.count v - u.count v).factorial : ℝ))))))) *
              ((((s0 - u).map (fun w => tiltedMu F P n g.val w.1)).prod) /
                (∏ v : P.Particle g.val, (((s0 - u).count v).factorial : ℝ)))) *
            (((eta F n i / rho) ^ (t0.card - u.card) *
              (visitQ F.q n i / rho ^ (2 : ℕ)) ^
                ((zeroMemoryIndices t0).card - (t0.card - u.card))) *
              (((eta F n i * P.V g.val / rho) ^ (s0 - u).card * d ^ (s0 - u).card)))) := by
          ring
        rw [hLHS_factor, hRHS_factor, hSym, hCoeff]
        ring
      · -- Invalid: u disagrees, both fiberAs zero
        have hnpres_t : ¬ nonzeroPreserved (P := P) (g := g) t0 u := by
          intro ht
          apply hagree_u
          intro v hv
          have hs_eq := hagree_st v hv
          have ht_eq := ht v hv
          exact ht_eq.trans hs_eq.symm
        have hnvalid_s : ¬ (nonzeroPreserved (P := P) (g := g) s0 u ∧ u ≤ s0) :=
          fun h => hagree_u h.1
        have hnvalid_t : ¬ (nonzeroPreserved (P := P) (g := g) t0 u ∧ u ≤ t0) :=
          fun h => hnpres_t h.1
        have hfib_s0 : (fiberA (P := P) (g := g) s0 u).card = 0 := by
          have hcard : (fiberA (P := P) (g := g) s0 u).card =
              (if nonzeroPreserved (P := P) (g := g) s0 u ∧ u ≤ s0 then
                ∏ v : P.Particle g.val, Nat.choose (s0.count v) (u.count v)
              else 0) := fiberA_card (P := P) (g := g) s0 u
          rw [if_neg hnvalid_s] at hcard
          exact hcard
        have hfib_t0 : (fiberA (P := P) (g := g) t0 u).card = 0 := by
          have hcard : (fiberA (P := P) (g := g) t0 u).card =
              (if nonzeroPreserved (P := P) (g := g) t0 u ∧ u ≤ t0 then
                ∏ v : P.Particle g.val, Nat.choose (t0.count v) (u.count v)
              else 0) := fiberA_card (P := P) (g := g) t0 u
          rw [if_neg hnvalid_t] at hcard
          exact hcard
        simp only [hfib_s0, hfib_t0, Nat.cast_zero, mul_zero, zero_mul]
    · -- Invalid: ¬(u≤t0), forward perU=0, reverse fiberA=0
      have hperU_fwd0 : perU_term F n rho d i g s0 t0 u = 0 := by
        unfold perU_term
        rw [dif_neg hu_t]
      have hnvalid_t : ¬ (nonzeroPreserved (P := P) (g := g) t0 u ∧ u ≤ t0) :=
        fun h => hu_t h.2
      have hfib_t0 : (fiberA (P := P) (g := g) t0 u).card = 0 := by
        have hcard : (fiberA (P := P) (g := g) t0 u).card =
            (if nonzeroPreserved (P := P) (g := g) t0 u ∧ u ≤ t0 then
              ∏ v : P.Particle g.val, Nat.choose (t0.count v) (u.count v)
            else 0) := fiberA_card (P := P) (g := g) t0 u
        rw [if_neg hnvalid_t] at hcard
        exact hcard
      simp only [hperU_fwd0, hfib_t0, Nat.cast_zero, mul_zero, zero_mul]
  · -- Invalid: ¬(u≤s0), forward fiberA=0, reverse perU=0
    have hnvalid_s : ¬ (nonzeroPreserved (P := P) (g := g) s0 u ∧ u ≤ s0) :=
      fun h => hu_s h.2
    have hfib_s0 : (fiberA (P := P) (g := g) s0 u).card = 0 := by
      have hcard : (fiberA (P := P) (g := g) s0 u).card =
          (if nonzeroPreserved (P := P) (g := g) s0 u ∧ u ≤ s0 then
            ∏ v : P.Particle g.val, Nat.choose (s0.count v) (u.count v)
          else 0) := fiberA_card (P := P) (g := g) s0 u
      rw [if_neg hnvalid_s] at hcard
      exact hcard
    have hperU_rev0 : perU_term F n rho d i g t0 s0 u = 0 := by
      unfold perU_term
      rw [dif_neg hu_s]
    simp only [hfib_s0, hperU_rev0, Nat.cast_zero, mul_zero, zero_mul]

end Erdos821.P3Adj
