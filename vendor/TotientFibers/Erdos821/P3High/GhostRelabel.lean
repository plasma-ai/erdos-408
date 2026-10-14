import Erdos821.P3High.EdgeRelabel

/-! Conditional ghost rows.  A valid ghost choice into a bounded target is the same as its
deleted index sets and ordered birth batches (`GT`); constraining an ordered batch label to a
prescribed value keeps the factorial divisor and replaces its tilted mass by a point mass. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3High

open Erdos821.Blueprint.Graph hiding BirthAddress EdgeChoice GhostChoice MemoryHistory
  TransferChoice TransferMode absoluteMemoryEdgeKernel absoluteMemoryGhostKernel
  absoluteScaledMemoryGhostKernel deleteMemoryIndices distinctMemoryExpression
  edgeChoiceCoefficient edgeChoiceValid edgeDelta edgeForward edgeSymmetryFactor freshBigFactor
  ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEdgeKernel
  memoryEntry memoryGhostKernel permuteActive rawEdgeValid rawEdgeWeight retrievedIndices
  smallDamping smallOmega smallTargetFactor storedMemory transferModeAccept translateMemory
  translateParticle translateSmallResidues zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core Erdos821.P3Lowrank

attribute [local instance] bmsFintype

variable {F : FixedData} {P : PrimeGroups}

/-- Deleted indices and an ordered batch of at most `B` labels in every big group. -/
abbrev GT (P : PrimeGroups) {M : ℕ} (s : P.MemoryState M) (B : ℕ) :=
  (g : P.BigGroup) → Finset (Fin (s.2.2 g).card) × (Σ b : Fin (B + 1), Fin b.val → P.Prime g.val)

def gtTarget {M B : ℕ} (s : P.MemoryState M) (tr : GT P s B) : P.MemoryState M :=
  (s.1, s.2.1, fun g => deleteMemoryIndices (s.2.2 g) (tr g).1 + zeroBirthBatch (tr g).2.2)

def gtValid {M B : ℕ} {s : P.MemoryState M} (tr : GT P s B) : Prop :=
  ∀ g, (tr g).1 ⊆ zeroMemoryIndices (s.2.2 g)

def gtGroupWeight (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ}
    (s : P.MemoryState M) (g : P.BigGroup)
    (y : Finset (Fin (s.2.2 g).card) × (Σ b : Fin (B + 1), Fin b.val → P.Prime g.val)) : ℝ :=
  (-eta F n i / rho) ^ y.1.card *
    (visitQ F.q n i / rho ^ (2 : ℕ)) ^ ((zeroMemoryIndices (s.2.2 g)).card - y.1.card) *
    ((y.2.1.val.factorial : ℝ))⁻¹ *
    (-eta F n i * P.V g.val / rho) ^ y.2.1.val *
    ∏ h : Fin y.2.1.val, tiltedMu F P n g.val (y.2.2 h)

def gtWeight (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ}
    {s : P.MemoryState M} (tr : GT P s B) : ℝ :=
  ∏ g : P.BigGroup, gtGroupWeight F n rho i s g (tr g)

theorem card_le_memorySize {M : ℕ} (t : P.MemoryState M) (g : P.BigGroup) :
    (t.2.2 g).card ≤ P.memorySize t := by
  unfold PrimeGroups.memorySize
  exact Finset.single_le_sum (f := fun h => (t.2.2 h).card) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ g)

/-- Encode a ghost choice into a bounded target. -/
def gtEnc {M B : ℕ} (s t : P.MemoryState M) (ht : P.memorySize t ≤ B) (c : GhostChoice s t) :
    GT P s B :=
  fun g => (c.1 g, ⟨⟨(c.2.1 g).val, Nat.lt_succ_of_le
    ((Nat.le_of_lt_succ (c.2.1 g).isLt).trans ((card_le_memorySize t g).trans ht))⟩, c.2.2 g⟩)

theorem zeroBirthBatch_card' {g : P.Group} {b : ℕ} (p : Fin b → P.Prime g) :
    (zeroBirthBatch p).card = b := by
  simp [zeroBirthBatch]

theorem gtTarget_card {M B : ℕ} (s : P.MemoryState M) (tr : GT P s B) (g : P.BigGroup) :
    ((gtTarget s tr).2.2 g).card = (s.2.2 g).card - (tr g).1.card + (tr g).2.1.val := by
  simp only [gtTarget, Multiset.card_add, deleteMemoryIndices_card, zeroBirthBatch_card']

/-- Decode a bounded transition into a target and a literal ghost choice. -/
def gtDec {M B : ℕ} (s : P.MemoryState M) (tr : GT P s B)
    (hb : P.memorySize (gtTarget s tr) ≤ B) :
    Σ t : BoundedMemoryState P M B, GhostChoice s t.val :=
  ⟨⟨gtTarget s tr, hb⟩, (fun g => (tr g).1, ⟨fun g => ⟨(tr g).2.1.val, by
    rw [gtTarget_card]; omega⟩, fun g => (tr g).2.2⟩)⟩

theorem ghost_sigma_ext {M B : ℕ} (s : P.MemoryState M) (t1 t2 : BoundedMemoryState P M B)
    (c1 : GhostChoice s t1.val) (c2 : GhostChoice s t2.val) (ht : t1 = t2)
    (h1 : c1.1 = c2.1) (h2 : ∀ g, (c1.2.1 g).val = (c2.2.1 g).val)
    (h3 : ∀ g, HEq (c1.2.2 g) (c2.2.2 g)) :
    (⟨t1, c1⟩ : Σ t : BoundedMemoryState P M B, GhostChoice s t.val) = ⟨t2, c2⟩ := by
  subst ht
  obtain ⟨A1, b1, l1⟩ := c1
  obtain ⟨A2, b2, l2⟩ := c2
  simp only at h1 h2 h3
  subst h1
  have hb : b1 = b2 := funext fun g => Fin.ext (h2 g)
  subst hb
  have hl : l1 = l2 := funext fun g => eq_of_heq (h3 g)
  subst hl
  rfl

/-- Valid bounded ghost row terms are exactly the valid bounded transitions. -/
theorem ghost_transfer {M B : ℕ} (s : P.MemoryState M) (H : GT P s B → ℝ) :
    ∑ t : BoundedMemoryState P M B, ∑ c : GhostChoice s t.val,
        (if (s.1 = t.val.1 ∧ s.2.1 = t.val.2.1) ∧ ghostChoiceValid c
          then H (gtEnc s t.val t.property c) else 0) =
      ∑ tr : GT P s B,
        (if gtValid tr ∧ P.memorySize (gtTarget s tr) ≤ B then H tr else 0) := by
  rw [← Fintype.sum_sigma (fun x : Σ t : BoundedMemoryState P M B, GhostChoice s t.val =>
    if (s.1 = x.1.val.1 ∧ s.2.1 = x.1.val.2.1) ∧ ghostChoiceValid x.2
      then H (gtEnc s x.1.val x.1.property x.2) else 0)]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have htarget : ∀ x : Σ t : BoundedMemoryState P M B, GhostChoice s t.val,
      (s.1 = x.1.val.1 ∧ s.2.1 = x.1.val.2.1) ∧ ghostChoiceValid x.2 →
        gtTarget s (gtEnc s x.1.val x.1.property x.2) = x.1.val := by
    intro x hx
    exact Prod.ext hx.1.1 (Prod.ext hx.1.2 (funext fun g => (hx.2 g).2))
  refine Finset.sum_bij' (fun x _ => gtEnc s x.1.val x.1.property x.2)
    (fun tr htr => gtDec s tr (Finset.mem_filter.1 htr).2.2) ?hi ?hj ?li ?ri ?hh
  case hi =>
    intro x hx
    have hx' := (Finset.mem_filter.1 hx).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun g => (hx'.2 g).1, ?_⟩
    rw [htarget x hx']
    exact x.1.property
  case hj =>
    intro tr htr
    have htr' := (Finset.mem_filter.1 htr).2
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨rfl, rfl⟩, fun g => ⟨htr'.1 g, rfl⟩⟩
  case li =>
    intro x hx
    have hx' := (Finset.mem_filter.1 hx).2
    obtain ⟨t, c⟩ := x
    refine ghost_sigma_ext s _ t _ c ?_ rfl (fun _ => rfl) (fun _ => HEq.rfl)
    exact Subtype.ext (htarget ⟨t, c⟩ hx')
  case ri =>
    intro tr _
    rfl
  case hh =>
    intro x _
    rfl

/-- The constraint at batch address `(g, h)`. -/
def gtValAt {M B : ℕ} {s : P.MemoryState M} (tr : GT P s B) (x : P.BigGroup × Fin B) : ℕ :=
  if hh : x.2.val < (tr x.1).2.1.val then ((tr x.1).2.2 ⟨x.2.val, hh⟩).val else 0

def gtSlotCond {M B : ℕ} {s : P.MemoryState M} (vals : P.BigGroup × Fin B → ℕ)
    (tr : GT P s B) (x : P.BigGroup × Fin B) : Prop :=
  x.2.val < (tr x.1).2.1.val ∧ gtValAt tr x = vals x

def ghostValAt {M B : ℕ} {s t : P.MemoryState M} (c : GhostChoice s t)
    (x : P.BigGroup × Fin B) : ℕ :=
  if hh : x.2.val < (c.2.1 x.1).val then ((c.2.2 x.1 ⟨x.2.val, hh⟩)).val else 0

def ghostSlotCond {M B : ℕ} {s t : P.MemoryState M} (vals : P.BigGroup × Fin B → ℕ)
    (c : GhostChoice s t) (x : P.BigGroup × Fin B) : Prop :=
  x.2.val < (c.2.1 x.1).val ∧ ghostValAt c x = vals x

/-- Indicator multiplier constraining the ordered ghost batch addresses `Sl` at one visit. -/
def ghostMult {M B : ℕ} (Sl : Finset (P.BigGroup × Fin B)) (vals : P.BigGroup × Fin B → ℕ) :
    (s t : P.MemoryState M) → GhostChoice s t → ℝ :=
  fun _ _ c => if ∀ x ∈ Sl, ghostSlotCond vals c x then 1 else 0

/-- Replace the batch label of group `g` at ordered index `h` (if that index is born). -/
def gtRelabel {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) : GT P s B :=
  Function.update tr g ((tr g).1, ⟨(tr g).2.1,
    if hh : h.val < (tr g).2.1.val then Function.update (tr g).2.2 ⟨h.val, hh⟩ p
    else (tr g).2.2⟩)

theorem gtRelabel_apply_self {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) :
    gtRelabel g h p tr g = ((tr g).1, ⟨(tr g).2.1,
      if hh : h.val < (tr g).2.1.val then Function.update (tr g).2.2 ⟨h.val, hh⟩ p
      else (tr g).2.2⟩) := by
  simp only [gtRelabel, Function.update_self]

theorem gtRelabel_apply_ne {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) (g' : P.BigGroup) (hg : g' ≠ g) :
    gtRelabel g h p tr g' = tr g' := by
  simp only [gtRelabel, Function.update_of_ne hg]

theorem gtRelabel_fst {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) (g' : P.BigGroup) :
    (gtRelabel g h p tr g').1 = (tr g').1 := by
  by_cases hg : g' = g
  · subst hg
    rw [gtRelabel_apply_self]
  · rw [gtRelabel_apply_ne g h p tr g' hg]

theorem gtRelabel_batch {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) (g' : P.BigGroup) :
    (gtRelabel g h p tr g').2.1 = (tr g').2.1 := by
  by_cases hg : g' = g
  · subst hg
    rw [gtRelabel_apply_self]
  · rw [gtRelabel_apply_ne g h p tr g' hg]

theorem gtValid_relabel {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) : gtValid (gtRelabel g h p tr) ↔ gtValid tr := by
  unfold gtValid
  simp only [gtRelabel_fst]

theorem memorySize_gtTarget_relabel {M B : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (h : Fin B) (p : P.Prime g.val) (tr : GT P s B) :
    P.memorySize (gtTarget s (gtRelabel g h p tr)) = P.memorySize (gtTarget s tr) := by
  unfold PrimeGroups.memorySize
  apply Finset.sum_congr rfl
  intro g' _
  rw [gtTarget_card, gtTarget_card, gtRelabel_fst, gtRelabel_batch]

def valOf {B : ℕ} {g : P.BigGroup} {k : ℕ}
    (y : Finset (Fin k) × (Σ b : Fin (B + 1), Fin b.val → P.Prime g.val)) (h : Fin B) : ℕ :=
  if hh : h.val < y.2.1.val then (y.2.2 ⟨h.val, hh⟩).val else 0

theorem gtValAt_eq {M B : ℕ} {s : P.MemoryState M} (tr : GT P s B) (x : P.BigGroup × Fin B) :
    gtValAt tr x = valOf (tr x.1) x.2 := rfl

theorem gtValAt_relabel_self {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) (hh : h.val < (tr g).2.1.val) :
    gtValAt (gtRelabel g h p tr) (g, h) = p.val := by
  rw [gtValAt_eq]
  show valOf (gtRelabel g h p tr g) h = p.val
  rw [gtRelabel_apply_self]
  simp only [valOf, dif_pos hh, Function.update_self]

theorem gtValAt_relabel_ne {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p : P.Prime g.val) (tr : GT P s B) (x : P.BigGroup × Fin B) (hx : x ≠ (g, h)) :
    gtValAt (gtRelabel g h p tr) x = gtValAt tr x := by
  rcases x with ⟨g', h'⟩
  rw [gtValAt_eq, gtValAt_eq]
  show valOf (gtRelabel g h p tr g') h' = valOf (tr g') h'
  by_cases hg : g' = g
  · subst hg
    have hh' : h' ≠ h := fun he => hx (by rw [he])
    rw [gtRelabel_apply_self]
    unfold valOf
    by_cases hb : h'.val < (tr g').2.1.val
    · simp only [dif_pos hb]
      by_cases hh : h.val < (tr g').2.1.val
      · simp only [dif_pos hh]
        rw [Function.update_of_ne]
        intro he
        apply hh'
        exact Fin.ext (Fin.mk.inj he)
      · simp only [dif_neg hh]
    · simp only [dif_neg hb]
  · rw [gtRelabel_apply_ne g h p tr g' hg]

theorem gtRelabel_relabel {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (p q : P.Prime g.val) (tr : GT P s B) :
    gtRelabel g h p (gtRelabel g h q tr) = gtRelabel g h p tr := by
  funext g'
  by_cases hg : g' = g
  · subst hg
    rw [gtRelabel_apply_self, gtRelabel_apply_self, gtRelabel_apply_self]
    by_cases hh : h.val < (tr g').2.1.val
    · simp only [dif_pos hh, Function.update_idem]
    · simp only [dif_neg hh]
  · rw [gtRelabel_apply_ne g h p _ g' hg, gtRelabel_apply_ne g h q _ g' hg,
      gtRelabel_apply_ne g h p _ g' hg]

theorem gtRelabel_eq_self {M B : ℕ} {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B)
    (tr : GT P s B) (hh : h.val < (tr g).2.1.val) :
    gtRelabel g h ((tr g).2.2 ⟨h.val, hh⟩) tr = tr := by
  funext g'
  by_cases hg : g' = g
  · subst hg
    rw [gtRelabel_apply_self]
    simp only [dif_pos hh, Function.update_eq_self]
  · rw [gtRelabel_apply_ne g h _ tr g' hg]

theorem prod_update_scale {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (x : ι)
    (a c d : ℝ) (h : a * c = f x * d) :
    (∏ y, Function.update f x a y) * c = (∏ y, f y) * d := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ x),
    Finset.prod_eq_mul_prod_diff_singleton x f (fun hx => (hx (Finset.mem_univ x)).elim)]
  calc a * (∏ y ∈ Finset.univ \ {x}, f y) * c = (a * c) * ∏ y ∈ Finset.univ \ {x}, f y := by
        ring
    _ = _ := by rw [h]; ring

theorem gtWeight_relabel (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ}
    {s : P.MemoryState M} (g : P.BigGroup) (h : Fin B) (p : P.Prime g.val) (tr : GT P s B)
    (hh : h.val < (tr g).2.1.val) :
    gtWeight F n rho i (gtRelabel g h p tr) * tiltedMu F P n g.val ((tr g).2.2 ⟨h.val, hh⟩) =
      gtWeight F n rho i tr * tiltedMu F P n g.val p := by
  unfold gtWeight
  have hpt : (fun g' => gtGroupWeight F n rho i s g' (gtRelabel g h p tr g')) =
      Function.update (fun g' => gtGroupWeight F n rho i s g' (tr g')) g
        (gtGroupWeight F n rho i s g (gtRelabel g h p tr g)) := by
    funext g'
    by_cases hg : g' = g
    · subst hg
      rw [Function.update_self]
    · rw [Function.update_of_ne hg, gtRelabel_apply_ne g h p tr g' hg]
  rw [show (∏ g', gtGroupWeight F n rho i s g' (gtRelabel g h p tr g')) =
    ∏ g', (fun g' => gtGroupWeight F n rho i s g' (gtRelabel g h p tr g')) g' from rfl, hpt]
  apply prod_update_scale
  rw [gtRelabel_apply_self]
  unfold gtGroupWeight
  simp only [dif_pos hh]
  have hin : (fun h' => tiltedMu F P n g.val (Function.update (tr g).2.2 ⟨h.val, hh⟩ p h')) =
      Function.update (fun h' => tiltedMu F P n g.val ((tr g).2.2 h')) ⟨h.val, hh⟩
        (tiltedMu F P n g.val p) := by
    funext h'
    by_cases he : h' = ⟨h.val, hh⟩
    · subst he
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne he, Function.update_of_ne he]
  have key := prod_update_scale (fun h' => tiltedMu F P n g.val ((tr g).2.2 h')) ⟨h.val, hh⟩
    (tiltedMu F P n g.val p) (tiltedMu F P n g.val ((tr g).2.2 ⟨h.val, hh⟩))
    (tiltedMu F P n g.val p) (mul_comm _ _)
  rw [← hin] at key
  calc _ = ((-eta F n i / rho) ^ (tr g).1.card *
        (visitQ F.q n i / rho ^ (2 : ℕ)) ^ ((zeroMemoryIndices (s.2.2 g)).card - (tr g).1.card) *
        (((tr g).2.1.val.factorial : ℝ))⁻¹ *
        (-eta F n i * P.V g.val / rho) ^ (tr g).2.1.val) *
        ((∏ h', tiltedMu F P n g.val (Function.update (tr g).2.2 ⟨h.val, hh⟩ p h')) *
          tiltedMu F P n g.val ((tr g).2.2 ⟨h.val, hh⟩)) := by ring
    _ = _ := by rw [key]; ring

/-- One absolute ghost transition term with its target weight. -/
def gtTerm (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ} (v : ℝ)
    (s : P.MemoryState M) (tr : GT P s B) : ℝ :=
  if gtValid tr ∧ P.memorySize (gtTarget s tr) ≤ B then
    |gtWeight F n rho i tr| * P.memoryWeight v (gtTarget s tr) else 0

theorem gtTerm_nonneg (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ} (v : ℝ)
    (hv : 0 ≤ v) (s : P.MemoryState M) (tr : GT P s B) : 0 ≤ gtTerm F n rho i v s tr := by
  unfold gtTerm
  split_ifs
  · exact mul_nonneg (abs_nonneg _) (pow_nonneg hv _)
  · exact le_rfl

theorem ghost_single (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ} (v : ℝ)
    (hv : 0 ≤ v)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmass1 : ∀ g : P.BigGroup, 1 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p)
    (s : P.MemoryState M) (Q : GT P s B → Prop) (x : P.BigGroup × Fin B)
    (hQ : ∀ p tr, Q (gtRelabel x.1 x.2 p tr) ↔ Q tr) (vx : ℕ) :
    ∑ tr : GT P s B, (if Q tr ∧ (x.2.val < (tr x.1).2.1.val ∧ gtValAt tr x = vx)
        then gtTerm F n rho i v s tr else 0) ≤
      muHat F P n x.1 vx * ∑ tr : GT P s B, (if Q tr then gtTerm F n rho i v s tr else 0) := by
  rcases x with ⟨g, h⟩
  dsimp only at hQ ⊢
  have hf0 := gtTerm_nonneg F n rho i v hv s (B := B)
  have hR0 : 0 ≤ ∑ tr : GT P s B, (if Q tr then gtTerm F n rho i v s tr else 0) :=
    Finset.sum_nonneg fun tr _ => by
      split_ifs
      · exact hf0 tr
      · exact le_rfl
  have hRHS0 := mul_nonneg (muHat_nonneg F P n hμ g vx) hR0
  by_cases hvx : vx ∈ P.primes g.val
  swap
  · have hz : ∀ tr : GT P s B, ¬ (Q tr ∧ (h.val < (tr g).2.1.val ∧ gtValAt tr (g, h) = vx)) := by
      rintro tr ⟨-, hb, he⟩
      apply hvx
      rw [← he]
      unfold gtValAt
      rw [dif_pos hb]
      exact ((tr g).2.2 _).property
    rw [Finset.sum_eq_zero fun tr _ => if_neg (hz tr)]
    exact hRHS0
  let α : P.Prime g.val := ⟨vx, hvx⟩
  have hmu : muHat F P n g vx = tiltedMu F P n g.val α := muHat_of_mem F P n g α
  let T := Finset.univ.filter (fun tr : GT P s B => Q tr ∧
    (gtValid tr ∧ P.memorySize (gtTarget s tr) ≤ B) ∧
      (h.val < (tr g).2.1.val ∧ gtValAt tr (g, h) = vx))
  let S := Finset.univ.filter Q
  have hlab : ∀ tr : GT P s B, ∀ hb : h.val < (tr g).2.1.val, gtValAt tr (g, h) = vx →
      (tr g).2.2 ⟨h.val, hb⟩ = α := by
    intro tr hb he
    apply Subtype.ext
    unfold gtValAt at he
    rw [dif_pos hb] at he
    exact he
  have hLHS : (∑ tr : GT P s B, (if Q tr ∧ (h.val < (tr g).2.1.val ∧ gtValAt tr (g, h) = vx)
      then gtTerm F n rho i v s tr else 0)) = ∑ tr ∈ T, gtTerm F n rho i v s tr := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro tr _
    by_cases hvb : gtValid tr ∧ P.memorySize (gtTarget s tr) ≤ B
    · by_cases hc : Q tr ∧ (h.val < (tr g).2.1.val ∧ gtValAt tr (g, h) = vx)
      · rw [if_pos hc, if_pos ⟨hc.1, hvb, hc.2⟩]
      · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.1, h'.2.2⟩)]
    · have hz : gtTerm F n rho i v s tr = 0 := by unfold gtTerm; rw [if_neg hvb]
      rw [hz]
      split_ifs <;> rfl
  have hS : (∑ tr : GT P s B, (if Q tr then gtTerm F n rho i v s tr else 0)) =
      ∑ tr ∈ S, gtTerm F n rho i v s tr := (Finset.sum_filter _ _).symm
  have key := relabel_sum_le (gtTerm F n rho i v s) T S Finset.univ
    (fun tr p => gtRelabel g h p tr) (tiltedMu F P n g.val) (tiltedMu F P n g.val α) 1
    (fun tr _ => hf0 tr) (fun tr _ => hf0 tr) (hμ _ _).le one_pos (hmass1 g)
    (by
      intro tr htr p _
      rw [Finset.mem_filter] at htr ⊢
      exact ⟨Finset.mem_univ _, (hQ p tr).mpr htr.2.1⟩)
    (by
      intro tr1 htr1 p1 _ tr2 htr2 p2 _ he
      obtain ⟨-, -, -, hb1, hv1⟩ := Finset.mem_filter.1 htr1
      obtain ⟨-, -, -, hb2, hv2⟩ := Finset.mem_filter.1 htr2
      have hp : p1 = p2 := by
        have h3 : gtValAt (gtRelabel g h p1 tr1) (g, h) = gtValAt (gtRelabel g h p2 tr2) (g, h) :=
          congrArg (fun tr => gtValAt tr (g, h)) he
        rw [gtValAt_relabel_self g h p1 tr1 hb1, gtValAt_relabel_self g h p2 tr2 hb2] at h3
        exact Subtype.ext h3
      refine ⟨?_, hp⟩
      have hα1 := hlab tr1 hb1 hv1
      have hα2 := hlab tr2 hb2 hv2
      calc tr1 = gtRelabel g h ((tr1 g).2.2 ⟨h.val, hb1⟩) tr1 := (gtRelabel_eq_self g h tr1 hb1).symm
        _ = gtRelabel g h α tr1 := by rw [hα1]
        _ = gtRelabel g h α (gtRelabel g h p1 tr1) := (gtRelabel_relabel g h α p1 tr1).symm
        _ = gtRelabel g h α (gtRelabel g h p2 tr2) := by rw [he]
        _ = gtRelabel g h α tr2 := gtRelabel_relabel g h α p2 tr2
        _ = gtRelabel g h ((tr2 g).2.2 ⟨h.val, hb2⟩) tr2 := by rw [hα2]
        _ = tr2 := gtRelabel_eq_self g h tr2 hb2)
    (by
      intro tr htr p _
      obtain ⟨-, -, hvb, hb, hv⟩ := Finset.mem_filter.1 htr
      have hα := hlab tr hb hv
      have hvb' : gtValid (gtRelabel g h p tr) ∧
          P.memorySize (gtTarget s (gtRelabel g h p tr)) ≤ B :=
        ⟨(gtValid_relabel g h p tr).mpr hvb.1, by rw [memorySize_gtTarget_relabel]; exact hvb.2⟩
      have hW := gtWeight_relabel F n rho i g h p tr hb
      have hW' := congrArg abs hW
      rw [abs_mul, abs_mul, abs_of_pos (hμ _ _), abs_of_pos (hμ _ _), hα] at hW'
      have hw : P.memoryWeight v (gtTarget s (gtRelabel g h p tr)) =
          P.memoryWeight v (gtTarget s tr) := by
        unfold PrimeGroups.memoryWeight
        rw [memorySize_gtTarget_relabel]
      unfold gtTerm
      rw [if_pos hvb, if_pos hvb', hw]
      calc |gtWeight F n rho i tr| * P.memoryWeight v (gtTarget s tr) * tiltedMu F P n g.val p
          = (|gtWeight F n rho i tr| * tiltedMu F P n g.val p) *
              P.memoryWeight v (gtTarget s tr) := by ring
        _ = _ := by rw [← hW']; ring)
  rw [hLHS, hS, hmu]
  calc _ ≤ tiltedMu F P n g.val α / 1 * ∑ tr ∈ S, gtTerm F n rho i v s tr := key
    _ = _ := by ring

theorem ghost_slots (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ} (v : ℝ)
    (hv : 0 ≤ v)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmass1 : ∀ g : P.BigGroup, 1 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p)
    (s : P.MemoryState M) (vals : P.BigGroup × Fin B → ℕ) :
    ∀ Sl : Finset (P.BigGroup × Fin B),
    ∑ tr : GT P s B, (if ∀ x ∈ Sl, gtSlotCond vals tr x then gtTerm F n rho i v s tr else 0) ≤
      (∏ x ∈ Sl, muHat F P n x.1 (vals x)) * ∑ tr : GT P s B, gtTerm F n rho i v s tr := by
  intro Sl
  induction Sl using Finset.induction_on with
  | empty => simp
  | insert y S hy ih =>
      have hrw : ∀ tr : GT P s B,
          (if ∀ x ∈ insert y S, gtSlotCond vals tr x then gtTerm F n rho i v s tr else 0) =
          (if (∀ x ∈ S, gtSlotCond vals tr x) ∧
              (y.2.val < (tr y.1).2.1.val ∧ gtValAt tr y = vals y)
            then gtTerm F n rho i v s tr else 0) := by
        intro tr
        by_cases h1 : ∀ x ∈ insert y S, gtSlotCond vals tr x
        · rw [if_pos h1, if_pos ⟨fun x hx => h1 x (Finset.mem_insert_of_mem hx),
            h1 y (Finset.mem_insert_self y S)⟩]
        · rw [if_neg h1, if_neg]
          rintro ⟨h2, h3⟩
          apply h1
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact h3
          · exact h2 x hx
      rw [Finset.sum_congr rfl (fun tr _ => hrw tr)]
      have hQ : ∀ (p : P.Prime y.1.val) (tr : GT P s B),
          (∀ x ∈ S, gtSlotCond vals (gtRelabel y.1 y.2 p tr) x) ↔
            (∀ x ∈ S, gtSlotCond vals tr x) := by
        intro p tr
        have hx : ∀ x ∈ S, gtSlotCond vals (gtRelabel y.1 y.2 p tr) x ↔ gtSlotCond vals tr x := by
          intro x hxS
          have hne : x ≠ (y.1, y.2) := by
            rw [Prod.mk.eta]
            rintro rfl
            exact hy hxS
          unfold gtSlotCond
          rw [gtRelabel_batch, gtValAt_relabel_ne _ _ _ _ x hne]
        exact ⟨fun h x hxS => (hx x hxS).mp (h x hxS), fun h x hxS => (hx x hxS).mpr (h x hxS)⟩
      have hstep := ghost_single F n rho i v hv hμ hmass1 s
        (fun tr => ∀ x ∈ S, gtSlotCond vals tr x) y hQ (vals y)
      have hm0 : 0 ≤ muHat F P n y.1 (vals y) := muHat_nonneg F P n hμ _ _
      calc _ ≤ muHat F P n y.1 (vals y) * ∑ tr : GT P s B,
              (if ∀ x ∈ S, gtSlotCond vals tr x then gtTerm F n rho i v s tr else 0) := by
            convert hstep
        _ ≤ muHat F P n y.1 (vals y) * ((∏ x ∈ S, muHat F P n x.1 (vals x)) *
              ∑ tr : GT P s B, gtTerm F n rho i v s tr) :=
            mul_le_mul_of_nonneg_left ih hm0
        _ = _ := by rw [Finset.prod_insert hy]; ring

theorem gtTarget_enc {M B : ℕ} (s t : P.MemoryState M) (ht : P.memorySize t ≤ B)
    (c : GhostChoice s t) (hsd : s.1 = t.1 ∧ s.2.1 = t.2.1) (hc : ghostChoiceValid c) :
    gtTarget s (gtEnc s t ht c) = t :=
  Prod.ext hsd.1 (Prod.ext hsd.2 (funext fun g => (hc g).2))

theorem gtTerm_enc (F : FixedData) (n : ℕ) (rho : ℝ) (i : Fin (n + 1)) {M B : ℕ} (v : ℝ)
    (s t : P.MemoryState M) (ht : P.memorySize t ≤ B)
    (c : GhostChoice s t) (hsd : s.1 = t.1 ∧ s.2.1 = t.2.1) (hc : ghostChoiceValid c) :
    gtTerm F n rho i v s (gtEnc s t ht c) = |ghostChoiceWeight F n rho i c| * P.memoryWeight v t := by
  have htg := gtTarget_enc s t ht c hsd hc
  unfold gtTerm
  rw [if_pos ⟨fun g => (hc g).1, by rw [htg]; exact ht⟩, htg]
  rfl

/-- The conditional weighted ghost row: constrained batch addresses cost a point mass each. -/
theorem ghost_row_constrained (F : FixedData) (J n : ℕ) (rho : ℝ) (i : Fin (n + 1)) (B : ℕ)
    (v : ℝ) (hv : 0 ≤ v)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmass1 : ∀ g : P.BigGroup, 1 ≤ ∑ p : P.Prime g.val, tiltedMu F P n g.val p)
    (Sl : Finset (P.BigGroup × Fin B)) (vals : P.BigGroup × Fin B → ℕ)
    (s : P.MemoryState (J + F.ell)) :
    ∑ t : BoundedMemoryState P (J + F.ell) B,
        ghostK F J n rho i (ghostMult Sl vals) s t.val * P.memoryWeight v t.val ≤
      (∏ x ∈ Sl, muHat F P n x.1 (vals x)) * ∑ t : BoundedMemoryState P (J + F.ell) B,
        absoluteScaledMemoryGhostKernel F J n rho 1 i s t.val * P.memoryWeight v t.val := by
  let mult : GT P s B → ℝ := fun tr => if ∀ x ∈ Sl, gtSlotCond vals tr x then 1 else 0
  have step1 : ∀ t : BoundedMemoryState P (J + F.ell) B,
      ghostK F J n rho i (ghostMult Sl vals) s t.val * P.memoryWeight v t.val =
        ∑ c : GhostChoice s t.val,
          (if (s.1 = t.val.1 ∧ s.2.1 = t.val.2.1) ∧ ghostChoiceValid c then
            gtTerm F n rho i v s (gtEnc s t.val t.property c) *
              mult (gtEnc s t.val t.property c) else 0) := by
    intro t
    unfold ghostK
    by_cases hsd : s.1 = t.val.1 ∧ s.2.1 = t.val.2.1
    · rw [if_pos hsd, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : ghostChoiceValid c
      · rw [if_pos hc, if_pos ⟨hsd, hc⟩, gtTerm_enc F n rho i v s t.val t.property c hsd hc]
        unfold ghostMult
        by_cases hS : ∀ x ∈ Sl, ghostSlotCond vals c x
        · have hS' : ∀ x ∈ Sl, gtSlotCond vals (gtEnc s t.val t.property c) x := hS
          simp only [mult, if_pos hS, if_pos hS']
          ring
        · have hS' : ¬ ∀ x ∈ Sl, gtSlotCond vals (gtEnc s t.val t.property c) x := hS
          simp only [mult, if_neg hS, if_neg hS']
          ring
      · rw [if_neg hc, if_neg (fun h => hc h.2), zero_mul]
    · rw [if_neg hsd, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg (fun h => hsd h.1)]
  have step6 : ∀ t : BoundedMemoryState P (J + F.ell) B,
      absoluteScaledMemoryGhostKernel F J n rho 1 i s t.val * P.memoryWeight v t.val =
        ∑ c : GhostChoice s t.val,
          (if (s.1 = t.val.1 ∧ s.2.1 = t.val.2.1) ∧ ghostChoiceValid c then
            gtTerm F n rho i v s (gtEnc s t.val t.property c) else 0) := by
    intro t
    unfold absoluteScaledMemoryGhostKernel
    by_cases hsd : s.1 = t.val.1 ∧ s.2.1 = t.val.2.1
    · rw [if_pos hsd, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : ghostChoiceValid c
      · rw [if_pos hc, if_pos ⟨hsd, hc⟩, gtTerm_enc F n rho i v s t.val t.property c hsd hc,
          one_pow, mul_one]
      · rw [if_neg hc, if_neg (fun h => hc h.2), zero_mul]
    · rw [if_neg hsd, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg (fun h => hsd h.1)]
  have hT0 := gtTerm_nonneg F n rho i v hv s (B := B)
  calc ∑ t : BoundedMemoryState P (J + F.ell) B,
        ghostK F J n rho i (ghostMult Sl vals) s t.val * P.memoryWeight v t.val
      = ∑ tr : GT P s B, (if gtValid tr ∧ P.memorySize (gtTarget s tr) ≤ B then
          gtTerm F n rho i v s tr * mult tr else 0) := by
        rw [Finset.sum_congr rfl (fun t _ => step1 t)]
        exact ghost_transfer s (fun tr => gtTerm F n rho i v s tr * mult tr)
    _ = ∑ tr : GT P s B,
          (if ∀ x ∈ Sl, gtSlotCond vals tr x then gtTerm F n rho i v s tr else 0) := by
        apply Finset.sum_congr rfl
        intro tr _
        by_cases hvb : gtValid tr ∧ P.memorySize (gtTarget s tr) ≤ B
        · rw [if_pos hvb]
          by_cases hS : ∀ x ∈ Sl, gtSlotCond vals tr x
          · simp only [mult, if_pos hS, mul_one]
          · simp only [mult, if_neg hS, mul_zero]
        · have hz : gtTerm F n rho i v s tr = 0 := by unfold gtTerm; rw [if_neg hvb]
          rw [if_neg hvb, hz]
          split_ifs <;> rfl
    _ ≤ (∏ x ∈ Sl, muHat F P n x.1 (vals x)) * ∑ tr : GT P s B, gtTerm F n rho i v s tr :=
        ghost_slots F n rho i v hv hμ hmass1 s vals Sl
    _ = _ := by
        congr 1
        rw [Finset.sum_congr rfl (fun t _ => step6 t), ghost_transfer s (gtTerm F n rho i v s)]
        apply Finset.sum_congr rfl
        intro tr _
        by_cases hvb : gtValid tr ∧ P.memorySize (gtTarget s tr) ≤ B
        · rw [if_pos hvb]
        · have hz : gtTerm F n rho i v s tr = 0 := by unfold gtTerm; rw [if_neg hvb]
          rw [if_neg hvb, hz]

end Erdos821.P3High
