import Erdos821.P3High.HistoryPath
import Erdos821.P3High.Relabel

/-! Replacing one big active label of a memory state, and its effect on tilted products. -/

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
open Erdos821.S2Core

variable {P : PrimeGroups}

/-- Replace the label of big group `g` at slot `h`. -/
def relabelLabels {M : ℕ} (a : P.Labels M) (g : P.BigGroup) (h : Fin M) (p : P.Prime g.val) :
    P.Labels M :=
  Function.update a g.val (Function.update (a g.val) h p)

def relabelState {M : ℕ} (g : P.BigGroup) (h : Fin M) (p : P.Prime g.val)
    (t : P.MemoryState M) : P.MemoryState M :=
  (t.1, relabelLabels t.2.1 g h p, t.2.2)

theorem relabelLabels_self {M : ℕ} (a : P.Labels M) (g : P.BigGroup) (h : Fin M)
    (p : P.Prime g.val) : relabelLabels a g h p g.val h = p := by
  simp [relabelLabels]

theorem relabelLabels_ne_group {M : ℕ} (a : P.Labels M) (g : P.BigGroup) (h : Fin M)
    (p : P.Prime g.val) (g' : P.Group) (hg : g' ≠ g.val) :
    relabelLabels a g h p g' = a g' := by
  simp [relabelLabels, Function.update_of_ne hg]

theorem relabelLabels_ne_slot {M : ℕ} (a : P.Labels M) (g : P.BigGroup) (h : Fin M)
    (p : P.Prime g.val) (i : Fin M) (hi : i ≠ h) :
    relabelLabels a g h p g.val i = a g.val i := by
  simp [relabelLabels, Function.update_of_ne hi]

/-- Away from the replaced big slot every label is unchanged. -/
theorem relabelLabels_of_ne {M : ℕ} (a : P.Labels M) (g : P.BigGroup) (h : Fin M)
    (p : P.Prime g.val) (g' : P.BigGroup) (i : Fin M) (hx : (g', i) ≠ (g, h)) :
    relabelLabels a g h p g'.val i = a g'.val i := by
  by_cases hg : g' = g
  · subst hg
    have hi : i ≠ h := fun hi => hx (by rw [hi])
    exact relabelLabels_ne_slot a g' h p i hi
  · have hg' : g'.val ≠ g.val := fun he => hg (Subtype.ext he)
    rw [relabelLabels_ne_group a g h p g'.val hg']

theorem relabelLabels_relabel {M : ℕ} (a : P.Labels M) (g : P.BigGroup) (h : Fin M)
    (p q : P.Prime g.val) :
    relabelLabels (relabelLabels a g h q) g h p = relabelLabels a g h p := by
  funext g' i
  by_cases hg : g' = g.val
  · subst hg
    by_cases hi : i = h
    · subst hi
      simp only [relabelLabels_self]
    · rw [relabelLabels_ne_slot _ g h p i hi, relabelLabels_ne_slot _ g h q i hi,
        relabelLabels_ne_slot _ g h p i hi]
  · rw [relabelLabels_ne_group _ g h p g' hg, relabelLabels_ne_group _ g h q g' hg,
      relabelLabels_ne_group _ g h p g' hg]

theorem relabelLabels_eq_self {M : ℕ} (a : P.Labels M) (g : P.BigGroup) (h : Fin M) :
    relabelLabels a g h (a g.val h) = a := by
  funext g' i
  by_cases hg : g' = g.val
  · subst hg
    by_cases hi : i = h
    · subst hi
      simp only [relabelLabels_self]
    · rw [relabelLabels_ne_slot _ g h _ i hi]
  · rw [relabelLabels_ne_group _ g h _ g' hg]

theorem relabelState_relabel {M : ℕ} (g : P.BigGroup) (h : Fin M) (p q : P.Prime g.val)
    (t : P.MemoryState M) :
    relabelState g h p (relabelState g h q t) = relabelState g h p t := by
  simp only [relabelState, relabelLabels_relabel]

theorem relabelState_eq_self {M : ℕ} (g : P.BigGroup) (h : Fin M) (t : P.MemoryState M) :
    relabelState g h (t.2.1 g.val h) t = t := by
  simp only [relabelState, relabelLabels_eq_self]

theorem memorySize_relabelState {M : ℕ} (g : P.BigGroup) (h : Fin M) (p : P.Prime g.val)
    (t : P.MemoryState M) : P.memorySize (relabelState g h p t) = P.memorySize t := rfl

theorem memoryWeight_relabelState {M : ℕ} (v : ℝ) (g : P.BigGroup) (h : Fin M)
    (p : P.Prime g.val) (t : P.MemoryState M) :
    P.memoryWeight v (relabelState g h p t) = P.memoryWeight v t := rfl

/-- Relabelling on the bounded state type. -/
def relabelB {M B : ℕ} (g : P.BigGroup) (h : Fin M) (p : P.Prime g.val)
    (t : BoundedMemoryState P M B) : BoundedMemoryState P M B :=
  ⟨relabelState g h p t.val, t.property⟩

/-- Relabelling commutes with the endpoint permutation, moving the slot. -/
theorem permuteActive_relabel {M : ℕ} (τ : P.Permutations M) (g : P.BigGroup) (h : Fin M)
    (p : P.Prime g.val) (t : P.MemoryState M) :
    permuteActive τ (relabelState g (τ g.val h) p t) =
      relabelState g h p (permuteActive τ t) := by
  simp only [permuteActive, relabelState, Prod.mk.injEq, true_and, and_true]
  funext g' i
  show relabelLabels t.2.1 g (τ g.val h) p g' (τ g' i) = relabelLabels (P.act τ t.2.1) g h p g' i
  by_cases hg : g' = g.val
  · subst hg
    by_cases hi : i = h
    · subst hi
      simp only [relabelLabels_self]
    · have hti : τ g.val i ≠ τ g.val h := fun he => hi ((τ g.val).injective he)
      rw [relabelLabels_ne_slot _ g _ p _ hti, relabelLabels_ne_slot _ g h p i hi]
      rfl
  · rw [relabelLabels_ne_group _ g _ p g' hg, relabelLabels_ne_group _ g h p g' hg]
    rfl

theorem prod_update_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (x : ι) (a : ℝ) :
    (∏ y, Function.update f x a y) * f x = (∏ y, f y) * a := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ x),
    Finset.prod_eq_mul_prod_diff_singleton x f (fun hx => (hx (Finset.mem_univ x)).elim)]
  ring

/-- A product of tilted label masses over unconditioned big slots scales at the replaced slot. -/
theorem tilted_prod_relabel (F : FixedData) (n : ℕ) {M : ℕ}
    (cond : P.BigGroup × Fin M → Prop) (a : P.Labels M) (g : P.BigGroup) (h : Fin M)
    (p : P.Prime g.val) (hc : ¬ cond (g, h)) :
    (∏ x : P.BigGroup × Fin M,
        if cond x then (1 : ℝ) else tiltedMu F P n x.1.val (relabelLabels a g h p x.1.val x.2)) *
      tiltedMu F P n g.val (a g.val h) =
    (∏ x : P.BigGroup × Fin M,
        if cond x then (1 : ℝ) else tiltedMu F P n x.1.val (a x.1.val x.2)) *
      tiltedMu F P n g.val p := by
  let f : P.BigGroup × Fin M → ℝ := fun x =>
    if cond x then (1 : ℝ) else tiltedMu F P n x.1.val (a x.1.val x.2)
  have hpt : (fun x : P.BigGroup × Fin M =>
      if cond x then (1 : ℝ) else tiltedMu F P n x.1.val (relabelLabels a g h p x.1.val x.2)) =
      Function.update f (g, h) (tiltedMu F P n g.val p) := by
    funext x
    by_cases hx : x = (g, h)
    · subst hx
      simp only [Function.update_self, if_neg hc, relabelLabels_self]
    · rw [Function.update_of_ne hx]
      simp only [f]
      rcases x with ⟨g', i⟩
      rw [relabelLabels_of_ne a g h p g' i hx]
  have hf : f (g, h) = tiltedMu F P n g.val (a g.val h) := if_neg hc
  rw [hpt, ← hf]
  exact prod_update_mul f (g, h) _

end Erdos821.P3High
