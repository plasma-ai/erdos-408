import Erdos821.S2.MemoryEdge

/-! Expanded histories record births before global distinctness is imposed. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- At each visit, before/after refer to the ghost operation.
Edges go from `after i.castSucc` to `before i.succ`. -/
structure MemoryHistory (A : Model F P J m) (n : ℕ) where
  before : Fin (n + 1) → P.MemoryState (J + F.ell)
  after : Fin (n + 1) → P.MemoryState (J + F.ell)
  ghost : (i : Fin (n + 1)) → GhostChoice (before i) (after i)
  edge : (i : Fin n) → EdgeChoice A (after i.castSucc)

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

def Valid : Prop :=
  (∀ g, (H.before 0).2.2 g = 0) ∧
  (∀ g, (H.after (Fin.last n)).2.2 g = 0) ∧
  (∀ i, (H.before i).1 = (H.after i).1 ∧
    (H.before i).2.1 = (H.after i).2.1 ∧ ghostChoiceValid (H.ghost i)) ∧
  (∀ i, edgeChoiceValid A .all i (H.after i.castSucc) (H.before i.succ) (H.edge i))

def Truncated (B : ℕ) : Prop :=
  ∀ i, P.memorySize (H.before i) ≤ B ∧ P.memorySize (H.after i) ≤ B

def initialBirthValues : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ i : Fin (J + F.ell), {((H.before 0).2.1 g.val i).val}

def ghostBirthValues (i : Fin (n + 1)) : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ h : Fin ((H.ghost i).2.1 g).val, {((H.ghost i).2.2 g h).val}

def freshTargetSlots (i : Fin n) (g : P.BigGroup) : Finset (Fin (J + F.ell)) :=
  Finset.univ.filter (fun h => ¬ (A.pattern (H.edge i).2.2.1).shared g.val h ∧
    h ∉ (H.edge i).2.2.2.2.2.1 g)

def freshBirthValues (i : Fin n) : Multiset ℕ :=
  ∑ g : P.BigGroup, ∑ h ∈ H.freshTargetSlots i g,
    {((permuteActive (H.edge i).2.1 (H.before i.succ)).2.1 g.val h).val}

/-- Initial slots, fresh target slots and ghost batches; auxiliary draws are absent. -/
def birthValues : Multiset ℕ :=
  H.initialBirthValues + ∑ i, H.ghostBirthValues i + ∑ i, H.freshBirthValues i

def DistinctBirths : Prop := H.birthValues.Nodup

def totalGhostBirths : ℕ := ∑ i, ghostBirthCount (H.ghost i)

def Weight (rho theta : ℝ) : ℂ :=
  (P.memoryMass F J n (H.before 0) : ℂ) *
    (∏ i : Fin (n + 1), (ghostChoiceWeight F n rho i (H.ghost i) : ℂ)) *
    (∏ i : Fin n, (edgeSymmetryFactor P (J + F.ell) : ℂ) *
      edgeChoiceCoefficient A n rho theta i (H.after i.castSucc) (H.before i.succ) (H.edge i))

end MemoryHistory

/-- This is a sum over individual histories, with global birth distinctness
inside the expansion. Summability must be proved before tsum manipulations. -/
def distinctMemoryExpression (A : Model F P J m) (n : ℕ) (rho theta : ℝ) : ℂ :=
  ∑' H : MemoryHistory A n, if H.Valid ∧ H.DistinctBirths then H.Weight rho theta else 0

/-- Fixed potential addresses after memory truncation. -/
abbrev BirthAddress (P : PrimeGroups) (M n B : ℕ) :=
  (P.BigGroup × Fin M) ⊕ ((Fin n × P.BigGroup × Fin M) ⊕
    (Fin (n + 1) × P.BigGroup × Fin B))

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

def addressPerformed (B : ℕ) : BirthAddress P (J + F.ell) n B → Prop
  | .inl _ => True
  | .inr (.inl (i, g, h)) => h ∈ H.freshTargetSlots i g
  | .inr (.inr (i, g, h)) => h.val < ((H.ghost i).2.1 g).val

def addressValue (B : ℕ) : BirthAddress P (J + F.ell) n B → ℕ
  | .inl (g, h) => ((H.before 0).2.1 g.val h).val
  | .inr (.inl (i, g, h)) =>
      ((permuteActive (H.edge i).2.1 (H.before i.succ)).2.1 g.val h).val
  | .inr (.inr (i, g, h)) =>
      if hh : h.val < ((H.ghost i).2.1 g).val then ((H.ghost i).2.2 g ⟨h.val, hh⟩).val else 0

end MemoryHistory

theorem birthAddress_card (P : PrimeGroups) (M n B : ℕ) :
    Fintype.card (BirthAddress P M n B) =
      M * Fintype.card P.BigGroup * (n + 1) +
        (n + 1) * Fintype.card P.BigGroup * B := by
  simp only [BirthAddress, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring


end Erdos821.S2Core
