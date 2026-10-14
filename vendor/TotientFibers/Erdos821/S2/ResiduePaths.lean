import Erdos821.S2.MemoryEdge

/-! Literal finite alternating paths, before independent residues are averaged. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

structure ResiduePath (A : Model F P J m) (n : ℕ) where
  labels : Fin (n + 1) → P.Labels (J + F.ell)
  sourcePerm : Fin n → P.Permutations (J + F.ell)
  targetPerm : Fin n → P.Permutations (J + F.ell)
  pattern : Fin n → Fin A.patternCount
  free : Fin n → P.Aux J

instance (A : Model F P J m) (n : ℕ) : Fintype (ResiduePath A n) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (n + 1) → P.Labels (J + F.ell)) ×
      (Fin n → P.Permutations (J + F.ell)) ×
      (Fin n → P.Permutations (J + F.ell)) ×
      (Fin n → Fin A.patternCount) × (Fin n → P.Aux J))
    { toFun := fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2⟩
      invFun := fun Q => ⟨Q.labels, Q.sourcePerm, Q.targetPerm, Q.pattern, Q.free⟩
      left_inv := fun v => by rcases v with ⟨a, b, c, d, e⟩; rfl
      right_inv := fun Q => by cases Q; rfl }

namespace ResiduePath

variable {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n)

def source (i : Fin n) : P.Labels (J + F.ell) := P.act (Q.sourcePerm i) (Q.labels i.castSucc)
def target (i : Fin n) : P.Labels (J + F.ell) := P.act (Q.targetPerm i) (Q.labels i.succ)
def step (i : Fin n) : ℤ := edgeDelta A (A.pattern (Q.pattern i)) (edgeForward i) (Q.source i) (Q.free i)
def offset (i : Fin (n + 1)) : ℤ := ∑ e : Fin n, if e.val < i.val then Q.step e else 0

def active (i : Fin (n + 1)) : Finset ℕ :=
  Finset.univ.biUnion (fun g : P.Group => Finset.univ.image (fun h => (Q.labels i g h).val))

def Valid : Prop :=
  (∀ i g, Function.Injective (Q.labels i g)) ∧
  (∀ i, (A.pattern (Q.pattern i)).compatible (Q.source i) (Q.target i) ∧
    (A.pattern (Q.pattern i)).ban (Q.source i) (Q.target i) (Q.free i))

def edgeCoefficient (theta : ℝ) (i : Fin n) : ℂ :=
  let ν := A.pattern (Q.pattern i)
  let D := ν.D (Q.source i) (Q.free i)
  let uBig : P.BigAux J := fun g => Q.free i g.val
  let z := ν.coefficient (P.restrictBig (Q.source i)) (P.restrictBig (Q.target i)) uBig *
    imaginaryPower D A.zeta
  let zr := star (ν.coefficient (P.restrictBig (Q.target i)) (P.restrictBig (Q.source i)) uBig *
    imaginaryPower D A.zeta)
  (edgeSymmetryFactor P (J + F.ell) * ν.auxMass (Q.free i) * ν.physicalTargetMass : ℝ) *
    (if edgeForward i then z else zr) * phase (theta * (Q.step i : ℝ))

def Weight (theta : ℝ) : ℂ :=
  (P.markMass (J + F.ell) : ℂ) * (∏ i, Q.edgeCoefficient theta i) *
    (P.residueExpectation n (visitQ F.q n) Q.offset Q.active : ℂ)

theorem offset_zero : Q.offset 0 = 0 := by
  simp [offset]

theorem active_subset (i : Fin (n + 1)) : Q.active i ⊆ P.allPrimes := by
  intro p hp
  obtain ⟨g, _, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, (Q.labels i g h).property⟩

theorem active_card_le (i : Fin (n + 1)) : (Q.active i).card ≤ (J + F.ell) * P.count := by
  calc
    _ ≤ ∑ g : P.Group, (Finset.univ.image (fun h => (Q.labels i g h).val)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _g : P.Group, (J + F.ell) := by
      apply Finset.sum_le_sum
      intro g _
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin (J + F.ell))))
        (f := fun h => (Q.labels i g h).val)
    _ = _ := by simp [PrimeGroups.Group, Nat.mul_comm]

end ResiduePath

/-- All orientations, permutations, patterns and free draws remain inside this sum. -/
def residueExpression (A : Model F P J m) (n : ℕ) (theta : ℝ) : ℂ :=
  ∑ Q : ResiduePath A n, if Q.Valid then Q.Weight theta else 0


end Erdos821.S2Core
