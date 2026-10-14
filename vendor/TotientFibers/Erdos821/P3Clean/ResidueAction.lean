import Erdos821.P3Clean.CyclicAction
import Erdos821.P3Clean.Truncation

/-! Uniform small residues and cutoff multiset memory carry a finite translation action. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

variable {P : PrimeGroups}

abbrev PendingState (P : PrimeGroups) := P.SmallResidues × ((g : P.BigGroup) → P.Memory g.val)

def pendingSize (s : PendingState P) : ℕ := ∑ g : P.BigGroup, (s.2 g).card

abbrev CutPendingState (P : PrimeGroups) (B : ℕ) := {s : PendingState P // pendingSize s ≤ B}

instance finite_cutPendingState (P : PrimeGroups) (B : ℕ) : Finite (CutPendingState P B) := by
  let encode (s : CutPendingState P B) :
      P.SmallResidues × ((g : P.BigGroup) → {z : P.Memory g.val // z.card ≤ B}) :=
    (s.val.1, fun g => ⟨s.val.2 g, by
      exact (Finset.single_le_sum (fun h _ => Nat.zero_le ((s.val.2 h).card))
        (Finset.mem_univ g)).trans s.property⟩)
  apply Finite.of_injective encode
  intro s t h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun c => c.1) h
  · funext g
    exact congrArg (fun c => (c.2 g).val) h

theorem translateParticle_add (a b : ℤ) {g : P.Group} (z : P.Particle g) :
    translateParticle a (translateParticle b z) = translateParticle (a + b) z := by
  rcases z with ⟨p, r⟩
  simp only [translateParticle]
  congr 1
  push_cast
  abel

theorem translateParticle_zero {g : P.Group} (z : P.Particle g) : translateParticle 0 z = z := by
  rcases z with ⟨p, r⟩
  simp [translateParticle]

theorem translateMemory_add (a b : ℤ) {g : P.Group} (z : P.Memory g) :
    translateMemory a (translateMemory b z) = translateMemory (a + b) z := by
  simp only [translateMemory, Multiset.map_map]
  congr 1
  funext p
  exact translateParticle_add a b p

theorem translateMemory_zero {g : P.Group} (z : P.Memory g) : translateMemory 0 z = z := by
  unfold translateMemory
  simpa only [translateParticle_zero] using Multiset.map_id' z

theorem translateSmallResidues_add (a b : ℤ) (y : P.SmallResidues) :
    translateSmallResidues a (translateSmallResidues b y) = translateSmallResidues (a + b) y := by
  funext g p
  simp only [translateSmallResidues]
  push_cast
  abel

theorem translateSmallResidues_zero (y : P.SmallResidues) : translateSmallResidues 0 y = y := by
  funext g p
  simp [translateSmallResidues]

def translatePending (delta : ℤ) (s : PendingState P) : PendingState P :=
  (translateSmallResidues delta s.1, fun g => translateMemory delta (s.2 g))

theorem translatePending_size (delta : ℤ) (s : PendingState P) :
    pendingSize (translatePending delta s) = pendingSize s := by
  simp only [pendingSize, translatePending, translateMemory_card]

theorem translatePending_add (a b : ℤ) (s : PendingState P) :
    translatePending a (translatePending b s) = translatePending (a + b) s := by
  apply Prod.ext
  · exact translateSmallResidues_add a b s.1
  · funext g
    exact translateMemory_add a b (s.2 g)

theorem translatePending_zero (s : PendingState P) : translatePending 0 s = s := by
  apply Prod.ext
  · exact translateSmallResidues_zero s.1
  · funext g
    exact translateMemory_zero (s.2 g)

def pendingTranslationEquiv (B : ℕ) (delta : ℤ) : Equiv.Perm (CutPendingState P B) where
  toFun s := ⟨translatePending delta s.val, by simpa only [translatePending_size] using s.property⟩
  invFun s := ⟨translatePending (-delta) s.val, by simpa only [translatePending_size] using s.property⟩
  left_inv := by
    intro s
    apply Subtype.ext
    exact (translatePending_add (-delta) delta s.val).trans
      (by simpa only [neg_add_cancel] using translatePending_zero s.val)
  right_inv := by
    intro s
    apply Subtype.ext
    exact (translatePending_add delta (-delta) s.val).trans
      (by simpa only [add_neg_cancel] using translatePending_zero s.val)

theorem pendingTranslationEquiv_add (B : ℕ) (a b : ℤ) :
    pendingTranslationEquiv (P := P) B (a + b) =
      pendingTranslationEquiv B a * pendingTranslationEquiv B b := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  exact (translatePending_add a b s.val).symm

theorem pendingTranslationEquiv_zero (B : ℕ) :
    pendingTranslationEquiv (P := P) B 0 = 1 := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  exact translatePending_zero s.val

def pendingTranslationHom (B : ℕ) : ℤ →+ Additive (Equiv.Perm (CutPendingState P B)) where
  toFun delta := Additive.ofMul (pendingTranslationEquiv B delta)
  map_zero' := congrArg Additive.ofMul (pendingTranslationEquiv_zero B)
  map_add' a b := congrArg Additive.ofMul (pendingTranslationEquiv_add B a b)

theorem pendingTranslationEquiv_zpow (B : ℕ) (delta : ℤ) :
    pendingTranslationEquiv (P := P) B delta = pendingTranslationEquiv B 1 ^ delta := by
  have h := (pendingTranslationHom (P := P) B).map_zsmul delta 1
  have hh := congrArg Additive.toMul h
  simpa [zsmul_eq_mul, pendingTranslationHom, toMul_zsmul] using hh

def pendingMass (F : FixedData) (n : ℕ) (s : PendingState P) : ℝ :=
  (Fintype.card P.SmallResidues : ℝ)⁻¹ *
    ∏ g : P.BigGroup, P.groupMemoryMass F n g.val (s.2 g)

theorem pendingMass_translate (F : FixedData) (n : ℕ) (delta : ℤ) (s : PendingState P) :
    pendingMass F n (translatePending delta s) = pendingMass F n s := by
  simp only [pendingMass, translatePending, translateMemory_groupMass]


end Erdos821.P3Clean
