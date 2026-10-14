import Erdos821.P3Clean.Damping

/-! Counting the ell-slot extensions of a fixed ordered small prefix. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups} {g : P.Group}

def smallPrefixFibre (J ell : ℕ) (y : (p : P.Prime g) → ZMod p.val)
    (d : Fin J → P.Prime g) : Finset (Fin (J + ell) → P.Prime g) :=
  Finset.univ.filter (fun a => Function.Injective a ∧ (∀ i, y (a i) = 0) ∧
    ∀ j : Fin J, a (Fin.castAdd ell j) = d j)

theorem smallPrefixFibre_nonempty (J ell : ℕ) (y : (p : P.Prime g) → ZMod p.val)
    (d : Fin J → P.Prime g) (h : (smallPrefixFibre J ell y d).Nonempty) :
    Function.Injective d ∧ (∀ j, y (d j) = 0) ∧
      J + ell ≤ (Finset.univ.filter (fun p : P.Prime g => y p = 0)).card := by
  classical
  obtain ⟨a, ha⟩ := h
  obtain ⟨hinj, hzero, hprefix⟩ := (Finset.mem_filter.mp ha).2
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val (hinj ((hprefix i).trans (hij.trans (hprefix j).symm)))
    exact hh
  · intro j
    rw [← hprefix j]
    exact hzero _
  · have hcard : (Finset.univ.image a).card = J + ell := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    rw [← hcard]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero _⟩

theorem smallPrefixFibre_card (J ell : ℕ) (y : (p : P.Prime g) → ZMod p.val)
    (d : Fin J → P.Prime g) (hd : Function.Injective d) (hy : ∀ j, y (d j) = 0) :
    (smallPrefixFibre J ell y d).card ≤
      ((Finset.univ.filter (fun p : P.Prime g => y p = 0)).card - J).descFactorial ell := by
  classical
  let Z := Finset.univ.filter (fun p : P.Prime g => y p = 0)
  let D := Finset.univ.image d
  let B := Z \ D
  have hDZ : D ⊆ Z := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy j⟩
  have hD : D.card = J := by
    rw [Finset.card_image_of_injective _ hd]
    simp
  have hB : B.card = Z.card - J := by
    rw [Finset.card_sdiff_of_subset hDZ, hD]
  let suffix : {a // a ∈ smallPrefixFibre J ell y d} → (Fin ell ↪ {p // p ∈ B}) :=
    fun a => {
      toFun := fun i => ⟨a.val (Fin.natAdd J i), by
        obtain ⟨ha, hzero, hprefix⟩ := (Finset.mem_filter.mp a.property).2
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero _⟩, ?_⟩
        intro hp
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp
        have heq : Fin.castAdd ell j = Fin.natAdd J i := ha ((hprefix j).trans hj)
        have hv := congrArg Fin.val heq
        simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hv
        omega⟩
      inj' := by
        intro i j hij
        obtain ⟨ha, _, _⟩ := (Finset.mem_filter.mp a.property).2
        have hh := ha (congrArg Subtype.val hij)
        apply Fin.ext
        have hv := congrArg Fin.val hh
        simp only [Fin.coe_natAdd] at hv
        omega
    }
  have hinj : Function.Injective suffix := by
    intro a b hab
    apply Subtype.ext
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have ha := ((Finset.mem_filter.mp a.property).2).2.2 j
      have hb := ((Finset.mem_filter.mp b.property).2).2.2 j
      exact ha.trans hb.symm
    · exact congrArg Subtype.val (congrArg (fun f : Fin ell ↪ {p // p ∈ B} => f j) hab)
  have hc := Fintype.card_le_of_injective suffix hinj
  simpa only [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_fin, hB] using hc


end Erdos821.P3Clean
