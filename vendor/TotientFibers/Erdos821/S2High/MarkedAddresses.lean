import Erdos821.S2High.PivotAssignments

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m n B : ℕ} {A : Model F P J m}

local notation "PivotAddrFin" => BirthAddressFin P (J + F.ell) n B
local notation "PivotAddr" => Erdos821.S2Core.BirthAddress P (J + F.ell) n B
abbrev PivotBlocks (pi : Finset (Finset PivotAddrFin)) := {C : Finset PivotAddrFin // C ∈ pi}

def performedAddressSet (pi : Finset (Finset PivotAddrFin)) : Finset PivotAddrFin :=
  pi.biUnion id

def blockContaining (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (j : PivotAddrFin) (hj : j ∈ performedAddressSet pi) : PivotBlocks pi := by
  classical
  let h := Finset.mem_biUnion.mp hj
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem blockContaining_mem (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (j : PivotAddrFin) (hj : j ∈ performedAddressSet pi) :
    j ∈ (blockContaining pi hpi j hj).val := by
  classical
  exact (Classical.choose_spec (Finset.mem_biUnion.mp hj)).2

theorem blockContaining_eq (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (j : PivotAddrFin) (hj : j ∈ performedAddressSet pi)
    (C : Finset PivotAddrFin) (hC : C ∈ pi) (hjC : j ∈ C) :
    blockContaining pi hpi j hj = ⟨C, hC⟩ := by
  apply Subtype.ext
  by_contra hne
  have hdis := hpi.2 (blockContaining pi hpi j hj).property hC hne
  exact (Finset.disjoint_left.mp hdis (blockContaining_mem pi hpi j hj)) hjC

def pivotValueAtAddress (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (values : PivotAssignment pi hpi) (j : PivotAddrFin)
    (hj : j ∈ performedAddressSet pi) : ℕ :=
  (values (blockContaining pi hpi j hj)).val

theorem pivotValueAtAddress_eq (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (values : PivotAssignment pi hpi) (j : PivotAddrFin)
    (hj : j ∈ performedAddressSet pi) (C : Finset PivotAddrFin)
    (hC : C ∈ pi) (hjC : j ∈ C) :
    pivotValueAtAddress pi hpi values j hj = (values ⟨C, hC⟩).val := by
  unfold pivotValueAtAddress
  rw [blockContaining_eq pi hpi j hj C hC hjC]

def addressIndex (a : PivotAddr) : PivotAddrFin := Fintype.equivFin PivotAddr a

def edgeAddress (i : Fin n) (g : P.BigGroup) (h : Fin (J + F.ell)) : PivotAddr :=
  .inr (.inl (i, g, h))

def ghostAddress (i : Fin (n + 1)) (g : P.BigGroup) (h : Fin B) : PivotAddr :=
  .inr (.inr (i, g, h))

def initialAddress (g : P.BigGroup) (h : Fin (J + F.ell)) : PivotAddr := .inl (g, h)

def markedEdgeSlots (pi : Finset (Finset PivotAddrFin)) (i : Fin n) :
    Finset (P.BigGroup × Fin (J + F.ell)) :=
  Finset.univ.filter (fun gh => addressIndex (edgeAddress i gh.1 gh.2) ∈ performedAddressSet pi)

def markedGhostSlots (pi : Finset (Finset PivotAddrFin)) (i : Fin (n + 1)) :
    Finset (P.BigGroup × Fin B) :=
  Finset.univ.filter (fun gh => addressIndex (ghostAddress i gh.1 gh.2) ∈ performedAddressSet pi)

def markedInitialSlots (pi : Finset (Finset PivotAddrFin)) :
    Finset (P.BigGroup × Fin (J + F.ell)) :=
  Finset.univ.filter (fun gh => addressIndex (initialAddress gh.1 gh.2) ∈ performedAddressSet pi)

def markedEdgeValue (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (values : PivotAssignment pi hpi) (i : Fin n) (g : P.BigGroup)
    (h : Fin (J + F.ell))
    (hm : (g, h) ∈ markedEdgeSlots pi i) : ℕ :=
  pivotValueAtAddress pi hpi values (addressIndex (edgeAddress i g h))
    (Finset.mem_filter.mp hm).2

def markedGhostValue (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (values : PivotAssignment pi hpi) (i : Fin (n + 1)) (g : P.BigGroup)
    (h : Fin B) (hm : (g, h) ∈ markedGhostSlots pi i) : ℕ :=
  pivotValueAtAddress pi hpi values (addressIndex (ghostAddress i g h))
    (Finset.mem_filter.mp hm).2

def markedInitialValue (pi : Finset (Finset PivotAddrFin)) (hpi : BirthCollection pi)
    (values : PivotAssignment pi hpi) (g : P.BigGroup)
    (h : Fin (J + F.ell)) (hm : (g, h) ∈ markedInitialSlots pi) : ℕ :=
  pivotValueAtAddress pi hpi values (addressIndex (initialAddress g h))
    (Finset.mem_filter.mp hm).2


end Erdos821.S2High
