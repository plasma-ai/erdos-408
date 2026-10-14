import Erdos821.S2High.PivotAddresses

noncomputable section

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m n B : ℕ} {A : Model F P J m}

abbrev BirthAddressFin (P : PrimeGroups) (M n B : ℕ) :=
  Fin (Fintype.card (Erdos821.S2Core.BirthAddress P M n B))

def blockPivotIndex (pi : Finset (Finset (BirthAddressFin P (J + F.ell) n B)))
    (hpi : BirthCollection pi) (C : {C : Finset (BirthAddressFin P (J + F.ell) n B) // C ∈ pi}) :
    BirthAddressFin P (J + F.ell) n B :=
  birthBlockPivot C.val (Finset.card_pos.mp (by
    have hcard := hpi.1 C.val C.property
    omega))

def blockPivotGroup (pi : Finset (Finset (BirthAddressFin P (J + F.ell) n B)))
    (hpi : BirthCollection pi) (C : {C : Finset (BirthAddressFin P (J + F.ell) n B) // C ∈ pi}) :
    P.BigGroup :=
  birthAddressGroup ((Fintype.equivFin
    (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm (blockPivotIndex pi hpi C))

def PivotAssignment (pi : Finset (Finset (BirthAddressFin P (J + F.ell) n B)))
    (hpi : BirthCollection pi) :=
  (C : {C : Finset (BirthAddressFin P (J + F.ell) n B) // C ∈ pi}) →
    P.Prime (blockPivotGroup pi hpi C)

def PivotCompatible (H : Erdos821.S2Core.MemoryHistory A n)
    (pi : Finset (Finset (BirthAddressFin P (J + F.ell) n B)))
    (hpi : BirthCollection pi) (values : PivotAssignment pi hpi) : Prop :=
  ∀ C : {C : Finset (BirthAddressFin P (J + F.ell) n B) // C ∈ pi},
    ∀ j ∈ C.val,
      H.addressPerformed B ((Fintype.equivFin
        (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j) ∧
      H.addressValue B ((Fintype.equivFin
        (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j) = (values C).val

theorem birthEvent_iff_exists_pivotAssignment
    (H : Erdos821.S2Core.MemoryHistory A n)
    (pi : Finset (Finset (BirthAddressFin P (J + F.ell) n B)))
    (hpi : BirthCollection pi) :
    birthEvent (H.performedFin B) (H.valueFin B) pi ↔
      ∃ values : PivotAssignment pi hpi, PivotCompatible H pi hpi values := by
  classical
  constructor
  · intro he
    let values : PivotAssignment pi hpi := fun C =>
      ⟨H.valueFin B (blockPivotIndex pi hpi C), by
        have hpivotMem : blockPivotIndex pi hpi C ∈ C.val := by
          exact birthBlockPivot_mem _ _
        have hperf : blockPivotIndex pi hpi C ∈ H.performedFin B :=
          (he C.val C.property).1 hpivotMem
        have haddr : H.addressPerformed B ((Fintype.equivFin
            (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm
              (blockPivotIndex pi hpi C)) := by
          simpa [Erdos821.S2Core.MemoryHistory.performedFin] using hperf
        change H.addressValue B ((Fintype.equivFin
          (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm
            (blockPivotIndex pi hpi C)) ∈ P.primes (blockPivotGroup pi hpi C).val
        exact addressValue_mem_group H _ haddr⟩
    refine ⟨values, ?_⟩
    intro C j hj
    have hpivotMem : blockPivotIndex pi hpi C ∈ C.val := birthBlockPivot_mem _ _
    have hperf : j ∈ H.performedFin B := (he C.val C.property).1 hj
    have haddr : H.addressPerformed B ((Fintype.equivFin
        (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j) := by
      simpa [Erdos821.S2Core.MemoryHistory.performedFin] using hperf
    have hEq : H.valueFin B j = H.valueFin B (blockPivotIndex pi hpi C) :=
      (he C.val C.property).2 j hj (blockPivotIndex pi hpi C) hpivotMem
    refine ⟨haddr, ?_⟩
    change H.valueFin B j = H.valueFin B (blockPivotIndex pi hpi C)
    exact hEq
  · rintro ⟨values, hv⟩
    intro C hC
    constructor
    · intro j hj
      simpa [Erdos821.S2Core.MemoryHistory.performedFin] using (hv ⟨C, hC⟩ j hj).1
    · intro i hi j hj
      have hiEq : H.valueFin B i = (values ⟨C, hC⟩).val := by
        simpa [Erdos821.S2Core.MemoryHistory.valueFin] using (hv ⟨C, hC⟩ i hi).2
      have hjEq : H.valueFin B j = (values ⟨C, hC⟩).val := by
        simpa [Erdos821.S2Core.MemoryHistory.valueFin] using (hv ⟨C, hC⟩ j hj).2
      exact hiEq.trans hjEq.symm


end Erdos821.S2High
