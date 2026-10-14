import Erdos821.S2High.AddressHelpers

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

def birthBlockPivot {a : ℕ} (B : Finset (Fin a)) (hB : B.Nonempty) : Fin a :=
  Classical.choose hB

theorem birthBlockPivot_mem {a : ℕ} (B : Finset (Fin a)) (hB : B.Nonempty) :
    birthBlockPivot B hB ∈ B := Classical.choose_spec hB

theorem birthEvent_groupHomogeneous {F : FixedData} {P : PrimeGroups} {J m n B : ℕ}
    {A : Model F P J m}
    (H : Erdos821.S2Core.MemoryHistory A n)
    (pi : Finset (Finset (Fin (Fintype.card
      (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)))))
    (hpi : BirthCollection pi)
    (hEvent : birthEvent (H.performedFin B) (H.valueFin B) pi)
    (C : Finset (Fin (Fintype.card
      (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)))) (hC : C ∈ pi)
    (j : Fin (Fintype.card (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)))
    (hj : j ∈ C) :
    birthAddressGroup ((Fintype.equivFin
      (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j) =
      birthAddressGroup ((Fintype.equivFin
        (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm
          (birthBlockPivot C (Finset.card_pos.mp (by
            have hcard := hpi.1 C hC
            omega)))) := by
  have hCcard : 2 ≤ C.card := hpi.1 C hC
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega)
  let pivot : Fin (Fintype.card
      (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)) :=
    birthBlockPivot C hCne
  have hpivotMem : pivot ∈ C := birthBlockPivot_mem _ _
  have hperfJ : j ∈ H.performedFin B := (hEvent C hC).1 hj
  have hperfPivot : pivot ∈ H.performedFin B := (hEvent C hC).1 hpivotMem
  have haddrJ : H.addressPerformed B
      ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j) := by
    simpa [Erdos821.S2Core.MemoryHistory.performedFin] using hperfJ
  have haddrPivot : H.addressPerformed B
      ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm pivot) := by
    simpa [Erdos821.S2Core.MemoryHistory.performedFin] using hperfPivot
  have hval : H.valueFin B j = H.valueFin B pivot :=
    (hEvent C hC).2 j hj pivot hpivotMem
  have hmemJ : H.addressValue B
      ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j) ∈
        P.primes (birthAddressGroup
          ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j)).val :=
    addressValue_mem_group H _ haddrJ
  have hmemPivot : H.addressValue B
      ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm pivot) ∈
        P.primes (birthAddressGroup
          ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm pivot)).val :=
    addressValue_mem_group H _ haddrPivot
  have hval' : H.addressValue B
      ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm j) =
    H.addressValue B
      ((Fintype.equivFin (Erdos821.S2Core.BirthAddress P (J + F.ell) n B)).symm pivot) := hval
  rw [hval'] at hmemJ
  exact big_groups_eq_of_common_prime _ _ _ hmemJ hmemPivot


end Erdos821.S2High
