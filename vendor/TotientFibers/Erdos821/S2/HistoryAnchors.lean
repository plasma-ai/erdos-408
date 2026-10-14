import Erdos821.S2.HistoryProjection
import Erdos821.S2.HistoryFinite

/-! Each distinct birth fixes one prime's congruence anchor for its entire lifespan. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

namespace MemoryHistory

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n)

def birthBound (_H : MemoryHistory A n) : ℕ := P.allPrimes.card + n * ((J + F.ell) * Fintype.card P.BigGroup)

def birthOffset : BirthAddress P (J + F.ell) n H.birthBound → ℤ
  | .inl _ => 0
  | .inr (.inl (i, _, _)) => H.toResiduePath.offset i.succ
  | .inr (.inr (i, _, _)) => H.toResiduePath.offset i

def anchorOffset (p : ℕ) : ℤ :=
  if h : ∃ a : BirthAddress P (J + F.ell) n H.birthBound,
      H.addressPerformed H.birthBound a ∧ H.addressValue H.birthBound a = p then
    H.birthOffset (Classical.choose h)
  else 0

/-- Distinctness makes this choice independent of the witness. -/
theorem anchorOffset_eq_birth (hH : H.Valid) (hd : H.DistinctBirths)
    (a : BirthAddress P (J + F.ell) n H.birthBound) (p : ℕ)
    (ha : H.addressPerformed H.birthBound a) (hp : H.addressValue H.birthBound a = p) :
    H.anchorOffset p = H.birthOffset a := by
  have hx : ∃ a : BirthAddress P (J + F.ell) n H.birthBound,
      H.addressPerformed H.birthBound a ∧ H.addressValue H.birthBound a = p := ⟨a, ha, hp⟩
  rw [anchorOffset, dite_eq_left hx]
  have hs := Classical.choose_spec hx
  have ht : H.Truncated H.birthBound := H.distinct_truncated hH hd
  have hi := (H.distinctBirths_iff_addresses H.birthBound ht).mp hd
  have he : Classical.choose hx = a := hi
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩) (hs.2.trans hp.symm)
  exact congrArg H.birthOffset he

theorem anchorOffset_initial (hH : H.Valid) (hd : H.DistinctBirths) (g : P.BigGroup) (i : Fin (J + F.ell)) :
    H.anchorOffset ((H.before 0).2.1 g.val i).val = 0 :=
  H.anchorOffset_eq_birth hH hd (.inl (g, i)) _ True.intro rfl

/-- All big active and pending coordinates keep the same unique birth anchor. -/
def AnchorInvariant (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)) : Prop :=
  (∀ g : P.BigGroup, ∀ j : Fin (J + F.ell),
    (H.toResiduePath.offset i : ZMod (s.2.1 g.val j).val) =
      (H.anchorOffset (s.2.1 g.val j).val : ZMod (s.2.1 g.val j).val)) ∧
  (∀ g : P.BigGroup, ∀ z ∈ s.2.2 g,
    z.2 = ((H.toResiduePath.offset i - H.anchorOffset z.1.val : ℤ) : ZMod z.1.val))

theorem anchorInvariant_initial (hH : H.Valid) (hd : H.DistinctBirths) : H.AnchorInvariant 0 (H.before 0) := by
  constructor
  · intro g j
    rw [ResiduePath.offset_zero, H.anchorOffset_initial hH hd]
  · intro g z hz
    rw [hH.1 g] at hz
    have hz' : False := by simpa using hz
    exact hz'.elim

end MemoryHistory

/-- Structural forward correctness of the residue anchors. No analytic bounds,
step-size asymptotics, or auxiliary label laws enter this task. -/
def HistoryAnchorTask : Prop :=
  ∀ (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (H : MemoryHistory A n), H.Valid → H.DistinctBirths →
      ∀ i, H.AnchorInvariant i (H.before i) ∧ H.AnchorInvariant i (H.after i)


end Erdos821.S2Core
