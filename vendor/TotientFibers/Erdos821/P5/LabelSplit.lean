import Erdos821.P5.SharedProbability
import Erdos821.P5.SharedLists

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

abbrev UnsharedDraw {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :=
  (g : P.Group) → {i : Fin (J + ell) // i ∈ unsharedSlots ν g} → P.Prime g

def sharedSource {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (g : P.Group) (i : Fin (J + ell)) (hi : ν.shared g i) :
    {j : Fin J // j ∈ sharedSlots ν g} :=
  ⟨Classical.choose hi, by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Classical.choose_spec hi).2⟩⟩

theorem slot_sharedSource {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (g : P.Group) (i : Fin (J + ell)) (hi : ν.shared g i) :
    ν.slot (sharedSource ν g i hi).val = i := (Classical.choose_spec hi).1

theorem sharedSource_slot {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (g : P.Group) (j : {j : Fin J // j ∈ sharedSlots ν g})
    (hi : ν.shared g (ν.slot j.val)) : sharedSource ν g (ν.slot j.val) hi = j := by
  apply Subtype.ext
  exact shared_slot_injective ν (slot_sharedSource ν g _ hi)

def assembleLabels {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (z : SharedDraw ν) (r : UnsharedDraw ν) : P.Labels (J + ell) := fun g i =>
  if hi : ν.shared g i then z ⟨g, sharedSource ν g i hi⟩
  else r g ⟨i, (mem_unsharedSlots ν g i).mpr hi⟩

theorem assembleLabels_shared {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (z : SharedDraw ν) (r : UnsharedDraw ν) (g : P.Group)
    (i : {i : Fin J // i ∈ sharedSlots ν g}) :
    assembleLabels ν z r g (ν.slot i.val) = z ⟨g, i⟩ := by
  have hi : ν.shared g (ν.slot i.val) := ⟨i.val, rfl, (Finset.mem_sdiff.mp i.property).2⟩
  rw [assembleLabels, dif_pos hi, sharedSource_slot]

theorem assembleLabels_unshared {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (z : SharedDraw ν) (r : UnsharedDraw ν) (g : P.Group)
    (i : {i : Fin (J + ell) // i ∈ unsharedSlots ν g}) :
    assembleLabels ν z r g i.val = r g i := by
  rw [assembleLabels, dif_neg ((mem_unsharedSlots ν g i.val).mp i.property)]

def labelSplit {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m) :
    P.Labels (J + ell) ≃ SharedDraw ν × UnsharedDraw ν where
  toFun a := (sharedRestriction ν a, fun g i => a g i.val)
  invFun zr := assembleLabels ν zr.1 zr.2
  left_inv a := by
    funext g i
    dsimp [assembleLabels]
    split_ifs with hi
    · change a g (ν.slot (sharedSource ν g i hi).val) = a g i
      rw [slot_sharedSource]
    · rfl
  right_inv zr := by
    apply Prod.ext
    · funext j
      exact assembleLabels_shared ν zr.1 zr.2 j.1 j.2
    · funext g i
      exact assembleLabels_unshared ν zr.1 zr.2 g i

theorem sharedRestriction_assemble {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (r : UnsharedDraw ν) :
    sharedRestriction ν (assembleLabels ν z r) = z := by
  funext j
  exact assembleLabels_shared ν z r j.1 j.2

theorem compatible_iff_sharedRestriction {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a b : P.Labels (J + ell)) :
    ν.compatible a b ↔ sharedRestriction ν a = sharedRestriction ν b := by
  constructor
  · intro hab
    funext j
    exact hab j.1 (ν.slot j.2.val)
      ⟨j.2.val, rfl, (Finset.mem_sdiff.mp j.2.property).2⟩
  · intro hab g i hi
    have h := congrFun hab ⟨g, sharedSource ν g i hi⟩
    change a g (ν.slot (sharedSource ν g i hi).val) =
      b g (ν.slot (sharedSource ν g i hi).val) at h
    simpa only [slot_sharedSource] using h

theorem compatible_assemble_iff {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z z' : SharedDraw ν) (r s : UnsharedDraw ν) :
    ν.compatible (assembleLabels ν z r) (assembleLabels ν z' s) ↔ z = z' := by
  rw [compatible_iff_sharedRestriction, sharedRestriction_assemble, sharedRestriction_assemble]

/-- Compatible endpoint lists share precisely one draw of every selected
shared coordinate; their remaining coordinates are independent. -/
theorem sum_compatible_labels {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) {R : Type*} [AddCommMonoid R]
    (f : P.Labels (J + ell) → P.Labels (J + ell) → R) :
    (∑ a, ∑ b, if ν.compatible a b then f a b else 0) =
      ∑ z : SharedDraw ν, ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
        f (assembleLabels ν z r) (assembleLabels ν z s) := by
  rw [← (labelSplit ν).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro r hr
  rw [← (labelSplit ν).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  change (∑ z' : SharedDraw ν, ∑ s : UnsharedDraw ν,
    if ν.compatible (assembleLabels ν z r) (assembleLabels ν z' s)
    then f (assembleLabels ν z r) (assembleLabels ν z' s) else 0) = _
  simp_rw [compatible_assemble_iff]
  rw [Finset.sum_comm]
  simp

theorem sum_compatible_labels_harmonic {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m)
    (f : P.Labels (J + ell) → P.Labels (J + ell) → ℂ) :
    (∑ a, ∑ b, if ν.compatible a b then (sharedLaw ν a : ℂ) * f a b else 0) =
      ∑ z : SharedDraw ν, (sharedDrawLaw ν z : ℂ) *
        ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
          f (assembleLabels ν z r) (assembleLabels ν z s) := by
  rw [sum_compatible_labels]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← sharedDrawLaw_restriction, sharedRestriction_assemble]

end Erdos821.P5Core
