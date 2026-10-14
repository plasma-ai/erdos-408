import Erdos821.P5.GoodSharedDraws

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

def UnsharedPhysical {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (n : ℕ) (r : UnsharedDraw ν) : Prop :=
  ∀ g, Function.Injective (r g) ∧ ∀ i, (r g i).val ∣ n

/-- Once the shared primes avoid n, distinctness of the full list is exactly
distinctness of the remaining list. Shared primes already divide its root. -/
theorem physical_assemble_iff {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (r : UnsharedDraw ν) (n : ℕ)
    (hz : Function.Injective (fun i : SharedIndex ν => (z i).val))
    (hn : ∀ i : SharedIndex ν, ¬(z i).val ∣ n) :
    P.physical (J + ell) ((sharedDrawProduct ν z * n : ℕ) : ℤ)
      (assembleLabels ν z r) ↔ UnsharedPhysical ν n r := by
  constructor
  · intro ha g
    refine ⟨?_, ?_⟩
    · intro i j hij
      apply Subtype.ext
      apply (ha g).1
      simpa only [assembleLabels_unshared] using hij
    · intro i
      have ha' : P.physical (J + ell)
          ((sharedProduct ν (assembleLabels ν z r) * n : ℕ) : ℤ)
          (assembleLabels ν z r) := by
        simpa only [sharedProduct_assemble] using ha
      simpa only [assembleLabels_unshared] using
        unshared_label_dvd_strip ν (assembleLabels ν z r) n ha' g i.val
          ((mem_unsharedSlots ν g i.val).mp i.property)
  · intro hr g
    refine ⟨?_, ?_⟩
    · intro i j hij
      by_cases hi : ν.shared g i <;> by_cases hj : ν.shared g j
      · rw [assembleLabels, dif_pos hi, assembleLabels, dif_pos hj] at hij
        have heq := hz (congrArg (fun p : P.Prime g => p.val) hij)
        have hslot := congrArg (fun k : SharedIndex ν => ν.slot k.2.val) heq
        simpa only [slot_sharedSource] using hslot
      · rw [assembleLabels, dif_pos hi, assembleLabels, dif_neg hj] at hij
        have hd := (hr g).2 ⟨j, (mem_unsharedSlots ν g j).mpr hj⟩
        rw [← hij] at hd
        exact False.elim (hn ⟨g, sharedSource ν g i hi⟩ hd)
      · rw [assembleLabels, dif_neg hi, assembleLabels, dif_pos hj] at hij
        have hd := (hr g).2 ⟨i, (mem_unsharedSlots ν g i).mpr hi⟩
        rw [hij] at hd
        exact False.elim (hn ⟨g, sharedSource ν g j hj⟩ hd)
      · rw [assembleLabels, dif_neg hi, assembleLabels, dif_neg hj] at hij
        exact congrArg Subtype.val ((hr g).1 hij)
    · intro i
      apply Int.natCast_dvd_natCast.mpr
      by_cases hi : ν.shared g i
      · rw [assembleLabels, dif_pos hi]
        apply dvd_mul_of_dvd_left
        exact Finset.dvd_prod_of_mem (fun k : SharedIndex ν => (z k).val)
          (Finset.mem_univ (⟨g, sharedSource ν g i hi⟩ : SharedIndex ν))
      · rw [assembleLabels, dif_neg hi]
        exact dvd_mul_of_dvd_right ((hr g).2 ⟨i, (mem_unsharedSlots ν g i).mpr hi⟩) _

theorem physical_assemble_good_iff {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (r : UnsharedDraw ν) (n n' D : ℕ)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : D ≠ 0) (hz : GoodSharedDraw ν n n' D z) :
    P.physical (J + ell) ((sharedDrawProduct ν z * n : ℕ) : ℤ)
      (assembleLabels ν z r) ↔ UnsharedPhysical ν n r := by
  have h := (goodSharedDraw_iff ν n n' D hn hn' hD z).mp hz
  exact physical_assemble_iff ν z r n h.2 (fun i => (h.1 i).1)

theorem physical_assemble_good_right_iff {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (r : UnsharedDraw ν) (n n' D : ℕ)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : D ≠ 0) (hz : GoodSharedDraw ν n n' D z) :
    P.physical (J + ell) ((sharedDrawProduct ν z * n' : ℕ) : ℤ)
      (assembleLabels ν z r) ↔ UnsharedPhysical ν n' r := by
  have h := (goodSharedDraw_iff ν n n' D hn hn' hD z).mp hz
  exact physical_assemble_iff ν z r n' h.2 (fun i => (h.1 i).2.1)

/-- Exact finite row identity after removing bad shared draws. The harmonic
factor is the one supplied by stripping the root's shared product. -/
theorem good_physical_row_sum {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (n n' D : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : D ≠ 0)
    (f : P.Labels (J + ell) → P.Labels (J + ell) → ℂ) :
    (∑ a, ∑ b, if ν.compatible a b ∧
      GoodSharedDraw ν n n' D (sharedRestriction ν a) ∧
      P.physical (J + ell) ((sharedProduct ν a * n : ℕ) : ℤ) a ∧
      P.physical (J + ell) ((sharedProduct ν a * n' : ℕ) : ℤ) b
      then (sharedLaw ν a : ℂ) * f a b else 0) =
      ∑ z : SharedDraw ν, (sharedDrawLaw ν z : ℂ) *
        ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
          if GoodSharedDraw ν n n' D z ∧ UnsharedPhysical ν n r ∧ UnsharedPhysical ν n' s
          then f (assembleLabels ν z r) (assembleLabels ν z s) else 0 := by
  have hnest : (∑ a, ∑ b, if ν.compatible a b ∧
      GoodSharedDraw ν n n' D (sharedRestriction ν a) ∧
      P.physical (J + ell) ((sharedProduct ν a * n : ℕ) : ℤ) a ∧
      P.physical (J + ell) ((sharedProduct ν a * n' : ℕ) : ℤ) b
      then (sharedLaw ν a : ℂ) * f a b else 0) =
    ∑ a, ∑ b, if ν.compatible a b then (sharedLaw ν a : ℂ) *
      (if GoodSharedDraw ν n n' D (sharedRestriction ν a) ∧
        P.physical (J + ell) ((sharedProduct ν a * n : ℕ) : ℤ) a ∧
        P.physical (J + ell) ((sharedProduct ν a * n' : ℕ) : ℤ) b
        then f a b else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : ν.compatible a b <;> simp [h]
  rw [hnest, sum_compatible_labels_harmonic]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  simp only [sharedRestriction_assemble, sharedProduct_assemble]
  by_cases hgood : GoodSharedDraw ν n n' D z
  · rw [physical_assemble_good_iff ν z r n n' D hn hn' hD hgood,
      physical_assemble_good_right_iff ν z s n n' D hn hn' hD hgood]
  · simp only [hgood, false_and, if_false]

end Erdos821.P5Core
