import Erdos821.P5.FreeSlotExclusion
import Erdos821.P5.UnsharedMarks

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

def UnsharedBan {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (r s : UnsharedDraw ν) (u : FreeDraw ν) : Prop :=
  ∀ i : FreeIndex ν, ∀ j : {j : Fin (J + ell) // j ∈ unsharedSlots ν i.1},
    u i ≠ r i.1 j ∧ u i ≠ s i.1 j

theorem unshared_ban_violation_free_divisor {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (r s : UnsharedDraw ν) (u : FreeDraw ν)
    (n n' : ℕ) (k : ℤ) (hr : UnsharedPhysical ν n r) (hs : UnsharedPhysical ν n' s)
    (hshift : (n' : ℤ) = (n : ℤ) + k * (freeDrawProduct ν u : ℤ))
    (hban : ¬UnsharedBan ν r s u) : FreeCollisionEvent ν u n := by
  unfold UnsharedBan at hban
  push Not at hban
  obtain ⟨i, j, hneq⟩ := hban
  have heq : u i = r i.1 j ∨ u i = s i.1 j := by
    by_cases h : u i = r i.1 j
    · exact Or.inl h
    · exact Or.inr (hneq h)
  refine ⟨i, ?_⟩
  rcases heq with heq | heq
  · rw [heq]
    exact (hr i.1).2 j
  · have hp : (u i).val ∣ n' := by rw [heq]; exact (hs i.1).2 j
    exact (dvd_shift_iff (u i).val (freeDrawProduct ν u) n n' k
      (free_prime_dvd_freeDrawProduct ν u i) hshift).mpr hp

/-- Once free/shared coincidences have been excluded, the graph ban is
exactly the ban between free labels and the two unshared endpoint lists. -/
theorem pattern_ban_assemble_iff {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (z : SharedDraw ν) (r s : UnsharedDraw ν)
    (u : FreeDraw ν) (unused : SharedDraw ν)
    (hzD : ∀ j : SharedIndex ν, ¬(z j).val ∣ freeDrawProduct ν u) :
    ν.ban (assembleLabels ν z r) (assembleLabels ν z s) (assembleAux ν u unused) ↔
      UnsharedBan ν r s u := by
  constructor
  · intro h i j
    have hi := h i.1 i.2.val i.2.property j.val
    simpa only [assembleAux_free, assembleLabels_unshared] using hi
  · intro h g i hi j
    rw [assembleAux_free ν u unused g ⟨i, hi⟩]
    by_cases hj : ν.shared g j
    · have hne : u ⟨g, ⟨i, hi⟩⟩ ≠ z ⟨g, sharedSource ν g j hj⟩ := by
        intro heq
        apply hzD ⟨g, sharedSource ν g j hj⟩
        rw [← heq]
        exact free_prime_dvd_freeDrawProduct ν u ⟨g, ⟨i, hi⟩⟩
      simp only [assembleLabels, dif_pos hj]
      exact ⟨hne, hne⟩
    · have hj' := (mem_unsharedSlots ν g j).mpr hj
      have hjs := h ⟨g, ⟨i, hi⟩⟩ ⟨j, hj'⟩
      simpa only [assembleLabels_unshared ν z r g ⟨j, hj'⟩,
        assembleLabels_unshared ν z s g ⟨j, hj'⟩] using hjs

end Erdos821.P5Core
