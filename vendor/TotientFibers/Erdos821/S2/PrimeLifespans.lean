import Erdos821.S2.LifespanAlgebra

/-! The active-prime part of the exact lifespan expansion. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

/-- Independent-residue expectation for one prime and prescribed active visits. -/
def onePrimeExpectation (p n : ℕ) [NeZero p] (eta : Fin n → ℝ)
    (h : Fin n → ZMod p) (active : Finset (Fin n)) : ℝ :=
  (p : ℝ)⁻¹ * ∑ r : ZMod p, ∏ i : Fin n,
    if i ∈ active then (if r + h i = 0 then 1 else 0)
    else 1 - eta i * if r + h i = 0 then 1 else 0

/-- Any active visit pins the residue. Compatibility of all other active
 offsets is retained explicitly. No later hit pays a reciprocal prime. -/
theorem onePrimeExpectation_active (p n : ℕ) [NeZero p] (eta : Fin n → ℝ)
    (h : Fin n → ZMod p) (active : Finset (Fin n)) (a : Fin n) (ha : a ∈ active) :
    onePrimeExpectation p n eta h active = (p : ℝ)⁻¹ *
      (if ∀ i ∈ active, h i = h a then
        ∏ i ∈ Finset.univ.filter (fun i => i ∉ active),
          (1 - eta i * if h i = h a then 1 else 0)
      else 0) := by
  have hh (i : Fin n) : -h a + h i = 0 ↔ h i = h a := by
    constructor
    · intro he
      have he' := congrArg (fun z => h a + z) he
      simpa only [add_assoc, add_neg_cancel_left, add_zero] using he'
    · rintro he
      simp [he]
  unfold onePrimeExpectation
  congr 1
  rw [Finset.sum_eq_single (-h a)]
  · simp only [hh]
    by_cases hc : ∀ i ∈ active, h i = h a
    · rw [ite_eq_left hc]
      calc
        _ = ∏ i : Fin n, if i ∉ active then (1 - eta i * if h i = h a then 1 else 0) else 1 := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i ∈ active
          · simp [hi, hc i hi]
          · simp [hi]
        _ = _ := (Finset.prod_filter _ _).symm
    · rw [ite_eq_right hc]
      obtain ⟨i, hi, he⟩ : ∃ i ∈ active, h i ≠ h a := by
        push Not at hc
        exact hc
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [ite_eq_left hi, ite_eq_right he]
  · intro r _ hr
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    have hn : ¬ r + h a = 0 := by
      intro he
      apply hr
      calc
        r = (r + h a) - h a := by abel
        _ = -h a := by rw [he]; simp
    simp only [ite_eq_left ha, ite_eq_right hn]
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

/-- Split the unmarked product into a prefix, gaps within the active span,
and a suffix. This is the interval decomposition used by the memory identity. -/
theorem unmarked_product_split {R : Type*} [CommMonoid R] (n : ℕ)
    (f : Fin n → R) (active : Finset (Fin n)) (a z : Fin n)
    (ha : a ∈ active) (hz : z ∈ active)
    (hfirst : ∀ i ∈ active, a ≤ i) (hlast : ∀ i ∈ active, i ≤ z) :
    (∏ i ∈ Finset.univ.filter (fun i => i ∉ active), f i) =
      (∏ i ∈ Finset.univ.filter (fun i => i < a), f i) *
      (∏ i ∈ Finset.univ.filter (fun i => a < i ∧ i < z ∧ i ∉ active), f i) *
      (∏ i ∈ Finset.univ.filter (fun i => z < i), f i) := by
  simp only [Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have haz := hfirst z hz
  by_cases hi : i ∈ active
  · have hlo := hfirst i hi
    have hhi := hlast i hi
    have hpre : ¬ i < a := not_lt.mpr hlo
    have hpost : ¬ z < i := not_lt.mpr hhi
    simp [hi, hpre, hpost]
  · have hia : i ≠ a := fun he => hi (he.symm ▸ ha)
    have hiz : i ≠ z := fun he => hi (he.symm ▸ hz)
    by_cases hpre : i < a
    · have hmid : ¬ a < i := not_lt.mpr (le_of_lt hpre)
      have hpost : ¬ z < i := not_lt.mpr (le_trans (le_of_lt hpre) haz)
      simp [hi, hpre, hmid, hpost]
    · by_cases hpost : z < i
      · have hmid : ¬ i < z := not_lt.mpr (le_of_lt hpost)
        simp [hi, hpre, hpost, hmid]
      · have hlo : a < i := lt_of_le_of_ne (le_of_not_gt hpre) (Ne.symm hia)
        have hhi : i < z := lt_of_le_of_ne (le_of_not_gt hpost) hiz
        simp [hi, hpre, hpost, hlo, hhi]

/-- Prefix/suffix ghost endpoints are charged only at their own visits.
The middle product records pending hits between the first and last activity. -/
theorem active_lifespan_expansion (n : ℕ) (f : Fin n → ℝ)
    (active : Finset (Fin n)) (a z : Fin n) (ha : a ∈ active) (hz : z ∈ active)
    (hfirst : ∀ i ∈ active, a ≤ i) (hlast : ∀ i ∈ active, i ≤ z) :
    (∏ i ∈ Finset.univ.filter (fun i => i ∉ active), (1 - f i)) =
      (1 - ∑ j ∈ Finset.univ.filter (fun j => j < a),
        f j * ∏ i ∈ Finset.univ.filter (fun i => j < i ∧ i < a), (1 - f i)) *
      (∏ i ∈ Finset.univ.filter (fun i => a < i ∧ i < z ∧ i ∉ active), (1 - f i)) *
      (1 - ∑ j ∈ Finset.univ.filter (fun j => z < j),
        f j * ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < j), (1 - f i)) := by
  rw [unmarked_product_split n (fun i => 1 - f i) active a z ha hz hfirst hlast]
  have hp : (∏ i ∈ Finset.univ.filter (fun i => i < a), (1 - f i)) =
      1 - ∑ j ∈ Finset.univ.filter (fun j => j < a),
        f j * ∏ i ∈ Finset.univ.filter (fun i => j < i ∧ i < a), (1 - f i) := by
    simpa only [Finset.filter_filter, and_comm] using
      Erdos821.S2.prefix_ghost_ordered (Finset.univ.filter (fun i => i < a)) f
  have hs : (∏ i ∈ Finset.univ.filter (fun i => z < i), (1 - f i)) =
      1 - ∑ j ∈ Finset.univ.filter (fun j => z < j),
        f j * ∏ i ∈ Finset.univ.filter (fun i => z < i ∧ i < j), (1 - f i) := by
    simpa only [Finset.filter_filter] using
      Finset.prod_one_sub_ordered (Finset.univ.filter (fun i => z < i)) f
  rw [hp, hs]


end Erdos821.S2Core
