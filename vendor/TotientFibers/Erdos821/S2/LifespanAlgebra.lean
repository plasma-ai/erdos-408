import Mathlib

/-! Polynomial identities underlying the one-prime lifespan expansion. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2

lemma prefix_ghost_ordered {ι R : Type*} [LinearOrder ι] [CommRing R]
    (s : Finset ι) (f : ι → R) :
    (∏ i ∈ s, (1 - f i)) =
      1 - ∑ j ∈ s, f j * ∏ i ∈ s.filter (fun i => j < i), (1 - f i) := by
  classical
  exact Finset.prod_one_sub_ordered (ι := OrderDual ι) s f

theorem prefix_ghost {R : Type*} [CommRing R] (n : ℕ) (f : ℕ → R) :
    (∏ i ∈ Finset.range n, (1 - f i)) =
      1 - ∑ j ∈ Finset.range n, f j * ∏ i ∈ (Finset.range n).filter (fun i => j < i), (1 - f i) :=
  prefix_ghost_ordered (Finset.range n) f

theorem suffix_ghost {R : Type*} [CommRing R] (n : ℕ) (f : ℕ → R) :
    (∏ i ∈ Finset.range n, (1 - f i)) =
      1 - ∑ j ∈ Finset.range n, f j * ∏ i ∈ (Finset.range n).filter (fun i => i < j), (1 - f i) :=
  Finset.prod_one_sub_ordered (Finset.range n) f

/-- Group all terms of degree at least two by their first and last indices. -/
theorem orphan_polynomial_ordered {ι R : Type*} [LinearOrder ι] [CommRing R]
    (s : Finset ι) (f : ι → R) :
    (∏ i ∈ s, (1 - f i)) =
      1 - (∑ i ∈ s, f i) +
        ∑ j ∈ s, ∑ i ∈ s.filter (fun i => j < i),
          f j * f i * ∏ t ∈ s.filter (fun t => j < t ∧ t < i), (1 - f t) := by
  classical
  have hs (j : ι) :
      (∏ i ∈ s.filter (fun i => j < i), (1 - f i)) =
        1 - ∑ i ∈ s.filter (fun i => j < i),
          f i * ∏ t ∈ s.filter (fun t => j < t ∧ t < i), (1 - f t) := by
    simpa only [Finset.filter_filter] using
      Finset.prod_one_sub_ordered (s.filter (fun i => j < i)) f
  calc
    _ = 1 - ∑ j ∈ s, f j *
        (1 - ∑ i ∈ s.filter (fun i => j < i),
          f i * ∏ t ∈ s.filter (fun t => j < t ∧ t < i), (1 - f t)) := by
      rw [prefix_ghost_ordered]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [hs]
    _ = _ := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
      ring

theorem orphan_polynomial {R : Type*} [CommRing R] (n : ℕ) (f : ℕ → R) :
    (∏ i ∈ Finset.range n, (1 - f i)) =
      1 - (∑ i ∈ Finset.range n, f i) +
        ∑ j ∈ Finset.range n, ∑ i ∈ (Finset.range n).filter (fun i => j < i),
          f j * f i * ∏ t ∈ (Finset.range n).filter (fun t => j < t ∧ t < i), (1 - f t) :=
  orphan_polynomial_ordered (Finset.range n) f


end Erdos821.S2
