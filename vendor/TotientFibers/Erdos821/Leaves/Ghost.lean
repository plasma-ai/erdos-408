import Mathlib
import Erdos821.Blueprint.Graph
import Erdos821.Blueprint.Analytic

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Erdos821.GraphLemmas

theorem tail_filter (n j : ℕ) (hj : j < n) :
    ((Finset.range (n + 1)).filter (fun i => j < i))
    = insert n ((Finset.range n).filter (fun i => j < i)) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  simp [hj]

theorem tail_interval_eq (n j : ℕ) :
    ((Finset.range (n + 1)).filter (fun t => j < t ∧ t < n))
    = ((Finset.range n).filter (fun t => j < t)) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem interval_stable_eq (n j i : ℕ) (hi : i < n) :
    ((Finset.range (n + 1)).filter (fun t => j < t ∧ t < i))
    = ((Finset.range n).filter (fun t => j < t ∧ t < i)) := by
  rw [Finset.range_add_one, Finset.filter_insert]
  have hneg : ¬ (j < n ∧ n < i) := by omega
  simp [hneg]

theorem inner_empty_eq (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun i => n < i)) = ∅ := by
  ext t
  simp

end Erdos821.GraphLemmas

namespace Erdos821.Blueprint.Graph

/-- §2 prefix ghost identity, by induction (new element is maximal). -/
theorem prefix_ghost {R : Type*} [CommRing R] (n : ℕ) (f : ℕ → R) :
    (∏ i ∈ Finset.range n, (1 - f i)) =
      1 - ∑ j ∈ Finset.range n, f j * ∏ i ∈ Finset.range n with j < i, (1 - f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htail : ∀ j ∈ Finset.range n,
        (∏ i ∈ Finset.range (n + 1) with j < i, (1 - f i))
        = (∏ i ∈ Finset.range n with j < i, (1 - f i)) * (1 - f n) := by
      intro j hj
      have hjlt : j < n := Finset.mem_range.mp hj
      have hfilter := Erdos821.GraphLemmas.tail_filter n j hjlt
      have hnm : n ∉ (Finset.range n).filter (fun i => j < i) :=
        Finset.notMem_mono (Finset.filter_subset _ _) Finset.notMem_range_self
      show ∏ i ∈ (Finset.range (n+1)).filter (fun i => j < i), (1 - f i) = _
      rw [hfilter, Finset.prod_insert hnm, mul_comm]
    have hempty : (∏ i ∈ Finset.range (n + 1) with n < i, (1 - f i)) = 1 := by
      rw [Erdos821.GraphLemmas.inner_empty_eq]
      exact Finset.prod_empty
    have hprod : ∏ i ∈ Finset.range (n + 1), (1 - f i)
        = (∏ i ∈ Finset.range n, (1 - f i)) * (1 - f n) :=
      Finset.prod_range_succ _ n
    have hsum : (∑ j ∈ Finset.range (n + 1), f j * ∏ i ∈ Finset.range (n + 1) with j < i, (1 - f i))
        = (∑ j ∈ Finset.range n, f j * (∏ i ∈ Finset.range n with j < i, (1 - f i))) * (1 - f n)
          + f n := by
      rw [Finset.sum_range_succ, hempty, mul_one]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [htail j hj, mul_assoc]
    rw [hprod, hsum, ih]
    ring

example : @Erdos821.Blueprint.Graph.prefix_ghost =
    @Erdos821.Blueprint.Graph.prefix_ghost := rfl

/-- §2 suffix ghost identity: exactly `Finset.prod_one_sub_ordered`. -/
theorem suffix_ghost {R : Type*} [CommRing R] (n : ℕ) (f : ℕ → R) :
    (∏ i ∈ Finset.range n, (1 - f i)) =
      1 - ∑ j ∈ Finset.range n, f j * ∏ i ∈ Finset.range n with i < j, (1 - f i) :=
  Finset.prod_one_sub_ordered _ _

example : @Erdos821.Blueprint.Graph.suffix_ghost =
    @Erdos821.Blueprint.Graph.suffix_ghost := rfl

/-- §2 orphan polynomial: earliest/latest grouping, by induction using prefix. -/
theorem orphan_polynomial {R : Type*} [CommRing R] (n : ℕ) (f : ℕ → R) :
    (∏ i ∈ Finset.range n, (1 - f i)) =
      1 - (∑ i ∈ Finset.range n, f i) +
        ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n with j < i,
          f j * f i * ∏ t ∈ Finset.range n with j < t ∧ t < i, (1 - f t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprod : ∏ i ∈ Finset.range (n + 1), (1 - f i)
        = (∏ i ∈ Finset.range n, (1 - f i)) * (1 - f n) :=
      Finset.prod_range_succ _ n
    have hS : (∑ i ∈ Finset.range (n + 1), f i)
        = (∑ i ∈ Finset.range n, f i) + f n :=
      Finset.sum_range_succ _ n
    have hinner : ∀ j ∈ Finset.range n,
        (∑ i ∈ Finset.range (n + 1) with j < i,
          f j * f i * ∏ t ∈ Finset.range (n + 1) with j < t ∧ t < i, (1 - f t))
        = (∑ i ∈ Finset.range n with j < i,
          f j * f i * ∏ t ∈ Finset.range n with j < t ∧ t < i, (1 - f t))
          + f j * f n * ∏ t ∈ Finset.range n with j < t, (1 - f t) := by
      intro j hj
      have hjlt : j < n := Finset.mem_range.mp hj
      have hfilter : (Finset.range (n + 1)).filter (fun i => j < i)
          = insert n ((Finset.range n).filter (fun i => j < i)) :=
        Erdos821.GraphLemmas.tail_filter n j hjlt
      have hnm : n ∉ (Finset.range n).filter (fun i => j < i) :=
        Finset.notMem_mono (Finset.filter_subset _ _) Finset.notMem_range_self
      have hrew : (∑ i ∈ Finset.range (n+1) with j < i,
          f j * f i * ∏ t ∈ Finset.range (n+1) with j < t ∧ t < i, (1 - f t))
          = ∑ i ∈ insert n ((Finset.range n).filter (fun i => j < i)),
            f j * f i * ∏ t ∈ (Finset.range (n+1)).filter (fun t => j < t ∧ t < i), (1 - f t) := by
        rw [← hfilter]
      rw [hrew, Finset.sum_insert hnm, add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        have hi_lt : i < n := hi.1
        rw [Erdos821.GraphLemmas.interval_stable_eq n j i hi_lt]
      · rw [Erdos821.GraphLemmas.tail_interval_eq n j]
    have hempty_inner : (∑ i ∈ Finset.range (n + 1) with n < i,
        f n * f i * ∏ t ∈ Finset.range (n + 1) with n < t ∧ t < i, (1 - f t)) = 0 := by
      have hfil : (Finset.range (n+1)).filter (fun i => n < i) = ∅ :=
        Erdos821.GraphLemmas.inner_empty_eq n
      have hconv : (∑ i ∈ Finset.range (n+1) with n < i,
        f n * f i * ∏ t ∈ Finset.range (n+1) with n < t ∧ t < i, (1 - f t))
        = ∑ i ∈ (Finset.range (n+1)).filter (fun i => n < i),
          f n * f i * ∏ t ∈ (Finset.range (n+1)).filter (fun t => n < t ∧ t < i), (1 - f t) := rfl
      rw [hconv, hfil]
      exact Finset.sum_empty
    have hD : (∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1) with j < i,
          f j * f i * ∏ t ∈ Finset.range (n + 1) with j < t ∧ t < i, (1 - f t))
        = (∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n with j < i,
          f j * f i * ∏ t ∈ Finset.range n with j < t ∧ t < i, (1 - f t))
          + f n * (∑ j ∈ Finset.range n, f j * ∏ t ∈ Finset.range n with j < t, (1 - f t)) := by
      rw [Finset.sum_range_succ, hempty_inner, add_zero,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hinner j hj]
      ring
    have hpref := prefix_ghost n f
    have htailsum : (∑ j ∈ Finset.range n, f j * ∏ i ∈ Finset.range n with j < i, (1 - f i))
        = 1 - ∏ i ∈ Finset.range n, (1 - f i) := by
      rw [hpref]
      ring
    rw [hprod, hS, hD, htailsum, ih]
    ring

example : @Erdos821.Blueprint.Graph.orphan_polynomial =
    @Erdos821.Blueprint.Graph.orphan_polynomial := rfl

end Erdos821.Blueprint.Graph
