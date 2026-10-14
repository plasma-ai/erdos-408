import Erdos821.P5.PhysicalKernelDomination

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

theorem pattern_D_le_sup_pow {G : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (a : G.Labels (J + ell)) (u : G.Aux J) :
    ν.D a u ≤ (G.allPrimes.sup id) ^ (J * G.count) := by
  unfold Pattern.D
  calc
    _ ≤ ∏ g : G.Group, ∏ _i : Fin J, G.allPrimes.sup id := by
      apply Finset.prod_le_prod
      intro g hg
      apply Finset.prod_le_prod
      intro i hi
      apply Finset.le_sup (f := id)
      apply Finset.mem_biUnion.mpr
      refine ⟨g, Finset.mem_univ g, ?_⟩
      change (if i ∈ ν.changed g then (u g i).val else (a g (ν.slot i)).val) ∈ G.primes g
      split_ifs <;> exact Subtype.property _
    _ = _ := by simp [← pow_mul]

theorem physicalKernel_zero_outside_neighbors {F : FixedData} {G : PrimeGroups} {J m : ℕ}
    (A : Model F G J m) (absolute : Bool) (z z' : A.State)
    (hnot : z' ∉ A.neighbors z.1) : A.physicalKernel absolute z z' = 0 := by
  have hD : ∀ v a u, |(A.k : ℝ)| * ((A.pattern v).D a u : ℝ) ≤ (A.stepBound : ℝ) := by
    intro v a u
    unfold Model.stepBound
    rw [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast pattern_D_le_sup_pow (A.pattern v) a u)
      (abs_nonneg _)
  have hfar : (A.stepBound : ℝ) < |(z'.1 : ℝ) - z.1| := by
    by_contra h
    have habs := abs_le.mp (le_of_not_gt h)
    have hlo : z.1 - (A.stepBound : ℤ) ≤ z'.1 := by
      have : (z.1 : ℝ) - A.stepBound ≤ (z'.1 : ℝ) := by linarith [habs.1]
      exact_mod_cast this
    have hhi : z'.1 ≤ z.1 + (A.stepBound : ℤ) := by
      have : (z'.1 : ℝ) ≤ (z.1 : ℝ) + A.stepBound := by linarith [habs.2]
      exact_mod_cast this
    exact hnot (Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi⟩, Finset.mem_univ _⟩)
  exact physicalKernel_eq_zero_of_far A _ hD absolute z.1 z'.1 z.2 z'.2 hfar

theorem physicalKernel_zero_outside_reverse_neighbors {F : FixedData} {G : PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (absolute : Bool) (z z' : A.State)
    (hnot : z ∉ A.neighbors z'.1) : A.physicalKernel absolute z z' = 0 := by
  apply physicalKernel_zero_outside_neighbors A absolute z z'
  intro hz
  obtain ⟨hn, ha⟩ := Finset.mem_product.mp hz
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  apply hnot
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_univ _⟩

theorem norm_sum_le_of_support {α : Type*} (s t : Finset α) (f : α → ℂ)
    (h : ∀ a, a ∉ t → f a = 0) : (∑ a ∈ s, ‖f a‖) ≤ ∑ a ∈ t, ‖f a‖ := by
  have heq : (∑ a ∈ s, ‖f a‖) = ∑ a ∈ s ∩ t, ‖f a‖ := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro a ha hnot
    have hat : a ∉ t := fun ht => hnot (Finset.mem_inter.mpr ⟨ha, ht⟩)
    rw [h a hat, norm_zero]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun a ha hnot => norm_nonneg _)

end Erdos821.P5Core
