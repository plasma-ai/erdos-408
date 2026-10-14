import Erdos821.P4Probe.Anova

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

lemma productFull_zero (w : ∀ i, α i → ℝ) (I : Finset ι) :
    productFull w I (fun _ : ProductSample α => 0) = (fun _ => 0) := by
  funext x
  simp [productFull, productAverage]

lemma productFull_anova_eq (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (I S : Finset ι) (hIS : I ⊆ S) (f : ProductSample α → ℂ) :
    productFull w I (productAnova w Finset.univ S f) = productAnova w Finset.univ S f := by
  induction I using Finset.induction_on with
  | empty => exact productFull_empty w hsum _
  | @insert i I hi hI =>
      have hiS : i ∈ S := hIS (Finset.mem_insert_self _ _)
      have hIS' : I ⊆ S := fun j hj => hIS (Finset.mem_insert_of_mem hj)
      rw [productFull_insert w hsum I i hi, hI hIS',
        productAnova_mean_zero w hsum Finset.univ S i hiS]
      funext x
      simp

lemma productFull_anova_zero (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (I S : Finset ι) (hIS : ¬I ⊆ S) (f : ProductSample α → ℂ) :
    productFull w I (productAnova w Finset.univ S f) = (fun _ => 0) := by
  obtain ⟨i, hiI, hiS⟩ := Finset.not_subset.mp hIS
  calc
    _ = productFull w I (productAverage w {i} (productAnova w Finset.univ S f)) := by
      rw [productAnova_independent w hsum Finset.univ S i (Finset.mem_univ _) hiS]
    _ = productAverage w {i} (productFull w I (productAnova w Finset.univ S f)) :=
      productFull_average_commute w hsum I {i} _
    _ = _ := productFull_mean_zero w hsum I i hiI _

lemma productAverage_anova_eq (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (A S : Finset ι) (hAS : Disjoint A S) (f : ProductSample α → ℂ) :
    productAverage w A (productAnova w Finset.univ S f) = productAnova w Finset.univ S f := by
  induction A using Finset.induction_on with
  | empty => exact productAverage_empty w hsum _
  | @insert i A hi hA =>
      have hiS : i ∉ S := fun h => Finset.disjoint_left.mp hAS
        (Finset.mem_insert_self _ _) h
      have hAS' : Disjoint A S := hAS.mono_left (Finset.subset_insert _ _)
      have havg : productAverage w (insert i A) (productAnova w Finset.univ S f) =
          productAverage w {i} (productAverage w A (productAnova w Finset.univ S f)) := by
        funext x
        rw [productAverage_union w hsum {i} A, Finset.singleton_union]
      rw [havg, hA hAS']
      exact productAnova_independent w hsum Finset.univ S i (Finset.mem_univ _) hiS f

lemma productAverage_anova_zero (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (A S : Finset ι) (hAS : ¬Disjoint A S) (f : ProductSample α → ℂ) :
    productAverage w A (productAnova w Finset.univ S f) = (fun _ => 0) := by
  obtain ⟨i, hiA, hiS⟩ := Finset.not_disjoint_iff.mp hAS
  have hu : A ∪ {i} = A := by
    apply Finset.union_eq_left.mpr
    simpa only [Finset.singleton_subset_iff] using hiA
  have havg : productAverage w A (productAverage w {i} (productAnova w Finset.univ S f)) =
      productAverage w A (productAnova w Finset.univ S f) := by
    funext x
    rw [productAverage_union w hsum A {i}, hu]
  rw [productAnova_mean_zero w hsum Finset.univ S i hiS, productAverage_zero] at havg
  exact havg.symm

lemma productFull_sum {β : Type*} (w : ∀ i, α i → ℝ) (I : Finset ι)
    (V : Finset β) (c : β → ℂ) (f : β → ProductSample α → ℂ) (x : ProductSample α) :
    productFull w I (fun y => ∑ v ∈ V, c v * f v y) x =
      ∑ v ∈ V, c v * productFull w I (f v) x := by
  unfold productFull
  simp_rw [productAverage_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := I.powerset) (t := V)]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro U _
  ring

lemma productFull_full_commute (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (f : ProductSample α → ℂ) :
    productFull w I (productFull w S f) = productFull w S (productFull w I f) := by
  funext x
  change productFull w I
    (fun y => ∑ U ∈ S.powerset, (-1 : ℂ) ^ U.card * productAverage w U f y) x = _
  rw [productFull_sum]
  change (∑ U ∈ S.powerset, (-1 : ℂ) ^ U.card *
    productFull w I (productAverage w U f) x) =
      ∑ U ∈ S.powerset, (-1 : ℂ) ^ U.card * productAverage w U (productFull w I f) x
  apply Finset.sum_congr rfl
  intro U _
  rw [productFull_average_commute w hsum I U]

lemma productAverage_commute (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (f : ProductSample α → ℂ) :
    productAverage w I (productAverage w S f) = productAverage w S (productAverage w I f) := by
  funext x
  rw [productAverage_union w hsum I S, productAverage_union w hsum S I,
    Finset.union_comm]

def productProbeProjection (w : ∀ i, α i → ℝ) (tail I : Finset ι)
    (f : ProductSample α → ℂ) : ProductSample α → ℂ :=
  productFull w I (productAverage w tail f)

lemma productAnova_probe_commute (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (tail I S : Finset ι) (f : ProductSample α → ℂ) :
    productAnova w Finset.univ S (productProbeProjection w tail I f) =
      productProbeProjection w tail I (productAnova w Finset.univ S f) := by
  unfold productAnova productProbeProjection
  rw [← productFull_average_commute w hsum I (Finset.univ \ S),
    productFull_full_commute w hsum S I,
    productAverage_commute w hsum (Finset.univ \ S) tail,
    productFull_average_commute w hsum S tail]

lemma productAnova_probe_selector (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (tail I S : Finset ι) (f : ProductSample α → ℂ) :
    productAnova w Finset.univ S (productProbeProjection w tail I f) =
      if I ⊆ S ∧ Disjoint tail S then productAnova w Finset.univ S f else (fun _ => 0) := by
  rw [productAnova_probe_commute w hsum tail I S]
  unfold productProbeProjection
  by_cases ht : Disjoint tail S
  · rw [productAverage_anova_eq w hsum tail S ht]
    by_cases hI : I ⊆ S
    · rw [productFull_anova_eq w hsum I S hI]
      simp [hI, ht]
    · rw [productFull_anova_zero w hsum I S hI]
      simp [hI]
  · rw [productAverage_anova_zero w hsum tail S ht, productFull_zero]
    simp [ht]

lemma productProbeProjection_energy (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (tail I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (productProbeProjection w tail I f) =
      ∑ S ∈ (Finset.univ : Finset ι).powerset,
        if I ⊆ S ∧ Disjoint tail S then productSqNorm w (productAnova w Finset.univ S f) else 0 := by
  rw [← productAnova_energy w hsum Finset.univ (productProbeProjection w tail I f)]
  apply Finset.sum_congr rfl
  intro S _
  rw [productAnova_probe_selector w hsum tail I S]
  split_ifs
  · rfl
  · simp [productSqNorm]

end
end Erdos821.P4Probe
