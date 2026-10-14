import Erdos821.P4Probe.FullProjection

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

def productAnova (w : ∀ i, α i → ℝ) (I S : Finset ι)
    (f : ProductSample α → ℂ) : ProductSample α → ℂ :=
  productFull w S (productAverage w (I \ S) f)

lemma productAnova_empty (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (f : ProductSample α → ℂ) : productAnova w ∅ ∅ f = f := by
  rw [productAnova, Finset.sdiff_empty, productAverage_empty w hsum,
    productFull_empty w hsum]

lemma productAnova_insert_unselected (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (i : ι)
    (hi : i ∉ I) (hS : S ⊆ I) (f : ProductSample α → ℂ) :
    productAnova w (insert i I) S f = productAverage w {i} (productAnova w I S f) := by
  have hiS : i ∉ S := fun h => hi (hS h)
  have hdiff : insert i I \ S = {i} ∪ (I \ S) := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [hi, hiS]
    · simp [hj]
  have havg : productAverage w (insert i I \ S) f =
      productAverage w {i} (productAverage w (I \ S) f) := by
    funext x
    rw [productAverage_union w hsum {i} (I \ S), hdiff]
  unfold productAnova
  rw [havg, productFull_average_commute w hsum S {i}]

lemma productAnova_insert_selected (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (i : ι)
    (hi : i ∉ I) (hS : S ⊆ I) (f : ProductSample α → ℂ) :
    productAnova w (insert i I) (insert i S) f =
      fun x => productAnova w I S f x - productAverage w {i} (productAnova w I S f) x := by
  have hiS : i ∉ S := fun h => hi (hS h)
  have hdiff : insert i I \ insert i S = I \ S := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [hi, hiS]
    · simp [hj]
  unfold productAnova
  rw [hdiff, productFull_insert w hsum S i hiS]

lemma productAnova_sum (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (I : Finset ι) (f : ProductSample α → ℂ) :
    (fun x => ∑ S ∈ I.powerset, productAnova w I S f x) = f := by
  induction I using Finset.induction_on with
  | empty =>
      simp only [Finset.powerset_empty, Finset.sum_singleton, productAnova_empty w hsum]
  | @insert i I hi hI =>
      funext x
      rw [Finset.sum_powerset_insert hi]
      have hleft : (∑ S ∈ I.powerset, productAnova w (insert i I) S f x) =
          ∑ S ∈ I.powerset, productAverage w {i} (productAnova w I S f) x := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [productAnova_insert_unselected w hsum I S i hi (Finset.mem_powerset.mp hS)]
      have hright : (∑ S ∈ I.powerset, productAnova w (insert i I) (insert i S) f x) =
          ∑ S ∈ I.powerset,
            (productAnova w I S f x - productAverage w {i} (productAnova w I S f) x) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [productAnova_insert_selected w hsum I S i hi (Finset.mem_powerset.mp hS)]
      rw [hleft, hright, Finset.sum_sub_distrib]
      have hx := congrFun hI x
      change (∑ S ∈ I.powerset, productAnova w I S f x) = f x at hx
      rw [← hx]
      ring

lemma productAnova_energy (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (I : Finset ι) (f : ProductSample α → ℂ) :
    (∑ S ∈ I.powerset, productSqNorm w (productAnova w I S f)) = productSqNorm w f := by
  induction I using Finset.induction_on with
  | empty =>
      simp only [Finset.powerset_empty, Finset.sum_singleton, productAnova_empty w hsum]
  | @insert i I hi hI =>
      rw [Finset.sum_powerset_insert hi, ← Finset.sum_add_distrib]
      trans ∑ S ∈ I.powerset, productSqNorm w (productAnova w I S f)
      · apply Finset.sum_congr rfl
        intro S hS
        rw [productAnova_insert_unselected w hsum I S i hi (Finset.mem_powerset.mp hS),
          productAnova_insert_selected w hsum I S i hi (Finset.mem_powerset.mp hS)]
        have he := productAverage_energy_split w hsum {i} (productAnova w I S f)
        linarith
      · exact hI

lemma productAnova_mean_zero (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (i : ι)
    (hi : i ∈ S) (f : ProductSample α → ℂ) :
    productAverage w {i} (productAnova w I S f) = (fun _ => 0) :=
  productFull_mean_zero w hsum S i hi _

lemma productAnova_independent (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (i : ι)
    (hi : i ∈ I) (hiS : i ∉ S) (f : ProductSample α → ℂ) :
    productAverage w {i} (productAnova w I S f) = productAnova w I S f := by
  have hin : i ∈ I \ S := Finset.mem_sdiff.mpr ⟨hi, hiS⟩
  have hu : {i} ∪ (I \ S) = I \ S := by
    apply Finset.union_eq_right.mpr
    simpa only [Finset.singleton_subset_iff] using hin
  unfold productAnova
  rw [← productFull_average_commute w hsum S {i}]
  congr 1
  funext x
  rw [productAverage_union w hsum {i} (I \ S), hu]

lemma productPair_star_swap (w : ∀ i, α i → ℝ) (f g : ProductSample α → ℂ) :
    star (productPair w f g) = productPair w g f := by
  unfold productPair
  simp only [star_sum, star_mul, star_star, Complex.star_def, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro x _
  change star (g x) * (star (star (f x)) * (productWeight w x : ℂ)) =
    (productWeight w x : ℂ) * star (g x) * f x
  rw [star_star]
  ring

lemma productAnova_pair_zero_of_mem (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S T : Finset ι) (hT : T ⊆ I)
    (i : ι) (hi : i ∈ S) (hiI : i ∈ I) (hiT : i ∉ T) (f g : ProductSample α → ℂ) :
    productPair w (productAnova w I S f) (productAnova w I T g) = 0 := by
  have h := productAverage_duality w {i} (productAnova w I S f) (productAnova w I T g)
  rw [productAnova_independent w hsum I T i hiI hiT,
    productAnova_mean_zero w hsum I S i hi] at h
  simpa only [productPair, star_zero, mul_zero, zero_mul, Finset.sum_const_zero] using h

lemma productAnova_pairwise_orthogonal (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S T : Finset ι) (hS : S ⊆ I) (hT : T ⊆ I)
    (hne : S ≠ T) (f g : ProductSample α → ℂ) :
    productPair w (productAnova w I S f) (productAnova w I T g) = 0 := by
  by_cases hST : S ⊆ T
  · have hTS : ¬T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
    obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hTS
    have hrev := productAnova_pair_zero_of_mem w hsum I T S hS i hiT (hT hiT) hiS g f
    have h := congrArg star hrev
    simpa only [productPair_star_swap, star_zero] using h
  · obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp hST
    exact productAnova_pair_zero_of_mem w hsum I S T hT i hiS (hS hiS) hiT f g

lemma productAnova_component_sqNorm_le (w : ∀ i, α i → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hsum : ∀ i, ∑ a, w i a = 1)
    (I S : Finset ι) (hS : S ⊆ I) (f : ProductSample α → ℂ) :
    productSqNorm w (productAnova w I S f) ≤ productSqNorm w f := by
  calc
    _ ≤ ∑ T ∈ I.powerset, productSqNorm w (productAnova w I T f) :=
      Finset.single_le_sum (fun T _ => productSqNorm_nonneg w hw _) (Finset.mem_powerset.mpr hS)
    _ = _ := productAnova_energy w hsum I f

end
end Erdos821.P4Probe
