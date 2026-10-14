import Erdos821.P4Probe.AverageOrthogonality

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

lemma productAverage_empty (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (f : ProductSample α → ℂ) : productAverage w ∅ f = f := by
  funext x
  have ht : ∑ y : ProductSample α, (productWeight w y : ℂ) = 1 := by
    exact_mod_cast productWeight_total w hsum
  have hm (y : ProductSample α) : mixCoords (∅ : Finset ι) x y = x := by
    funext i
    simp [mixCoords]
  simp only [productAverage, hm]
  rw [← Finset.sum_mul, ht, one_mul]

lemma productAverage_sum {β : Type*} (w : ∀ i, α i → ℝ) (S : Finset ι)
    (V : Finset β) (c : β → ℂ) (f : β → ProductSample α → ℂ) (x : ProductSample α) :
    productAverage w S (fun y => ∑ v ∈ V, c v * f v y) x =
      ∑ v ∈ V, c v * productAverage w S (f v) x := by
  unfold productAverage
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  ring

def productFull (w : ∀ i, α i → ℝ) (I : Finset ι)
    (f : ProductSample α → ℂ) (x : ProductSample α) : ℂ :=
  ∑ U ∈ I.powerset, (-1 : ℂ) ^ U.card * productAverage w U f x

lemma productFull_empty (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (f : ProductSample α → ℂ) : productFull w ∅ f = f := by
  funext x
  simp only [productFull, Finset.powerset_empty, Finset.sum_singleton,
    Finset.card_empty, pow_zero, one_mul, productAverage_empty w hsum f]

lemma productFull_insert (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (I : Finset ι) (i : ι) (hi : i ∉ I) (f : ProductSample α → ℂ) :
    productFull w (insert i I) f =
      fun x => productFull w I f x - productAverage w {i} (productFull w I f) x := by
  funext x
  unfold productFull
  rw [Finset.sum_powerset_insert hi, productAverage_sum]
  have ht : (∑ U ∈ I.powerset, (-1 : ℂ) ^ (insert i U).card *
      productAverage w (insert i U) f x) =
      -(∑ U ∈ I.powerset, (-1 : ℂ) ^ U.card *
        productAverage w {i} (productAverage w U f) x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro U hU
    have hiU : i ∉ U := fun h => hi (Finset.mem_powerset.mp hU h)
    rw [Finset.card_insert_of_notMem hiU,
      productAverage_union w hsum {i} U, Finset.singleton_union, pow_succ]
    ring
  rw [ht]
  ring

lemma productFull_sqNorm_le (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1) (I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (productFull w I f) ≤ productSqNorm w f := by
  induction I using Finset.induction_on with
  | empty => rw [productFull_empty w hsum]
  | @insert i I hi hI =>
      rw [productFull_insert w hsum I i hi]
      exact (productComplement_sqNorm_le w hw hsum {i} (productFull w I f)).trans hI

lemma productFull_average_commute (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I S : Finset ι) (f : ProductSample α → ℂ) :
    productFull w I (productAverage w S f) = productAverage w S (productFull w I f) := by
  funext x
  unfold productFull
  rw [productAverage_sum]
  apply Finset.sum_congr rfl
  intro U _
  rw [productAverage_union w hsum U S, productAverage_union w hsum S U,
    Finset.union_comm]

end
end Erdos821.P4Probe
