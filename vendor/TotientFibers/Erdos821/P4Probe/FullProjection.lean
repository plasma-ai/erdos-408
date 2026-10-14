import Erdos821.P4Probe.AlternatingProjections

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

lemma productAverage_sub (w : ∀ i, α i → ℝ) (S : Finset ι)
    (f g : ProductSample α → ℂ) :
    productAverage w S (fun x => f x - g x) =
      fun x => productAverage w S f x - productAverage w S g x := by
  funext x
  simp only [productAverage, mul_sub, Finset.sum_sub_distrib]

lemma productAverage_zero (w : ∀ i, α i → ℝ) (S : Finset ι) :
    productAverage w S (fun _ : ProductSample α => 0) = (fun _ => 0) := by
  funext x
  simp [productAverage]

lemma productFull_mean_zero (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (I : Finset ι) (i : ι) (hi : i ∈ I) (f : ProductSample α → ℂ) :
    productAverage w {i} (productFull w I f) = (fun _ => 0) := by
  rw [← Finset.insert_erase hi, productFull_insert w hsum (I.erase i) i (by simp)]
  rw [productAverage_sub, productAverage_idempotent w hsum {i}]
  funext x
  simp

lemma productFull_average_subset_zero (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I U : Finset ι) (hU : U ⊆ I)
    (hn : U.Nonempty) (f : ProductSample α → ℂ) :
    productAverage w U (productFull w I f) = (fun _ => 0) := by
  obtain ⟨i, hi⟩ := hn
  have hu : U ∪ {i} = U := by
    apply Finset.union_eq_left.mpr
    simpa only [Finset.singleton_subset_iff] using hi
  have h : productAverage w U (productAverage w {i} (productFull w I f)) =
      productAverage w U (productFull w I f) := by
    funext x
    rw [productAverage_union w hsum U {i}, hu]
  rw [productFull_mean_zero w hsum I i (hU hi), productAverage_zero] at h
  exact h.symm

lemma productFull_idempotent (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I : Finset ι) (f : ProductSample α → ℂ) :
    productFull w I (productFull w I f) = productFull w I f := by
  funext x
  change (∑ U ∈ I.powerset, (-1 : ℂ) ^ U.card *
    productAverage w U (productFull w I f) x) = _
  rw [Finset.sum_eq_single ∅]
  · simp only [Finset.card_empty, pow_zero, one_mul, productAverage_empty w hsum]
  · intro U hU hne
    rw [productFull_average_subset_zero w hsum I U (Finset.mem_powerset.mp hU)
      (Finset.nonempty_iff_ne_empty.mpr hne), mul_zero]
  · simp

lemma productFull_duality (w : ∀ i, α i → ℝ) (I : Finset ι)
    (f g : ProductSample α → ℂ) :
    productPair w f (productFull w I g) = productPair w (productFull w I f) g := by
  unfold productPair productFull
  simp only [star_sum, star_mul, star_pow, star_neg, star_one]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := I.powerset),
    Finset.sum_comm (s := Finset.univ) (t := I.powerset)]
  apply Finset.sum_congr rfl
  intro U _
  have h := productAverage_duality w U f g
  have hleft : (∑ x : ProductSample α,
      (productWeight w x : ℂ) * star (f x) *
        ((-1 : ℂ) ^ U.card * productAverage w U g x)) =
      (-1 : ℂ) ^ U.card *
        ∑ x, (productWeight w x : ℂ) * star (f x) * productAverage w U g x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hright : (∑ x : ProductSample α,
      (productWeight w x : ℂ) *
        (star (productAverage w U f x) * (-1 : ℂ) ^ U.card) * g x) =
      (-1 : ℂ) ^ U.card *
        ∑ x, (productWeight w x : ℂ) * star (productAverage w U f x) * g x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hleft, hright, h]

lemma productFull_pair_self (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I : Finset ι) (f : ProductSample α → ℂ) :
    productPair w f (productFull w I f) =
      productPair w (productFull w I f) (productFull w I f) := by
  have h := productFull_duality w I f (productFull w I f)
  rw [productFull_idempotent w hsum I f] at h
  exact h

lemma productFull_energy_split (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (fun x => f x - productFull w I f x) +
        productSqNorm w (productFull w I f) = productSqNorm w f := by
  have hfg := productFull_pair_self w hsum I f
  have hgf : productPair w (productFull w I f) f =
      productPair w (productFull w I f) (productFull w I f) :=
    (productFull_duality w I f f).symm.trans hfg
  have h := productPair_sub_sub w f (productFull w I f)
  rw [hfg, hgf] at h
  have hre := congrArg Complex.re h
  simp only [productPair_self_re, Complex.sub_re, Complex.add_re] at hre
  linarith

lemma productFull_complement_sqNorm_le (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1) (I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (fun x => f x - productFull w I f x) ≤ productSqNorm w f := by
  have he := productFull_energy_split w hsum I f
  have hn := productSqNorm_nonneg w hw (productFull w I f)
  linarith

end
end Erdos821.P4Probe
