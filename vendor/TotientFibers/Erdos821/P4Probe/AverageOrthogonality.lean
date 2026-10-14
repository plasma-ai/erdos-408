import Erdos821.P4Probe.ProductAverages

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

def productPair (w : ∀ i, α i → ℝ) (f g : ProductSample α → ℂ) : ℂ :=
  ∑ x, (productWeight w x : ℂ) * star (f x) * g x

def productSqNorm (w : ∀ i, α i → ℝ) (f : ProductSample α → ℂ) : ℝ :=
  ∑ x, productWeight w x * ‖f x‖ ^ 2

lemma productPair_self_re (w : ∀ i, α i → ℝ) (f : ProductSample α → ℂ) :
    (productPair w f f).re = productSqNorm w f := by
  unfold productPair productSqNorm
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_assoc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  simpa only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add, Complex.normSq_apply] using Complex.normSq_eq_norm_sq (f x)

lemma productPair_sub_sub (w : ∀ i, α i → ℝ) (f g : ProductSample α → ℂ) :
    productPair w (fun x => f x - g x) (fun x => f x - g x) =
      productPair w f f - productPair w f g - productPair w g f + productPair w g g := by
  unfold productPair
  simp only [star_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

lemma productAverage_idempotent (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι) (f : ProductSample α → ℂ) :
    productAverage w S (productAverage w S f) = productAverage w S f := by
  funext x
  simpa only [Finset.union_self] using productAverage_union w hsum S S f x

lemma productAverage_pair_self (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι) (f : ProductSample α → ℂ) :
    productPair w f (productAverage w S f) =
      productPair w (productAverage w S f) (productAverage w S f) := by
  have h := productAverage_duality w S f (productAverage w S f)
  rw [productAverage_idempotent w hsum S f] at h
  exact h

lemma productAverage_energy_split (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (fun x => f x - productAverage w S f x) +
        productSqNorm w (productAverage w S f) = productSqNorm w f := by
  have hfg := productAverage_pair_self w hsum S f
  have hgf : productPair w (productAverage w S f) f =
      productPair w (productAverage w S f) (productAverage w S f) := by
    exact (productAverage_duality w S f f).symm.trans hfg
  have h := productPair_sub_sub w f (productAverage w S f)
  rw [hfg, hgf] at h
  have hre := congrArg Complex.re h
  simp only [productPair_self_re, Complex.sub_re, Complex.add_re] at hre
  linarith

lemma productSqNorm_nonneg (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (f : ProductSample α → ℂ) : 0 ≤ productSqNorm w f := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (sq_nonneg _)
  exact Finset.prod_nonneg (fun i _ => hw i (x i))

lemma productAverage_sqNorm_le (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (productAverage w S f) ≤ productSqNorm w f := by
  have he := productAverage_energy_split w hsum S f
  have hn := productSqNorm_nonneg w hw (fun x => f x - productAverage w S f x)
  linarith

lemma productComplement_sqNorm_le (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (fun x => f x - productAverage w S f x) ≤ productSqNorm w f := by
  have he := productAverage_energy_split w hsum S f
  have hn := productSqNorm_nonneg w hw (productAverage w S f)
  linarith

end
end Erdos821.P4Probe
