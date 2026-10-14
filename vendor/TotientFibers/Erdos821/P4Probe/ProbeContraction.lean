import Erdos821.P4Probe.ProjectionSelector

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

lemma productProbeProjection_tail_fixed (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (tail I : Finset ι) (f : ProductSample α → ℂ) :
    productAverage w tail (productProbeProjection w tail I f) = productProbeProjection w tail I f := by
  unfold productProbeProjection
  rw [← productFull_average_commute w hsum I tail, productAverage_idempotent w hsum tail]

lemma productProbeProjection_idempotent (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (tail I : Finset ι) (f : ProductSample α → ℂ) :
    productProbeProjection w tail I (productProbeProjection w tail I f) =
      productProbeProjection w tail I f := by
  unfold productProbeProjection
  rw [← productFull_average_commute w hsum I tail,
    productAverage_idempotent w hsum tail, productFull_idempotent w hsum I]

lemma productProbeProjection_duality (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (tail I : Finset ι) (f g : ProductSample α → ℂ) :
    productPair w f (productProbeProjection w tail I g) =
      productPair w (productProbeProjection w tail I f) g := by
  unfold productProbeProjection
  rw [productFull_duality]
  have h : productPair w (productFull w I f) (productAverage w tail g) =
      productPair w (productAverage w tail (productFull w I f)) g :=
    productAverage_duality w tail (productFull w I f) g
  rw [h, ← productFull_average_commute w hsum I tail]

lemma productProbeProjection_energy_split (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (tail I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (fun x => f x - productProbeProjection w tail I f x) +
      productSqNorm w (productProbeProjection w tail I f) = productSqNorm w f := by
  have hfg := productProbeProjection_duality w hsum tail I f
    (productProbeProjection w tail I f)
  rw [productProbeProjection_idempotent w hsum tail I f] at hfg
  have hgf := (productProbeProjection_duality w hsum tail I f f).symm.trans hfg
  have h := productPair_sub_sub w f (productProbeProjection w tail I f)
  rw [hfg, hgf] at h
  have hre := congrArg Complex.re h
  simp only [productPair_self_re, Complex.sub_re, Complex.add_re] at hre
  linarith

lemma productProbeProjection_sqNorm_le (w : ∀ i, α i → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hsum : ∀ i, ∑ a, w i a = 1)
    (tail I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (productProbeProjection w tail I f) ≤ productSqNorm w f := by
  have he := productProbeProjection_energy_split w hsum tail I f
  have hn := productSqNorm_nonneg w hw (fun x => f x - productProbeProjection w tail I f x)
  linarith

lemma productProbeProjection_complement_sqNorm_le (w : ∀ i, α i → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hsum : ∀ i, ∑ a, w i a = 1)
    (tail I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (fun x => f x - productProbeProjection w tail I f x) ≤ productSqNorm w f := by
  have he := productProbeProjection_energy_split w hsum tail I f
  have hn := productSqNorm_nonneg w hw (productProbeProjection w tail I f)
  linarith

lemma productProbeProjection_average_complement_sqNorm_le (w : ∀ i, α i → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hsum : ∀ i, ∑ a, w i a = 1)
    (tail I : Finset ι) (f : ProductSample α → ℂ) :
    productSqNorm w (fun x => productAverage w tail f x -
      productProbeProjection w tail I f x) ≤ productSqNorm w f := by
  have h := productProbeProjection_complement_sqNorm_le w hw hsum tail I
    (productAverage w tail f)
  have hid : productProbeProjection w tail I (productAverage w tail f) =
      productProbeProjection w tail I f := by
    unfold productProbeProjection
    rw [productAverage_idempotent w hsum tail]
  rw [hid] at h
  exact h.trans (productAverage_sqNorm_le w hw hsum tail f)

end
end Erdos821.P4Probe
