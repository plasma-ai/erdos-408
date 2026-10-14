import Erdos821.P4Probe.ProductAverages

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

abbrev PartialSample (S : Finset ι) (α : ι → Type*) := ∀ i : {i // i ∈ S}, α i.val

def partialProductWeight (w : ∀ i, α i → ℝ) (S : Finset ι)
    (a : PartialSample S α) : ℝ := ∏ i, w i.val (a i)

def fillCoords (S : Finset ι) (x : ProductSample α) (a : PartialSample S α) :
    ProductSample α := fun i => if hi : i ∈ S then a ⟨i, hi⟩ else x i

lemma fillCoords_restrict (S : Finset ι) (x y : ProductSample α) :
    fillCoords S x (fun i => y i.val) = mixCoords S x y := by
  funext i
  by_cases hi : i ∈ S <;> simp [fillCoords, mixCoords, hi]

lemma productWeight_split (w : ∀ i, α i → ℝ) (S : Finset ι) (y : ProductSample α) :
    productWeight w y = partialProductWeight w S (fun i => y i.val) *
      productWeight (fun i : {i // i ∉ S} => w i.val) (fun i => y i.val) := by
  convert (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)
    (fun i => w i (y i))).symm using 1 <;> congr! 2
  unfold partialProductWeight
  congr!

lemma productAverage_marginal (w : ∀ i, α i → ℝ)
    (hsum : ∀ i, ∑ a, w i a = 1) (S : Finset ι)
    (f : ProductSample α → ℂ) (x : ProductSample α) :
    productAverage w S f x =
      ∑ a : PartialSample S α, (partialProductWeight w S a : ℂ) * f (fillCoords S x a) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) α
  let H : PartialSample S α × (∀ i : {i // i ∉ S}, α i.val) → ℂ := fun z =>
    (partialProductWeight w S z.1 : ℂ) *
      (productWeight (fun i : {i // i ∉ S} => w i.val) z.2 : ℂ) * f (fillCoords S x z.1)
  have hreindex : productAverage w S f x = ∑ z, H z := by
    unfold productAverage
    apply Fintype.sum_equiv e
    intro y
    dsimp [H, e, Equiv.piEquivPiSubtypeProd]
    rw [fillCoords_restrict, productWeight_split w S y, Complex.ofReal_mul]
  have htotal : (∑ b : ∀ i : {i // i ∉ S}, α i.val,
      (productWeight (fun i : {i // i ∉ S} => w i.val) b : ℂ)) = 1 := by
    have ht : (∑ b : ∀ i : {i // i ∉ S}, α i.val,
        productWeight (fun i : {i // i ∉ S} => w i.val) b) = 1 := by
      convert productWeight_total (fun i : {i // i ∉ S} => w i.val)
        (fun i => hsum i.val) using 1 <;> congr! 2
    exact_mod_cast ht
  rw [hreindex, Fintype.sum_prod_type H]
  apply Finset.sum_congr rfl
  intro a _
  dsimp [H]
  calc
    (∑ b : ∀ i : {i // i ∉ S}, α i.val,
        (partialProductWeight w S a : ℂ) *
          (productWeight (fun i : {i // i ∉ S} => w i.val) b : ℂ) * f (fillCoords S x a)) =
      (partialProductWeight w S a : ℂ) * f (fillCoords S x a) *
        ∑ b : ∀ i : {i // i ∉ S}, α i.val,
          (productWeight (fun i : {i // i ∉ S} => w i.val) b : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [htotal, mul_one]

end
end Erdos821.P4Probe
