import Mathlib

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

abbrev ProductSample (α : ι → Type*) := ∀ i, α i

def productWeight (w : ∀ i, α i → ℝ) (x : ProductSample α) : ℝ := ∏ i, w i (x i)

def mixCoords (S : Finset ι) (x y : ProductSample α) : ProductSample α :=
  fun i => if i ∈ S then y i else x i

def productAverage (w : ∀ i, α i → ℝ) (S : Finset ι)
    (f : ProductSample α → ℂ) (x : ProductSample α) : ℂ :=
  ∑ y, (productWeight w y : ℂ) * f (mixCoords S x y)

lemma mixCoords_involution (S : Finset ι) (x y : ProductSample α) :
    mixCoords S (mixCoords S x y) (mixCoords S y x) = x := by
  funext i
  by_cases hi : i ∈ S <;> simp [mixCoords, hi]

def swapCoords (S : Finset ι) :
    ProductSample α × ProductSample α ≃ ProductSample α × ProductSample α where
  toFun z := (mixCoords S z.1 z.2, mixCoords S z.2 z.1)
  invFun z := (mixCoords S z.1 z.2, mixCoords S z.2 z.1)
  left_inv z := by ext <;> simp only [mixCoords_involution]
  right_inv z := by ext <;> simp only [mixCoords_involution]

lemma productWeight_swap (w : ∀ i, α i → ℝ) (S : Finset ι)
    (x y : ProductSample α) :
    productWeight w (mixCoords S x y) * productWeight w (mixCoords S y x) =
      productWeight w x * productWeight w y := by
  unfold productWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [mixCoords, hi, mul_comm]

lemma productWeight_total (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1) :
    ∑ x : ProductSample α, productWeight w x = 1 := by
  change (∑ x : ProductSample α, ∏ i, w i (x i)) = 1
  trans ∏ i, ∑ a : α i, w i a
  · exact (Fintype.prod_sum w).symm
  · simp only [hsum, Finset.prod_const_one]

lemma mixCoords_union (A B : Finset ι) (x y z : ProductSample α) :
    mixCoords B (mixCoords A x y) z = mixCoords (A ∪ B) x (mixCoords B y z) := by
  funext i
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [mixCoords, ha, hb]

lemma productAverage_union (w : ∀ i, α i → ℝ) (hsum : ∀ i, ∑ a, w i a = 1)
    (A B : Finset ι) (f : ProductSample α → ℂ) (x : ProductSample α) :
    productAverage w A (productAverage w B f) x = productAverage w (A ∪ B) f x := by
  have htotal : ∑ y : ProductSample α, (productWeight w y : ℂ) = 1 := by
    exact_mod_cast productWeight_total w hsum
  let H : ProductSample α × ProductSample α → ℂ := fun z =>
    (productWeight w z.1 : ℂ) * (productWeight w z.2 : ℂ) * f (mixCoords (A ∪ B) x z.1)
  have heq : (∑ y : ProductSample α, ∑ z : ProductSample α,
      (productWeight w y : ℂ) * (productWeight w z : ℂ) *
        f (mixCoords B (mixCoords A x y) z)) = ∑ z, H z := by
    rw [← Fintype.sum_prod_type (fun z : ProductSample α × ProductSample α =>
      (productWeight w z.1 : ℂ) * (productWeight w z.2 : ℂ) *
        f (mixCoords B (mixCoords A x z.1) z.2))]
    apply Fintype.sum_equiv (swapCoords B)
    intro z
    dsimp [H, swapCoords]
    rw [mixCoords_union]
    have hw : (productWeight w (mixCoords B z.1 z.2) : ℂ) *
        (productWeight w (mixCoords B z.2 z.1) : ℂ) =
        (productWeight w z.1 : ℂ) * (productWeight w z.2 : ℂ) := by
      exact_mod_cast productWeight_swap w B z.1 z.2
    rw [hw]
  unfold productAverage
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [heq, Fintype.sum_prod_type]
  dsimp [H]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ z : ProductSample α, (productWeight w y : ℂ) * (productWeight w z : ℂ) *
        f (mixCoords (A ∪ B) x y)) =
      (productWeight w y : ℂ) * f (mixCoords (A ∪ B) x y) *
        ∑ z : ProductSample α, (productWeight w z : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [htotal, mul_one]

lemma productAverage_duality (w : ∀ i, α i → ℝ) (S : Finset ι)
    (f g : ProductSample α → ℂ) :
    (∑ x, (productWeight w x : ℂ) * star (f x) * productAverage w S g x) =
      ∑ x, (productWeight w x : ℂ) * star (productAverage w S f x) * g x := by
  let R : ProductSample α × ProductSample α → ℂ := fun z =>
    (productWeight w z.1 : ℂ) * (productWeight w z.2 : ℂ) *
      star (f (mixCoords S z.1 z.2)) * g z.1
  have heq : (∑ x : ProductSample α, ∑ y : ProductSample α,
      (productWeight w x : ℂ) * (productWeight w y : ℂ) *
        star (f x) * g (mixCoords S x y)) = ∑ z, R z := by
    rw [← Fintype.sum_prod_type (fun z : ProductSample α × ProductSample α =>
      (productWeight w z.1 : ℂ) * (productWeight w z.2 : ℂ) *
        star (f z.1) * g (mixCoords S z.1 z.2))]
    apply Fintype.sum_equiv (swapCoords S)
    intro z
    dsimp [R, swapCoords]
    rw [mixCoords_involution]
    have hw : (productWeight w (mixCoords S z.1 z.2) : ℂ) *
        (productWeight w (mixCoords S z.2 z.1) : ℂ) =
        (productWeight w z.1 : ℂ) * (productWeight w z.2 : ℂ) := by
      exact_mod_cast productWeight_swap w S z.1 z.2
    rw [hw]
  unfold productAverage
  simp_rw [Finset.mul_sum]
  have hleft : (∑ x : ProductSample α, ∑ y : ProductSample α,
      (productWeight w x : ℂ) * star (f x) *
        ((productWeight w y : ℂ) * g (mixCoords S x y))) =
      ∑ x : ProductSample α, ∑ y : ProductSample α,
        (productWeight w x : ℂ) * (productWeight w y : ℂ) *
          star (f x) * g (mixCoords S x y) := by
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hleft, heq, Fintype.sum_prod_type]
  simp only [R, star_sum, star_mul, Complex.star_def, Complex.conj_ofReal]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

end
end Erdos821.P4Probe
