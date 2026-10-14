import Erdos821.P5.HarmonicLists

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core

def productLaw {ι : Type*} [Fintype ι] {α : ι → Type*}
    (w : ∀ i, α i → ℝ) (z : ∀ i, α i) : ℝ := ∏ i, w i (z i)

theorem productLaw_nonneg {ι : Type*} [Fintype ι] {α : ι → Type*}
    (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a) (z : ∀ i, α i) :
    0 ≤ productLaw w z := Finset.prod_nonneg (fun i hi => hw i (z i))

theorem productLaw_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (w : ∀ i, α i → ℝ) (hs : ∀ i, (∑ a, w i a) = 1) :
    (∑ z : ∀ i, α i, productLaw w z) = 1 := by
  unfold productLaw
  rw [← Fintype.prod_sum]
  simp only [hs, Finset.prod_const_one]

theorem productLaw_splitAt {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    (w : ∀ i, α i → ℝ) (i : ι) (z : ∀ i, α i) :
    productLaw w z = w i (z i) *
      productLaw (fun j : {j : ι // j ≠ i} => w j.val) (fun j => z j.val) := by
  exact Fintype.prod_eq_mul_prod_subtype_ne (fun j => w j (z j)) i

/-- Exact conditional summation over one independent coordinate. The test
may depend on every other coordinate. -/
theorem productLaw_sum_splitAt {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (i : ι) (f : (∀ i, α i) → ℝ) :
    (∑ z, productLaw w z * f z) =
      ∑ r : ∀ j : {j : ι // j ≠ i}, α j.val,
        productLaw (fun j : {j : ι // j ≠ i} => w j.val) r *
          ∑ a : α i, w i a * f ((Equiv.piSplitAt i α).symm (a, r)) := by
  have heq := Fintype.sum_equiv (Equiv.piSplitAt i α)
    (fun z => productLaw w z * f z)
    (fun z : α i × (∀ j : {j : ι // j ≠ i}, α j.val) =>
      w i z.1 * productLaw (fun j : {j : ι // j ≠ i} => w j.val) z.2 *
        f ((Equiv.piSplitAt i α).symm z)) ?_
  · rw [heq, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  · intro z
    have hz : (Equiv.piSplitAt i α).symm (z i, fun j => z j.val) = z :=
      (Equiv.piSplitAt i α).symm_apply_apply z
    rw [productLaw_splitAt w i z]
    simp only [Equiv.piSplitAt_apply]
    rw [hz]

theorem productLaw_conditional_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (w : ∀ i, α i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hs : ∀ i, (∑ a, w i a) = 1) (i : ι) (f : (∀ i, α i) → ℝ) (B : ℝ)
    (hb : ∀ r : ∀ j : {j : ι // j ≠ i}, α j.val,
      (∑ a : α i, w i a * f ((Equiv.piSplitAt i α).symm (a, r))) ≤ B) :
    (∑ z, productLaw w z * f z) ≤ B := by
  rw [productLaw_sum_splitAt]
  calc
    _ ≤ ∑ r : ∀ j : {j : ι // j ≠ i}, α j.val,
        productLaw (fun j : {j : ι // j ≠ i} => w j.val) r * B :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hb r)
        (productLaw_nonneg _ (fun j a => hw j.val a) r))
    _ = B := by
      have hrest : (∑ r : ∀ j : {j : ι // j ≠ i}, α j.val,
          productLaw (fun j : {j : ι // j ≠ i} => w j.val) r) = 1 :=
        productLaw_sum (α := fun j : {j : ι // j ≠ i} => α j.val) _ (fun j => hs j.val)
      rw [← Finset.sum_mul, hrest, one_mul]

end Erdos821.P5Core
