import Erdos821.P4Probe.SharedPairingTask

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Shared

noncomputable section

open Erdos821.P4Probe

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

abbrev FreshSample (S : Finset ι) (α : ι → Type*) :=
  ∀ i : {i // i ∉ S}, α i.val

lemma freshProductWeight_eq_productWeight
    (w : ∀ i, α i → ℝ) (S : Finset ι) (y : ProductSample α) :
    freshProductWeight w S y =
      productWeight (fun i : {i // i ∉ S} => w i.val) (fun i => y i.val) := by
  classical
  unfold freshProductWeight productWeight
  change (∏ i ∈ Finset.univ, if i ∈ S then (1 : ℝ) else w i (y i)) =
    ∏ i : {i // i ∉ S}, w i.val (y i.val)
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  exact Finset.prod_subtype (p := fun i : ι => i ∉ S)
    (Finset.univ.filter fun i : ι => i ∉ S)
    (by intro i; simp) (fun i => w i (y i))

lemma joinSharedFresh_shared (S : Finset ι) (s : PartialSample S α)
    (u : FreshSample S α) :
    (fun i : {i // i ∈ S} => joinSharedFresh S s u i.val) = s := by
  funext i
  simp [joinSharedFresh, Equiv.piEquivPiSubtypeProd, i.property]

lemma joinSharedFresh_fresh (S : Finset ι) (s : PartialSample S α)
    (u : FreshSample S α) :
    (fun i : {i // i ∉ S} => joinSharedFresh S s u i.val) = u := by
  funext i
  simp [joinSharedFresh, Equiv.piEquivPiSubtypeProd, i.property]

lemma productWeight_joinSharedFresh (w : ∀ i, α i → ℝ) (S : Finset ι)
    (s : PartialSample S α) (u : FreshSample S α) :
    productWeight w (joinSharedFresh S s u) =
      partialProductWeight w S s *
        productWeight (fun i : {i // i ∉ S} => w i.val) u := by
  rw [productWeight_split]
  rw [joinSharedFresh_shared, joinSharedFresh_fresh]

lemma freshProductWeight_joinSharedFresh (w : ∀ i, α i → ℝ) (S : Finset ι)
    (s : PartialSample S α) (u : FreshSample S α) :
    freshProductWeight w S (joinSharedFresh S s u) =
      productWeight (fun i : {i // i ∉ S} => w i.val) u := by
  rw [freshProductWeight_eq_productWeight, joinSharedFresh_fresh]

lemma sameShared_joinSharedFresh_iff (S : Finset ι)
    (s t : PartialSample S α) (u v : FreshSample S α) :
    sameShared S (joinSharedFresh S s u) (joinSharedFresh S t v) ↔ s = t := by
  constructor
  · intro h
    funext i
    have hi := h i.val i.property
    simpa [joinSharedFresh, Equiv.piEquivPiSubtypeProd] using hi
  · intro h i hi
    subst t
    simp [joinSharedFresh, Equiv.piEquivPiSubtypeProd, hi]

theorem SharedPairingTask_proof : P4Probe.SharedPairingTask := by
  intro ι _ α _ w S H
  let e : ProductSample α ≃ PartialSample S α × FreshSample S α :=
    Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) α
  let q : ProductSample α × ProductSample α ≃
      (PartialSample S α × FreshSample S α) × (PartialSample S α × FreshSample S α) :=
    e.prodCongr e
  let G : ((PartialSample S α × FreshSample S α) ×
      (PartialSample S α × FreshSample S α)) → ℂ := fun z =>
    if sameShared S (joinSharedFresh S z.1.1 z.1.2) (joinSharedFresh S z.2.1 z.2.2) then
      ((productWeight w (joinSharedFresh S z.1.1 z.1.2) *
        freshProductWeight w S (joinSharedFresh S z.2.1 z.2.2) : ℝ) : ℂ) *
        H (joinSharedFresh S z.1.1 z.1.2) (joinSharedFresh S z.2.1 z.2.2)
    else 0
  have hreindex :
      (∑ x : ProductSample α, ∑ y : ProductSample α,
        if sameShared S x y then
          ((productWeight w x * freshProductWeight w S y : ℝ) : ℂ) * H x y else 0) =
        ∑ z, G z := by
    calc
      _ = ∑ z : ProductSample α × ProductSample α,
          (if sameShared S z.1 z.2 then
            ((productWeight w z.1 * freshProductWeight w S z.2 : ℝ) : ℂ) *
              H z.1 z.2 else 0) := by
            rw [← Fintype.sum_prod_type (fun z : ProductSample α × ProductSample α =>
              if sameShared S z.1 z.2 then
                ((productWeight w z.1 * freshProductWeight w S z.2 : ℝ) : ℂ) * H z.1 z.2
              else 0)]
      _ = ∑ z, G z := by
            apply Fintype.sum_equiv q
            intro z
            simp [G, q, e, P4Probe.joinSharedFresh, Equiv.piEquivPiSubtypeProd]
  have hfactor :
      (∑ z : (PartialSample S α × FreshSample S α) ×
          (PartialSample S α × FreshSample S α), G z) =
        ∑ s : PartialSample S α, ∑ u : FreshSample S α,
          ∑ t : PartialSample S α, ∑ v : FreshSample S α,
            if s = t then
              ((partialProductWeight w S s *
                productWeight (fun i : {i // i ∉ S} => w i.val) u *
                productWeight (fun i : {i // i ∉ S} => w i.val) v : ℝ) : ℂ) *
                H (joinSharedFresh S s u) (joinSharedFresh S t v)
            else 0 := by
    calc
      _ = ∑ p : PartialSample S α × FreshSample S α,
          ∑ r : PartialSample S α × FreshSample S α, G (p, r) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ s : PartialSample S α, ∑ u : FreshSample S α,
          ∑ t : PartialSample S α, ∑ v : FreshSample S α, G ((s, u), (t, v)) := by
            simp only [Fintype.sum_prod_type]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro s _
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro v _
            dsimp [G]
            rw [sameShared_joinSharedFresh_iff,
              productWeight_joinSharedFresh, freshProductWeight_joinSharedFresh]
            split_ifs <;> simp [mul_assoc]
  have hcollapse :
      (∑ s : PartialSample S α, ∑ u : FreshSample S α,
        ∑ t : PartialSample S α, ∑ v : FreshSample S α,
          if s = t then
            ((partialProductWeight w S s *
              productWeight (fun i : {i // i ∉ S} => w i.val) u *
              productWeight (fun i : {i // i ∉ S} => w i.val) v : ℝ) : ℂ) *
              H (joinSharedFresh S s u) (joinSharedFresh S t v)
          else 0) =
      ∑ s : PartialSample S α, ∑ u : FreshSample S α, ∑ v : FreshSample S α,
        ((partialProductWeight w S s *
          productWeight (fun i : {i // i ∉ S} => w i.val) u *
          productWeight (fun i : {i // i ∉ S} => w i.val) v : ℝ) : ℂ) *
          H (joinSharedFresh S s u) (joinSharedFresh S s v) := by
    classical
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_comm]
    simp
  calc
    _ = ∑ z, G z := hreindex
    _ = ∑ s : PartialSample S α, ∑ u : FreshSample S α,
        ∑ t : PartialSample S α, ∑ v : FreshSample S α,
          if s = t then
            ((partialProductWeight w S s *
              productWeight (fun i : {i // i ∉ S} => w i.val) u *
              productWeight (fun i : {i // i ∉ S} => w i.val) v : ℝ) : ℂ) *
              H (joinSharedFresh S s u) (joinSharedFresh S t v)
          else 0 := hfactor
    _ = ∑ s : PartialSample S α, ∑ u : FreshSample S α, ∑ v : FreshSample S α,
        ((partialProductWeight w S s *
          productWeight (fun i : {i // i ∉ S} => w i.val) u *
          productWeight (fun i : {i // i ∉ S} => w i.val) v : ℝ) : ℂ) *
          H (joinSharedFresh S s u) (joinSharedFresh S s v) := hcollapse

end
end Erdos821.P4Shared
