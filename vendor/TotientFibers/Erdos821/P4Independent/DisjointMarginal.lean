import Erdos821.P4Probe.SelectedTuples
import Erdos821.P4Probe.DisjointMarginalTask

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Indep

open Erdos821.P4Probe

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {α : ι → Type*} [∀ i, Fintype (α i)]

def splitPartial (S T : Finset ι) (c : PartialSample (S ∪ T) α) :
    PartialSample S α × PartialSample T α :=
  (fun i => c ⟨i.val, Finset.mem_union.mpr (Or.inl i.property)⟩,
   fun i => c ⟨i.val, Finset.mem_union.mpr (Or.inr i.property)⟩)

def joinPartial (S T : Finset ι) (hST : Disjoint S T)
    (a : PartialSample S α) (b : PartialSample T α) : PartialSample (S ∪ T) α :=
  fun i => if hi : i.val ∈ S then a ⟨i.val, hi⟩ else
    b ⟨i.val, by
      rcases Finset.mem_union.mp i.property with hs | ht
      · exact False.elim (hi hs)
      · exact ht⟩

def partialUnionEquiv (S T : Finset ι) (hST : Disjoint S T) :
    PartialSample (S ∪ T) α ≃ PartialSample S α × PartialSample T α where
  toFun := splitPartial S T
  invFun := fun z => joinPartial S T hST z.1 z.2
  left_inv := by
    intro c
    funext i
    by_cases hi : i.val ∈ S
    · simp [splitPartial, joinPartial, hi]
    · have ht : i.val ∈ T := by
        rcases Finset.mem_union.mp i.property with hs | ht
        · exact False.elim (hi hs)
        · exact ht
      simp [splitPartial, joinPartial, hi, ht]
  right_inv := by
    intro z
    rcases z with ⟨a, b⟩
    apply Prod.ext
    · funext i
      simp [splitPartial, joinPartial, i.property]
    · funext i
      have hi : i.val ∉ S := by
        intro his
        exact (Finset.disjoint_left.mp hST) his i.property
      simp [splitPartial, joinPartial, hi]

lemma partialProductWeight_join (w : ∀ i, α i → ℝ)
    (S T : Finset ι) (hST : Disjoint S T)
    (a : PartialSample S α) (b : PartialSample T α) :
    partialProductWeight w (S ∪ T) (joinPartial S T hST a b) =
      partialProductWeight w S a * partialProductWeight w T b := by
  let eS : {i : {i // i ∈ S ∪ T} // i.val ∈ S} ≃ {i // i ∈ S} := {
    toFun := fun z => ⟨z.val.val, z.property⟩
    invFun := fun z => ⟨⟨z.val, Finset.mem_union.mpr (Or.inl z.property)⟩, z.property⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
  }
  let eT : {i : {i // i ∈ S ∪ T} // i.val ∉ S} ≃ {i // i ∈ T} := {
    toFun := fun z => ⟨z.val.val, (Finset.mem_union.mp z.val.property).resolve_left z.property⟩
    invFun := fun z => ⟨⟨z.val, Finset.mem_union.mpr (Or.inr z.property)⟩, by
      intro hs
      exact (Finset.disjoint_left.mp hST) hs z.property⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
  }
  have hs :
      (∏ z : {i : {i // i ∈ S ∪ T} // i.val ∈ S},
        w z.val.val (joinPartial S T hST a b z.val)) = partialProductWeight w S a := by
    unfold partialProductWeight
    apply Fintype.prod_equiv eS
    intro z
    simp [joinPartial, z.property, eS]
  have ht :
      (∏ z : {i : {i // i ∈ S ∪ T} // i.val ∉ S},
        w z.val.val (joinPartial S T hST a b z.val)) = partialProductWeight w T b := by
    unfold partialProductWeight
    apply Fintype.prod_equiv eT
    intro z
    simp [joinPartial, z.property, eT]
  unfold partialProductWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun i : {i // i ∈ S ∪ T} => i.val ∈ S)]
  rw [hs, ht]
  simp only [partialProductWeight]

end

end Erdos821.P4Indep

namespace Erdos821.P4Probe

open Erdos821.P4Indep

noncomputable section

theorem DisjointMarginalTask_proof : DisjointMarginalTask := by
  intro ι _ α _ w S T hsum hST H
  let U : Finset ι := S ∪ T
  let e : PartialSample U α ≃ PartialSample S α × PartialSample T α :=
    partialUnionEquiv S T hST
  let K : PartialSample U α → ℂ := fun c => H (e c).1 (e c).2
  have hnorm :
      (∑ y : ProductSample α, (productWeight w y : ℂ) *
        H (fun i => y i.val) (fun i => y i.val)) =
      ∑ c : PartialSample U α, (partialProductWeight w U c : ℂ) * K c := by
    simpa [K, e, U, partialUnionEquiv, splitPartial] using
      (partial_expectation_complex w hsum U K)
  calc
    (∑ y : ProductSample α, (productWeight w y : ℂ) *
        H (fun i => y i.val) (fun i => y i.val)) =
      ∑ c : PartialSample U α, (partialProductWeight w U c : ℂ) * K c := hnorm
    _ = ∑ a : PartialSample S α, ∑ b : PartialSample T α,
          ((partialProductWeight w S a * partialProductWeight w T b : ℝ) : ℂ) * H a b := by
      rw [← Fintype.sum_prod_type (fun z : PartialSample S α × PartialSample T α =>
        ((partialProductWeight w S z.1 * partialProductWeight w T z.2 : ℝ) : ℂ) *
          H z.1 z.2)]
      apply Fintype.sum_equiv e
      intro c
      dsimp [K]
      have hw := partialProductWeight_join w S T hST
        (e c).1 (e c).2
      have hc : joinPartial S T hST (e c).1 (e c).2 = c := by
        change (partialUnionEquiv S T hST).invFun
          ((partialUnionEquiv S T hST).toFun c) = c
        exact (partialUnionEquiv S T hST).left_inv c
      rw [hc] at hw
      rw [hw]

end

end Erdos821.P4Probe
