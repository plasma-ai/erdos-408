import Erdos821.P4Probe.ProjectionSelector
import Erdos821.P4Probe.ProjectionTasks

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {s M : ℕ} {α : Fin s → Type} [∀ g, Fintype (α g)]

abbrev RowSite (s M : ℕ) := Fin s × Fin M
abbrev FlatAlphabet (α : Fin s → Type) (M : ℕ) : RowSite s M → Type := fun z => α z.1

local instance rowSiteDecidableEq (s M : ℕ) : DecidableEq (RowSite s M) := Classical.decEq _

def flattenRows : ProbeSample α M ≃ ProductSample (FlatAlphabet α M) where
  toFun x := fun z => x z.1 z.2
  invFun x := fun g i => x (g, i)
  left_inv _ := rfl
  right_inv _ := rfl

def flatWeight (w : ∀ g, α g → ℝ) : ∀ z : RowSite s M, FlatAlphabet α M z → ℝ :=
  fun z => w z.1

lemma flatWeight_eq (w : ∀ g, α g → ℝ) (x : ProbeSample α M) :
    productWeight (flatWeight w) (flattenRows x) = sampleWeight w x := by
  exact Fintype.prod_prod_type (fun z : RowSite s M => w z.1 (x z.1 z.2))

lemma flatSqNorm_eq (w : ∀ g, α g → ℝ) (f : ProbeSample α M → ℂ) :
    productSqNorm (flatWeight w) (fun x => f (flattenRows.symm x)) = sampleSqNorm w f := by
  unfold productSqNorm sampleSqNorm
  symm
  apply Fintype.sum_equiv flattenRows
  intro x
  rw [flatWeight_eq]
  simp [flattenRows]

lemma flat_replace (I : Finset (RowSite s M)) (x y : ProbeSample α M) :
    flattenRows.symm (mixCoords I (flattenRows x) (flattenRows y)) = replaceCoords I x y := by
  funext g i
  by_cases hi : (g, i) ∈ I <;> simp [flattenRows, mixCoords, replaceCoords, hi]

lemma flat_average (w : ∀ g, α g → ℝ) (I : Finset (RowSite s M))
    (f : ProbeSample α M → ℂ) (x : ProbeSample α M) :
    productAverage (flatWeight w) I (fun y => f (flattenRows.symm y)) (flattenRows x) =
      averageCoords w I f x := by
  unfold productAverage averageCoords
  symm
  apply Fintype.sum_equiv flattenRows
  intro y
  simp only [flatWeight_eq, flat_replace]

lemma flat_fullProbe (w : ∀ g, α g → ℝ) (hsum : ∀ g, ∑ a, w g a = 1)
    (tail I : Finset (RowSite s M)) (f : ProbeSample α M → ℂ) (x : ProbeSample α M) :
    productProbeProjection (flatWeight w) tail I (fun y => f (flattenRows.symm y)) (flattenRows x) =
      fullProbeComponent w tail I f x := by
  unfold productProbeProjection productFull fullProbeComponent
  apply Finset.sum_congr rfl
  intro U _
  rw [productAverage_union (flatWeight w) (fun z => hsum z.1) U tail]
  rw [Finset.union_comm U tail, flat_average]
  congr!

lemma flat_fullProbe_energy (w : ∀ g, α g → ℝ) (hsum : ∀ g, ∑ a, w g a = 1)
    (tail I : Finset (RowSite s M)) (f : ProbeSample α M → ℂ) :
    sampleSqNorm w (fullProbeComponent w tail I f) =
      ∑ S ∈ (Finset.univ : Finset (RowSite s M)).powerset,
        if I ⊆ S ∧ Disjoint tail S then
          productSqNorm (flatWeight w)
            (productAnova (flatWeight w) Finset.univ S (fun y => f (flattenRows.symm y))) else 0 := by
  have hfun : (fun y => fullProbeComponent w tail I f (flattenRows.symm y)) =
      productProbeProjection (flatWeight w) tail I (fun y => f (flattenRows.symm y)) := by
    funext y
    have h := flat_fullProbe w hsum tail I f (flattenRows.symm y)
    simpa only [Equiv.apply_symm_apply] using h.symm
  rw [← flatSqNorm_eq, hfun]
  convert productProbeProjection_energy (flatWeight w) (fun z => hsum z.1) tail I
    (fun y => f (flattenRows.symm y)) using 1 <;> congr! 2

end
end Erdos821.P4Probe
