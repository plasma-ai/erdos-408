import Erdos821.P4Probe.PatternBridgeTasks
import Erdos821.P4Probe.AverageOrthogonality

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

abbrev BigSite (P : PrimeGroups) (M : ℕ) := P.BigGroup × Fin M
abbrev BigAlphabet (P : PrimeGroups) (M : ℕ) : BigSite P M → Type := fun z => P.Prime z.1.val

local instance bigSiteDecidableEq (P : PrimeGroups) (M : ℕ) : DecidableEq (BigSite P M) := Classical.decEq _

def flattenBig (P : PrimeGroups) (M : ℕ) : P.BigLabels M ≃ ProductSample (BigAlphabet P M) where
  toFun a := fun z => a z.1 z.2
  invFun a := fun g i => a (g, i)
  left_inv _ := rfl
  right_inv _ := rfl

def bigFlatWeight (P : PrimeGroups) (M : ℕ) : ∀ z : BigSite P M, BigAlphabet P M z → ℝ :=
  fun z p => P.mu z.1.val p

def bigFlatSet (P : PrimeGroups) (M : ℕ) (S : P.BigGroup → Finset (Fin M)) : Finset (BigSite P M) :=
  Finset.univ.filter (fun z => z.2 ∈ S z.1)

lemma bigFlatWeight_eq (P : PrimeGroups) (M : ℕ) (a : P.BigLabels M) :
    productWeight (bigFlatWeight P M) (flattenBig P M a) = P.idealMass a := by
  exact Fintype.prod_prod_type (fun z : BigSite P M => P.mu z.1.val (a z.1 z.2))

lemma bigFlat_sqNorm (P : PrimeGroups) (M : ℕ) (f : P.BigLabels M → ℂ) :
    productSqNorm (bigFlatWeight P M) (fun a => f ((flattenBig P M).symm a)) =
      ∑ a, P.idealMass a * ‖f a‖ ^ 2 := by
  unfold productSqNorm
  symm
  apply Fintype.sum_equiv (flattenBig P M)
  intro a
  rw [bigFlatWeight_eq]
  simp [flattenBig]

lemma bigFlat_average (P : PrimeGroups) (M : ℕ) (S : P.BigGroup → Finset (Fin M))
    (f : P.BigLabels M → ℂ) (a : P.BigLabels M) :
    productAverage (bigFlatWeight P M) (bigFlatSet P M S)
      (fun y => f ((flattenBig P M).symm y)) (flattenBig P M a) =
      bigCoordinateAverage P M S f a := by
  unfold productAverage bigCoordinateAverage
  symm
  apply Fintype.sum_equiv (flattenBig P M)
  intro y
  rw [bigFlatWeight_eq]
  have he : (fun g i => if i ∈ S g then y g i else a g i) =
      (flattenBig P M).symm (mixCoords (bigFlatSet P M S) (flattenBig P M a) (flattenBig P M y)) := by
    funext g i
    by_cases hi : i ∈ S g <;> simp [flattenBig, mixCoords, bigFlatSet, hi]
  exact congrArg (fun z => (P.idealMass y : ℂ) * f z) he

lemma bigCoordinateAverage_sqNorm_le (P : PrimeGroups) (M : ℕ) (hV : ∀ g, 0 < P.V g)
    (S : P.BigGroup → Finset (Fin M)) (f : P.BigLabels M → ℂ) :
    (∑ a, P.idealMass a * ‖bigCoordinateAverage P M S f a‖ ^ 2) ≤
      ∑ a, P.idealMass a * ‖f a‖ ^ 2 := by
  have h := productAverage_sqNorm_le (bigFlatWeight P M)
    (fun z p => (graph_mu_pos P z.1.val (hV z.1.val) p).le)
    (fun z => graph_mu_sum P z.1.val (hV z.1.val)) (bigFlatSet P M S)
    (fun a => f ((flattenBig P M).symm a))
  rw [bigFlat_sqNorm] at h
  have hf : productAverage (bigFlatWeight P M) (bigFlatSet P M S)
      (fun y => f ((flattenBig P M).symm y)) =
      (fun y => bigCoordinateAverage P M S f ((flattenBig P M).symm y)) := by
    funext y
    have h' := bigFlat_average P M S f ((flattenBig P M).symm y)
    simpa only [Equiv.apply_symm_apply] using h'
  rw [hf, bigFlat_sqNorm] at h
  exact h

lemma bigCoordinateAverage_norm_le (P : PrimeGroups) (M : ℕ) (hV : ∀ g, 0 < P.V g)
    (S : P.BigGroup → Finset (Fin M)) (f : P.BigLabels M → ℂ) :
    idealVectorNorm P M (bigCoordinateAverage P M S f) ≤ idealVectorNorm P M f :=
  Real.sqrt_le_sqrt (bigCoordinateAverage_sqNorm_le P M hV S f)

end
end Erdos821.P4Probe
