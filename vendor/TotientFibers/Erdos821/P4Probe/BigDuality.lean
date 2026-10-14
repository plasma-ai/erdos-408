import Erdos821.P4Probe.BigAveraging

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

local instance (P : PrimeGroups) (M : ℕ) : DecidableEq (BigSite P M) := Classical.decEq _

lemma bigCoordinateAverage_star (P : PrimeGroups) (M : ℕ)
    (S : P.BigGroup → Finset (Fin M)) (f : P.BigLabels M → ℂ) :
    bigCoordinateAverage P M S (fun x => star (f x)) =
      fun x => star (bigCoordinateAverage P M S f x) := by
  funext x
  simp only [bigCoordinateAverage, star_sum, star_mul, Complex.star_def,
    Complex.conj_ofReal, mul_comm]

lemma bigCoordinateAverage_duality (P : PrimeGroups) (M : ℕ)
    (S : P.BigGroup → Finset (Fin M)) (f g : P.BigLabels M → ℂ) :
    (∑ a, (P.idealMass a : ℂ) * star (f a) * bigCoordinateAverage P M S g a) =
      ∑ a, (P.idealMass a : ℂ) * star (bigCoordinateAverage P M S f a) * g a := by
  let ff : ProductSample (BigAlphabet P M) → ℂ := fun x => f ((flattenBig P M).symm x)
  let gg : ProductSample (BigAlphabet P M) → ℂ := fun x => g ((flattenBig P M).symm x)
  have hl : (∑ a, (P.idealMass a : ℂ) * star (f a) * bigCoordinateAverage P M S g a) =
      ∑ x : ProductSample (BigAlphabet P M), (productWeight (bigFlatWeight P M) x : ℂ) *
        star (ff x) * productAverage (bigFlatWeight P M) (bigFlatSet P M S) gg x := by
    apply Fintype.sum_equiv (flattenBig P M)
    intro a
    rw [bigFlatWeight_eq, bigFlat_average]
    simp [ff, gg]
  have hr : (∑ a, (P.idealMass a : ℂ) * star (bigCoordinateAverage P M S f a) * g a) =
      ∑ x : ProductSample (BigAlphabet P M), (productWeight (bigFlatWeight P M) x : ℂ) *
        star (productAverage (bigFlatWeight P M) (bigFlatSet P M S) ff x) * gg x := by
    apply Fintype.sum_equiv (flattenBig P M)
    intro a
    rw [bigFlatWeight_eq, bigFlat_average]
    simp [ff, gg]
  rw [hl, hr]
  exact productAverage_duality (bigFlatWeight P M) (bigFlatSet P M S) ff gg

lemma idealFullPair_source_average (P : PrimeGroups) (M : ℕ)
    (S : P.BigGroup → Finset (Fin M)) (K : P.BigLabels M → P.BigLabels M → ℂ)
    (hK : ∀ b, bigCoordinateAverage P M S (fun a => K a b) = fun a => K a b)
    (f g : P.BigLabels M → ℂ) :
    idealFullPair K (bigCoordinateAverage P M S f) g = idealFullPair K f g := by
  unfold idealFullPair
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have h := bigCoordinateAverage_duality P M S f (fun a => K a b)
  rw [hK b] at h
  exact congrArg (fun z => z * g b) h.symm

lemma idealFullPair_target_average (P : PrimeGroups) (M : ℕ)
    (S : P.BigGroup → Finset (Fin M)) (H : P.BigLabels M → P.BigLabels M → ℂ)
    (hH : ∀ a, bigCoordinateAverage P M S (H a) = H a)
    (f g : P.BigLabels M → ℂ) :
    idealFullPair (fun a b => (P.idealMass b : ℂ) * H a b) f
      (bigCoordinateAverage P M S g) =
        idealFullPair (fun a b => (P.idealMass b : ℂ) * H a b) f g := by
  unfold idealFullPair
  apply Finset.sum_congr rfl
  intro a _
  have h := bigCoordinateAverage_duality P M S (fun b => star (H a b)) g
  rw [bigCoordinateAverage_star, hH a] at h
  simp only [star_star] at h
  simpa only [Finset.mul_sum, mul_assoc] using
    congrArg (fun z => (P.idealMass a : ℂ) * star (f a) * z) h

end
end Erdos821.P4Probe
