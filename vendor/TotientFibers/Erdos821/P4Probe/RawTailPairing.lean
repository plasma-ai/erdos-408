import Erdos821.P4Probe.RawAssembly
import Erdos821.P4Probe.BigDuality

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def tailCoordinates (P : PrimeGroups) (J ell : ℕ) : P.BigGroup → Finset (Fin (J + ell)) :=
  fun _ => Finset.univ.filter (fun i => J ≤ i.val)

lemma tailMix_prefix (P : PrimeGroups) (J ell : ℕ) (a y : P.BigLabels (J + ell)) :
    (splitBigLabels P J ell (fun g i =>
      if i ∈ tailCoordinates P J ell g then y g i else a g i)).1 =
        (splitBigLabels P J ell a).1 := by
  funext g i
  simp [splitBigLabels, tailCoordinates, not_le_of_gt i.isLt]

lemma tailAverage_prefix_function (P : PrimeGroups) (J ell : ℕ)
    (hV : ∀ g, 0 < P.V g) (F : P.BigLabels J → ℂ) :
    bigCoordinateAverage P (J + ell) (tailCoordinates P J ell)
      (fun a => F ((splitBigLabels P J ell a).1)) =
        fun a => F ((splitBigLabels P J ell a).1) := by
  funext a
  unfold bigCoordinateAverage
  simp_rw [tailMix_prefix]
  have ht : (∑ y : P.BigLabels (J + ell), (P.idealMass y : ℂ)) = 1 := by
    exact_mod_cast idealMass_sum P (J + ell) hV
  rw [← Finset.sum_mul, ht, one_mul]

def rawPrefixDensity (P : PrimeGroups) (J ell : ℕ) (θ ζ : ℝ)
    (a b : P.BigLabels (J + ell)) : ℂ :=
  if (splitBigLabels P J ell a).1 = (splitBigLabels P J ell b).1 then
    (P.idealMass ((splitBigLabels P J ell a).1) : ℂ)⁻¹ *
      imaginaryPower (prefixProduct ((splitBigLabels P J ell a).1)) ζ *
      phase (θ * prefixProduct ((splitBigLabels P J ell a).1))
  else 0

lemma rawPrefixKernel_eq_targetMass (P : PrimeGroups) (J ell : ℕ)
    (hV : ∀ g, 0 < P.V g) (θ ζ : ℝ) (a b : P.BigLabels (J + ell)) :
    rawPrefixKernel P J ell θ ζ a b = (P.idealMass b : ℂ) * rawPrefixDensity P J ell θ ζ a b := by
  by_cases hp : (splitBigLabels P J ell a).1 = (splitBigLabels P J ell b).1
  · have hμ : (P.idealMass ((splitBigLabels P J ell a).1) : ℂ) ≠ 0 := by
      exact_mod_cast (idealMass_pos P J hV ((splitBigLabels P J ell a).1)).ne'
    simp only [rawPrefixKernel, rawTransition, rawPrefixDensity, hp, ite_true]
    rw [idealMass_split P J ell b, ← hp]
    simp only [Complex.ofReal_mul]
    field_simp
  · simp [rawPrefixKernel, rawTransition, rawPrefixDensity, hp]

lemma rawFullPair_tail_average (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hV : ∀ g, 0 < P.V g) (θ ζ : ℝ) (f g : P.BigLabels (J + F.ell) → ℂ) :
    idealFullPair (((rawFamily F P J m).model 1 ζ).idealRaw θ) f g =
      idealFullPair (((rawFamily F P J m).model 1 ζ).idealRaw θ)
        (bigCoordinateAverage P (J + F.ell) (tailCoordinates P J F.ell) f)
        (bigCoordinateAverage P (J + F.ell) (tailCoordinates P J F.ell) g) := by
  have hk : ((rawFamily F P J m).model 1 ζ).idealRaw θ = rawPrefixKernel P J F.ell θ ζ := by
    funext a b
    exact rawModel_idealRaw_eq F P J m hV θ ζ a b
  rw [hk]
  have hs : ∀ b, bigCoordinateAverage P (J + F.ell) (tailCoordinates P J F.ell)
      (fun a => rawPrefixKernel P J F.ell θ ζ a b) = fun a => rawPrefixKernel P J F.ell θ ζ a b := by
    intro b
    simpa [rawPrefixKernel, rawTransition, mul_ite, ite_mul] using
      tailAverage_prefix_function P J F.ell hV (fun p =>
        ((if p = (splitBigLabels P J F.ell b).1 then
          P.idealMass ((splitBigLabels P J F.ell b).2) else 0 : ℝ) : ℂ) *
          imaginaryPower (prefixProduct p) ζ * phase (θ * prefixProduct p))
  have ht : ∀ a, bigCoordinateAverage P (J + F.ell) (tailCoordinates P J F.ell)
      (rawPrefixDensity P J F.ell θ ζ a) = rawPrefixDensity P J F.ell θ ζ a := by
    intro a
    exact tailAverage_prefix_function P J F.ell hV (fun p =>
      if (splitBigLabels P J F.ell a).1 = p then
        (P.idealMass ((splitBigLabels P J F.ell a).1) : ℂ)⁻¹ *
          imaginaryPower (prefixProduct ((splitBigLabels P J F.ell a).1)) ζ *
          phase (θ * prefixProduct ((splitBigLabels P J F.ell a).1)) else 0)
  calc
    _ = idealFullPair (rawPrefixKernel P J F.ell θ ζ)
        (bigCoordinateAverage P (J + F.ell) (tailCoordinates P J F.ell) f) g :=
      (idealFullPair_source_average P (J + F.ell) (tailCoordinates P J F.ell) _ hs f g).symm
    _ = _ := by
      have hd : rawPrefixKernel P J F.ell θ ζ =
          fun a b => (P.idealMass b : ℂ) * rawPrefixDensity P J F.ell θ ζ a b := by
        funext a b
        exact rawPrefixKernel_eq_targetMass P J F.ell hV θ ζ a b
      rw [hd]
      exact (idealFullPair_target_average P (J + F.ell) (tailCoordinates P J F.ell)
        _ ht _ g).symm

end
end Erdos821.P4Probe
