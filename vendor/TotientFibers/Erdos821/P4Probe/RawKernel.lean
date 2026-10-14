import Erdos821.P4Probe.RawLabels
import Erdos821.P4Probe.FiniteSchur

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

def rawTransition (P : PrimeGroups) (J ell : ℕ)
    (a b : P.BigLabels (J + ell)) : ℝ :=
  if (splitBigLabels P J ell a).1 = (splitBigLabels P J ell b).1
    then P.idealMass ((splitBigLabels P J ell b).2) else 0

lemma rawTransition_nonneg (P : PrimeGroups) (J ell : ℕ) (hV : ∀ g, 0 < P.V g)
    (a b : P.BigLabels (J + ell)) : 0 ≤ rawTransition P J ell a b := by
  unfold rawTransition
  split_ifs
  · exact (idealMass_pos P ell hV _).le
  · exact le_rfl

lemma rawTransition_row (P : PrimeGroups) (J ell : ℕ) (hV : ∀ g, 0 < P.V g)
    (a : P.BigLabels (J + ell)) : ∑ b, rawTransition P J ell a b = 1 := by
  trans ∑ z : P.BigLabels J × P.BigLabels ell,
    if (splitBigLabels P J ell a).1 = z.1 then P.idealMass z.2 else 0
  · apply Fintype.sum_equiv (splitBigLabels P J ell)
    intro b
    rfl
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp
    exact idealMass_sum P ell hV

lemma rawTransition_column (P : PrimeGroups) (J ell : ℕ) (hV : ∀ g, 0 < P.V g)
    (b : P.BigLabels (J + ell)) :
    (∑ a, P.idealMass a * rawTransition P J ell a b) = P.idealMass b := by
  trans ∑ z : P.BigLabels J × P.BigLabels ell,
    P.idealMass z.1 * P.idealMass z.2 *
      (if z.1 = (splitBigLabels P J ell b).1 then P.idealMass ((splitBigLabels P J ell b).2) else 0)
  · apply Fintype.sum_equiv (splitBigLabels P J ell)
    intro a
    rw [idealMass_split P J ell a]
    rfl
  · rw [Fintype.sum_prod_type]
    simp_rw [mul_ite, mul_zero]
    simp
    rw [← Finset.sum_mul, ← Finset.mul_sum, idealMass_sum P ell hV, mul_one]
    exact (idealMass_split P J ell b).symm

lemma imaginaryPower_norm (n : ℕ) (ζ : ℝ) : ‖imaginaryPower n ζ‖ = 1 := by
  unfold imaginaryPower
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, mul_one, Real.exp_zero]

lemma phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

def rawPrefixKernel (P : PrimeGroups) (J ell : ℕ) (θ ζ : ℝ)
    (a b : P.BigLabels (J + ell)) : ℂ :=
  (rawTransition P J ell a b : ℂ) *
    imaginaryPower (prefixProduct ((splitBigLabels P J ell a).1)) ζ *
    phase (θ * prefixProduct ((splitBigLabels P J ell a).1))

lemma rawPrefixKernel_norm (P : PrimeGroups) (J ell : ℕ) (hV : ∀ g, 0 < P.V g)
    (θ ζ : ℝ) (a b : P.BigLabels (J + ell)) :
    ‖rawPrefixKernel P J ell θ ζ a b‖ = rawTransition P J ell a b := by
  simp only [rawPrefixKernel, norm_mul, imaginaryPower_norm, phase_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rawTransition_nonneg P J ell hV a b)]

lemma rawPrefixKernel_normBound (P : PrimeGroups) (J ell : ℕ) (hV : ∀ g, 0 < P.V g)
    (θ ζ : ℝ) :
    NormBound (P.idealMass (M := J + ell)) (rawPrefixKernel P J ell θ ζ) 1 := by
  apply finite_schur _ _ 1 (fun a => (idealMass_pos P (J + ell) hV a).le) (by norm_num)
  · intro a
    simp only [rawPrefixKernel_norm P J ell hV θ ζ]
    exact (rawTransition_row P J ell hV a).le
  · intro b
    simp only [rawPrefixKernel_norm P J ell hV θ ζ, one_mul]
    exact (rawTransition_column P J ell hV b).le

end
end Erdos821.P4Probe
