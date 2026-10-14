import Erdos821.S2.ClosedPaths
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A unit-period Fourier integral enforces return of the physical position. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, phase (f i)) = phase (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, phase_add]

theorem continuous_phase_int (n : ℤ) : Continuous (fun theta : ℝ => phase (theta * (n : ℝ))) := by
  unfold phase
  fun_prop

theorem integral_phase_int (n : ℤ) :
    (∫ theta : ℝ in (0 : ℝ)..1, phase (theta * (n : ℝ))) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [phase]
  · rw [ite_eq_right hn]
    let c : ℂ := 2 * (Real.pi : ℂ) * (n : ℂ) * Complex.I
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) hnc) Complex.I_ne_zero
    have hf (theta : ℝ) : phase (theta * (n : ℝ)) = Complex.exp (c * theta) := by
      unfold phase
      congr 1
      dsimp only [c]
      push_cast
      ring
    have hexp : Complex.exp c = 1 := by
      have he : c = (n : ℂ) * (2 * Real.pi * Complex.I) := by dsimp only [c]; ring
      rw [he]
      exact Complex.exp_int_mul_two_pi_mul_I n
    simp_rw [hf]
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, hexp,
      Complex.exp_zero, sub_self, zero_div]

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

theorem offset_last : Q.offset (Fin.last n) = ∑ i : Fin n, Q.step i := by
  unfold offset
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_last, ite_eq_left i.isLt]

theorem edgeCoefficient_phase (theta : ℝ) (i : Fin n) :
    Q.edgeCoefficient theta i = Q.edgeCoefficient 0 i * phase (theta * (Q.step i : ℝ)) := by
  simp only [edgeCoefficient, zero_mul, phase, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one]

theorem weight_phase_factor (theta : ℝ) :
    Q.Weight theta = Q.Weight 0 * phase (theta * (Q.offset (Fin.last n) : ℝ)) := by
  unfold Weight
  simp_rw [Q.edgeCoefficient_phase theta]
  rw [Finset.prod_mul_distrib, phase_prod]
  have hs : (∑ i : Fin n, theta * (Q.step i : ℝ)) = theta * (Q.offset (Fin.last n) : ℝ) := by
    rw [← Finset.mul_sum, Q.offset_last, Int.cast_sum]
  rw [hs]
  ac_rfl

theorem weight_continuous : Continuous (fun theta : ℝ => Q.Weight theta) := by
  have he : (fun theta : ℝ => Q.Weight theta) =
      (fun theta : ℝ => Q.Weight 0 * phase (theta * (Q.offset (Fin.last n) : ℝ))) :=
    funext Q.weight_phase_factor
  rw [he]
  exact continuous_const.mul (continuous_phase_int _)

theorem integral_weight :
    (∫ theta : ℝ in (0 : ℝ)..1, Q.Weight theta) =
      if Q.offset (Fin.last n) = 0 then Q.Weight 0 else 0 := by
  have he : (fun theta : ℝ => Q.Weight theta) =
      (fun theta : ℝ => Q.Weight 0 * phase (theta * (Q.offset (Fin.last n) : ℝ))) :=
    funext Q.weight_phase_factor
  rw [he]
  rw [intervalIntegral.integral_const_mul, integral_phase_int]
  by_cases h : Q.offset (Fin.last n) = 0 <;> simp [h]

end ResiduePath

theorem residueExpression_continuous {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℕ) : Continuous (fun theta : ℝ => residueExpression A n theta) := by
  unfold residueExpression
  apply continuous_finset_sum
  intro Q _
  by_cases h : Q.Valid
  · simp only [h, ite_true]
    exact Q.weight_continuous
  · simp only [h, ite_false]
    exact continuous_const

theorem integral_residueExpression {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℕ) :
    (∫ theta : ℝ in (0 : ℝ)..1, residueExpression A n theta) = closedResidueExpression A n := by
  unfold residueExpression
  rw [intervalIntegral.integral_finsetSum]
  · unfold closedResidueExpression
    apply Finset.sum_congr rfl
    intro Q _
    by_cases hq : Q.Valid
    · simp only [hq, ite_true, Q.integral_weight]
      by_cases hc : Q.offset (Fin.last n) = 0 <;>
        simp [closedPathCoefficient, hq, hc, ResiduePath.Weight]
    · simp [hq, closedPathCoefficient]
  · intro Q _
    by_cases hq : Q.Valid
    · simp only [hq, ite_true]
      exact Q.weight_continuous.intervalIntegrable 0 1
    · simp only [hq, ite_false]
      exact intervalIntegrable_const


end Erdos821.S2Core
