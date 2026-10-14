import Erdos821.P3Clean.IdealMultiplier

/-! Averages of local multiplier magnitudes suffice for the ideal Schur estimate. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem idealMultiplierRaw_norm_le_average (A : Model F P J m) (theta delta : ℝ)
    (w : Fin A.patternCount → P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → P.BigAux J → ℂ)
    (hw : ∀ v a b, (∑ u : P.BigAux J, (A.pattern v).bigAuxMass u * ‖w v a b u‖) ≤ delta)
    (a b : P.BigLabels (J + F.ell)) :
    ‖idealMultiplierRaw A theta w a b‖ ≤
      ∑ v : Fin A.patternCount, (delta * patternAmplitude A v) *
        (if (A.pattern v).matchesBig a b then (A.pattern v).freshMass b else 0) := by
  unfold idealMultiplierRaw
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro v _
  by_cases h : (A.pattern v).matchesBig a b
  · simp only [if_pos h]
    calc
      _ ≤ ∑ u : P.BigAux J, ‖((A.pattern v).bigAuxMass u * (A.pattern v).freshMass b : ℝ) *
          (A.pattern v).coefficient a b u * imaginaryPower ((A.pattern v).DBig a u) A.zeta *
          phase (theta * ((A.pattern v).DBig a u : ℝ)) * w v a b u‖ := norm_sum_le _ _
      _ ≤ ∑ u : P.BigAux J, ((A.pattern v).bigAuxMass u * ‖w v a b u‖) *
          (patternAmplitude A v * (A.pattern v).freshMass b) := by
        apply Finset.sum_le_sum
        intro u _
        have hu := bigAuxMass_nonneg (A.pattern v) u
        have hf := freshMass_nonneg (A.pattern v) b
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hu, abs_of_nonneg hf, imaginaryPower_norm, phase_norm, mul_one]
        have hh := mul_le_mul_of_nonneg_left (coefficient_norm_le_amplitude A v a b u)
          (mul_nonneg (mul_nonneg hu hf) (norm_nonneg (w v a b u)))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
      _ = (∑ u : P.BigAux J, (A.pattern v).bigAuxMass u * ‖w v a b u‖) *
          (patternAmplitude A v * (A.pattern v).freshMass b) := by rw [Finset.sum_mul]
      _ ≤ delta * (patternAmplitude A v * (A.pattern v).freshMass b) :=
        mul_le_mul_of_nonneg_right (hw v a b)
          (mul_nonneg (patternAmplitude_nonneg A v) (freshMass_nonneg (A.pattern v) b))
      _ = _ := by ring
  · simp only [if_neg h, Finset.sum_const_zero, norm_zero, mul_zero, le_refl]

theorem normBound_idealMultiplierRaw_average (A : Model F P J m) (theta delta : ℝ) (hd : 0 ≤ delta)
    (w : Fin A.patternCount → P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → P.BigAux J → ℂ)
    (hw : ∀ v a b, (∑ u : P.BigAux J, (A.pattern v).bigAuxMass u * ‖w v a b u‖) ≤ delta)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0) :
    NormBound P.idealMass (idealMultiplierRaw A theta w) (delta * A.patternMass) := by
  let R (v : Fin A.patternCount) (a b : P.BigLabels (J + F.ell)) : ℝ :=
    if (A.pattern v).matchesBig a b then (A.pattern v).freshMass b else 0
  have hm (a : P.BigLabels (J + F.ell)) : 0 ≤ P.idealMass a := by
    apply Finset.prod_nonneg
    intro g _
    exact Finset.prod_nonneg (fun i _ => (mu_pos g.val _).le)
  have hR (v : Fin A.patternCount) (a b : P.BigLabels (J + F.ell)) : 0 ≤ R v a b := by
    unfold R
    split_ifs
    · exact freshMass_nonneg (A.pattern v) b
    · exact le_refl 0
  have hrow (v : Fin A.patternCount) (a : P.BigLabels (J + F.ell)) : (∑ b, R v a b) = 1 := by
    exact bigFreshMass_row_sum (A.pattern v) (fun g p => P.mu g.val p)
      (fun g => mu_sum g.val (hV g)) a
  have hrev (v : Fin A.patternCount) (a b : P.BigLabels (J + F.ell)) :
      P.idealMass a * R v a b = P.idealMass b * R v b a := by
    have hs : (A.pattern v).matchesBig a b ↔ (A.pattern v).matchesBig b a := by
      unfold Pattern.matchesBig
      exact forall_congr' (fun g => forall_congr' (fun i => imp_congr_right (fun _ => eq_comm)))
    by_cases h : (A.pattern v).matchesBig a b
    · simp only [R, if_pos h, if_pos (hs.mp h)]
      exact bigFreshMass_reversal (A.pattern v) (fun g p => P.mu g.val p) a b h
    · simp only [R, if_neg h, if_neg (fun hh => h (hs.mpr hh)), mul_zero]
  have h := normBound_probability_mixture P.idealMass R (fun v => delta * patternAmplitude A v)
    (idealMultiplierRaw A theta w) hm hR
    (fun v => mul_nonneg hd (patternAmplitude_nonneg A v)) hrow hrev
    (idealMultiplierRaw_norm_le_average A theta delta w hw)
  simpa only [← Finset.mul_sum, sum_patternAmplitude] using h


end Erdos821.P3Clean
