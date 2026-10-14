import Erdos821.P3Clean.Contractions

/-! Unitary square-root density identification in the finite-support norm. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

def densityNormalizedKernel {α : Type*} (density : α → ℝ) (K : α → α → ℂ) (a b : α) : ℂ :=
  (Real.sqrt (density a) : ℂ) / (Real.sqrt (density b) : ℂ) * K a b

theorem normBound_density_identification {α : Type*} (mass density : α → ℝ)
    (K : α → α → ℂ) (C : ℝ) (hd : ∀ a, 0 < density a)
    (hK : NormBound mass (densityNormalizedKernel density K) C) :
    NormBound (fun a => mass a * density a) K C := by
  intro s t f g
  have hs (a : α) : 0 ≤ density a := (hd a).le
  have hnorm (a : α) (z : ℂ) : ‖(Real.sqrt (density a) : ℂ) * z‖ ^ 2 = density a * ‖z‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hs a)]
  have h := hK s t (fun a => (Real.sqrt (density a) : ℂ) * f a)
    (fun b => (Real.sqrt (density b) : ℂ) * g b)
  have hentry (a b : α) :
      (mass a : ℂ) * star ((Real.sqrt (density a) : ℂ) * f a) *
        densityNormalizedKernel density K a b * ((Real.sqrt (density b) : ℂ) * g b) =
      (mass a * density a : ℝ) * star (f a) * K a b * g b := by
    have hb : (Real.sqrt (density b) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hd b)))
    have ha : (Real.sqrt (density a) : ℂ) ^ 2 = (density a : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hs a)
    simp only [densityNormalizedKernel, star_mul, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_mul]
    simp only [starRingEnd_apply]
    field_simp [hb]
    calc
      _ = (mass a : ℂ) * (Real.sqrt (density a) : ℂ) ^ 2 * star (f a) * K a b * g b := by ring
      _ = _ := by rw [ha]; ring
  simp only [hentry, hnorm] at h
  simpa only [mul_assoc] using h


end Erdos821.P3Clean
