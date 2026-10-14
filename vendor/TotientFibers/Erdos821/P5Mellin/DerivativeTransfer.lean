import Erdos821.Blueprint.Analytic

open MeasureTheory
open scoped BigOperators ContDiff

namespace Erdos821.P5Mellin

open Erdos821.Blueprint.Analytic

noncomputable section

def coordinateEval : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0

def expCompDerivativeConstant (hi : ℝ) (bounds : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition n, bounds c.length * (max 1 hi) ^ n

def piExpCompDerivativeConstant (hi : ℝ) (bounds : ℕ → ℝ) (n : ℕ) : ℝ :=
  expCompDerivativeConstant hi bounds n * ‖coordinateEval‖ ^ n

theorem expCompDerivativeConstant_nonneg (hi : ℝ) (bounds : ℕ → ℝ)
    (hbounds : ∀ j, 0 ≤ bounds j) (n : ℕ) :
    0 ≤ expCompDerivativeConstant hi bounds n := by
  apply Finset.sum_nonneg
  intro c hc
  exact mul_nonneg (hbounds c.length) (pow_nonneg (le_trans (by norm_num) (le_max_left 1 hi)) _)

theorem piExpCompDerivativeConstant_nonneg (hi : ℝ) (bounds : ℕ → ℝ)
    (hbounds : ∀ j, 0 ≤ bounds j) (n : ℕ) :
    0 ≤ piExpCompDerivativeConstant hi bounds n := by
  exact mul_nonneg (expCompDerivativeConstant_nonneg hi bounds hbounds n)
    (pow_nonneg (norm_nonneg coordinateEval) _)

theorem exp_comp_iteratedDeriv_bound (x C lo hi : ℝ) (bounds : ℕ → ℝ)
    (Ψ : ℝ → ℂ) (hC : 0 < C)
    (hbounds : ∀ j, 0 ≤ bounds j)
    (hcut : CutoffBound x C lo hi Ψ bounds) (hL : 1 ≤ L x) :
    ∀ n r, ‖iteratedDeriv n (fun u : ℝ => Ψ (Real.exp u)) r‖ ≤
      expCompDerivativeConstant hi bounds n * L x ^ (C * ((n : ℝ) + 1)) := by
  intro n r
  let H : ℝ := max 1 hi
  have hH1 : 1 ≤ H := le_max_left 1 hi
  have hHhi : hi ≤ H := le_max_right 1 hi
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  have hΨsmooth : ContDiff ℝ ∞ Ψ := hcut.1
  have hExpSmooth : ContDiff ℝ ∞ Real.exp := Real.contDiff_exp
  have hΨtsupport : tsupport Ψ ⊆ Set.Icc lo hi := by
    change closure (Function.support Ψ) ⊆ Set.Icc lo hi
    exact closure_minimal hcut.2.1 isClosed_Icc
  have hformula := iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (g := Ψ) (f := Real.exp) (x := r) (i := n)
    (hΨsmooth.contDiffAt) (hExpSmooth.contDiffAt) (by simp : (n : ℕ∞ω) ≤ ∞)
  change ‖iteratedDeriv n (Ψ ∘ Real.exp) r‖ ≤ _
  rw [hformula]
  calc
    _ ≤ ∑ c : OrderedFinpartition n,
        bounds c.length * H ^ n * L x ^ (C * ((n : ℝ) + 1)) := by
      calc
        _ ≤ ∑ c : OrderedFinpartition n,
            ‖(∏ j : Fin c.length, iteratedDeriv (c.partSize j) Real.exp r) •
                iteratedDeriv c.length Ψ (Real.exp r)‖ := norm_sum_le _ _
        _ ≤ ∑ c : OrderedFinpartition n,
            bounds c.length * H ^ n * L x ^ (C * ((n : ℝ) + 1)) := by
          apply Finset.sum_le_sum
          intro c hc
          have hExpDeriv (k : ℕ) : iteratedDeriv k Real.exp r = Real.exp r := by
            simpa using congrFun (iteratedDeriv_exp_const_mul k 1) r
          have hTermBound :
              ‖(∏ j : Fin c.length, iteratedDeriv (c.partSize j) Real.exp r) •
                  iteratedDeriv c.length Ψ (Real.exp r)‖ ≤
                bounds c.length * H ^ n * L x ^ (C * ((n : ℝ) + 1)) := by
            by_cases hzero : iteratedDeriv c.length Ψ (Real.exp r) = 0
            · have hnonneg :
                  0 ≤ bounds c.length * H ^ n * L x ^ (C * ((n : ℝ) + 1)) :=
                mul_nonneg (mul_nonneg (hbounds c.length)
                  (pow_nonneg (le_trans (by norm_num) hH1) _))
                  (Real.rpow_nonneg hLpos.le _)
              simpa [hzero] using hnonneg
            · have hExpLeH : Real.exp r ≤ H := by
                by_contra hnot
                have hgt : H < Real.exp r := lt_of_not_ge hnot
                have hgtHi : hi < Real.exp r := lt_of_le_of_lt hHhi hgt
                have hfd : iteratedFDeriv ℝ c.length Ψ (Real.exp r) ≠ 0 := by
                  intro hfd
                  apply hzero
                  apply norm_eq_zero.mp
                  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfd]
                  simp
                have hts : Real.exp r ∈ tsupport Ψ :=
                  (support_iteratedFDeriv_subset c.length) (Function.mem_support.mpr hfd)
                have hinterval := hΨtsupport hts
                exact (not_le_of_gt hgtHi) hinterval.2
              have hFactor :
                  ‖∏ j : Fin c.length, iteratedDeriv (c.partSize j) Real.exp r‖ ≤ H ^ n := by
                rw [show (∏ j : Fin c.length, iteratedDeriv (c.partSize j) Real.exp r) =
                  Real.exp r ^ c.length by simp [hExpDeriv]]
                rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.exp_pos r).le _)]
                calc
                  Real.exp r ^ c.length ≤ H ^ c.length :=
                    pow_le_pow_left₀ (Real.exp_pos r).le hExpLeH _
                  _ ≤ H ^ n := by
                    apply pow_le_pow_right₀ hH1
                    exact OrderedFinpartition.length_le c
              have hLogPow :
                  L x ^ (C * ((c.length : ℝ) + 1)) ≤ L x ^ (C * ((n : ℝ) + 1)) := by
                apply Real.rpow_le_rpow_of_exponent_le hL
                have hlen : (c.length : ℝ) ≤ (n : ℝ) := by
                  exact_mod_cast OrderedFinpartition.length_le c
                nlinarith
              have hDerivativeNorm :
                  ‖iteratedDeriv c.length Ψ (Real.exp r)‖ ≤
                    bounds c.length * L x ^ (C * ((c.length : ℝ) + 1)) :=
                hcut.2.2 c.length (Real.exp r)
              calc
                _ = ‖∏ j : Fin c.length, iteratedDeriv (c.partSize j) Real.exp r‖ *
                      ‖iteratedDeriv c.length Ψ (Real.exp r)‖ := norm_smul _ _
                _ ≤ H ^ n * (bounds c.length * L x ^ (C * ((c.length : ℝ) + 1))) :=
                  mul_le_mul hFactor hDerivativeNorm (norm_nonneg _)
                    (pow_nonneg (le_trans (by norm_num) hH1) _)
                _ ≤ H ^ n * (bounds c.length * L x ^ (C * ((n : ℝ) + 1))) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hLogPow (hbounds c.length))
                    (pow_nonneg (le_trans (by norm_num) hH1) _)
                _ = bounds c.length * H ^ n * L x ^ (C * ((n : ℝ) + 1)) := by ring
          exact hTermBound
    _ = expCompDerivativeConstant hi bounds n * L x ^ (C * ((n : ℝ) + 1)) := by
      simp only [expCompDerivativeConstant, H]
      rw [Finset.sum_mul]

theorem pi_exp_comp_iteratedFDeriv_bound (x C lo hi : ℝ) (bounds : ℕ → ℝ)
    (Ψ : ℝ → ℂ) (hC : 0 < C) (hbounds : ∀ j, 0 ≤ bounds j)
    (hcut : CutoffBound x C lo hi Ψ bounds) (hL : 1 ≤ L x) :
    ∀ j y, ‖iteratedFDeriv ℝ j
        ((Ψ ∘ Real.exp) ∘ coordinateEval) y‖ ≤
      piExpCompDerivativeConstant hi bounds j * L x ^ (C * ((j : ℝ) + 1)) := by
  intro j y
  have hscalar := exp_comp_iteratedDeriv_bound x C lo hi bounds Ψ hC hbounds hcut hL j
    (coordinateEval y)
  have hcomp := coordinateEval.iteratedFDeriv_comp_right
    (hcut.1.comp Real.contDiff_exp) y (i := j) (by simp)
  calc
    _ = ‖(iteratedFDeriv ℝ j (Ψ ∘ Real.exp) (coordinateEval y)).compContinuousLinearMap
          (fun _ : Fin j => coordinateEval)‖ := by rw [hcomp]
    _ ≤ ‖iteratedFDeriv ℝ j (Ψ ∘ Real.exp) (coordinateEval y)‖ *
          ∏ _ : Fin j, ‖coordinateEval‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedDeriv j (Ψ ∘ Real.exp) (coordinateEval y)‖ *
          ‖coordinateEval‖ ^ j := by simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ ≤ expCompDerivativeConstant hi bounds j * L x ^ (C * ((j : ℝ) + 1)) *
          ‖coordinateEval‖ ^ j :=
        mul_le_mul_of_nonneg_right hscalar (pow_nonneg (norm_nonneg _) _)
    _ = piExpCompDerivativeConstant hi bounds j * L x ^ (C * ((j : ℝ) + 1)) := by
        simp only [piExpCompDerivativeConstant]
        ring

end
end Erdos821.P5Mellin
