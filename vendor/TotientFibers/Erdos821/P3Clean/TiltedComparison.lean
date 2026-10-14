import Erdos821.P3Clean.DensityBounds
import Erdos821.P3Clean.AuxiliaryBan
import Erdos821.P3Clean.AveragedMultiplier
import Erdos821.P3Clean.BigNormAverage
import Erdos821.P3Clean.TiltedIdealKernel

/-! Density normalization and the quantitative signed ideal comparison. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def cleanBigMultiplier (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J) : ℂ :=
  (Real.sqrt (freshDensity F n ν a) * Real.sqrt (freshDensity F n ν b) : ℝ) *
    (if bigBan ν a b u then 1 else 0)

theorem cleanBigMultiplier_average_error (F : FixedData) (n : ℕ)
    (ν : Pattern P J F.ell m) (D atom : ℝ) (hD : 1 ≤ D) (hat : 0 ≤ atom)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0)
    (hatom : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, P.mu g.val p ≤ atom)
    (hsqrt : ∀ a b, 1 ≤ Real.sqrt (freshDensity F n ν a) * Real.sqrt (freshDensity F n ν b) ∧
      Real.sqrt (freshDensity F n ν a) * Real.sqrt (freshDensity F n ν b) ≤ D)
    (a b : P.BigLabels (J + F.ell)) :
    (∑ u : P.BigAux J, ν.bigAuxMass u * ‖cleanBigMultiplier F n ν a b u - 1‖) ≤
      (D - 1) + D * ((Fintype.card P.BigGroup : ℝ) * J * (J + F.ell) * (2 * atom)) := by
  have hs := hsqrt a b
  have hp (u : P.BigAux J) : ‖cleanBigMultiplier F n ν a b u - 1‖ ≤
      (D - 1) + D * (if bigBan ν a b u then (0 : ℝ) else 1) := by
    by_cases h : bigBan ν a b u
    · simp only [cleanBigMultiplier, if_pos h, mul_one, mul_zero, add_zero]
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith : 0 ≤
        Real.sqrt (freshDensity F n ν a) * Real.sqrt (freshDensity F n ν b) - 1)]
      linarith
    · simp only [cleanBigMultiplier, if_neg h, mul_zero, zero_sub, norm_neg, norm_one, mul_one]
      linarith
  calc
    _ ≤ ∑ u : P.BigAux J, ν.bigAuxMass u *
        ((D - 1) + D * (if bigBan ν a b u then (0 : ℝ) else 1)) :=
      Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hp u) (bigAuxMass_nonneg ν u))
    _ = (D - 1) + D * ∑ u : P.BigAux J, ν.bigAuxMass u *
        (if bigBan ν a b u then (0 : ℝ) else 1) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, bigAuxMass_sum ν hV,
        one_mul, mul_left_comm, ← Finset.mul_sum]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_left
      (bigAuxMass_ban_probability ν hV atom hatom a b) (zero_le_one.trans hD)) _

theorem normalizedTiltedBannedRaw_forward (A : Model F P J m) (n : ℕ) (theta : ℝ)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    densityNormalizedKernel (activeDensity F n) (tiltedBannedRaw A n theta true) =
      idealMultiplierRaw A theta (fun v => cleanBigMultiplier F n (A.pattern v)) := by
  funext a b
  simp only [densityNormalizedKernel, tiltedBannedRaw, idealMultiplierRaw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  by_cases hm : (A.pattern v).matchesBig a b
  · by_cases hban : bigBan (A.pattern v) a b u
    · have hg : (A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u := ⟨hm, hban⟩
      simp only [if_pos hm, if_pos hg, cleanBigMultiplier, if_pos hban,
        mul_one, bigSignedCoefficient, Bool.true_eq, if_true]
      have h := normalizedFreshDensityFactor F P n (A.pattern v) a b hb hm
      have hc : ((Real.sqrt (activeDensity F n a) / Real.sqrt (activeDensity F n b) *
          tiltedFreshMass F n (A.pattern v) b : ℝ) : ℂ) =
          ((A.pattern v).freshMass b : ℂ) *
            (Real.sqrt (freshDensity F n (A.pattern v) a) *
              Real.sqrt (freshDensity F n (A.pattern v) b) : ℝ) := by
        exact_mod_cast h
      simp only [Complex.ofReal_mul, Complex.ofReal_div] at hc ⊢
      calc
        _ = (((A.pattern v).bigAuxMass u : ℂ) *
            ((Real.sqrt (activeDensity F n a) : ℂ) / (Real.sqrt (activeDensity F n b) : ℂ) *
              (tiltedFreshMass F n (A.pattern v) b : ℂ))) *
            ((A.pattern v).coefficient a b u * imaginaryPower ((A.pattern v).DBig a u) A.zeta) *
            phase (theta * ((A.pattern v).DBig a u : ℝ)) := by ring
        _ = _ := by rw [hc]; ring
    · have hg : ¬ ((A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u) := fun h => hban h.2
      simp only [if_pos hm, if_neg hg, cleanBigMultiplier, if_neg hban, mul_zero]
  · have hg : ¬ ((A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u) := fun h => hm h.1
    simp only [if_neg hm, if_neg hg, mul_zero]

theorem densityNormalizedKernel_averageBig (n : ℕ)
    (K : P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → ℂ) :
    densityNormalizedKernel (activeDensity F n) (averageBigKernel K) =
      averageBigKernel (densityNormalizedKernel (activeDensity F n) K) := by
  funext a b
  simp only [densityNormalizedKernel, averageBigKernel, activeDensity_actBig,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem averageBigKernel_sub (K H : P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → ℂ) :
    averageBigKernel (fun a b => K a b - H a b) =
      fun a b => averageBigKernel K a b - averageBigKernel H a b := by
  funext a b
  simp only [averageBigKernel, Finset.sum_sub_distrib, mul_sub]

theorem normBound_tiltedBannedKernel_forward (A : Model F P J m) (n : ℕ) (theta C D atom : ℝ)
    (hD : 1 ≤ D) (hat : 0 ≤ atom)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hatom : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, P.mu g.val p ≤ atom)
    (hsqrt : ∀ v : Fin A.patternCount, ∀ a b,
      1 ≤ Real.sqrt (freshDensity F n (A.pattern v) a) * Real.sqrt (freshDensity F n (A.pattern v) b) ∧
        Real.sqrt (freshDensity F n (A.pattern v) a) * Real.sqrt (freshDensity F n (A.pattern v) b) ≤ D)
    (hideal : NormBound P.idealMass (A.idealKernel theta) C) :
    NormBound (tiltedIdealMass F n) (tiltedBannedKernel A n theta true)
      (C + ((D - 1) + D * ((Fintype.card P.BigGroup : ℝ) * J * (J + F.ell) * (2 * atom))) *
        A.patternMass) := by
  let delta := (D - 1) + D * ((Fintype.card P.BigGroup : ℝ) * J * (J + F.ell) * (2 * atom))
  have hd : 0 ≤ delta := by unfold delta; positivity
  have herr := normBound_idealMultiplierRaw_average A theta delta hd
    (fun v a b u => cleanBigMultiplier F n (A.pattern v) a b u - 1)
    (fun v a b => cleanBigMultiplier_average_error F n (A.pattern v) D atom hD hat hV hatom
      (hsqrt v) a b) hV
  have havg := normBound_averageBigKernel P.idealMass _ _
    (fun p a => bigProductMass_actBig (fun g q => P.mu g.val q) p a) herr
  have he : averageBigKernel
      (idealMultiplierRaw A theta (fun v a b u => cleanBigMultiplier F n (A.pattern v) a b u - 1)) =
      fun a b => densityNormalizedKernel (activeDensity F n) (tiltedBannedKernel A n theta true) a b -
        A.idealKernel theta a b := by
    have hraw : idealMultiplierRaw A theta
        (fun v a b u => cleanBigMultiplier F n (A.pattern v) a b u - 1) =
        fun a b => idealMultiplierRaw A theta (fun v => cleanBigMultiplier F n (A.pattern v)) a b -
          A.idealRaw theta a b := by
      funext a b
      exact (idealMultiplierRaw_sub_one A theta (fun v => cleanBigMultiplier F n (A.pattern v)) a b).symm
    rw [hraw, averageBigKernel_sub]
    rw [← normalizedTiltedBannedRaw_forward A n theta hb, ← densityNormalizedKernel_averageBig]
    rfl
  rw [he] at havg
  have hadd := Erdos821.S2Core.normBound_add P.idealMass (A.idealKernel theta) _ C
    (delta * A.patternMass) hideal havg
  have hn : NormBound P.idealMass
      (densityNormalizedKernel (activeDensity F n) (tiltedBannedKernel A n theta true))
      (C + delta * A.patternMass) := by
    have hk : (fun a b => A.idealKernel theta a b +
        (densityNormalizedKernel (activeDensity F n) (tiltedBannedKernel A n theta true) a b -
          A.idealKernel theta a b)) =
        densityNormalizedKernel (activeDensity F n) (tiltedBannedKernel A n theta true) := by
      funext a b
      ring
    rw [hk] at hadd
    exact hadd
  have ht := normBound_density_identification P.idealMass (activeDensity F n)
    (tiltedBannedKernel A n theta true) _ (activeDensity_pos F n hb) hn
  simpa only [← tiltedIdealMass_density] using ht


end Erdos821.P3Clean
