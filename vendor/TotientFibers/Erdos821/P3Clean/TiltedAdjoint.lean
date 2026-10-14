import Erdos821.P3Clean.TiltedComparison
import Erdos821.P3Clean.Adjoint
import Erdos821.P3Clean.MassPositivity

/-! The backward signed big kernel is the weighted adjoint at opposite frequency. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem phase_star (theta : ℝ) : star (phase theta) = phase (-theta) := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Complex.ofReal_neg, map_ofNat]
  congr 1
  ring

theorem bigBan_comm (ν : Pattern P J F.ell m) (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    bigBan ν a b u ↔ bigBan ν b a u := by
  unfold bigBan
  exact forall_congr' (fun _ => forall_congr' (fun _ => imp_congr_right
    (fun _ => forall_congr' (fun _ => and_comm))))

theorem tiltedIdealMass_pos (F : FixedData) (n : ℕ)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    {M : ℕ} (a : P.BigLabels M) : 0 < tiltedIdealMass F n a := by
  exact Finset.prod_pos (fun g _ => Finset.prod_pos (fun i _ =>
    tiltedMu_pos F P n g.val (a g i) (hb g _)))

theorem tiltedFreshMass_reversal (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (a b : P.BigLabels (J + F.ell)) (h : ν.matchesBig a b) :
    tiltedIdealMass F n a * tiltedFreshMass F n ν b =
      tiltedIdealMass F n b * tiltedFreshMass F n ν a :=
  bigFreshMass_reversal ν (fun g q => tiltedMu F P n g.val q) a b h

theorem tiltedBannedRaw_backward (A : Model F P J m) (n : ℕ) (theta : ℝ)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    tiltedBannedRaw A n theta false =
      weightedAdjoint (tiltedIdealMass F n) (tiltedBannedRaw A n (-theta) true) := by
  funext a b
  simp only [tiltedBannedRaw, weightedAdjoint, star_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  have hmatches : (A.pattern v).matchesBig a b ↔ (A.pattern v).matchesBig b a := by
    unfold Pattern.matchesBig
    exact forall_congr' (fun _ => forall_congr' (fun _ => imp_congr_right (fun _ => eq_comm)))
  have hg : ((A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u) ↔
      ((A.pattern v).matchesBig b a ∧ bigBan (A.pattern v) b a u) :=
    and_congr hmatches (bigBan_comm (A.pattern v) a b u)
  by_cases h : (A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u
  · have hs (t : ℝ) : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [if_pos h, if_pos (hg.mp h)]
    simp only [bigSignedCoefficient, Bool.false_eq_true, if_false, if_true]
    simp only [star_mul, phase_star, hs]
    rw [← DBig_eq_of_matches (A.pattern v) a b u h.1]
    have hr : (tiltedIdealMass F n b / tiltedIdealMass F n a) * tiltedFreshMass F n (A.pattern v) a =
        tiltedFreshMass F n (A.pattern v) b := by
      have hm := (tiltedIdealMass_pos F n hb a).ne'
      rw [div_mul_eq_mul_div]
      apply (div_eq_iff hm).mpr
      simpa only [mul_comm] using (tiltedFreshMass_reversal F n (A.pattern v) a b h.1).symm
    have hc := congrArg Complex.ofReal hr
    simp only [Complex.ofReal_mul, Complex.ofReal_div] at hc
    simp only [neg_mul, neg_neg, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
    calc
      _ = ((A.pattern v).bigAuxMass u : ℂ) * (tiltedFreshMass F n (A.pattern v) b : ℂ) *
          star ((A.pattern v).coefficient b a u * imaginaryPower ((A.pattern v).DBig a u) A.zeta) *
          phase (theta * ((A.pattern v).DBig a u : ℝ)) := by simp only [star_mul]
      _ = _ := by rw [← hc]; simp only [star_mul]; ring
  · simp only [if_neg h, if_neg (fun hh => h (hg.mpr hh)), star_zero, mul_zero]

theorem weightedAdjoint_averageBig (mass : P.BigLabels (J + F.ell) → ℝ)
    (K : P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → ℂ)
    (hm : ∀ p : P.BigPermutations (J + F.ell), ∀ a, mass (P.actBig p a) = mass a) :
    weightedAdjoint mass (averageBigKernel K) = averageBigKernel (weightedAdjoint mass K) := by
  funext a b
  simp only [weightedAdjoint, averageBigKernel, star_mul, star_sum, Finset.mul_sum, hm]
  have hs : star (bigSymmetryFactor P (J + F.ell)) = bigSymmetryFactor P (J + F.ell) := by
    simp only [bigSymmetryFactor, map_inv₀, map_pow, Complex.star_def, Complex.conj_natCast]
  rw [hs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem tiltedBannedKernel_backward (A : Model F P J m) (n : ℕ) (theta : ℝ)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    tiltedBannedKernel A n theta false =
      weightedAdjoint (tiltedIdealMass F n) (tiltedBannedKernel A n (-theta) true) := by
  change averageBigKernel (tiltedBannedRaw A n theta false) =
    weightedAdjoint (tiltedIdealMass F n) (averageBigKernel (tiltedBannedRaw A n (-theta) true))
  rw [tiltedBannedRaw_backward A n theta hb,
    weightedAdjoint_averageBig _ _ (tiltedIdealMass_actBig F n)]


end Erdos821.P3Clean
