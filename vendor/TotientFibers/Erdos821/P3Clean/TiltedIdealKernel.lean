import Erdos821.P3Clean.TwistedKernel
import Erdos821.P3Clean.PermutationSplit
import Erdos821.P3Clean.BigRefresh

/-! The signed big kernel at the character frequency, with literal density and ban changes. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def tiltedBannedRaw (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (a b : P.BigLabels (J + F.ell)) : ℂ :=
  ∑ v : Fin A.patternCount, ∑ u : P.BigAux J,
    if (A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u then
      ( (A.pattern v).bigAuxMass u * tiltedFreshMass F n (A.pattern v) b : ℝ) *
        bigSignedCoefficient A (A.pattern v) forward a b u *
        phase (theta * ((A.pattern v).DBig a u : ℝ)) else 0

def tiltedBannedKernel (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    (a b : P.BigLabels (J + F.ell)) : ℂ :=
  bigSymmetryFactor P (J + F.ell) *
    ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
      tiltedBannedRaw A n theta forward (P.actBig p a) (P.actBig q b)

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_combine (s t a : ℝ) : phase (s * a) * phase (t * a) = phase ((s + t) * a) := by
  rw [← phase_add]
  congr 1
  ring

theorem bigStep_real (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (d : SmallLabels P J) (a : P.BigLabels (J + F.ell)) (u : P.BigAux J) :
    (bigStep A ν forward d a u : ℝ) =
      (((if forward then A.k else -A.k) * (prefixPrimeProduct J d : ℤ) : ℤ) : ℝ) *
        (ν.DBig a u : ℝ) := by
  unfold bigStep
  push_cast
  ring

theorem DBig_eq_of_matches (ν : Pattern P J F.ell m) (a b : P.BigLabels (J + F.ell))
    (u : P.BigAux J) (h : ν.matchesBig a b) : ν.DBig a u = ν.DBig b u := by
  unfold Pattern.DBig
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ν.changed g.val
  · simp only [if_pos hi]
  · simp only [if_neg hi, h g (ν.slot i) ⟨i, rfl, hi⟩]

theorem regularCycleKernel_ideal_frequency (A : Model F P J m) (n B : ℕ)
    [Fintype (CutPendingState P B)] (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (psi : AddChar (PendingCycle P B) ℂ) :
    ∃ theta' : ℝ, ∀ a b : P.BigLabels (J + F.ell),
      fourierFibre (regularCycleKernel A n B theta forward d) psi a b =
        smallSignedCoefficient A forward d * tiltedBannedRaw A n theta' forward a b := by
  obtain ⟨t, ht⟩ := cycleDisplacement_character A B forward d psi
  let base : ℝ := (((if forward then A.k else -A.k) * (prefixPrimeProduct J d : ℤ) : ℤ) : ℝ)
  refine ⟨theta * base + t, ?_⟩
  intro a b
  rw [regularCycleKernel_fibre]
  simp only [tiltedBannedRaw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : (A.pattern v).matchesBig a b ∧ bigBan (A.pattern v) a b u
  · simp only [if_pos h, bigCleanCoefficient, ht, bigStep_real]
    change _ = _
    have hp : phase (theta * (base * ((A.pattern v).DBig a u : ℝ))) *
        phase (t * ((A.pattern v).DBig a u : ℝ)) =
        phase ((theta * base + t) * ((A.pattern v).DBig a u : ℝ)) := by
      rw [← mul_assoc]
      exact phase_combine _ _ _
    calc
      _ = smallSignedCoefficient A forward d *
          (((A.pattern v).bigAuxMass u * tiltedFreshMass F n (A.pattern v) b : ℝ) *
            bigSignedCoefficient A (A.pattern v) forward a b u *
            (phase (theta * (base * ((A.pattern v).DBig a u : ℝ))) *
              phase (t * ((A.pattern v).DBig a u : ℝ)))) := by ring
      _ = _ := by rw [hp]
  · simp only [if_neg h, mul_zero]


end Erdos821.P3Clean
