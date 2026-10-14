import Erdos821.P3Clean.ControlledKernel
import Erdos821.P3Clean.SymmetricFibre
import Erdos821.P3Clean.MassPositivity

/-! Transfer the symmetrized big Fourier bounds to the literal conditioned family. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem bigAveragedConditionedKernel_controlled (A : Model F P J m) (n B : ℕ)
    [Fintype (CutPendingState P B)] (theta : ℝ) (forward : Bool) (d : SmallLabels P J) :
    bigAveragedConditionedKernel A n theta forward (B := B) d =
      controlledKernel (symmetricCycleKernel A n B theta forward d)
        (cycleAct (pendingTranslationEquiv (P := P) B 1)) := by
  funext a b
  simp only [bigAveragedConditionedKernel, cutoffConditionedKernel_cycle, permuteBetween]
  change (bigSymmetryFactor P (J + F.ell) *
    ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell), ∑ r : PendingCycle P B,
      if cycleAct (pendingTranslationEquiv (P := P) B 1) r a.2 = b.2 then
        regularCycleKernel A n B theta forward d (P.actBig p a.1) (P.actBig q b.1) r else 0) = _
  have hs : (∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell), ∑ r : PendingCycle P B,
      if cycleAct (pendingTranslationEquiv (P := P) B 1) r a.2 = b.2 then
        regularCycleKernel A n B theta forward d (P.actBig p a.1) (P.actBig q b.1) r else 0) =
      ∑ r : PendingCycle P B, ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
        if cycleAct (pendingTranslationEquiv (P := P) B 1) r a.2 = b.2 then
          regularCycleKernel A n B theta forward d (P.actBig p a.1) (P.actBig q b.1) r else 0 := by
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun q r => if cycleAct (pendingTranslationEquiv (P := P) B 1) r a.2 = b.2 then
        regularCycleKernel A n B theta forward d (P.actBig _ a.1) (P.actBig q b.1) r else 0)]
    rw [Finset.sum_comm]
  rw [hs, Finset.mul_sum]
  unfold controlledKernel
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : cycleAct (pendingTranslationEquiv (P := P) B 1) r a.2 = b.2
  · simp only [if_pos h, symmetricCycleKernel]
  · simp only [if_neg h, Finset.sum_const_zero, mul_zero]

theorem normBound_bigAveragedConditionedKernel (A : Model F P J m) (n B : ℕ)
    [Fintype (CutPendingState P B)] (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hbig : ∀ theta' : ℝ, NormBound (tiltedIdealMass F n) (tiltedBannedKernel A n theta' forward) C) :
    NormBound (betweenMass F n (B := B))
      (bigAveragedConditionedKernel A n theta forward (B := B) d) C := by
  have hm (a : P.BigLabels (J + F.ell)) : 0 ≤ tiltedIdealMass F n a := by
    exact Finset.prod_nonneg (fun g _ => Finset.prod_nonneg (fun i _ =>
      (tiltedMu_pos F P n g.val (a g i) (hb g _)).le))
  have hw (a : CutPendingState P B) : 0 ≤ pendingMass F n a.val := by
    unfold pendingMass
    exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun g _ =>
      groupMemoryMass_nonneg F P n g.val (hb g) (a.val.2 g)))
  have hf (psi : AddChar (PendingCycle P B) ℂ) :
      NormBound (tiltedIdealMass F n) (fourierFibre (symmetricCycleKernel A n B theta forward d) psi) C := by
    obtain ⟨theta', he⟩ := symmetricCycleKernel_ideal_frequency A n B theta forward d psi
    have h := normBound_mul_endpoints hm hC (hbig theta')
      (fun _ => smallSignedCoefficient A forward d) (fun _ => 1)
      (fun _ => (smallSignedCoefficient_norm A forward d).le) (fun _ => by simp)
    have hk : fourierFibre (symmetricCycleKernel A n B theta forward d) psi =
        (fun a b => smallSignedCoefficient A forward d * tiltedBannedKernel A n theta' forward a b) :=
      funext (fun a => funext (he a))
    rw [hk]
    simpa only [mul_one] using h
  rw [bigAveragedConditionedKernel_controlled A n B theta forward d]
  exact normBound_controlledKernel (tiltedIdealMass F n) (fun a : CutPendingState P B => pendingMass F n a.val)
    (cycleAct (pendingTranslationEquiv (P := P) B 1))
    (cycleAct_preserves_weight (pendingTranslationEquiv (P := P) B 1)
      (fun a : CutPendingState P B => pendingMass F n a.val)
      (fun a : CutPendingState P B => pendingMass_translate F n 1 a.val))
    (cycleAct_add _) (symmetricCycleKernel A n B theta forward d) C hm hw hC hf


end Erdos821.P3Clean
