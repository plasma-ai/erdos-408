import Erdos821.P3Clean.TiltedIdealKernel
import Erdos821.P3Clean.BigAverage

/-! Big endpoint averaging commutes with the finite cyclic Fourier reduction. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def symmetricCycleKernel (A : Model F P J m) (n B : ℕ) [Fintype (CutPendingState P B)]
    (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (a b : P.BigLabels (J + F.ell)) (r : PendingCycle P B) : ℂ :=
  bigSymmetryFactor P (J + F.ell) *
    ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
      regularCycleKernel A n B theta forward d (P.actBig p a) (P.actBig q b) r

theorem symmetricCycleKernel_fibre (A : Model F P J m) (n B : ℕ)
    [Fintype (CutPendingState P B)] (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (psi : AddChar (PendingCycle P B) ℂ) (a b : P.BigLabels (J + F.ell)) :
    fourierFibre (symmetricCycleKernel A n B theta forward d) psi a b =
      bigSymmetryFactor P (J + F.ell) *
        ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
          fourierFibre (regularCycleKernel A n B theta forward d) psi (P.actBig p a) (P.actBig q b) := by
  unfold fourierFibre symmetricCycleKernel
  simp only [Finset.mul_sum, Finset.sum_mul]
  have h (r : PendingCycle P B) :
      (∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
        bigSymmetryFactor P (J + F.ell) *
          regularCycleKernel A n B theta forward d (P.actBig p a) (P.actBig q b) r * psi r) =
      ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
        bigSymmetryFactor P (J + F.ell) *
          (regularCycleKernel A n B theta forward d (P.actBig p a) (P.actBig q b) r * psi r) := by
    simp only [mul_assoc]
  simp only [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]

theorem symmetricCycleKernel_ideal_frequency (A : Model F P J m) (n B : ℕ)
    [Fintype (CutPendingState P B)] (theta : ℝ) (forward : Bool) (d : SmallLabels P J)
    (psi : AddChar (PendingCycle P B) ℂ) :
    ∃ theta' : ℝ, ∀ a b : P.BigLabels (J + F.ell),
      fourierFibre (symmetricCycleKernel A n B theta forward d) psi a b =
        smallSignedCoefficient A forward d * tiltedBannedKernel A n theta' forward a b := by
  obtain ⟨theta', ht⟩ := regularCycleKernel_ideal_frequency A n B theta forward d psi
  refine ⟨theta', ?_⟩
  intro a b
  rw [symmetricCycleKernel_fibre]
  simp only [ht, tiltedBannedKernel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring


end Erdos821.P3Clean
