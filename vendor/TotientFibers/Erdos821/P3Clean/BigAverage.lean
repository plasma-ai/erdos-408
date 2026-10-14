import Erdos821.P3Clean.PermutationSplit
import Erdos821.P3Clean.RawNormAssembly

/-! Big symmetrization remains inside the exact conditioned family. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

def permuteBetween {M B : ℕ} (p : P.BigPermutations M) (a : BetweenState P M B) :
    BetweenState P M B := (P.actBig p a.1, a.2)

def permuteCoordinateBig {M B : ℕ} (p : P.BigPermutations M) (a : CoordinateState P M B) :
    CoordinateState P M B := (a.1, permuteBetween p a.2)

def bigAveragedRawKernel (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool) {B : ℕ}
    (a b : CoordinateState P (J + F.ell) B) : ℂ :=
  bigSymmetryFactor P (J + F.ell) *
    ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
      coordinateRawKernel A n theta forward (permuteCoordinateBig p a) (permuteCoordinateBig q b)

def bigAveragedConditionedKernel (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool) {B : ℕ}
    (d : SmallLabels P J) (a b : BetweenState P (J + F.ell) B) : ℂ :=
  bigSymmetryFactor P (J + F.ell) *
    ∑ p : P.BigPermutations (J + F.ell), ∑ q : P.BigPermutations (J + F.ell),
      cutoffConditionedKernel A n theta forward d (permuteBetween p a) (permuteBetween q b)

theorem bigAveragedRawKernel_entry (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool)
    {B : ℕ} (a b : CoordinateState P (J + F.ell) B)
    (hV : ∀ g : P.SmallGroup, 0 < P.V g.val) :
    (smallMarkMass P (J + F.ell) : ℂ) * bigAveragedRawKernel A n theta forward a b =
      if smallCleanGate J F.ell a.1 b.1 a.2.2.val b.2.2.val then
        star (physicalSmallCoefficient F P J a.2.2.val.1) *
          physicalSmallCoefficient F P J b.2.2.val.1 *
          bigAveragedConditionedKernel A n theta forward (smallArrayPrefix J F.ell a.1) a.2 b.2
      else 0 := by
  have he (p q : P.BigPermutations (J + F.ell)) :
      (smallMarkMass P (J + F.ell) : ℂ) *
        coordinateRawKernel A n theta forward (permuteCoordinateBig p a) (permuteCoordinateBig q b) =
      if smallCleanGate J F.ell a.1 b.1 a.2.2.val b.2.2.val then
        star (physicalSmallCoefficient F P J a.2.2.val.1) *
          physicalSmallCoefficient F P J b.2.2.val.1 *
          cutoffConditionedKernel A n theta forward (smallArrayPrefix J F.ell a.1)
            (permuteBetween p a.2) (permuteBetween q b.2) else 0 := by
    exact rawCleanKernel_coordinates A n theta forward a.1 b.1
      (P.actBig p a.2.1) (P.actBig q b.2.1) a.2.2.val b.2.2.val hV
  unfold bigAveragedRawKernel bigAveragedConditionedKernel
  rw [mul_left_comm, Finset.mul_sum]
  simp_rw [Finset.mul_sum, he]
  by_cases hs : smallCleanGate J F.ell a.1 b.1 a.2.2.val b.2.2.val
  · simp only [if_pos hs]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  · simp only [if_neg hs, Finset.sum_const_zero, mul_zero]


theorem big_averaged_clean_norm (F : FixedData) :
    ∃ Cs : ℝ, ∀ (x : ℝ) (P : PrimeGroups), P.Admissible F x → 0 < L x →
      ∀ (J m n B : ℕ) [Fintype (CutPendingState P B)]
        (A : Model F P J m) (theta : ℝ) (forward : Bool) (C : ℝ), 0 ≤ C →
        (∀ a : BetweenState P (J + F.ell) B, 0 ≤ betweenMass F n a) →
        (∀ d : SmallLabels P J, NormBound (betweenMass F n (B := B))
          (bigAveragedConditionedKernel A n theta forward (B := B) d) C) →
        NormBound (coordinateMass F J n B)
          (bigAveragedRawKernel A n theta forward (B := B)) (C * (L x) ^ Cs) := by
  obtain ⟨Cs, hentryNorm⟩ := clean_norm_from_entry F
  refine ⟨Cs, ?_⟩
  intro x P hP hL J m n B _ A theta forward C hC hm hH
  apply hentryNorm x P hP hL J n B
    (bigAveragedRawKernel A n theta forward (B := B))
    (bigAveragedConditionedKernel A n theta forward (B := B)) C hC hm hH
  intro a b
  have hV (g : P.SmallGroup) : 0 < P.V g.val := F.vMin_pos.trans_le ((hP.2.2.2.2.1 g.val).1)
  have h := bigAveragedRawKernel_entry A n theta forward a b hV
  by_cases hs : smallCleanGate J F.ell a.1 b.1 a.2.2.val b.2.2.val
  · rw [if_pos hs] at h
    simp only [smallCleanGate] at hs
    simpa only [if_pos hs] using h
  · rw [if_neg hs] at h
    simp only [smallCleanGate] at hs
    simpa only [if_neg hs] using h


end Erdos821.P3Clean
