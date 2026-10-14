import Erdos821.P3Clean.ConditionedKernel
import Erdos821.P3Clean.FibreSandwich
import Erdos821.P3Clean.PhysicalConditioning

/-! Assemble the literal raw clean norm from its conditioned family. -/

noncomputable section
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

local instance (priority := 11000) assemblyBoolEqDecidable (b c : Bool) : Decidable (b = c) :=
  instDecidableEqBool b c

local instance assemblyLabelsDecidableEq (P : PrimeGroups) (M : ℕ) :
    DecidableEq (SmallLabels P M) := Classical.decEq _

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

abbrev BetweenState (P : PrimeGroups) (M B : ℕ) := P.BigLabels M × CutPendingState P B

abbrev CoordinateState (P : PrimeGroups) (M B : ℕ) := SmallLabels P M × BetweenState P M B

def betweenMass (F : FixedData) (n : ℕ) {M B : ℕ} (a : BetweenState P M B) : ℝ :=
  tiltedIdealMass F n a.1 * pendingMass F n a.2.val

def coordinateMass (F : FixedData) (J n B : ℕ) (a : CoordinateState P (J + F.ell) B) : ℝ :=
  fibreMass (fun y => smallArrayStates P (J + F.ell) y.2.val.1)
    (smallMarkMass P (J + F.ell)) (betweenMass F n) a

def coordinateRawKernel (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool) {B : ℕ}
    (a b : CoordinateState P (J + F.ell) B) : ℂ :=
  rawCleanKernel A n theta forward
    (a.2.2.val.1, joinLabels a.1 a.2.1, a.2.2.val.2)
    (b.2.2.val.1, joinLabels b.1 b.2.1, b.2.2.val.2)

def cutoffConditionedKernel (A : Model F P J m) (n : ℕ) (theta : ℝ) (forward : Bool) {B : ℕ}
    (d : SmallLabels P J) (a b : BetweenState P (J + F.ell) B) : ℂ :=
  conditionedKernel A n theta forward d (a.1, a.2.val) (b.1, b.2.val)

theorem coordinateMass_eq_memoryMass (F : FixedData) (J n B : ℕ)
    (a : CoordinateState P (J + F.ell) B) :
    coordinateMass F J n B a =
      P.memoryMass F J n ((cutoffStateCoordinates P (J + F.ell) B).symm a).val := by
  change coordinateMass F J n B a =
    P.memoryMass F J n (a.2.2.val.1, joinLabels a.1 a.2.1, a.2.2.val.2)
  rw [memoryMass_coordinates]
  unfold coordinateMass fibreMass betweenMass
  split_ifs <;> ring

theorem clean_norm_from_entry (F : FixedData) :
    ∃ Cs : ℝ, ∀ (x : ℝ) (P : PrimeGroups), P.Admissible F x → 0 < L x →
      ∀ (J n B : ℕ) [Fintype (CutPendingState P B)]
        (K : CoordinateState P (J + F.ell) B → CoordinateState P (J + F.ell) B → ℂ)
        (H : SmallLabels P J → BetweenState P (J + F.ell) B → BetweenState P (J + F.ell) B → ℂ)
        (C : ℝ), 0 ≤ C →
        (∀ a : BetweenState P (J + F.ell) B, 0 ≤ betweenMass F n a) →
        (∀ d : SmallLabels P J, NormBound (betweenMass F n (B := B)) (H d) C) →
        (∀ a b, (smallMarkMass P (J + F.ell) : ℂ) * K a b =
          if a.1 ∈ smallArrayStates P (J + F.ell) a.2.2.val.1 ∧
            b.1 ∈ smallArrayStates P (J + F.ell) b.2.2.val.1 ∧
            smallArrayPrefix J F.ell a.1 = smallArrayPrefix J F.ell b.1 then
              star (physicalSmallCoefficient F P J a.2.2.val.1) *
                physicalSmallCoefficient F P J b.2.2.val.1 *
                H (smallArrayPrefix J F.ell a.1) a.2 b.2 else 0) →
        NormBound (coordinateMass F J n B) K (C * (L x) ^ Cs) := by
  obtain ⟨Cs, hmap⟩ := physical_conditioning_log_gain F
  refine ⟨Cs, ?_⟩
  intro x P hP hL J n B _ K H C hC hm hH hentry
  apply normBound_fibreSandwich
    (fun y : BetweenState P (J + F.ell) B => smallArrayStates P (J + F.ell) y.2.val.1)
    (smallArrayPrefix J F.ell)
    (fun y : BetweenState P (J + F.ell) B => physicalSmallCoefficient F P J y.2.val.1)
    (smallMarkMass P (J + F.ell)) (betweenMass F n (B := B)) K H
    C ((L x) ^ Cs) hm hC (Real.rpow_nonneg hL.le _) hH
  · intro y f
    exact hmap x P hP hL J y.2.val.1 f
  · intro a b
    have h := hentry a b
    by_cases hs : a.1 ∈ smallArrayStates P (J + F.ell) a.2.2.val.1 ∧
        b.1 ∈ smallArrayStates P (J + F.ell) b.2.2.val.1 ∧
        smallArrayPrefix J F.ell a.1 = smallArrayPrefix J F.ell b.1
    · simpa only [if_pos hs] using h
    · simpa only [if_neg hs] using h

theorem raw_clean_norm_from_conditioned (F : FixedData) :
    ∃ Cs : ℝ, ∀ (x : ℝ) (P : PrimeGroups), P.Admissible F x → 0 < L x →
      ∀ (J m n B : ℕ) [Fintype (CutPendingState P B)]
        (A : Model F P J m) (theta : ℝ) (forward : Bool) (C : ℝ), 0 ≤ C →
        (∀ a : BetweenState P (J + F.ell) B, 0 ≤ betweenMass F n a) →
        (∀ d : SmallLabels P J,
          NormBound (betweenMass F n (B := B)) (cutoffConditionedKernel A n theta forward (B := B) d) C) →
        NormBound (coordinateMass F J n B) (coordinateRawKernel A n theta forward (B := B)) (C * (L x) ^ Cs) := by
  obtain ⟨Cs, hmap⟩ := physical_conditioning_log_gain F
  refine ⟨Cs, ?_⟩
  intro x P hP hL J m n B _ A theta forward C hC hm hH
  have hV (g : P.SmallGroup) : 0 < P.V g.val :=
    F.vMin_pos.trans_le ((hP.2.2.2.2.1 g.val).1)
  apply normBound_fibreSandwich
    (fun y : BetweenState P (J + F.ell) B => smallArrayStates P (J + F.ell) y.2.val.1)
    (smallArrayPrefix J F.ell)
    (fun y : BetweenState P (J + F.ell) B => physicalSmallCoefficient F P J y.2.val.1)
    (smallMarkMass P (J + F.ell)) (betweenMass F n (B := B))
    (coordinateRawKernel A n theta forward (B := B)) (cutoffConditionedKernel A n theta forward (B := B))
    C ((L x) ^ Cs) hm hC (Real.rpow_nonneg hL.le _) hH
  · intro y f
    exact hmap x P hP hL J y.2.val.1 f
  · intro a b
    have h := rawCleanKernel_coordinates A n theta forward a.1 b.1 a.2.1 b.2.1
      a.2.2.val b.2.2.val hV
    by_cases hs : smallCleanGate J F.ell a.1 b.1 a.2.2.val b.2.2.val
    · rw [if_pos hs] at h
      simp only [smallCleanGate] at hs
      rw [if_pos hs]
      exact h
    · rw [if_neg hs] at h
      simp only [smallCleanGate] at hs
      rw [if_neg hs]
      exact h


end Erdos821.P3Clean
