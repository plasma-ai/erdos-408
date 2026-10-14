import Erdos821.P3Clean.SmallNormalization

/-! The physical conditioning map, in the original small mark measure. -/

noncomputable section
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

local instance (priority := 11000) physicalBoolEqDecidable (b c : Bool) : Decidable (b = c) :=
  instDecidableEqBool b c

local instance physicalLabelsDecidableEq (P : PrimeGroups) (M : ℕ) :
    DecidableEq (SmallLabels P M) := Classical.decEq _

theorem physicalSmallCoefficient_norm_sq (F : FixedData) (P : PrimeGroups) (J : ℕ)
    (y : P.SmallResidues) (z : ℂ) (hV : ∀ g : P.SmallGroup, 0 ≤ P.V g.val) :
    ‖physicalSmallCoefficient F P J y * z‖ ^ 2 =
      smallMarkMass P (J + F.ell) * ‖smallArrayCoefficient F P J y * z‖ ^ 2 := by
  have hm : 0 ≤ smallMarkMass P (J + F.ell) :=
    Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g) _)
  rw [physicalSmallCoefficient, mul_assoc, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hm]

theorem physical_conditioning_log_gain (F : FixedData) :
    ∃ Cs : ℝ, ∀ (x : ℝ) (P : PrimeGroups), P.Admissible F x → 0 < L x →
      ∀ (J : ℕ) (y : P.SmallResidues) (f : SmallLabels P (J + F.ell) → ℂ),
        (∑ d : SmallLabels P J,
          ‖physicalSmallCoefficient F P J y *
            ∑ a ∈ (smallArrayStates P (J + F.ell) y).filter
              (fun a => smallArrayPrefix J F.ell a = d), f a‖ ^ 2) ≤
          (L x) ^ Cs * (smallMarkMass P (J + F.ell) *
            ∑ a ∈ smallArrayStates P (J + F.ell) y, ‖f a‖ ^ 2) := by
  obtain ⟨Cs, hbound⟩ := small_array_conditioning_log_gain F
  refine ⟨Cs, ?_⟩
  intro x P hP hL J y f
  have hV (g : P.SmallGroup) : 0 ≤ P.V g.val :=
    (F.vMin_pos.trans_le ((hP.2.2.2.2.1 g.val).1)).le
  have hm : 0 ≤ smallMarkMass P (J + F.ell) :=
    Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g) _)
  simp only [physicalSmallCoefficient_norm_sq F P J y _ hV]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (hbound x P hP hL J y f) hm
  calc
    _ ≤ smallMarkMass P (J + F.ell) *
        ((L x) ^ Cs * ∑ a ∈ smallArrayStates P (J + F.ell) y, ‖f a‖ ^ 2) := h
    _ = _ := by ring


end Erdos821.P3Clean
