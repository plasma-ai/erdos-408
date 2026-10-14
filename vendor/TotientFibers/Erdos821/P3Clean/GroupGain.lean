import Erdos821.P3Clean.Conditioning

/-! Converting a constant per small group into the fixed logarithmic exponent. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

theorem smallGroup_card (P : PrimeGroups) :
    Fintype.card P.SmallGroup = P.smallGroups.card := by
  rw [Fintype.card_subtype]
  rfl

theorem small_group_gain (F : FixedData) (C : ℝ) (hC : 1 ≤ C)
    (x : ℝ) (P : PrimeGroups) (hP : P.Admissible F x) (hL : 0 < L x) :
    C ^ Fintype.card P.SmallGroup ≤ (L x) ^ (F.C₀ * Real.log C) := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hs : (Fintype.card P.SmallGroup : ℝ) ≤ F.C₀ * T x := by
    rw [smallGroup_card]
    exact hP.2.1
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCp, Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  simpa only [T, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hs hlog

/-- One fixed exponent works for every J in the small-conditioning gain. -/
theorem small_conditioning_fixed_exponent (F : FixedData) :
    ∃ (C Cs : ℝ), 1 ≤ C ∧
      (∀ (P : PrimeGroups) (g : P.Group) (J : ℕ)
        (y : (p : P.Prime g) → ZMod p.val), F.vMin ≤ P.V g →
        ∀ f : (Fin (J + F.ell) → P.Prime g) → ℂ,
          (∑ d : Fin J → P.Prime g,
            ‖(normalizedSmallCoefficient F J (P.V g)
                ((Finset.univ.filter (fun p : P.Prime g => y p = 0)).card) : ℂ) *
              ∑ a ∈ smallPrefixFibre J F.ell y d, f a‖ ^ 2) ≤
            C * ∑ a ∈ Finset.univ.filter
              (fun a : Fin (J + F.ell) → P.Prime g =>
                Function.Injective a ∧ ∀ i, y (a i) = 0), ‖f a‖ ^ 2) ∧
      ∀ (x : ℝ) (P : PrimeGroups), P.Admissible F x → 0 < L x →
        C ^ Fintype.card P.SmallGroup ≤ (L x) ^ Cs := by
  obtain ⟨C, _, hbound⟩ := small_conditioning_normSq_uniform F
  refine ⟨max 1 C, F.C₀ * Real.log (max 1 C), le_max_left _ _, ?_, ?_⟩
  · intro P g J y hV f
    exact (hbound P g J y hV f).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  · intro x P hP hL
    exact small_group_gain F _ (le_max_left _ _) x P hP hL


end Erdos821.P3Clean
