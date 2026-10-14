import Erdos821.S2.MemoryIdentity
import Erdos821.S2.FourierClosure
import Erdos821.P3Adj.Weight

/-! The baseline and Fourier closure transfer a uniform memory bound to closed paths. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem baselinePrime_le_one (F : FixedData) (n p : ℕ) : baselinePrime F n p ≤ 1 := by
  have hs : 0 ≤ ∑ i : Fin (n + 1), eta F n i :=
    Finset.sum_nonneg (fun i _ => (Erdos821.P3Adj.eta_pos F n i).le)
  unfold baselinePrime
  exact sub_le_self _ (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) hs)

theorem bigBaseline_norm_le_one (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ baselinePrime F n p.val) :
    ‖(bigBaseline F P n : ℂ)‖ ≤ 1 := by
  have h0 : 0 ≤ bigBaseline F P n := by
    rw [bigBaseline_eq_subtypes]
    apply Finset.prod_nonneg
    intro g _
    exact Finset.prod_nonneg (fun p _ => hb g p)
  have h1 : bigBaseline F P n ≤ 1 := by
    rw [bigBaseline_eq_subtypes]
    apply Finset.prod_le_one₀
    · intro g _
      exact Finset.prod_nonneg (fun p _ => hb g p)
    · intro g _
      apply Finset.prod_le_one₀
      · intro p _
        exact hb g p
      · intro p _
        exact baselinePrime_le_one F n p.val
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using h1

theorem closedResidueExpression_norm_le_memory_bound
    {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m)
    (n : ℕ) (rho C : ℝ)
    (hId : ∀ theta : ℝ, residueExpression A n theta =
      (bigBaseline F P n : ℂ) * distinctMemoryExpression A n rho theta)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ baselinePrime F n p.val)
    (hMem : ∀ theta : ℝ, ‖distinctMemoryExpression A n rho theta‖ ≤ C) :
    ‖closedResidueExpression A n‖ ≤ C := by
  rw [← integral_residueExpression A n]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C) (f := fun theta => residueExpression A n theta)
    (fun theta _ => by
      rw [hId theta, norm_mul]
      exact (mul_le_mul (bigBaseline_norm_le_one F P n hb) (hMem theta)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul C))
  simpa only [sub_zero, abs_one, mul_one] using h


end Erdos821.S2Core
