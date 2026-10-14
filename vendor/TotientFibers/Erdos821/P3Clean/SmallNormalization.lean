import Erdos821.P3Clean.ProductConditioning

/-! The normalized small-conditioning coefficient has exactly the literal edge normalization. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

theorem normalizedSmallCoefficient_factor (F : FixedData) (J : ℕ) (V : ℝ) (z : ℕ)
    (hV : 0 ≤ V) :
    normalizedSmallCoefficient F J V z =
      Real.sqrt (V ^ (-(F.ell : ℤ))) * F.q ^ (((z : ℝ) - ((J + F.ell : ℕ) : ℝ)) / 2) := by
  unfold normalizedSmallCoefficient
  rw [Real.sqrt_mul (zpow_nonneg hV _)]
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul F.q_pos.le]
  congr 2
  ring

theorem productSmallCoefficient_factor (F : FixedData) (P : PrimeGroups) (J : ℕ)
    (z : P.SmallGroup → ℕ) (hV : ∀ g : P.SmallGroup, 0 ≤ P.V g.val) :
    (∏ g : P.SmallGroup, normalizedSmallCoefficient F J (P.V g.val) (z g)) =
      Real.sqrt (smallTargetFactor (P := P) F) *
        F.q ^ (((∑ g : P.SmallGroup, (z g : ℝ)) -
          ((J + F.ell : ℕ) : ℝ) * Fintype.card P.SmallGroup) / 2) := by
  simp only [normalizedSmallCoefficient_factor F J _ _ (hV _)]
  rw [Finset.prod_mul_distrib, ← Real.sqrt_prod Finset.univ
    (fun g _ => zpow_nonneg (hV g) _), ← Real.rpow_sum_of_pos F.q_pos]
  have he : (∑ g : P.SmallGroup, ((z g : ℝ) - ((J + F.ell : ℕ) : ℝ)) / 2) =
      ((∑ g : P.SmallGroup, (z g : ℝ)) - ((J + F.ell : ℕ) : ℝ) *
        Fintype.card P.SmallGroup) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  rw [he]
  rfl

theorem smallArrayCoefficient_factor (F : FixedData) (P : PrimeGroups) (J : ℕ)
    (y : P.SmallResidues) (hV : ∀ g : P.SmallGroup, 0 ≤ P.V g.val) :
    smallArrayCoefficient F P J y =
      (Real.sqrt (smallTargetFactor (P := P) F) : ℂ) * (smallDamping F J y : ℂ) := by
  have hcoef : smallArrayCoefficient F P J y =
      ((∏ g : P.SmallGroup, normalizedSmallCoefficient F J (P.V g.val)
        ((Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card) : ℝ) : ℂ) := by
    unfold smallArrayCoefficient
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro g _
    congr 3
    ext p
    simp
  rw [hcoef, productSmallCoefficient_factor F P J _ hV, Complex.ofReal_mul]
  congr 1
  congr 1
  unfold smallDamping smallOmega
  simp only [Nat.cast_sum, Nat.cast_add]

def smallMarkMass (P : PrimeGroups) (M : ℕ) : ℝ :=
  ∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℤ))

def physicalSmallCoefficient (F : FixedData) (P : PrimeGroups) (J : ℕ)
    (y : P.SmallResidues) : ℂ :=
  (Real.sqrt (smallMarkMass P (J + F.ell)) : ℂ) * smallArrayCoefficient F P J y

theorem physicalSmallCoefficient_joint (F : FixedData) (P : PrimeGroups) (J : ℕ)
    (y z : P.SmallResidues) (hV : ∀ g : P.SmallGroup, 0 ≤ P.V g.val) :
    star (physicalSmallCoefficient F P J y) * physicalSmallCoefficient F P J z =
      (smallMarkMass P (J + F.ell) * smallTargetFactor (P := P) F *
        smallDamping F J y * smallDamping F J z : ℝ) := by
  have hm : 0 ≤ smallMarkMass P (J + F.ell) :=
    Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g) _)
  have ht : 0 ≤ smallTargetFactor (P := P) F :=
    Finset.prod_nonneg (fun g _ => zpow_nonneg (hV g) _)
  simp only [physicalSmallCoefficient, smallArrayCoefficient_factor F P J _ hV,
    star_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
  have heq : Real.sqrt (smallMarkMass P (J + F.ell)) *
      (Real.sqrt (smallTargetFactor (P := P) F) * smallDamping F J y) *
      (Real.sqrt (smallMarkMass P (J + F.ell)) *
        (Real.sqrt (smallTargetFactor (P := P) F) * smallDamping F J z)) =
        smallMarkMass P (J + F.ell) * smallTargetFactor (P := P) F *
          smallDamping F J y * smallDamping F J z := by
    calc
      _ = (Real.sqrt (smallMarkMass P (J + F.ell))) ^ 2 *
          (Real.sqrt (smallTargetFactor (P := P) F)) ^ 2 *
          smallDamping F J y * smallDamping F J z := by ring
      _ = _ := by rw [Real.sq_sqrt hm, Real.sq_sqrt ht]
  exact congrArg Complex.ofReal heq


end Erdos821.P3Clean
