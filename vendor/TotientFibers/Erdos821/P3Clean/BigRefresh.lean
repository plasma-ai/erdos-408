import Erdos821.P3Clean.RefreshLaws
import Erdos821.P3Clean.CleanCoefficients

/-! The product refresh laws in the literal big-label coordinates. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups} {J ell m : ℕ}

def flattenBigLabels (P : PrimeGroups) (M : ℕ) :
    P.BigLabels M ≃ ((z : P.BigGroup × Fin M) → P.Prime z.1.val) where
  toFun a z := a z.1 z.2
  invFun a g i := a (g, i)
  left_inv := by intro a; rfl
  right_inv := by intro a; funext z; cases z; rfl

def bigProductMass {M : ℕ} (mu : (g : P.BigGroup) → P.Prime g.val → ℝ)
    (a : P.BigLabels M) : ℝ := ∏ g : P.BigGroup, ∏ i : Fin M, mu g (a g i)

def bigFreshMass (ν : Pattern P J ell m) (mu : (g : P.BigGroup) → P.Prime g.val → ℝ)
    (a : P.BigLabels (J + ell)) : ℝ :=
  ∏ g : P.BigGroup, ∏ i : Fin (J + ell), if ν.shared g.val i then 1 else mu g (a g i)

theorem flat_productMass {M : ℕ} (mu : (g : P.BigGroup) → P.Prime g.val → ℝ)
    (a : P.BigLabels M) :
    productMass (fun z : P.BigGroup × Fin M => mu z.1) (flattenBigLabels P M a) =
      bigProductMass mu a := by
  simp only [productMass, bigProductMass, Fintype.prod_prod_type, flattenBigLabels]
  rfl

theorem flat_refreshMass (ν : Pattern P J ell m)
    (mu : (g : P.BigGroup) → P.Prime g.val → ℝ) (a : P.BigLabels (J + ell)) :
    refreshMass (fun z : P.BigGroup × Fin (J + ell) => ν.shared z.1.val z.2)
      (fun z => mu z.1) (flattenBigLabels P (J + ell) a) = bigFreshMass ν mu a := by
  simp only [refreshMass, bigFreshMass, Fintype.prod_prod_type, flattenBigLabels]
  rfl

theorem flat_refreshMatches (ν : Pattern P J ell m) (a b : P.BigLabels (J + ell)) :
    refreshMatches (fun z : P.BigGroup × Fin (J + ell) => ν.shared z.1.val z.2)
      (flattenBigLabels P (J + ell) a) (flattenBigLabels P (J + ell) b) ↔ ν.matchesBig a b := by
  constructor
  · intro h g i hi
    exact h (g, i) hi
  · intro h z hz
    exact h z.1 z.2 hz

theorem bigFreshMass_reversal (ν : Pattern P J ell m)
    (mu : (g : P.BigGroup) → P.Prime g.val → ℝ) (a b : P.BigLabels (J + ell))
    (h : ν.matchesBig a b) :
    bigProductMass mu a * bigFreshMass ν mu b = bigProductMass mu b * bigFreshMass ν mu a := by
  have hh := refreshMass_reversal
    (fun z : P.BigGroup × Fin (J + ell) => ν.shared z.1.val z.2) (fun z => mu z.1)
    (flattenBigLabels P (J + ell) a) (flattenBigLabels P (J + ell) b)
    ((flat_refreshMatches ν a b).mpr h)
  simpa only [flat_productMass, flat_refreshMass] using hh

theorem bigFreshMass_row_sum (ν : Pattern P J ell m)
    (mu : (g : P.BigGroup) → P.Prime g.val → ℝ)
    (hmu : ∀ g, (∑ p : P.Prime g.val, mu g p) = 1) (a : P.BigLabels (J + ell)) :
    (∑ b : P.BigLabels (J + ell), if ν.matchesBig a b then bigFreshMass ν mu b else 0) = 1 := by
  have h := refreshKernel_row_sum
    (fun z : P.BigGroup × Fin (J + ell) => ν.shared z.1.val z.2)
    (fun z => mu z.1) (fun z => hmu z.1) (flattenBigLabels P (J + ell) a)
  have hs := Equiv.sum_comp (flattenBigLabels P (J + ell))
    (fun b => refreshKernel
      (fun z : P.BigGroup × Fin (J + ell) => ν.shared z.1.val z.2)
      (fun z => mu z.1) (flattenBigLabels P (J + ell) a) b)
  have hh := hs.trans h
  simpa only [refreshKernel, flat_refreshMatches, flat_refreshMass] using hh


end Erdos821.P3Clean
