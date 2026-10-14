import Erdos821.S2Empty.BoundaryAssembly
import Erdos821.S2.MassDecomposition

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

theorem fintype_sum_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    (∑ x, c * f x) = c * ∑ x, f x := by
  classical
  exact (Finset.mul_sum (s := Finset.univ) f c).symm

theorem initial_boundary_mass_factorization (F : FixedData) (P : PrimeGroups)
    (J m n : ℕ) (A : Model F P J m)
    (hV : ∀ g, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      0 < baselinePrime F n p.val) :
    Erdos821.S2Core.initialMemoryBoundaryMass A n =
      (Fintype.card P.SmallResidues : ℝ)⁻¹ *
        (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
        ((∑ y : P.SmallResidues, ∑ s : SmallLabels P (J + F.ell),
            if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0) *
          ∑ b : BigLabels P (J + F.ell), bigLabelWeight F P n (J + F.ell) b) := by
  classical
  let M := J + F.ell
  let C : ℝ := (Fintype.card P.SmallResidues : ℝ)⁻¹ *
    ∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℕ) : ℤ)
  have hCardNat : 0 < Fintype.card P.SmallResidues := by
    exact Fintype.card_pos_iff.mpr ⟨fun _ _ => 0⟩
  have hCard : 0 < (Fintype.card P.SmallResidues : ℝ) := by exact_mod_cast hCardNat
  have hsmallProd : 0 < ∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℕ) : ℤ) := by
    apply Finset.prod_pos
    intro g _
    exact zpow_pos (hV g.val) _
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (inv_pos.mpr hCard) hsmallProd
  have htilt (g : P.BigGroup) (p : P.Prime g.val) :
      0 < tiltedMu F P n g.val p := by
    unfold tiltedMu
    have hp : 0 < (p.val : ℝ) := by
      exact_mod_cast (P.prime g.val p.val p.property).pos
    exact inv_pos.mpr (mul_pos (mul_pos (hV g.val) hp) (hbase g p))
  have hweight (b : BigLabels P M) : 0 ≤ bigLabelWeight F P n M b := by
    apply Finset.prod_nonneg
    intro g _
    apply Finset.prod_nonneg
    intro j _
    exact (htilt g (b g j)).le
  have hterm (y : P.SmallResidues) (a : P.Labels M) :
      |P.memoryMass F J n (y, a, fun _ => 0)| =
        if P.smallPhysical y a then
          C * bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0 := by
    rw [Erdos821.S2Core.memoryMass_empty]
    by_cases hs : P.smallPhysical y a
    · rw [if_pos hs]
      have hcoeff :
          (Fintype.card P.SmallResidues : ℝ)⁻¹ *
              (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) = C := by
        rfl
      have hbig :
          (∏ g : P.BigGroup, ∏ j : Fin (J + F.ell),
            tiltedMu F P n g.val (a g.val j)) =
              bigLabelWeight F P n M ((labelSplitEquiv P M a).2) := by
        rfl
      calc
        _ = |C * bigLabelWeight F P n M ((labelSplitEquiv P M a).2)| := by
          rw [hcoeff, hbig]
        _ = _ := by
          rw [abs_of_nonneg (mul_nonneg hC.le (hweight _)), if_pos hs]
    · simp [hs]
  unfold Erdos821.S2Core.initialMemoryBoundaryMass
  simp_rw [hterm]
  change
    (∑ y : P.SmallResidues, ∑ a : P.Labels M,
      if P.smallPhysical y a then
        C * bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0) = _
  calc
    _ = ∑ y : P.SmallResidues, ∑ a : P.Labels M,
        C * (if P.smallPhysical y a then
          bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro a _
      by_cases hs : P.smallPhysical y a <;> simp [hs]
    _ = C * ∑ y : P.SmallResidues, ∑ a : P.Labels M,
        if P.smallPhysical y a then
          bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0 := by
      calc
        _ = ∑ y : P.SmallResidues, C * ∑ a : P.Labels M,
            if P.smallPhysical y a then
              bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          exact fintype_sum_const_mul C (fun a =>
            if P.smallPhysical y a then
              bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0)
        _ = _ := fintype_sum_const_mul C (fun y =>
          ∑ a : P.Labels M,
            if P.smallPhysical y a then
              bigLabelWeight F P n M ((labelSplitEquiv P M a).2) else 0)
    _ = C * ((∑ y : P.SmallResidues, ∑ s : SmallLabels P M,
          if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0) *
        ∑ b : BigLabels P M, bigLabelWeight F P n M b) := by
      congr 1
      calc
        _ = ∑ y : P.SmallResidues,
            (∑ s : SmallLabels P M,
              if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0) *
              ∑ b : BigLabels P M, bigLabelWeight F P n M b := by
          apply Finset.sum_congr rfl
          intro y _
          exact full_label_sum_factor F P n M y
        _ = _ := by rw [Finset.sum_mul]
    _ = _ := by
      simp [C, M]


end Erdos821.S2Empty
