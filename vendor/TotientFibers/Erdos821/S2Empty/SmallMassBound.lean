import Erdos821.S2Empty.MassAssembly

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

theorem small_boundary_factor_le_one (P : PrimeGroups) (M : ℕ)
    (hV : ∀ g, 0 < P.V g) :
    (Fintype.card P.SmallResidues : ℝ)⁻¹ *
      (∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℤ))) *
      (∑ y : P.SmallResidues, ∑ s : SmallLabels P M,
        if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0) ≤ 1 := by
  classical
  let localFactor (g : P.SmallGroup) : ℝ :=
    (Fintype.card (SmallLocalResidues P g) : ℝ)⁻¹ *
      (P.V g.val) ^ (-(M : ℤ)) *
      (∑ a : Fin M → P.Prime g.val, ∑ y : SmallLocalResidues P g,
        if smallLocalGood g y a then (1 : ℝ) else 0)
  have hcard : (Fintype.card P.SmallResidues : ℝ) =
      ∏ g : P.SmallGroup, (Fintype.card (SmallLocalResidues P g) : ℝ) := by
    simp [PrimeGroups.SmallResidues, SmallLocalResidues, Fintype.card_pi]
  have hcardInv : (Fintype.card P.SmallResidues : ℝ)⁻¹ =
      ∏ g : P.SmallGroup, (Fintype.card (SmallLocalResidues P g) : ℝ)⁻¹ := by
    rw [hcard]
    simp [Finset.prod_inv_distrib]
  have hsum := small_choice_sum_eq_prod P M
  have hfactor :
      (Fintype.card P.SmallResidues : ℝ)⁻¹ *
        (∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℤ))) *
        (∑ y : P.SmallResidues, ∑ s : SmallLabels P M,
          if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0) =
        ∏ g : P.SmallGroup, localFactor g := by
    rw [hsum, hcardInv]
    dsimp [localFactor]
    symm
    calc
      _ =
          (∏ g : P.SmallGroup,
            (Fintype.card (SmallLocalResidues P g) : ℝ)⁻¹ *
              (P.V g.val) ^ (-(M : ℤ))) *
            (∏ g : P.SmallGroup,
              ∑ a : Fin M → P.Prime g.val, ∑ y : SmallLocalResidues P g,
                if smallLocalGood g y a then (1 : ℝ) else 0) := by
        rw [Finset.prod_mul_distrib]
      _ = _ := by rw [Finset.prod_mul_distrib]
  have hlocal_le (g : P.SmallGroup) : localFactor g ≤ 1 := by
    dsimp [localFactor]
    change (Fintype.card ((p : P.Prime g.val) → ZMod p.val) : ℝ)⁻¹ *
        (P.V g.val) ^ (-(M : ℤ)) *
        (∑ a : Fin M → P.Prime g.val, ∑ y : SmallLocalResidues P g,
          if smallLocalGood g y a then (1 : ℝ) else 0) ≤ 1
    have hsumEq :
        (∑ a : Fin M → P.Prime g.val, ∑ y : SmallLocalResidues P g,
          if smallLocalGood g y a then (1 : ℝ) else 0) =
        (∑ a : Fin M → P.Prime g.val, ∑ y : (p : P.Prime g.val) → ZMod p.val,
          if Function.Injective a ∧ (∀ i, y (a i) = 0) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : Function.Injective a ∧ (∀ i, y (a i) = 0)
      · simp [smallLocalGood, h]
      · simp [smallLocalGood, h]
    rw [hsumEq]
    exact local_small_group_mass_le_one P g.val M (hV g.val)
  have hlocal_nonneg (g : P.SmallGroup) : 0 ≤ localFactor g := by
    dsimp [localFactor]
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact zpow_nonneg (hV g.val).le _
    · apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro y _
      split_ifs <;> positivity
  rw [hfactor]
  calc
    ∏ g : P.SmallGroup, localFactor g ≤ ∏ _g : P.SmallGroup, (1 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro g _
        exact hlocal_nonneg g
      · intro g _
        exact hlocal_le g
    _ = 1 := by simp


end Erdos821.S2Empty
