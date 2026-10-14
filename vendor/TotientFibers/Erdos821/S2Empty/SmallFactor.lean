import Erdos821.S2Empty.EmptyBoundaryMass

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

abbrev SmallLabels (P : PrimeGroups) (M : ℕ) :=
  (g : P.SmallGroup) → Fin M → P.Prime g.val

abbrev SmallLocalResidues (P : PrimeGroups) (g : P.SmallGroup) :=
  (p : P.Prime g.val) → ZMod p.val

def smallLocalGood {P : PrimeGroups} {M : ℕ} (g : P.SmallGroup)
    (y : SmallLocalResidues P g) (a : Fin M → P.Prime g.val) : Prop :=
  Function.Injective a ∧ ∀ i, y (a i) = 0

def piProductEquiv {G : Type*} {A B : G → Type*} :
    ((∀ g : G, A g) × (∀ g : G, B g)) ≃ (∀ g : G, A g × B g) where
  toFun z g := (z.1 g, z.2 g)
  invFun z := (fun g => (z g).1, fun g => (z g).2)
  left_inv z := by cases z; rfl
  right_inv z := by funext g; exact Prod.eta (z g)

theorem prod_indicator_forall {G : Type*} [Fintype G] [DecidableEq G]
    (p : G → Prop) [DecidablePred p] :
    (if ∀ g, p g then (1 : ℝ) else 0) = ∏ g, if p g then (1 : ℝ) else 0 := by
  classical
  by_cases h : ∀ g, p g
  · simp [h]
  · obtain ⟨g, hg⟩ := not_forall.mp h
    have hz : (∏ g, if p g then (1 : ℝ) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ g)
      simp [hg]
    simp [h, hz]

theorem small_choice_sum_eq_prod (P : PrimeGroups) (M : ℕ) :
    (∑ y : P.SmallResidues, ∑ a : SmallLabels P M,
      if ∀ g : P.SmallGroup, smallLocalGood g (y g) (a g) then (1 : ℝ) else 0) =
    ∏ g : P.SmallGroup,
      ∑ a : Fin M → P.Prime g.val, ∑ y : SmallLocalResidues P g,
        if smallLocalGood g y a then (1 : ℝ) else 0 := by
  classical
  let A : P.SmallGroup → Type := fun g => Fin M → P.Prime g.val
  let Y : P.SmallGroup → Type := fun g => SmallLocalResidues P g
  let e := piProductEquiv (G := P.SmallGroup) (A := Y) (B := A)
  let fPi : ((g : P.SmallGroup) → Y g) × ((g : P.SmallGroup) → A g) → ℝ :=
    fun z => if ∀ g : P.SmallGroup, smallLocalGood g (z.1 g) (z.2 g) then (1 : ℝ) else 0
  let f : P.SmallResidues → SmallLabels P M → ℝ := fun y a =>
    if ∀ g : P.SmallGroup, smallLocalGood g (y g) (a g) then (1 : ℝ) else 0
  have hpair :
      (∑ z : P.SmallResidues × SmallLabels P M, f z.1 z.2) =
        ∑ y : P.SmallResidues, ∑ a : SmallLabels P M, f y a :=
    Fintype.sum_prod_type' f
  calc
    _ = ∑ z : P.SmallResidues × SmallLabels P M, f z.1 z.2 := hpair.symm
    _ = ∑ z : (g : P.SmallGroup) → Y g × A g,
        if ∀ g : P.SmallGroup, smallLocalGood g (z g).1 (z g).2 then (1 : ℝ) else 0 := by
      exact Fintype.sum_equiv e fPi _ (by intro z; rfl)
    _ = ∑ z : (g : P.SmallGroup) → Y g × A g,
        ∏ g : P.SmallGroup,
          if smallLocalGood g (z g).1 (z g).2 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      exact prod_indicator_forall _
    _ = ∏ g : P.SmallGroup, ∑ z : Y g × A g,
        if smallLocalGood g z.1 z.2 then (1 : ℝ) else 0 := by
      exact sum_pi_prod (fun (g : P.SmallGroup) (z : Y g × A g) =>
        if smallLocalGood g z.1 z.2 then (1 : ℝ) else 0)
    _ = ∏ g : P.SmallGroup, ∑ a : Fin M → P.Prime g.val,
        ∑ y : SmallLocalResidues P g,
          if smallLocalGood g y a then (1 : ℝ) else 0 := by
      apply Finset.prod_congr rfl
      intro g _
      exact Fintype.sum_prod_type_right'
        (fun y : Y g => fun a : A g =>
          if smallLocalGood g y a then (1 : ℝ) else 0)


end Erdos821.S2Empty
