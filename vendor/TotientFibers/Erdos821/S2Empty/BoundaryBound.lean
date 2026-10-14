import Erdos821.S2Empty.SmallMassBound
import Erdos821.S2Empty.BigMass

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

theorem big_boundary_factor_le_two (F : FixedData) (P : PrimeGroups) (n M : ℕ)
    (e : ℝ) (he0 : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hbudget : (M : ℝ) * (Fintype.card P.BigGroup : ℝ) * e ≤ 1 / 2)
    (hV : ∀ g, 0 < P.V g)
    (hfloor : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      1 - e ≤ baselinePrime F n p.val) :
    (∑ b : BigLabels P M, bigLabelWeight F P n M b) ≤ 2 := by
  classical
  let S : P.BigGroup → ℝ := fun g => ∑ p : P.Prime g.val, tiltedMu F P n g.val p
  have htermPos (g : P.BigGroup) (p : P.Prime g.val) :
      0 < tiltedMu F P n g.val p := by
    have hp : 0 < (p.val : ℝ) := by
      exact_mod_cast (P.prime g.val p.val p.property).pos
    have hbase : 0 < baselinePrime F n p.val :=
      lt_of_lt_of_le (by linarith [hehalf]) (hfloor g p)
    unfold tiltedMu
    exact inv_pos.mpr (mul_pos (mul_pos (hV g.val) hp) hbase)
  have hS (g : P.BigGroup) : 0 ≤ S g ∧ S g ≤ (1 - e)⁻¹ := by
    constructor
    · dsimp [S]
      apply Finset.sum_nonneg
      intro p hp
      exact (htermPos g p).le
    · exact big_tilted_sum_le_inv F P n g e (hV g.val)
        (by linarith [hehalf]) (hfloor g)
  change (∑ b : BigLabels P M,
    ∏ g : P.BigGroup, ∏ j : Fin M, tiltedMu F P n g.val (b g j)) ≤ 2
  rw [big_label_sum_eq_prod F P n M]
  exact big_label_product_le_two P M e he0 hehalf hbudget S hS

theorem initial_boundary_mass_le_two_of_budget
    (F : FixedData) (P : PrimeGroups) (J m n : ℕ) (A : Model F P J m)
    (e : ℝ) (he0 : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hbudget : (J + F.ell : ℝ) * (Fintype.card P.BigGroup : ℝ) * e ≤ 1 / 2)
    (hV : ∀ g, 0 < P.V g)
    (hfloor : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      1 - e ≤ baselinePrime F n p.val) :
    Erdos821.S2Core.initialMemoryBoundaryMass A n ≤ 2 := by
  classical
  let M : ℕ := J + F.ell
  let smallTerm : ℝ :=
    (Fintype.card P.SmallResidues : ℝ)⁻¹ *
      (∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℤ))) *
      (∑ y : P.SmallResidues, ∑ s : SmallLabels P M,
        if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0)
  let bigTerm : ℝ := ∑ b : BigLabels P M, bigLabelWeight F P n M b
  have hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      0 < baselinePrime F n p.val := by
    intro g p
    exact lt_of_lt_of_le (by linarith [hehalf]) (hfloor g p)
  have hfactor : Erdos821.S2Core.initialMemoryBoundaryMass A n = smallTerm * bigTerm := by
    rw [initial_boundary_mass_factorization F P J m n A hV hbase]
    dsimp [smallTerm, bigTerm, M]
    ring
  have hsmall_le : smallTerm ≤ 1 := by
    simpa [smallTerm, M] using small_boundary_factor_le_one P (J + F.ell) hV
  have hbudget' : (J + F.ell : ℕ) * (Fintype.card P.BigGroup : ℝ) * e ≤ 1 / 2 := by
    simpa [Nat.cast_add] using hbudget
  have hbig_le : bigTerm ≤ 2 := by
    simpa [bigTerm, M] using big_boundary_factor_le_two F P n (J + F.ell)
      e he0 hehalf hbudget' hV hfloor
  have htermPos (g : P.BigGroup) (p : P.Prime g.val) :
      0 < tiltedMu F P n g.val p := by
    have hp : 0 < (p.val : ℝ) := by
      exact_mod_cast (P.prime g.val p.val p.property).pos
    have hbaseP : 0 < baselinePrime F n p.val :=
      lt_of_lt_of_le (by linarith [hehalf]) (hfloor g p)
    unfold tiltedMu
    exact inv_pos.mpr (mul_pos (mul_pos (hV g.val) hp) hbaseP)
  have hcardSmall : 0 < (Fintype.card P.SmallResidues : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ _ => 0⟩)
  have hsmallProduct :
      0 ≤ ∏ g : P.SmallGroup, (P.V g.val) ^ (-(M : ℤ)) := by
    apply Finset.prod_nonneg
    intro g hg
    exact zpow_nonneg (hV g.val).le _
  have hsmallSum :
      0 ≤ ∑ y : P.SmallResidues, ∑ s : SmallLabels P M,
        if ∀ g : P.SmallGroup, smallLocalGood g (y g) (s g) then (1 : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro y hy
    apply Finset.sum_nonneg
    intro s hs
    split_ifs <;> positivity
  have hsmall0 : 0 ≤ smallTerm := by
    dsimp [smallTerm]
    exact mul_nonneg (mul_nonneg (by positivity) hsmallProduct) hsmallSum
  have hweight0 (b : BigLabels P M) : 0 ≤ bigLabelWeight F P n M b := by
    unfold bigLabelWeight
    apply Finset.prod_nonneg
    intro g hg
    apply Finset.prod_nonneg
    intro j hj
    exact (htermPos g (b g j)).le
  have hbig0 : 0 ≤ bigTerm := by
    dsimp [bigTerm]
    apply Finset.sum_nonneg
    intro b hb
    exact hweight0 b
  calc
    Erdos821.S2Core.initialMemoryBoundaryMass A n = smallTerm * bigTerm := hfactor
    _ ≤ 1 * bigTerm := mul_le_mul_of_nonneg_right hsmall_le hbig0
    _ ≤ 1 * 2 := mul_le_mul_of_nonneg_left hbig_le (by norm_num)
    _ = 2 := by norm_num


end Erdos821.S2Empty
