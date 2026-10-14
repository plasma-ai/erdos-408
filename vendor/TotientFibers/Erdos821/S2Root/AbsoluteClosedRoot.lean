import Erdos821.S2.AbsoluteRootTask
import Erdos821.P3Tail.MemoryTail

/-! Absolute bounds for the closed residue paths. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Root

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

theorem visitQ_nonneg (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ visitQ F.q n i := by
  unfold visitQ
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact F.q_pos.le

theorem residueExpectation_visitQ_nonneg {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} {A : Model F P J m} (Q : ResiduePath A n) :
    0 ≤ P.residueExpectation n (visitQ F.q n) Q.offset Q.active := by
  have hpath (y : P.Residues) :
      0 ≤ P.residuePathFactor n (visitQ F.q n) Q.offset Q.active y := by
    unfold PrimeGroups.residuePathFactor
    apply Finset.prod_nonneg
    intro p hp
    apply Finset.prod_nonneg
    intro i hi
    by_cases ha : p.val ∈ Q.active i
    · by_cases hd : (p.val : ℤ) ∣ (y p).val + Q.offset i
      · simp only [if_pos ha, if_pos hd]
        norm_num
      · simp only [if_pos ha, if_neg hd]
        norm_num
    · simp only [if_neg ha]
      by_cases hd : (p.val : ℤ) ∣ (y p).val + Q.offset i
      · simp only [if_pos hd]
        exact visitQ_nonneg F n i
      · simp only [if_neg hd]
        norm_num
  unfold PrimeGroups.residueExpectation
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact Finset.sum_nonneg fun y _ => hpath y


end Erdos821.S2Root
