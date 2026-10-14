import Erdos821.S2Empty.SmallMassBound

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Empty

open Erdos821.Blueprint.Graph

theorem eta_unit_bounds (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    0 ≤ eta F n i ∧ eta F n i ≤ 1 := by
  have hs : Real.sqrt F.q ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · simpa using F.q_lt.le
  have hv0 : 0 ≤ visitQ F.q n i := by
    unfold visitQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact le_of_lt F.q_pos
  have hv1 : visitQ F.q n i ≤ 1 := by
    unfold visitQ
    split_ifs
    · exact hs
    · exact le_of_lt F.q_lt
  unfold eta
  constructor <;> linarith

theorem baseline_prime_floor_of_admissible (F : FixedData) (P : PrimeGroups) (x : ℝ)
    (hP : P.Admissible F x) :
    ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
      1 - ((N x : ℝ) + 1) / Real.exp ((L x) ^ F.c) ≤
        baselinePrime F (N x) p.val := by
  intro g p
  let epsilon : ℝ := ((N x : ℝ) + 1) / Real.exp ((L x) ^ F.c)
  have hsum_nonneg : 0 ≤ ∑ i : Fin (N x + 1), eta F (N x) i := by
    apply Finset.sum_nonneg
    intro i _
    exact (eta_unit_bounds F (N x) i).1
  have hsum_le : ∑ i : Fin (N x + 1), eta F (N x) i ≤ (N x : ℝ) + 1 := by
    calc
      _ ≤ ∑ i : Fin (N x + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact (eta_unit_bounds F (N x) i).2
      _ = (N x : ℝ) + 1 := by simp
  have hpInfo : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) ∧
      (p.val : ℝ) ≤ Real.exp ((L x) ^ F.d) := by
    simpa [g.property] using hP.2.2.2.2.2 g.val p.val p.property
  have hpPos : 0 < (p.val : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hpInfo.1
  have hinv : (p.val : ℝ)⁻¹ ≤ (Real.exp ((L x) ^ F.c))⁻¹ :=
    (inv_le_inv₀ hpPos (Real.exp_pos _)).mpr hpInfo.1
  have hmass :
      (p.val : ℝ)⁻¹ * ∑ i : Fin (N x + 1), eta F (N x) i ≤ epsilon := by
    calc
      _ ≤ (Real.exp ((L x) ^ F.c))⁻¹ *
          ∑ i : Fin (N x + 1), eta F (N x) i :=
        mul_le_mul_of_nonneg_right hinv hsum_nonneg
      _ ≤ (Real.exp ((L x) ^ F.c))⁻¹ * ((N x : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = epsilon := by
        dsimp [epsilon]
        ring
  unfold baselinePrime
  dsimp [epsilon] at hmass ⊢
  linarith


end Erdos821.S2Empty
