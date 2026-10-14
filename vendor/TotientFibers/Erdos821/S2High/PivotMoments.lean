import Erdos821.S2High.TiltedMass

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

theorem tiltedMu_power_sum_bound (F : FixedData) (P : PrimeGroups) (x : ℝ)
    (n : ℕ) (hP : P.Admissible F x)
    (hcut : (n + 1 : ℝ) ≤ Real.exp ((L x) ^ F.c) / 2)
    (g : P.BigGroup) (k : ℕ) (hk : 1 ≤ k) :
    (∑ p : P.Prime g.val, (tiltedMu F P n g.val p) ^ k) ≤
      2 * (2 / (F.vMin * Real.exp ((L x) ^ F.c))) ^ (k - 1) := by
  have hm := tiltedMu_group_mass_bounds F P x n hP hcut g
  let a : ℝ := 2 / (F.vMin * Real.exp ((L x) ^ F.c))
  have hden : 0 < F.vMin * Real.exp ((L x) ^ F.c) :=
    mul_pos F.vMin_pos (Real.exp_pos _)
  have haPos : 0 < a := by dsimp [a]; exact div_pos two_pos hden
  have ha : 0 ≤ a := haPos.le
  have hsum : (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2 := hm.2.2
  calc
    (∑ p : P.Prime g.val, (tiltedMu F P n g.val p) ^ k) ≤
        ∑ p : P.Prime g.val, a ^ (k - 1) * tiltedMu F P n g.val p := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : 0 ≤ tiltedMu F P n g.val p := (hm.1 p).1.le
      have hpA : tiltedMu F P n g.val p ≤ a := by
        simpa [a] using (hm.1 p).2
      have hpow : (tiltedMu F P n g.val p) ^ (k - 1) ≤ a ^ (k - 1) :=
        pow_le_pow_left₀ hp0 hpA _
      calc
        (tiltedMu F P n g.val p) ^ k =
            (tiltedMu F P n g.val p) ^ (k - 1) * tiltedMu F P n g.val p := by
          calc
            _ = (tiltedMu F P n g.val p) ^ ((k - 1) + 1) :=
              (congrArg (fun j : ℕ => (tiltedMu F P n g.val p) ^ j)
                (Nat.sub_add_cancel hk)).symm
            _ = _ := by rw [pow_succ]
        _ ≤ a ^ (k - 1) * tiltedMu F P n g.val p :=
          mul_le_mul_of_nonneg_right hpow hp0
    _ = a ^ (k - 1) * ∑ p : P.Prime g.val, tiltedMu F P n g.val p := by
      rw [← Finset.mul_sum]
    _ ≤ a ^ (k - 1) * 2 :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg ha _)
    _ = 2 * (2 / (F.vMin * Real.exp ((L x) ^ F.c))) ^ (k - 1) := by
      simp [a, mul_comm]

theorem birthCollection_card_le_rank {a : ℕ}
    (pi : Finset (Finset (Fin a))) (hpi : BirthCollection pi) :
    pi.card ≤ birthRank pi := by
  unfold birthRank
  calc
    pi.card = ∑ B ∈ pi, (1 : ℕ) := by simp
    _ ≤ ∑ B ∈ pi, (B.card - 1) := by
      apply Finset.sum_le_sum
      intro B hB
      have hcard := hpi.1 B hB
      omega


end Erdos821.S2High
