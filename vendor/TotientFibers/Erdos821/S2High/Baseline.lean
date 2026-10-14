import Erdos821.S2High.LocalEstimates

noncomputable section
open scoped BigOperators

namespace Erdos821.S2High

open Erdos821.Blueprint.Graph

theorem baselinePrime_eq_sum_div (F : FixedData) (n p : ℕ) :
    baselinePrime F n p = 1 - (∑ i : Fin (n + 1), eta F n i) / (p : ℝ) := by
  unfold baselinePrime
  congr 1
  ring

theorem baselinePrime_bounds_of_cutoff (F : FixedData) (P : PrimeGroups) (x : ℝ)
    (n : ℕ) (hP : P.Admissible F x)
    (hcut : (n + 1 : ℝ) ≤ Real.exp ((L x) ^ F.c) / 2)
    (g : P.BigGroup) (p : P.Prime g.val) :
    1 / 2 ≤ baselinePrime F n p.val ∧ baselinePrime F n p.val ≤ 1 := by
  rcases hP with ⟨_, _, _, _, hV, hPrime⟩
  have hpRange := hPrime g.val p.val p.property
  simp only [g.property, ite_true] at hpRange
  have hpstar : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) := hpRange.1
  have hpPos : 0 < (p.val : ℝ) := by
    exact_mod_cast (P.prime g.val p.val p.property).pos
  let e : ℝ := ∑ i : Fin (n + 1), eta F n i
  have he : 0 ≤ e := by
    dsimp [e]
    exact Finset.sum_nonneg (fun i _ => (eta_bounds F n i).1)
  have heLe : e ≤ (n + 1 : ℝ) := by
    dsimp [e]
    calc
      (∑ i : Fin (n + 1), eta F n i) ≤ ∑ i : Fin (n + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (eta_bounds F n i).2)
      _ = (n + 1 : ℝ) := by simp
  have hTwoE : 2 * e ≤ (p.val : ℝ) := by
    calc
      2 * e ≤ 2 * ((n + 1 : ℝ)) := by nlinarith
      _ ≤ Real.exp ((L x) ^ F.c) := by nlinarith
      _ ≤ (p.val : ℝ) := hpstar
  have hbaseEq : baselinePrime F n p.val = 1 - e / (p.val : ℝ) := by
    dsimp [e]
    rw [baselinePrime_eq_sum_div]
  have hdivNonneg : 0 ≤ e / (p.val : ℝ) := div_nonneg he hpPos.le
  have hdivLe : e / (p.val : ℝ) ≤ 1 / 2 :=
    (div_le_iff₀ hpPos).2 (by nlinarith)
  rw [hbaseEq]
  constructor <;> linarith


end Erdos821.S2High
