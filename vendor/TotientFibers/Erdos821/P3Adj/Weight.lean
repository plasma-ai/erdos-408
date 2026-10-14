import Erdos821.P3Adj.Factor
import Erdos821.P3Adj.Basic
import Erdos821.Blueprint.Graph

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Adj

open Erdos821.Blueprint.Graph hiding GhostChoice absoluteMemoryGhostKernel absoluteScaledMemoryGhostKernel deleteMemoryIndices ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEntry memoryGhostKernel zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core

variable {P : PrimeGroups} {F : FixedData} {n : ℕ} {rho : ℝ} {i : Fin (n + 1)}
  {g : P.BigGroup} {s0 t0 : P.Memory g.val}
  {A : Finset (Fin s0.card)} {b : Fin (t0.card + 1)}
  {p : Fin b.val → P.Prime g.val}

/-- eta is positive since visitQ < 1. -/
lemma eta_pos (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : 0 < eta F n i := by
  unfold eta
  have hq : visitQ F.q n i < 1 := by
    unfold visitQ
    by_cases h : i.val = 0 ∨ i.val = n
    · rw [if_pos h]
      have hq0 : 0 < F.q := F.q_pos
      have hq1 : F.q < 1 := F.q_lt
      have hsqrt : Real.sqrt F.q < 1 := by
        have h := Real.sqrt_lt_sqrt hq0.le hq1
        simpa only [Real.sqrt_one] using h
      exact hsqrt
    · rw [if_neg h]
      exact F.q_lt
  linarith

/-- visitQ is positive since q > 0. -/
lemma visitQ_pos (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : 0 < visitQ F.q n i := by
  unfold visitQ
  by_cases h : i.val = 0 ∨ i.val = n
  · rw [if_pos h]
    exact Real.sqrt_pos.mpr F.q_pos
  · rw [if_neg h]
    exact F.q_pos

/-- tiltedMu is positive from V>0 and baseline>0. -/
lemma tiltedMu_pos {P : PrimeGroups} {F : FixedData} {n : ℕ} {g : P.Group}
    {q : P.Prime g} (hV : 0 < P.V g)
    (hbase : 0 < baselinePrime F n q.val) :
    0 < tiltedMu F P n g q := by
  unfold tiltedMu
  apply inv_pos.mpr
  apply mul_pos
  apply mul_pos
  · exact hV
  · exact Nat.cast_pos.mpr (P.prime g q.val q.property).pos
  · exact hbase

/-- Absolute single weight in positive form. -/
lemma abs_singleWeight_eq {P : PrimeGroups} (F : FixedData) (n : ℕ) (rho : ℝ)
    (hrho : 0 < rho) (i : Fin (n + 1)) (g : P.BigGroup)
    (s0 t0 : P.Memory g.val) (A : Finset (Fin s0.card)) (b : Fin (t0.card + 1))
    (p : Fin b.val → P.Prime g.val)
    (hV : 0 < P.V g.val)
    (hbase : ∀ q : P.Prime g.val, 0 < baselinePrime F n q.val) :
    |singleWeight F n rho i g s0 t0 A b p| =
    (eta F n i / rho) ^ A.card *
    (visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices s0).card - A.card) *
    ((b.val.factorial : ℝ)⁻¹) *
    (eta F n i * P.V g.val / rho) ^ b.val *
    ∏ h : Fin b.val, tiltedMu F P n g.val (p h) := by
  unfold singleWeight
  have heta : 0 < eta F n i := eta_pos F n i
  have hQ : 0 < visitQ F.q n i := visitQ_pos F n i
  have hrho2 : 0 < rho ^ (2 : ℕ) := pow_pos hrho 2
  have hQr : 0 < visitQ F.q n i / rho ^ (2 : ℕ) := div_pos hQ hrho2
  have hfact : 0 < ((b.val.factorial : ℝ)⁻¹) := by
    apply inv_pos.mpr
    exact Nat.cast_pos.mpr (Nat.factorial_pos b.val)
  have hmu : 0 < ∏ h : Fin b.val, tiltedMu F P n g.val (p h) := by
    apply Finset.prod_pos
    intro h _
    exact tiltedMu_pos hV (hbase _)
  have her : 0 < eta F n i / rho := div_pos heta hrho
  have heVr : 0 < eta F n i * P.V g.val / rho :=
    div_pos (mul_pos heta hV) hrho
  -- Rewrite negatives as negations
  have hneg1 : (-eta F n i / rho) = -(eta F n i / rho) := by ring
  have hneg2 : (-eta F n i * P.V g.val / rho) = -(eta F n i * P.V g.val / rho) := by ring
  rw [hneg1, hneg2]
  simp only [abs_mul, abs_pow, abs_neg, abs_of_pos her, abs_of_pos heVr,
    abs_of_pos hQr, abs_of_pos hfact, abs_of_pos hmu]


end Erdos821.P3Adj
