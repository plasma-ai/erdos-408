import Erdos821.S2.MemoryEdge
import Mathlib

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

lemma visitQ_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) (i : Fin (n + 1)) :
    0 < visitQ q n i := by
  unfold visitQ
  split
  · exact Real.sqrt_pos.mpr hq0
  · exact hq0

lemma visitQ_lt_one (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) (i : Fin (n + 1)) :
    visitQ q n i < 1 := by
  unfold visitQ
  split
  · have h := Real.sqrt_lt_sqrt hq0.le hq1
    simpa using h
  · exact hq1

lemma eta_pos (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : 0 < eta F n i := by
  unfold eta
  have h := visitQ_lt_one F.q F.q_pos F.q_lt n i
  linarith

lemma eta_lt_one (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : eta F n i < 1 := by
  unfold eta
  have h := visitQ_pos F.q F.q_pos F.q_lt n i
  linarith

lemma L_pos_of_large (x : ℝ) (hx : 3 < x) : 0 < L x := by
  unfold L
  have h : Real.log 3 < Real.log x := Real.log_lt_log (by norm_num) hx
  have h3 : (0 : ℝ) < Real.log 3 := by
    have h1 : Real.log 1 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    simp at h1
    linarith
  linarith

lemma L_gt_one_of_large (x : ℝ) (hx : Real.exp 1 < x) : 1 < L x := by
  unfold L
  have h : Real.log (Real.exp 1) < Real.log x := Real.log_lt_log (Real.exp_pos _) hx
  simp at h
  linarith

end Erdos821.P3Edge
