import Erdos821.P5.SparseRows
import Erdos821.P5.MellinVectors
import Erdos821.P5.IntervalMaxima
import Erdos821.P5.Tasks
import Erdos821.Classical.DerivativeTests

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- §4 sparse residual, reduced to the full-interval Gram kernel task.
All other steps, including the closed-interval suprema, are proved here. -/
theorem sparse_residual_of_gram (hg : SparseGramKernelTask) :
    ∃ K Y₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧
      ∀ (Y U A : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (E : Finset ℤ),
      Y₀ ≤ Y → Y ^ (0.6 : ℝ) ≤ U → U ≤ Y → 0 ≤ A →
      (∀ n ∈ s, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U) →
      sqNorm s c ≤ A / U → (E.card : ℝ) ≤ Y ^ (0.05 : ℝ) →
      (∀ j ∈ E, |(j : ℝ)| ≤ Y) →
      ∑ j ∈ E, ⨆ t : Set.Icc (j : ℝ) ((j : ℝ) + 1), ‖dp s c t‖ ^ 2 ≤
        K * A * Real.log (2 * Y) := by
  classical
  obtain ⟨K, hK, hkernel⟩ := hg Blueprint.DerivativeTests_proof
  refine ⟨20 * K, Real.exp 1 + 1, by positivity, by linarith [Real.exp_pos 1], ?_⟩
  intro Y U A s c E hY hU hUY _hA hs hcoeff hcard hE
  have hYbig : Real.exp 1 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    exact h.trans hYbig
  have hYpos : 0 < Y := by linarith
  have hU1 : 1 ≤ U := (Real.one_le_rpow hY1 (by norm_num : (0 : ℝ) ≤ 0.6)).trans hU
  have hUpos : 0 < U := by linarith
  let I := Finset.Icc ⌈U⌉₊ ⌊2 * U⌋₊
  have hSI : s ⊆ I := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (hs n hn).1, Nat.le_floor (hs n hn).2⟩
  obtain ⟨t, ht, hsup⟩ := dp_maximizing_samples s c E
  have hgram : ∀ z : ℝ, |z| ≤ 4 * Y →
      ‖dp I (fun _ => 1) z‖ ≤ K * (U / (1 + |z|) + Real.sqrt (4 * Y)) := by
    intro z hz
    exact hkernel (4 * Y) U z hU1 (by linarith) hz
  have hrows := sparse_gram_rows K Y U E t hK hYbig hU hcard hE (fun j _ => ht j) hgram
  let R := 20 * K * U * Real.log (2 * Y)
  have hlog : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hframe := gram_bessel_bound E (fun j => mellinVector I (t j))
    (dpVector I (extendCoefficients s c)) R hR (by
      intro j hj
      simp_rw [mellinVector_gram]
      exact hrows j hj)
  have hsample (j : ℤ) :
      ⟪mellinVector I (t j), dpVector I (extendCoefficients s c)⟫_ℂ = dp s c (t j) := by
    rw [mellinVector_sample, dp_extend s I c hSI]
  rw [hsup]
  calc
    _ = ∑ j ∈ E, ‖⟪mellinVector I (t j), dpVector I (extendCoefficients s c)⟫_ℂ‖ ^ 2 := by
      simp_rw [hsample]
    _ ≤ R * ‖dpVector I (extendCoefficients s c)‖ ^ 2 := hframe
    _ = R * sqNorm s c := by rw [dpVector_norm_sq, sqNorm_extend s I c hSI]
    _ ≤ R * (A / U) := mul_le_mul_of_nonneg_left hcoeff hR
    _ = (20 * K) * A * Real.log (2 * Y) := by
      dsimp [R]
      field_simp <;> ring

example (hg : SparseGramKernelTask) : Erdos821.Blueprint.Analytic.sparse_residual_statement :=
  sparse_residual_of_gram hg

end Erdos821.P5Core
