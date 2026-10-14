import Erdos821.S34.ProbabilityDyads
import Erdos821.S34.BilinearDecayArithmetic

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def tuplePhase (G : PrimeGroups) (a b : Fin G.size → ℕ) (θ ζ : ℝ)
    (X : Tuple G a) (Y : Tuple G b) : ℂ :=
  mellin (product G a X * product G b Y) ζ * e (θ * product G a X * product G b Y)

theorem tuple_norm_nonneg (G : PrimeGroups) (k : Fin G.size → ℕ) (f : Tuple G k → ℂ) :
    0 ≤ tupleNorm G k f := Real.sqrt_nonneg _

theorem supported_tuple_bilinear (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (f : Tuple G a → ℂ) (g : Tuple G b → ℂ) (U V H θ η ζ : ℝ) (u : ℤ) (r : ℕ)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hH : 0 ≤ H) (hr : 1 ≤ r)
    (hu : Nat.Coprime u.natAbs r) (hθ : θ = (u : ℝ) / r + η)
    (hη : |η| ≤ (r : ℝ) ^ (-2 : ℤ))
    (hf : ∀ X, f X ≠ 0 → U / 2 ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 4 * U)
    (hg : ∀ Y, g Y ≠ 0 → V / 2 ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 4 * V)
    (hρa : ∀ n : ℕ, 0 < n → rho G a n ≤ H / n)
    (hρb : ∀ n : ℕ, 0 < n → rho G b n ≤ H / n) :
    ‖expect G a (fun X => expect G b (fun Y => f X * g Y * tuplePhase G a b θ ζ X Y))‖ ≤
      4 * integerBilinearConstant * H * Real.sqrt (bilinearDecay U V r) *
        tupleNorm G a f * tupleNorm G b g := by
  let s := Finset.univ.filter (fun X => f X ≠ 0)
  let t := Finset.univ.filter (fun Y => g Y ≠ 0)
  have hs (X : Tuple G a) (hX : X ∈ s) := hf X (Finset.mem_filter.mp hX).2
  have ht (Y : Tuple G b) (hY : Y ∈ t) := hg Y (Finset.mem_filter.mp hY).2
  have hb := probability_bilinear_dyads G a b s t f g U V H θ η ζ u r
    hU hV hH hr hu hθ hη hs ht hρa hρb
  have heq : expect G a (fun X => expect G b (fun Y => f X * g Y * tuplePhase G a b θ ζ X Y)) =
      ∑ X ∈ s, ∑ Y ∈ t, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) *
        f X * g Y * mellin (product G a X * product G b Y) ζ * e (θ * product G a X * product G b Y) := by
    unfold expect tuplePhase
    simp only [Finset.mul_sum]
    symm
    calc
      _ = ∑ X ∈ s, ∑ Y, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) *
          f X * g Y * mellin (product G a X * product G b Y) ζ * e (θ * product G a X * product G b Y) := by
        apply Finset.sum_congr rfl
        intro X _
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro Y _ hn
        have hy : g Y = 0 := by simpa [t] using hn
        simp [hy]
      _ = ∑ X, ∑ Y, (tupleWeight G a X : ℂ) * (tupleWeight G b Y : ℂ) *
          f X * g Y * mellin (product G a X * product G b Y) ζ * e (θ * product G a X * product G b Y) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro X _ hn
        have hx : f X = 0 := by simpa [s] using hn
        simp [hx]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro X _
        apply Finset.sum_congr rfl
        intro Y _
        ring
  rw [heq]
  apply hb.trans
  have hdec := bilinear_scale_sqrt_bound U V r H (by linarith) (by linarith)
    (by exact_mod_cast hr) hH
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdec integerBilinearConstant_pos.le) (tuple_norm_nonneg G a f))
        (tuple_norm_nonneg G b g)
  convert hm using 1 <;> ring

end
end Erdos821.S34Core
