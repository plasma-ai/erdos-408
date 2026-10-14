import Erdos821.S34.KernelDyadicSupport
import Erdos821.S34.LogMultiplier
import Erdos821.S34.MajorPointwise
import Erdos821.S34.RationalPhase

set_option autoImplicit false
open scoped BigOperators Classical

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

theorem dyadic_log_multiplier_error (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q : ℕ) (h ξ U V S β ζ : ℝ) (hh : 0 < h) (hh2 : h ≤ Real.log 2)
    (hU : 0 < U) (hV : 0 < V) (hS : 0 ≤ S) (hβ : |β| * (U * V) ≤ 2 * S)
    (X D : Tuple G a) (Y E : Tuple G b)
    (hX : U ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 2 * U)
    (hY : V ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 2 * V)
    (hK : cellKernel G a Q h ξ (product G a D) (product G a X) ≠ 0)
    (hH : cellKernel G b Q h ξ (product G b E) (product G b Y) ≠ 0) :
    ‖logMultiplier ζ β (Real.log (product G a D * product G b E)) -
        logMultiplier ζ β (Real.log (product G a X * product G b Y))‖ ≤
      2 * h * (|ζ| + 64 * Real.pi * S) := by
  have hD := kernel_dyadic_localization G a Q h ξ U hh hh2 _ _
    (tuple_product_pos G a D) (tuple_product_pos G a X) hX.1 hX.2 hK
  have hE := kernel_dyadic_localization G b Q h ξ V hh hh2 _ _
    (tuple_product_pos G b E) (tuple_product_pos G b Y) hY.1 hY.2 hH
  have ppos (k : Fin G.size → ℕ) (z : Tuple G k) : (0 : ℝ) < product G k z := by
    exact_mod_cast tuple_product_pos G k z
  have hprodD : (product G a D : ℝ) * product G b E ≤ 16 * (U * V) := by
    have ht := mul_le_mul hD.2 hE.2 (ppos b E).le (by positivity : 0 ≤ 4 * U)
    nlinarith
  have hprodX : (product G a X : ℝ) * product G b Y ≤ 16 * (U * V) := by
    have ht := mul_le_mul hX.2 hY.2 (ppos b Y).le (by positivity : 0 ≤ 2 * U)
    nlinarith
  have htop : 0 < 16 * (U * V) := by positivity
  have hlogD : Real.log (product G a D * product G b E) ≤ Real.log (16 * (U * V)) :=
    Real.log_le_log (mul_pos (ppos a D) (ppos b E)) hprodD
  have hlogX : Real.log (product G a X * product G b Y) ≤ Real.log (16 * (U * V)) :=
    Real.log_le_log (mul_pos (ppos a X) (ppos b Y)) hprodX
  have hlogdist : |Real.log (product G a D * product G b E) -
      Real.log (product G a X * product G b Y)| ≤ 2 * h := by
    rw [Real.log_mul (ppos a D).ne' (ppos b E).ne', Real.log_mul (ppos a X).ne' (ppos b Y).ne']
    have hlA := (kernel_log_localization G a Q h ξ hh _ _ hK).le
    have hlB := (kernel_log_localization G b Q h ξ hh _ _ hH).le
    calc
      _ = |(Real.log (product G a D) - Real.log (product G a X)) +
        (Real.log (product G b E) - Real.log (product G b Y))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 2 * h := by linarith
  have hcoeff : |ζ| + 2 * Real.pi * |β| * Real.exp (Real.log (16 * (U * V))) ≤
      |ζ| + 64 * Real.pi * S := by
    rw [Real.exp_log htop]
    have ht := mul_le_mul_of_nonneg_left hβ (by positivity : 0 ≤ 32 * Real.pi)
    nlinarith
  have ht := logMultiplier_difference ζ β _ _ (Real.log (16 * (U * V))) hlogX hlogD
  have he := mul_le_mul hcoeff hlogdist (abs_nonneg _) (by positivity : 0 ≤ |ζ| + 64 * Real.pi * S)
  exact ht.trans (by convert he using 1 <;> ring)

theorem dyadic_multiplier_freeze (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q : ℕ) (h ξ U V S β ζ : ℝ) (u : ℤ) (r : ℕ)
    (hh : 0 < h) (hh2 : h ≤ Real.log 2) (hξ : 0 < ξ)
    (hU : 0 < U) (hV : 0 < V) (hS : 0 ≤ S) (hβ : |β| * (U * V) ≤ 2 * S)
    (X : Tuple G a) (Y : Tuple G b)
    (hX : U ≤ (product G a X : ℝ) ∧ (product G a X : ℝ) ≤ 2 * U)
    (hY : V ≤ (product G b Y : ℝ) ∧ (product G b Y : ℝ) ≤ 2 * V) :
    ‖expect G a (fun D => expect G b (fun E =>
      cellKernel G a Q h ξ (product G a D) (product G a X) *
      cellKernel G b Q h ξ (product G b E) (product G b Y) *
      (logMultiplier ζ β (Real.log (product G a D * product G b E)) -
        logMultiplier ζ β (Real.log (product G a X * product G b Y))) *
      e ((u : ℝ) * (product G a D * product G b E) / r)))‖ ≤
      (Q : ℝ) ^ 4 * (2 * h * (|ζ| + 64 * Real.pi * S)) := by
  have hwa := Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) a
  have hwb := Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) b
  have ht := kernel_multiplier_freeze (tupleWeight G a) (tupleWeight G b) hwa hwb
    (fun D => cellKernel G a Q h ξ (product G a D) (product G a X))
    (fun E => cellKernel G b Q h ξ (product G b E) (product G b Y))
    (fun D E => logMultiplier ζ β (Real.log (product G a D * product G b E)))
    (fun D E => e ((u : ℝ) * (product G a D * product G b E) / r))
    (logMultiplier ζ β (Real.log (product G a X * product G b Y)))
    (2 * h * (|ζ| + 64 * Real.pi * S)) ((Q : ℝ) ^ 2) ((Q : ℝ) ^ 2)
    (by positivity) (sq_nonneg _) (sq_nonneg _)
    (kernel_l1_bound G a Q h ξ hξ _) (kernel_l1_bound G b Q h ξ hξ _)
    (fun D E => (norm_e _).le)
    (fun D E hK hH => dyadic_log_multiplier_error G a b Q h ξ U V S β ζ hh hh2 hU hV hS hβ X D Y E hX hY hK hH)
  convert ht using 1
  · simp only [expect, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro E _
    ring
  · ring

end
end Erdos821.S34Core
