import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic

/-!
# Collision probabilities of independent draws

Independent draws `z_e ∈ S_e` with laws `w_e` (nonnegative, of total mass one), so that a
tuple `z` has probability `∏_e w_e(z_e)`. If every atom has mass at most `ε`, then a
prescribed value at one coordinate, and a coincidence of two coordinates, each have
probability at most `ε`. These bound the shared labels and the pad collisions of PD §4.9.
-/

namespace Erdos408.OneSided

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A product of factors in `[0, 1]` is at most any one of them. -/
theorem prod_le_of_mem_of_le_one {f : ι → ℝ} (h0 : ∀ e, 0 ≤ f e) (h1 : ∀ e, f e ≤ 1) (c : ι) :
    ∏ e, f e ≤ f c := by
  rw [← mul_prod_erase univ f (mem_univ c)]
  exact mul_le_of_le_one_right (h0 c) (prod_le_one₀ (fun e _ => h0 e) fun e _ => h1 e)

/-- A product of factors in `[0, 1]` is at most the product of any two of them. -/
theorem prod_le_mul_of_le_one {f : ι → ℝ} (h0 : ∀ e, 0 ≤ f e) (h1 : ∀ e, f e ≤ 1) {c c' : ι}
    (hcc : c ≠ c') : ∏ e, f e ≤ f c * f c' := by
  rw [← mul_prod_erase univ f (mem_univ c),
    ← mul_prod_erase _ f (mem_erase.2 ⟨hcc.symm, mem_univ c'⟩), ← mul_assoc]
  exact mul_le_of_le_one_right (mul_nonneg (h0 c) (h0 c'))
    (prod_le_one₀ (fun e _ => h0 e) fun e _ => h1 e)

variable {S : ι → Finset ℕ} {w : ι → ℕ → ℝ}

/-- The draws have total mass one. -/
theorem sum_piFinset_prod_eq_one (hw : ∀ e, ∑ y ∈ S e, w e y = 1) :
    ∑ z ∈ Fintype.piFinset S, ∏ e, w e (z e) = 1 := by
  rw [← prod_univ_sum, prod_eq_one fun e _ => hw e]

/-- The law of the draws restricted coordinatewise: the factor at `e` is the mass of the
values satisfying `T e`. -/
theorem sum_piFinset_prod_ite (T : ι → ℕ → Prop) [∀ e, DecidablePred (T e)] :
    ∑ z ∈ Fintype.piFinset S, ∏ e, (if T e (z e) then w e (z e) else 0) =
      ∏ e, ∑ y ∈ S e, if T e y then w e y else 0 :=
  (prod_univ_sum S fun e y => if T e y then w e y else 0).symm

omit [Fintype ι] [DecidableEq ι] in
/-- A coordinatewise restricted mass lies in `[0, 1]`. -/
theorem sum_ite_mem_Icc (hw0 : ∀ e, ∀ y ∈ S e, 0 ≤ w e y) (hw : ∀ e, ∑ y ∈ S e, w e y = 1)
    (T : ι → ℕ → Prop) [∀ e, DecidablePred (T e)] (e : ι) :
    0 ≤ ∑ y ∈ S e, (if T e y then w e y else 0) ∧
      ∑ y ∈ S e, (if T e y then w e y else 0) ≤ 1 := by
  refine ⟨sum_nonneg fun y hy => ?_, (hw e).symm ▸ sum_le_sum fun y hy => ?_⟩
  · split_ifs
    · exact hw0 e y hy
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact hw0 e y hy

/-- A prescribed value at one coordinate has probability at most `ε`. -/
theorem sum_piFinset_ite_eq_le (hw0 : ∀ e, ∀ y ∈ S e, 0 ≤ w e y)
    (hw : ∀ e, ∑ y ∈ S e, w e y = 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ e, ∀ y ∈ S e, w e y ≤ ε)
    (c : ι) (v : ℕ) :
    ∑ z ∈ Fintype.piFinset S, (if z c = v then ∏ e, w e (z e) else 0) ≤ ε := by
  -- the indicator is the product of the coordinatewise indicators
  have hterm : ∀ z : ι → ℕ, (if z c = v then ∏ e, w e (z e) else 0) =
      ∏ e, (if (e = c → z e = v) then w e (z e) else 0) := by
    intro z
    by_cases hz : z c = v
    · rw [ite_eq_left hz]
      refine prod_congr rfl fun e _ => (ite_eq_left ?_).symm
      rintro rfl
      exact hz
    · rw [ite_eq_right hz]
      exact (prod_eq_zero (mem_univ c) (ite_eq_right fun h => hz (h rfl))).symm
  simp_rw [hterm]
  refine (sum_piFinset_prod_ite (S := S) (w := w) (fun e y => e = c → y = v)).trans_le ?_
  have hI := sum_ite_mem_Icc hw0 hw (fun e y => e = c → y = v)
  refine (prod_le_of_mem_of_le_one (fun e => (hI e).1) (fun e => (hI e).2) c).trans ?_
  simp only [forall_const]
  rw [sum_ite_eq']
  split_ifs with hv
  · exact hε c v hv
  · exact hε0

/-- A coincidence of two coordinates has probability at most `ε`. -/
theorem sum_piFinset_ite_eq_eq_le (hw0 : ∀ e, ∀ y ∈ S e, 0 ≤ w e y)
    (hw : ∀ e, ∑ y ∈ S e, w e y = 1) {ε : ℝ} (hε : ∀ e, ∀ y ∈ S e, w e y ≤ ε)
    {c c' : ι} (hcc : c ≠ c') :
    ∑ z ∈ Fintype.piFinset S, (if z c = z c' then ∏ e, w e (z e) else 0) ≤ ε := by
  -- split by the common value `v`
  have hsplit : ∀ z ∈ Fintype.piFinset S, (if z c = z c' then ∏ e, w e (z e) else 0) =
      ∑ v ∈ S c, ∏ e, (if ((e = c ∨ e = c') → z e = v) then w e (z e) else 0) := by
    intro z hz
    have hzc : z c ∈ S c := Fintype.mem_piFinset.1 hz c
    have hterm : ∀ v, ∏ e, (if ((e = c ∨ e = c') → z e = v) then w e (z e) else 0) =
        if v = z c then (if z c = z c' then ∏ e, w e (z e) else 0) else 0 := by
      intro v
      by_cases hv : v = z c
      · subst hv
        by_cases hzz : z c = z c'
        · rw [ite_eq_left rfl, ite_eq_left hzz]
          refine prod_congr rfl fun e _ => ite_eq_left ?_
          rintro (rfl | rfl)
          · rfl
          · exact hzz.symm
        · rw [ite_eq_left rfl, ite_eq_right hzz]
          exact prod_eq_zero (mem_univ c')
            (ite_eq_right fun h => hzz (h (Or.inr rfl)).symm)
      · rw [ite_eq_right hv]
        exact prod_eq_zero (mem_univ c) (ite_eq_right fun h => hv (h (Or.inl rfl)).symm)
    simp_rw [hterm]
    rw [sum_ite_eq' (S c) (z c), ite_eq_left hzc]
  rw [sum_congr rfl hsplit, sum_comm]
  -- each common value `v` has probability `w_c(v) w_{c'}(v) ≤ ε w_c(v)`
  calc ∑ v ∈ S c, ∑ z ∈ Fintype.piFinset S,
        ∏ e, (if ((e = c ∨ e = c') → z e = v) then w e (z e) else 0)
      ≤ ∑ v ∈ S c, w c v * ε := by
        refine sum_le_sum fun v hv => ?_
        refine (sum_piFinset_prod_ite (S := S) (w := w)
          (fun e y => (e = c ∨ e = c') → y = v)).trans_le ?_
        have hI := sum_ite_mem_Icc hw0 hw (fun e y => (e = c ∨ e = c') → y = v)
        refine (prod_le_mul_of_le_one (fun e => (hI e).1) (fun e => (hI e).2) hcc).trans ?_
        simp only [true_or, or_true, forall_const]
        rw [sum_ite_eq' (S c), ite_eq_left hv]
        refine mul_le_mul_of_nonneg_left ?_ (hw0 c v hv)
        rw [sum_ite_eq']
        split_ifs with hv'
        · exact hε c' v hv'
        · exact (hw0 c v hv).trans (hε c v hv)
    _ = ε := by rw [← sum_mul, hw c, one_mul]

end Erdos408.OneSided
