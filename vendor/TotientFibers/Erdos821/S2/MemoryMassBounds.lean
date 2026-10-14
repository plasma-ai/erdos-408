import Erdos821.S2.CountableSchur
import Erdos821.S2.GhostTasks

/-! Nonnegative memory measures and the assembly of the two ghost estimates. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {P : PrimeGroups}

theorem tiltedMu_big_pos (F : FixedData) (n : ℕ) (hV : ∀ g, 0 < P.V g)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (g : P.BigGroup) (p : P.Prime g.val) : 0 < tiltedMu F P n g.val p := by
  have hp : 0 < (p.val : ℝ) := by exact_mod_cast (P.prime g.val p.val p.property).pos
  exact inv_pos.mpr (mul_pos (mul_pos (hV g.val) hp) (hb g p))

theorem groupMemoryMass_nonneg (F : FixedData) (n : ℕ) (g : P.BigGroup)
    (hmu : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p) (z : P.Memory g.val) :
    0 ≤ P.groupMemoryMass F n g.val z := by
  unfold PrimeGroups.groupMemoryMass
  apply div_nonneg
  · apply Multiset.prod_nonneg
    intro x hx
    obtain ⟨u, _, rfl⟩ := Multiset.mem_map.mp hx
    exact hmu u.1
  · apply Finset.prod_nonneg
    intro u _
    positivity

theorem memoryMass_nonneg (F : FixedData) (J n : ℕ) (hV : ∀ g, 0 < P.V g)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (s : P.MemoryState (J + F.ell)) : 0 ≤ P.memoryMass F J n s := by
  unfold PrimeGroups.memoryMass
  split_ifs
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact Finset.prod_nonneg (fun g _ => (zpow_pos (hV g.val) _).le)
      · apply Finset.prod_nonneg
        intro g _
        exact Finset.prod_nonneg (fun i _ => (tiltedMu_big_pos F n hV hb g _).le)
    · apply Finset.prod_nonneg
      intro g _
      exact groupMemoryMass_nonneg F n g (fun p => (tiltedMu_big_pos F n hV hb g p).le) _
  · exact le_refl 0

/-- Once the independent row and factorial-adjoint tasks are proved, all local
modulus-one multipliers retain the same ghost L² bound. -/
theorem scaled_ghost_domination_of_tasks (hAdj : GhostAdjointTask) (hRows : GhostRowsTask)
    (F : FixedData) (J n : ℕ) (r : MemoryParameters F)
    (hV : ∀ g, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (i : Fin (n + 1))
    (d : ℝ) (hd : d = 1 ∨ d = 2)
    (K : P.MemoryState (J + F.ell) → P.MemoryState (J + F.ell) → ℂ)
    (hbound : ∀ s t, ‖K s t‖ ≤ absoluteScaledMemoryGhostKernel F J n r.rho d i s t) :
    NormBound (P.memoryMass F J n) K
      ((Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card) := by
  let C : ℝ := (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card
  have hC : 0 ≤ C := (pow_pos (Real.exp_pos _) _).le
  have hm := memoryMass_nonneg F J n (fun g => (hV g).1) hb
  have hw (s : P.MemoryState (J + F.ell)) : 0 < P.memoryWeight r.v s :=
    pow_pos (lt_trans zero_lt_one r.v_gt) _
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hr (s : P.MemoryState (J + F.ell)) := hRows F P J n r hV hb hmu d hd i s
  have hc (s t : P.MemoryState (J + F.ell)) :=
    hAdj F P J n r (fun g => (hV g).1) hb d hd i s t
  have hrow (s : P.MemoryState (J + F.ell)) (S : Finset (P.MemoryState (J + F.ell))) :
      ∑ t ∈ S, ‖K s t‖ * P.memoryWeight r.v t ≤ C * P.memoryWeight r.v s := by
    calc
      _ ≤ ∑ t ∈ S, absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t :=
        Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_right (hbound s t) (hw t).le)
      _ ≤ ∑' t, absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t :=
        (hr s).1.sum_le_tsum S (fun t _ => mul_nonneg ((norm_nonneg _).trans (hbound s t)) (hw t).le)
      _ ≤ _ := (hr s).2.1
  have hcol (t : P.MemoryState (J + F.ell)) (S : Finset (P.MemoryState (J + F.ell))) :
      ∑ s ∈ S, P.memoryMass F J n s * ‖K s t‖ * P.memoryWeight r.v s ≤
        C * P.memoryMass F J n t * P.memoryWeight r.v t := by
    calc
      _ ≤ ∑ s ∈ S, P.memoryMass F J n s *
          absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v s :=
        Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hbound s t) (hm s)) (hw s).le)
      _ = P.memoryMass F J n t * ∑ s ∈ S,
          ghostReversalFactor d t s * absoluteScaledMemoryGhostKernel F J n r.rho d i t s * P.memoryWeight r.v s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [hc s t]
        ring
      _ ≤ P.memoryMass F J n t * ∑' s,
          ghostReversalFactor d t s * absoluteScaledMemoryGhostKernel F J n r.rho d i t s * P.memoryWeight r.v s := by
        apply mul_le_mul_of_nonneg_left _ (hm t)
        apply (hr t).2.2.1.sum_le_tsum S
        intro s _
        have hfac : 0 ≤ ghostReversalFactor d t s := by
          apply Finset.prod_nonneg
          intro g _
          exact (zpow_pos (mul_pos hdpos (hV g.val).1) _).le
        exact mul_nonneg (mul_nonneg hfac ((norm_nonneg _).trans (hbound t s))) (hw s).le
      _ ≤ _ := by
        have he := mul_le_mul_of_nonneg_left (hr t).2.2.2 (hm t)
        simpa only [C, mul_assoc, mul_left_comm, mul_comm] using he
  simpa only [Real.sqrt_mul_self hC] using
    finite_support_schur (P.memoryMass F J n) (P.memoryWeight r.v)
      K C C hm hw hC hC hrow hcol

/-- Unscaled signed ghosts, with multipliers before choices are combined. -/
theorem ghost_norm_of_tasks (hAdj : GhostAdjointTask) (hRows : GhostRowsTask)
    (F : FixedData) (J n : ℕ) (r : MemoryParameters F)
    (hV : ∀ g, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (i : Fin (n + 1))
    (phi : (s t : P.MemoryState (J + F.ell)) → GhostChoice s t → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1) :
    NormBound (P.memoryMass F J n) (memoryGhostKernel F J n r.rho i phi)
      ((Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card) := by
  apply scaled_ghost_domination_of_tasks hAdj hRows F J n r hV hb hmu i 1 (Or.inl rfl)
  intro s t
  have he : absoluteScaledMemoryGhostKernel F J n r.rho 1 i s t =
      absoluteMemoryGhostKernel F J n r.rho i s t := by
    simp only [absoluteScaledMemoryGhostKernel, absoluteMemoryGhostKernel, one_pow, mul_one]
  rw [he]
  exact memoryGhostKernel_norm_le F J n r.rho i phi hphi s t


end Erdos821.S2Core
