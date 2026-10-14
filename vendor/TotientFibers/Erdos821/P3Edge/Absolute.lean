import Erdos821.P3Edge.CoeffBound
import Erdos821.P3Edge.NormOsc
import Erdos821.P3Edge.LargeX

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

lemma memoryWeight_pos (r : MemoryParameters F) (z : P.MemoryState (J + F.ell)) :
    0 < P.memoryWeight r.v z := by
  unfold PrimeGroups.memoryWeight
  exact pow_pos (lt_trans zero_lt_one r.v_gt) _

lemma memoryWeight_nonneg (r : MemoryParameters F) (z : P.MemoryState (J + F.ell)) :
    0 ≤ P.memoryWeight r.v z :=
  (memoryWeight_pos r z).le

lemma absoluteMemoryEdgeKernel_nonneg (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) :
    0 ≤ absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  unfold absoluteMemoryEdgeKernel
  apply mul_nonneg (edgeSymmetryFactor_nonneg P _)
  apply Finset.sum_nonneg
  intro c _
  split_ifs with hc
  · exact norm_nonneg _
  · exact le_refl 0

lemma norm_cast_absolute (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) :
    ‖((absoluteMemoryEdgeKernel A n rho theta i .all s t : ℝ) : ℂ)‖ =
      absoluteMemoryEdgeKernel A n rho theta i .all s t := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (absoluteMemoryEdgeKernel_nonneg A n rho theta i s t)]

-- Coefficient norms: oscillation (pattern coeff * imaginaryPower, phase) has
-- modulus ≤ patternMass; rawEdgeWeight carries all masses/dampings.
lemma edgeChoiceCoefficient_norm_le (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    ‖edgeChoiceCoefficient A n rho theta i s t c‖ ≤
      A.patternMass * |rawEdgeWeight A n rho (A.pattern c.2.2.1) c.2.2.2.1
        (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2| := by
  classical
  unfold edgeChoiceCoefficient
  simp only []
  -- Decompose: (raw:ℂ) * (z or zr) * phase.
  have hphase : ‖phase (theta * ((edgeDelta A (A.pattern c.2.2.1) (edgeForward i)
      (permuteActive c.1 s).2.1 c.2.2.2.1 : ℤ) : ℝ))‖ = 1 :=
    norm_phase _
  have hcoeff : ∀ (a b : P.BigLabels (J + F.ell)) (u : P.BigAux J),
      ‖(A.pattern c.2.2.1).coefficient a b u * imaginaryPower
        ((A.pattern c.2.2.1).D (permuteActive c.1 s).2.1 c.2.2.2.1) A.zeta‖ ≤
        A.patternMass := by
    intro a b u
    calc ‖(A.pattern c.2.2.1).coefficient a b u * imaginaryPower _ _‖
        = ‖(A.pattern c.2.2.1).coefficient a b u‖ * 1 := by
          rw [norm_mul, norm_imaginaryPower, mul_one]
      _ ≤ A.patternMass := by
          have h := coeff_le_patternMass A c.2.2.1 a b u
          linarith [norm_nonneg ((A.pattern c.2.2.1).coefficient a b u)]
  by_cases hf : edgeForward i = true
  · simp only [hf, ite_true] at ⊢
    rw [hf] at hphase
    have hz := hcoeff (P.restrictBig (permuteActive c.1 s).2.1)
      (P.restrictBig (permuteActive c.2.1 t).2.1) (fun g => c.2.2.2.1 g.val)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hphase, mul_one,
      mul_comm A.patternMass _]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  · rw [if_neg hf] at ⊢
    have hz := hcoeff (P.restrictBig (permuteActive c.2.1 t).2.1)
      (P.restrictBig (permuteActive c.1 s).2.1) (fun g => c.2.2.2.1 g.val)
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      hphase, mul_one, mul_comm A.patternMass _]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

end Erdos821.P3Edge
