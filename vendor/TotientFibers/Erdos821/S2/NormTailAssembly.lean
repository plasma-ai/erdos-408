import Erdos821.S2.MemorySplit
import Erdos821.S2.MomentCRT

/-! Pointwise scalar assembly of cutoff, tail and physical CRT estimates. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem full_memory_norm_le_two (A : Model F P J m) (n B : ℕ)
    (rho v theta CG CE U V : ℝ) (hv : 1 ≤ v) (hCG : 0 ≤ CG) (hCE : 0 ≤ CE)
    (hG : ∀ (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteScaledMemoryGhostKernel F J n rho 2 i s t * P.memoryWeight v t) ∧
      (∑' t, absoluteScaledMemoryGhostKernel F J n rho 2 i s t * P.memoryWeight v t) ≤
        CG * P.memoryWeight v s)
    (hE : ∀ (i : Fin n) (s : P.MemoryState (J + F.ell)),
      Summable (fun t => absoluteMemoryEdgeKernel A n rho theta i .all s t * P.memoryWeight v t) ∧
      (∑' t, absoluteMemoryEdgeKernel A n rho theta i .all s t * P.memoryWeight v t) ≤
        CE * P.memoryWeight v s)
    (hTrunc : ‖truncatedDistinctMemoryExpression A n B rho theta‖ ≤ U)
    (hCost : CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n ≤ V)
    (hGain : (2 : ℝ) ^ (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) * V ≤ U) :
    ‖distinctMemoryExpression A n rho theta‖ ≤ 2 * U := by
  have hpow : 0 ≤ (2 : ℝ) ^
      (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) :=
    zpow_nonneg (by norm_num) _
  have ht : (2 : ℝ) ^
        (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
        CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n ≤ U := by
    calc
      _ = (2 : ℝ) ^
          (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) *
          (CG ^ (n + 1) * CE ^ n * initialMemoryBoundaryMass A n) := by ring
      _ ≤ (2 : ℝ) ^
          (((n * ((J + F.ell) * Fintype.card P.BigGroup) : ℕ) : ℤ) - (B : ℤ)) * V :=
        mul_le_mul_of_nonneg_left hCost hpow
      _ ≤ U := hGain
  exact (distinctMemoryExpression_norm_le_cutoff A n B rho v theta CG CE hv hCG hCE hG hE).trans
    ((add_le_add hTrunc ht).trans_eq (by ring))

theorem averagedMoment_le_of_bounds (hPath : PhysicalPathExpansionTask)
    (A : Model F P J m) (r : ℕ) (hr : 0 < r) (X epsilon C D : ℝ) (heps : 0 ≤ epsilon)
    (hreplace : ∀ Q : ResiduePath A (2 * r), Q.Valid →
      |((dyad X).card : ℝ)⁻¹ * ∑ z ∈ dyad X,
          P.pathFactor (2 * r) (visitQ F.q (2 * r)) Q.offset Q.active z -
        P.residueExpectation (2 * r) (visitQ F.q (2 * r)) Q.offset Q.active| ≤
      epsilon * P.residueExpectation (2 * r) (visitQ F.q (2 * r)) Q.offset Q.active)
    (hClosed : ‖closedResidueExpression A (2 * r)‖ ≤ C)
    (hAbs : closedAbsoluteResidueExpression A (2 * r) ≤ D) :
    A.averagedMoment r X ≤ C + epsilon * D := by
  have hdiff := averagedMoment_replacement_bound A hPath r hr X epsilon hreplace
  have hreal := Complex.re_le_norm (closedResidueExpression A (2 * r))
  have habs := le_abs_self (A.averagedMoment r X - (closedResidueExpression A (2 * r)).re)
  have he : A.averagedMoment r X ≤ ‖closedResidueExpression A (2 * r)‖ +
      |A.averagedMoment r X - (closedResidueExpression A (2 * r)).re| := by linarith
  exact he.trans (add_le_add hClosed (hdiff.trans (mul_le_mul_of_nonneg_left hAbs heps)))


end Erdos821.S2Core
