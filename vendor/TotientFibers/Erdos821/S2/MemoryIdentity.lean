import Erdos821.S2.ComplexAssembly
import Erdos821.S2.LifespanSums
import Erdos821.S2.ResidueFactorizationTask

/-! Assemble the exact memory identity from explicit structural and local inputs. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem sum_pair_factor {α β : Type*} [Fintype α] [Fintype β]
    (c : ℂ) (f : α → ℂ) (g : β → ℂ) :
    (∑ a : α, ∑ b : β, c * f a * g b) = c * (∑ a : α, f a) * ∑ b : β, g b := by
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

def coefficientPrefactor (theta : ℝ) : ℂ :=
  (P.markMass (J + F.ell) : ℂ) * ∏ i : Fin n, Q.edgeCoefficient theta i

theorem smallResidueExpression_eq_subtype :
    Q.smallResidueExpression = (Fintype.card P.SmallResidues : ℝ)⁻¹ *
      ∑ y : {y : P.SmallResidues // Q.SmallCompatible y}, ∏ i : Fin n, Q.smallEdgeDamping y.val i := by
  change (Fintype.card P.SmallResidues : ℝ)⁻¹ *
      (∑ y : P.SmallResidues, if Q.SmallCompatible y then ∏ i : Fin n, Q.smallEdgeDamping y i else 0) = _
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter Q.SmallCompatible) (by simp)
    (fun y => ∏ i : Fin n, Q.smallEdgeDamping y i)

theorem factorial_weight_separated (hGhost : SpanGhostWeightTask) (hMark : SpanMarkWeightTask)
    (S : LifespanAssignment P n) (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g, P.V g ≠ 0) (y : P.SmallResidues) (hy : Q.SmallCompatible y)
    (rho theta : ℝ) (hrho : rho ≠ 0) :
    ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
        (Q.ghostBirthPrimes S i g).card.factorial : ℕ) : ℂ) *
        (Q.reconstructedHistory S hS y).Weight rho theta =
      Q.coefficientPrefactor theta * (Q.spanProduct S : ℂ) *
        (Complex.ofReal ((Fintype.card P.SmallResidues : ℝ)⁻¹) *
          (∏ i : Fin n, Q.smallEdgeDamping y i : ℝ)) := by
  rw [← Q.ghostFactorial_cast]
  calc
    _ = (Q.reconstructedHistory S hS y).Weight rho theta * (Q.ghostFactorial S : ℂ) := mul_comm _ _
    _ = _ := by
      rw [Q.reconstructed_weight_factorial hGhost hMark S hQ hS hk hV y hy rho theta hrho]
      simp only [coefficientPrefactor, spanProduct, Complex.ofReal_mul]
      ac_rfl

theorem memory_fiber_sum (hGhost : SpanGhostWeightTask) (hMark : SpanMarkWeightTask)
    (hSpan : SpanSumTask) (hRes : ResidueFactorizationTask) (hn : 0 < n) (hQ : Q.Valid)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g, P.V g ≠ 0)
    (hbp : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, baselinePrime F n p.val ≠ 0)
    (rho theta : ℝ) (hrho : rho ≠ 0) :
    (bigBaseline F P n : ℂ) *
      (∑ S : {S : LifespanAssignment P n // Q.lifespanValid S},
        ∑ y : {y : P.SmallResidues // Q.SmallCompatible y},
          ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
            (Q.ghostBirthPrimes S.val i g).card.factorial : ℕ) : ℂ) *
            (Q.reconstructedHistory S.val S.property y.val).Weight rho theta) = Q.Weight theta := by
  have hY : (∑ y : {y : P.SmallResidues // Q.SmallCompatible y},
      Complex.ofReal ((Fintype.card P.SmallResidues : ℝ)⁻¹) *
        (∏ i : Fin n, Q.smallEdgeDamping y.val i : ℝ)) = (Q.smallResidueExpression : ℂ) := by
    rw [Q.smallResidueExpression_eq_subtype]
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  have hB : (bigBaseline F P n : ℂ) *
      ((∑ S : {S : LifespanAssignment P n // Q.lifespanValid S}, Q.spanProduct S.val : ℝ) : ℂ) =
        (Q.bigResidueExpectation : ℂ) := by
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal
      (Q.baseline_mul_valid_spanProduct_sum hSpan hbp)
  have hR := hRes F P J m n A Q hn hQ
  change P.residueExpectation n (visitQ F.q n) Q.offset Q.active =
    Q.smallResidueExpression * Q.bigResidueExpectation at hR
  have hSep (S : {S : LifespanAssignment P n // Q.lifespanValid S})
      (y : {y : P.SmallResidues // Q.SmallCompatible y}) :=
    Q.factorial_weight_separated hGhost hMark S.val hQ S.property hk hV y.val y.property
      rho theta hrho
  simp_rw [hSep]
  rw [sum_pair_factor, hY]
  have hC : (∑ S : {S : LifespanAssignment P n // Q.lifespanValid S}, (Q.spanProduct S.val : ℂ)) =
      ((∑ S : {S : LifespanAssignment P n // Q.lifespanValid S}, Q.spanProduct S.val : ℝ) : ℂ) :=
    (Complex.ofReal_sum _ _).symm
  rw [hC]
  calc
    _ = Q.coefficientPrefactor theta * (Q.smallResidueExpression : ℂ) *
        ((bigBaseline F P n : ℂ) *
          ((∑ S : {S : LifespanAssignment P n // Q.lifespanValid S}, Q.spanProduct S.val : ℝ) : ℂ)) := by
      ac_rfl
    _ = Q.coefficientPrefactor theta * (Q.smallResidueExpression * Q.bigResidueExpectation : ℝ) := by
      rw [hB, Complex.ofReal_mul, mul_assoc]
    _ = Q.Weight theta := by
      rw [← hR]
      rfl

end ResiduePath

theorem residueExpression_eq_valid_sum {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℕ) (theta : ℝ) :
    residueExpression A n theta = ∑ Q : {Q : ResiduePath A n // Q.Valid}, Q.val.Weight theta := by
  unfold residueExpression
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun Q : ResiduePath A n => Q.Valid)) (by simp)
    (fun Q => Q.Weight theta)

theorem memory_identity_of_tasks {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (hStructure : HistoryStructureProofs) (hGhost : SpanGhostWeightTask) (hMark : SpanMarkWeightTask)
    (hSpan : SpanSumTask) (hRes : ResidueFactorizationTask) (A : Model F P J m)
    (n : ℕ) (hn : 0 < n)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g, P.V g ≠ 0)
    (hbp : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, baselinePrime F n p.val ≠ 0)
    (rho theta : ℝ) (hrho : rho ≠ 0) :
    residueExpression A n theta = (bigBaseline F P n : ℂ) * distinctMemoryExpression A n rho theta := by
  rw [residueExpression_eq_valid_sum,
    distinctMemoryExpression_eq_lifespans hStructure A n hn hk rho theta, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q _
  exact (Q.val.memory_fiber_sum hGhost hMark hSpan hRes hn Q.property hk hV hbp rho theta hrho).symm


end Erdos821.S2Core
