import Erdos821.S2.ScalarAssembly
import Erdos821.S2.ActualStructures
import Erdos821.S2.HistoryDamping

/-! Exact complex history coefficients retain every signed factor and phase. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

namespace ResiduePath

variable {F : FixedData} {P : PrimeGroups} {J m n : ℕ} {A : Model F P J m}
  (Q : ResiduePath A n)

theorem ghostFactorial_cast (S : LifespanAssignment P n) :
    (Q.ghostFactorial S : ℂ) =
      ((∏ i : Fin (n + 1), ∏ g : P.BigGroup,
        (Q.ghostBirthPrimes S i g).card.factorial : ℕ) : ℂ) := by
  simp [ghostFactorial]

theorem reconstructed_weight_factorial (hGhost : SpanGhostWeightTask)
    (hMark : SpanMarkWeightTask) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (hV : ∀ g, P.V g ≠ 0) (y : P.SmallResidues) (hy : Q.SmallCompatible y)
    (rho theta : ℝ) (hrho : rho ≠ 0) :
    (Q.reconstructedHistory S hS y).Weight rho theta * (Q.ghostFactorial S : ℂ) =
      ((Fintype.card P.SmallResidues : ℝ)⁻¹ * P.markMass (J + F.ell) *
          (∏ i : Fin n, Q.smallEdgeDamping y i) *
          (∏ g : P.BigGroup, ∏ p : P.Prime g.val, Q.spanWeight g p (S g p)) : ℝ) *
        ∏ i : Fin n, Q.edgeCoefficient theta i := by
  have hv := Q.reconstructedHistory_valid_of_lifespans S hQ hS hk y hy
  rw [(Q.reconstructedHistory S hS y).weight_rho_independent rho theta hrho hv,
    Q.reconstructed_weight_split S hS y 1 theta]
  have he : (Q.reconstructedScalarWeight S hS y 1 : ℂ) *
      (∏ i : Fin n, Q.edgeOscillation theta i) * (Q.ghostFactorial S : ℂ) =
      (Q.reconstructedScalarWeight S hS y 1 * Q.ghostFactorial S : ℝ) *
        ∏ i : Fin n, Q.edgeOscillation theta i := by
    simp only [Complex.ofReal_mul]
    ac_rfl
  rw [he, Q.reconstructedScalarWeight_factorial hGhost hMark S hQ hS hk hV y hy]
  simp_rw [Q.edgeCoefficient_split theta]
  simp only [scalarPathPrefactor, Complex.ofReal_mul, Complex.ofReal_prod,
    Finset.prod_mul_distrib]
  ac_rfl


end ResiduePath
end Erdos821.S2Core
