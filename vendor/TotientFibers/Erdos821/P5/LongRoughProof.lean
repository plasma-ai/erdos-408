import Erdos821.P5.LongTheorem
import Erdos821.P5Log.LogPhaseSum
import Erdos821.P2Rough.RoughPolynomial
import Erdos821.P1.ClassicalInputs

noncomputable section

namespace Erdos821.P5Core

theorem logPhaseSumTask_proof : LogPhaseSumTask :=
  P5Log.LogPhaseSumTask_proof

end Erdos821.P5Core

namespace Erdos821.Blueprint.Analytic

/-- §4 long rough-polynomial cancellation, using the proved P1/P2 inputs
and the accepted log-phase estimate. -/
theorem long_rough_polynomial_proof : Erdos821.Blueprint.Analytic.long_rough_polynomial_statement :=
  @P5Core.long_rough_polynomial_of_inputs
    (roughPolynomial_proof classical_inputs) P5Core.logPhaseSumTask_proof

example : Erdos821.Blueprint.Analytic.long_rough_polynomial_statement := @long_rough_polynomial_proof

end Erdos821.Blueprint.Analytic

