import Erdos821.P5.ShiftAssembly
import Erdos821.P5FourierArcProof.FourierArc
import Erdos821.P1.ClassicalInputs
import Erdos821.Prelim.SieveInputsProof
import Erdos821.S34.IdealInputs

set_option autoImplicit false

namespace Erdos821.P5Core

/-- Insert the proved Fourier arc and square tasks into the exact P5
package signature. Only the minor adapter and marked energy remain. -/
theorem shifted_cancellation_of_two_tasks
    (hadapter : ComparisonMinorArcAdapterTask) (henergy : MarkedEndpointEnergyTask) :
    Erdos821.Blueprint.shifted_cancellation_statement :=
  shifted_cancellation_of_remaining_tasks FourierArcTask_proof hadapter henergy

/-- The standalone frozen shift type with the proved P1, P2 and P4
packages, leaving P3 explicit until its final input is delivered. -/
theorem lifted_shift_of_two_tasks
    (ht : Blueprint.TransferenceInputs) (hadapter : ComparisonMinorArcAdapterTask)
    (henergy : MarkedEndpointEnergyTask) : Erdos821.Blueprint.Analytic.lifted_shift_statement :=
  shifted_cancellation_of_two_tasks hadapter henergy Blueprint.classical_inputs
    (Blueprint.sieve_inputs_proof Blueprint.classical_inputs) ht
    (Blueprint.ideal_inputs_proof Blueprint.classical_inputs)

end Erdos821.P5Core
