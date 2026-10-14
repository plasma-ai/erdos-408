import Erdos821.S34.IdealFiniteAssembly
import Erdos821.P4Cancel.Proof

set_option autoImplicit false

namespace Erdos821.Blueprint

theorem ideal_inputs_proof : Erdos821.Blueprint.ideal_inputs_statement := by
  intro _hc
  exact S34Core.ideal_inputs_of_cancellation_task
    P4Probe.FiniteProbeCancellationTask_proof

example : Erdos821.Blueprint.ideal_inputs_statement := @ideal_inputs_proof

end Erdos821.Blueprint
