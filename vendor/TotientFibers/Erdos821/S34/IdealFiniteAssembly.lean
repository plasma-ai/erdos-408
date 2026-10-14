import Erdos821.S34.IdealAssembly
import Erdos821.P4Probe.Construction
import Erdos821.P4Probe.InvarianceTasks
import Erdos821.P4Count.ProbeCounting
import Erdos821.P4Proj.Invariance

set_option autoImplicit false

namespace Erdos821.S34Core

/-- The final package reduced to the three pure finite tasks, with all
analytic comparison input and construction parameter choices discharged. -/
theorem ideal_inputs_of_finite_tasks
    (hcount : P4Probe.ProbeCountingTask)
    (hinvariant : P4Probe.RowAnovaInvariantTask)
    (hcancel : P4Probe.FiniteProbeCancellationTask) : Blueprint.IdealInputs :=
  ideal_inputs_of_probe (P4Probe.symmetricProbeTask_of_finite
    (P4Probe.symmetricFullComponentTask_of_counting hcount hinvariant) hcancel)

theorem ideal_inputs_of_remaining_tasks
    (hinvariant : P4Probe.RowAnovaInvariantTask)
    (hcancel : P4Probe.FiniteProbeCancellationTask) : Blueprint.IdealInputs :=
  ideal_inputs_of_finite_tasks P4Probe.ProbeCountingTask_proof hinvariant hcancel

theorem ideal_inputs_of_cancellation_task
    (hcancel : P4Probe.FiniteProbeCancellationTask) : Blueprint.IdealInputs :=
  ideal_inputs_of_remaining_tasks P4Probe.RowAnovaInvariantTask_proof hcancel

end Erdos821.S34Core
