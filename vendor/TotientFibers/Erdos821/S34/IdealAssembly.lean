import Erdos821.S34.ComparisonKernel
import Erdos821.S34.ProbeTasks

set_option autoImplicit false

namespace Erdos821.S34Core

theorem comparisonEstimate_proof : Blueprint.ComparisonEstimate :=
  @Blueprint.Analytic.comparison_kernel_proof

theorem ideal_inputs_of_probe (hprobe : SymmetricProbeTask) : Blueprint.IdealInputs :=
  ⟨comparisonEstimate_proof, hprobe comparisonEstimate_proof⟩

end Erdos821.S34Core
