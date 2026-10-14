import Erdos821.Blueprint.Ideal

set_option autoImplicit false

namespace Erdos821.S34Core

/-- Pure symmetric-probe construction after the analytic comparison is given.
Choose m from the Hoeffding suppression, then comparison accuracy paying 3^P,
then kernel parameters and C1, finally J0. Build the raw-plus-all-nonempty
probe-subset family. Coordinate averages give the orthogonal Efron–Stein
decomposition; symmetry counts the retained fraction per group. Alternate
subset signs cancel every pair with both missing sets nonempty. Bound the
two full-block exceptions before taking individual subset norms.
Proved factorial bounds are in the lead's S34/Hoeffding.lean; use those
proofs or reproduce them, never the owned blueprint placeholders. -/
def SymmetricProbeTask : Prop :=
  Blueprint.ComparisonEstimate → Blueprint.Graph.IdealConstruction

end Erdos821.S34Core
