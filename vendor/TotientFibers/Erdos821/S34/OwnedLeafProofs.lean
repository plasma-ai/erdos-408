import Erdos821.Blueprint.Analytic
import Erdos821.S34.Hoeffding
import Erdos821.S34.BilinearEstimate
import Erdos821.S34.Probability

set_option autoImplicit false

namespace Erdos821.S34Core

/-- The earlier standalone finite data has the same fields as the shared
analytic interface. This conversion reduces definitionally on every field. -/
def coreGroups (G : Blueprint.Analytic.PrimeGroups) : S34.Core.PrimeGroups where
  size := G.size
  primes := G.primes
  small := G.small
  prime := G.prime
  disjoint := G.disjoint

end Erdos821.S34Core

namespace Erdos821.Blueprint.Analytic

theorem hoeffding_fraction_proof : Erdos821.Blueprint.Analytic.hoeffding_fraction_statement :=
  @Erdos821.S34.Proofs.hoeffding_fraction

example : Erdos821.Blueprint.Analytic.hoeffding_fraction_statement := @hoeffding_fraction_proof

theorem hoeffding_fraction_bound_proof : Erdos821.Blueprint.Analytic.hoeffding_fraction_bound_statement :=
  @Erdos821.S34.Proofs.hoeffding_fraction_bound

example : Erdos821.Blueprint.Analytic.hoeffding_fraction_bound_statement := @hoeffding_fraction_bound_proof

theorem integer_bilinear_proof : Erdos821.Blueprint.Analytic.integer_bilinear_statement :=
  @Erdos821.S34.Proofs.integer_bilinear

example : Erdos821.Blueprint.Analytic.integer_bilinear_statement := @integer_bilinear_proof

theorem collapse_l2_proof : Erdos821.Blueprint.Analytic.collapse_l2_statement := by
  intro G k f s R hR hρ
  exact Erdos821.S34.Proofs.collapse_l2 (Erdos821.S34Core.coreGroups G) k f s R hR hρ

example : Erdos821.Blueprint.Analytic.collapse_l2_statement := @collapse_l2_proof

end Erdos821.Blueprint.Analytic
