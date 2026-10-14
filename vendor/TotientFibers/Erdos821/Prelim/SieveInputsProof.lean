import Erdos821.Prelim.SieveBlockProof
import Erdos821.P2Rough.RoughPolynomial

namespace Erdos821.Blueprint

/-- P2 boundary, assembled from the block and rough-polynomial certificates. -/
theorem sieve_inputs_proof (hc : ClassicalInputs) : SieveInputs :=
  ⟨PrelimLemmas.blockSieve_proof, roughPolynomial_proof hc⟩

example : Erdos821.Blueprint.sieve_inputs_statement := @sieve_inputs_proof

end Erdos821.Blueprint
