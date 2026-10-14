import Erdos821.P1.PrimeProgressions
import Erdos821.P1.Mertens
import Erdos821.P1.LargeSieve
import Erdos821.Classical.DirichletMean
import Erdos821.Classical.FourierSeparation
import Erdos821.Classical.DerivativeTests
import Erdos821.Classical.DivisorMoments
import Erdos821.Classical.HarmonicCharacters

namespace Erdos821.P1

theorem classical_inputs_of_harmonic
    (harmonic : Erdos821.Blueprint.HarmonicCharacters) :
    Erdos821.Blueprint.ClassicalInputs := by
  exact ⟨prime_progressions_proof, mertens_proof, harmonic,
    Erdos821.Blueprint.DivisorMoments_proof,
    Erdos821.Classical.blueprint_meanSquares,
    multiplicative_large_sieve_proof,
    Erdos821.Blueprint.DerivativeTests_proof,
    Erdos821.Classical.blueprint_lem_fourier_separation⟩

theorem classical_inputs_proof : Erdos821.Blueprint.ClassicalInputs :=
  classical_inputs_of_harmonic Erdos821.Blueprint.HarmonicCharacters_proof



end Erdos821.P1

/-- §1 classical inputs, assembled from the eight proved fields. -/
theorem Erdos821.Blueprint.classical_inputs : Erdos821.Blueprint.ClassicalInputs :=
  Erdos821.P1.classical_inputs_proof
