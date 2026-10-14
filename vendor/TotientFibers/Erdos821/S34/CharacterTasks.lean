import Erdos821.Blueprint.Analytic

set_option autoImplicit false

namespace Erdos821.S34Core

open Blueprint.Analytic

/-- Finite character facts used by the cell-kernel supremum, reproduction,
and frame estimates. CharacterIndex uses levels 1 through Q, never zero.
Route for count: Fintype.card of DirichletCharacter at level r is totient r;
each level has at most Q characters. Route for norm: character values are
zero on nonunits and roots of unity on units. -/
def PrimitiveCharacterTask : Prop :=
  (∀ Q : ℕ, (primitiveCharacters Q).card ≤ Q ^ 2) ∧
  (∀ (Q : ℕ) (χ : CharacterIndex Q) (n : ℕ), ‖charValue χ n‖ ≤ 1)

end Erdos821.S34Core
