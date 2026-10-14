import Erdos821.Blueprint.Classical

set_option autoImplicit false

open Filter

namespace Erdos821.S34Core

open Blueprint Blueprint.Analytic

/-- §3 ideal-character-cell, with harmonic SW supplied as a hypothesis.
Use the common lcm modulus of two distinct primitive characters, whose
quotient is nonprincipal. Condition on all but one selected big label;
the log cell and the prime group restrict that label to an interval.
Apply HarmonicCharacters, divide by the group mass, and average the other
labels. Precision is absolute and uniform in the cell width/location.
Use no owned blueprint placeholder. -/
def CharacterCellTask : Prop :=
  HarmonicCharacters → ∀ (P : Geometry) (m : ℕ) (qexp D : ℝ),
    0 < qexp → 0 < D → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x in atTop,
      ∀ G : PrimeGroups, Admissible P x G → ∀ k, bigSlots G k m →
      ∀ (Q : ℕ) (h : ℝ) (j : ℤ) (χ ψ : CharacterIndex Q),
        (Q : ℝ) ≤ L x ^ qexp → 0 < h → χ ∈ primitiveCharacters Q →
        ψ ∈ primitiveCharacters Q → χ ≠ ψ →
        ‖expect G k (fun z => if cell h (product G k z) = j then
          star (charValue χ (product G k z)) * charValue ψ (product G k z) else 0)‖ ≤
          K * L x ^ (-D)

end Erdos821.S34Core
