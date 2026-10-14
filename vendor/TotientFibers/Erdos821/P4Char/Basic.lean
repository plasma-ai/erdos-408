import Erdos821.Blueprint.Analytic

set_option autoImplicit false

open scoped BigOperators

namespace Erdos821.P4Char

open Blueprint.Analytic

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Finite character facts used by the cell-kernel supremum, reproduction,
and frame estimates. CharacterIndex uses levels 1 through Q, never zero.
Route for count: Fintype.card of DirichletCharacter at level r is totient r;
each level has at most Q characters. Route for norm: character values are
zero on nonunits and roots of unity on units. -/
def PrimitiveCharacterTask : Prop :=
  (∀ Q : ℕ, (primitiveCharacters Q).card ≤ Q ^ 2) ∧
  (∀ (Q : ℕ) (χ : CharacterIndex Q) (n : ℕ), ‖charValue χ n‖ ≤ 1)

/-- Each positive level contributes at most `m` Dirichlet characters. -/
lemma card_dirichlet_le (m : ℕ) (hm : 0 < m) :
    Fintype.card (DirichletCharacter ℂ m) ≤ m := by
  have : NeZero m := ⟨ne_of_gt hm⟩
  have : NeZero ((Monoid.exponent (ZMod m)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Fintype.card (DirichletCharacter ℂ m) = m.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ m
  rw [hcard]
  exact Nat.totient_le m

/-- Count part: the primitive characters at levels `1..Q` number at most `Q ^ 2`. -/
theorem count_part : ∀ Q : ℕ, (primitiveCharacters Q).card ≤ Q ^ 2 := by
  intro Q
  have hsub : (primitiveCharacters Q).card ≤ Fintype.card (CharacterIndex Q) :=
    Finset.card_le_univ _
  have huniv : Fintype.card (CharacterIndex Q) ≤ ∑ _r : Fin Q, Q := by
    show Fintype.card ((r : Fin Q) × DirichletCharacter ℂ (r.val + 1)) ≤ _
    rw [Fintype.card_sigma]
    apply Finset.sum_le_sum
    intro r _
    calc Fintype.card (DirichletCharacter ℂ (r.val + 1))
        ≤ r.val + 1 := card_dirichlet_le _ (Nat.succ_pos _)
      _ ≤ Q := Nat.succ_le_of_lt r.is_lt
  have hsum : ∑ _r : Fin Q, Q = Q ^ 2 := by
    simp [Finset.sum_const, Finset.card_univ, pow_two]
  exact hsub.trans (huniv.trans hsum.le)

/-- Norm part: every character value has norm at most one. -/
theorem norm_part :
    ∀ (Q : ℕ) (χ : CharacterIndex Q) (n : ℕ), ‖charValue χ n‖ ≤ 1 := by
  intro Q χ n
  show ‖χ.2 ((n : ℕ) : ZMod (χ.1.val + 1))‖ ≤ 1
  exact DirichletCharacter.norm_le_one _ _

theorem PrimitiveCharacterTask_proof : PrimitiveCharacterTask :=
  ⟨count_part, norm_part⟩

example : PrimitiveCharacterTask := PrimitiveCharacterTask_proof

end

end Erdos821.P4Char
