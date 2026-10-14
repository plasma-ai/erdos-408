import Mathlib

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

def rowPermutation (s M : ℕ) (π : Fin s → Equiv.Perm (Fin M)) :
    Equiv.Perm (Fin s × Fin M) where
  toFun z := (z.1, π z.1 z.2)
  invFun z := (z.1, (π z.1).symm z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- Pure cardinality part of symmetric probe suppression. E is any nonnegative
energy attached to coordinate subsets, invariant under independent row
permutations. Resolve row-cardinality tuples; each class has product choose
counts, and requiring m probes plus ell omissions retains the genuine
Hoeffding fraction in each block row. The energy may couple all rows.
The genuine fraction identity/bound are in S34/Hoeffding.lean, not the
owned blueprint placeholders. All ANOVA/projection algebra is already proved
in P4Probe/Anova and ProjectionSelector; this task needs no label spaces. -/
def ProbeCountingTask : Prop :=
  ∀ (s J ell m : ℕ) (block : Finset (Fin s))
    (E : Finset (Fin s × Fin (J + ell)) → ℝ),
    1 ≤ m → 1 ≤ ell → m ≤ J →
    (m + ell) * (m + ell - 1) ≤ J + ell →
    (∀ S, 0 ≤ E S) →
    (∀ (π : Fin s → Equiv.Perm (Fin (J + ell))) S,
      E (S.map (rowPermutation s (J + ell) π).toEmbedding) = E S) →
    let tail := Finset.univ.filter (fun z : Fin s × Fin (J + ell) => J ≤ z.2.val)
    let I := Finset.univ.filter
      (fun z : Fin s × Fin (J + ell) => z.1 ∈ block ∧ z.2.val < m)
    (∑ S ∈ (Finset.univ : Finset (Fin s × Fin (J + ell))).powerset,
      if I ⊆ S ∧ Disjoint tail S then E S else 0) ≤
        (2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell) ^ block.card *
          ∑ S ∈ (Finset.univ : Finset (Fin s × Fin (J + ell))).powerset, E S

end
end Erdos821.P4Probe
