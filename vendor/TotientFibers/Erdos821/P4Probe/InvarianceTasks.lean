import Erdos821.P4Probe.RowBridge
import Erdos821.P4Probe.CountingTasks

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

local instance invariantSiteDecidableEq (s M : ℕ) : DecidableEq (RowSite s M) := Classical.decEq _

/-- The remaining analytic-free row-symmetry fact: ANOVA component energy is
invariant under independent row permutations when the original vector is
symmetric. The row laws are identical at every coordinate. No positivity or
normalization is needed for this change-of-variables identity. -/
def RowAnovaInvariantTask : Prop :=
  ∀ (s M : ℕ) (α : Fin s → Type) [∀ g, Fintype (α g)]
    (w : ∀ g, α g → ℝ) (f : ProbeSample α M → ℂ),
    (∀ (π : Fin s → Equiv.Perm (Fin M)) x,
      f (fun g i => x g (π g i)) = f x) →
    ∀ (π : Fin s → Equiv.Perm (Fin M)) (S : Finset (RowSite s M)),
      productSqNorm (flatWeight w)
        (productAnova (flatWeight w) Finset.univ
          (S.map (rowPermutation s M π).toEmbedding) (fun y => f (flattenRows.symm y))) =
      productSqNorm (flatWeight w)
        (productAnova (flatWeight w) Finset.univ S (fun y => f (flattenRows.symm y)))

set_option maxHeartbeats 1000000 in
/-- Exact bridge: all averaging/decomposition algebra and row-space transport
are proved. Only cardinality counting and row-permutation invariance remain. -/
theorem symmetricFullComponentTask_of_counting (hcount : ProbeCountingTask)
    (hinv : RowAnovaInvariantTask) : SymmetricFullComponentTask := by
  intro s J ell m α _ w block f hw hsum hm hell hmJ hM hsym
  let E : Finset (RowSite s (J + ell)) → ℝ := fun S =>
    productSqNorm (flatWeight w)
      (productAnova (flatWeight w) Finset.univ S (fun y => f (flattenRows.symm y)))
  have hE : ∀ S, 0 ≤ E S := fun S =>
    productSqNorm_nonneg (flatWeight w) (fun z a => hw z.1 a) _
  have hEinv : ∀ (π : Fin s → Equiv.Perm (Fin (J + ell))) S,
      E (S.map (rowPermutation s (J + ell) π).toEmbedding) = E S :=
    hinv s (J + ell) α w f hsym
  have hc := hcount s J ell m block E hm hell hmJ hM hE hEinv
  dsimp only at hc ⊢
  rw [flat_fullProbe_energy w hsum]
  have ht : (∑ S ∈ (Finset.univ : Finset (RowSite s (J + ell))).powerset, E S) =
      sampleSqNorm w f := by
    rw [show (∑ S ∈ (Finset.univ : Finset (RowSite s (J + ell))).powerset, E S) =
      productSqNorm (flatWeight w) (fun y => f (flattenRows.symm y)) from
        productAnova_energy (flatWeight w) (fun z => hsum z.1) Finset.univ _, flatSqNorm_eq]
  rw [ht] at hc
  convert hc using 1 <;> congr! 2

end
end Erdos821.P4Probe
