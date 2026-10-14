import Erdos821.P4Probe.ProductMarginals

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

/-- Independence of two disjoint coordinate restrictions of a finite
product law. Integrate unused coordinates by their normalized mass, then
split the selected union into S and T. No positivity is needed. -/
def DisjointMarginalTask : Prop :=
  ∀ (ι : Type) [Fintype ι] (α : ι → Type) [∀ i, Fintype (α i)]
    (w : ∀ i, α i → ℝ) (S T : Finset ι),
    (∀ i, ∑ x, w i x = 1) → Disjoint S T →
    ∀ H : PartialSample S α → PartialSample T α → ℂ,
      (∑ y : ProductSample α, (productWeight w y : ℂ) *
        H (fun i => y i.val) (fun i => y i.val)) =
          ∑ a : PartialSample S α, ∑ b : PartialSample T α,
            ((partialProductWeight w S a * partialProductWeight w T b : ℝ) : ℂ) * H a b

end Erdos821.P4Probe
