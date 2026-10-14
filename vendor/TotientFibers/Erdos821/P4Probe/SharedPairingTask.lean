import Erdos821.P4Probe.ProductMarginals

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe

noncomputable section

variable {ι : Type*} {α : ι → Type*}

abbrev FreshSample (S : Finset ι) (α : ι → Type*) := ∀ i : {i // i ∉ S}, α i.val

def joinSharedFresh (S : Finset ι) (s : PartialSample S α) (u : FreshSample S α) :
    ProductSample α := (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) α).symm (s, u)

def sameShared (S : Finset ι) (x y : ProductSample α) : Prop :=
  ∀ i, i ∈ S → x i = y i

def freshProductWeight [Fintype ι] (w : ∀ i, α i → ℝ) (S : Finset ι)
    (y : ProductSample α) : ℝ :=
  ∏ i, if i ∈ S then 1 else w i (y i)

/-- Exact finite conditioning on coordinates shared by two samples.
Split each sample with piEquivPiSubtypeProd, factor its product law,
and sum the equality constraint on the two shared samples. No positivity
or normalization is required; this is pure finite Fubini algebra. -/
def SharedPairingTask : Prop :=
  ∀ (ι : Type) [Fintype ι] (α : ι → Type) [∀ i, Fintype (α i)]
    (w : ∀ i, α i → ℝ) (S : Finset ι) (H : ProductSample α → ProductSample α → ℂ),
    (∑ x : ProductSample α, ∑ y : ProductSample α,
      if sameShared S x y then
        ((productWeight w x * freshProductWeight w S y : ℝ) : ℂ) * H x y else 0) =
      ∑ s : PartialSample S α, ∑ u : FreshSample S α, ∑ v : FreshSample S α,
        ((partialProductWeight w S s *
          productWeight (fun i : {i // i ∉ S} => w i.val) u *
          productWeight (fun i : {i // i ∉ S} => w i.val) v : ℝ) : ℂ) *
            H (joinSharedFresh S s u) (joinSharedFresh S s v)

end
end Erdos821.P4Probe
