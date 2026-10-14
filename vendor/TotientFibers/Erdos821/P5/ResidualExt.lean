import Erdos821.Blueprint.Ideal

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Graph

theorem selectedEndpoint_ext {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (a a' : P.BigLabels (J + ell))
    (ha : ∀ g i, i ∈ ν.changed g.val → a g (ν.slot i) = a' g (ν.slot i)) :
    selectedEndpoint ν block side a = selectedEndpoint ν block side a' := by
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs with h
  · rw [ha g i h.2]
  · rfl

theorem selectedProduct_ext {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (u u' : P.BigAux J)
    (hu : ∀ g i, i ∈ ν.changed g.val → u g i = u' g i) :
    selectedProduct ν block side u = selectedProduct ν block side u' := by
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs with h
  · rw [hu g i h.2]
  · rfl

/-- In an actual residual family, coefficients use only changed designated
endpoint slots and free auxiliary labels. Shared endpoint labels are absent. -/
theorem residual_coefficient_changed_ext {F : FixedData} {P : PrimeGroups} {J m Q : ℕ}
    {h ξ : ℝ} (B : Family F P J m) (hB : B.Residual Q h ξ) (v : Fin B.count)
    (a a' b b' : P.BigLabels (J + F.ell)) (u u' : P.BigAux J)
    (ha : ∀ g i, i ∈ (B.pattern v).changed g.val →
      a g ((B.pattern v).slot i) = a' g ((B.pattern v).slot i))
    (hb : ∀ g i, i ∈ (B.pattern v).changed g.val →
      b g ((B.pattern v).slot i) = b' g ((B.pattern v).slot i))
    (hu : ∀ g i, i ∈ (B.pattern v).changed g.val → u g i = u' g i) :
    (B.pattern v).coefficient a b u = (B.pattern v).coefficient a' b' u' := by
  obtain ⟨raw, block, hrawchanged, hraw, hcomp⟩ := hB
  by_cases hv : v = raw
  · subst v
    rw [hraw, hraw]
  · have hc := (hcomp v hv).2.2
    rw [hc, hc]
    rw [selectedProduct_ext (B.pattern v) block false u u' hu,
      selectedProduct_ext (B.pattern v) block true u u' hu,
      selectedEndpoint_ext (B.pattern v) block false b b' hb,
      selectedEndpoint_ext (B.pattern v) block true a a' ha]

end Erdos821.P5Core
