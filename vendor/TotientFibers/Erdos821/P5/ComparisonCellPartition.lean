import Erdos821.P5.ComparisonRowExpansion
import Erdos821.P5.ResidualStripping

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

def comparisonCellPair {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (h : ℝ)
    (u : FreeDraw ν) : ℤ × ℤ :=
  (cell h (comparisonFreeProduct ν block false u),
    cell h (comparisonFreeProduct ν block true u))

def comparisonCells {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (h : ℝ) : Finset (ℤ × ℤ) :=
  Finset.univ.image (comparisonCellPair ν block h)

theorem sum_freeDraw_by_comparisonCells {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (h : ℝ)
    (f : FreeDraw ν → ℂ) :
    (∑ u : FreeDraw ν, f u) = ∑ j ∈ comparisonCells ν block h,
      ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j, f u := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f

/-- One fixed cell/character correlation, with its original finite root
support and cutoff. Its two mark functions are independent of the free draw. -/
def comparisonCellCorrelation {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (χA χB : CharacterIndex Q)
    (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (s : FreeDraw ν → Finset ℕ) : ℂ :=
  ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j,
    (freeDrawLaw ν u : ℂ) *
      star (charValue χA (comparisonFreeProduct ν block false u)) *
      star (charValue χB (comparisonFreeProduct ν block true u)) *
      ∑ n ∈ s u, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat)

/-- The complete stripped comparison, separated into its actual finite
cell pairs and characters. No bound on the number of family patterns is used. -/
theorem residualStrippedLift_comparison_cell_expansion {P : Geometry} {G : PrimeGroups}
    {J m : ℕ} (B : Family P.graph G.graph J m) (v : Fin B.count)
    (block : G.graph.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (hc : HasComparisonCoefficient (B.pattern v) block Q h ξ)
    (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (z : SharedDraw (B.pattern v)) (s : FreeDraw (B.pattern v) → Finset ℕ) :
    residualStrippedLift B v x Z a₁ a₂ E H Ψ k z s =
      ∑ j ∈ comparisonCells (B.pattern v) block h,
        ∑ χA ∈ primitiveCharacters Q, ∑ χB ∈ primitiveCharacters Q,
          (comparisonSign (B.pattern v) *
            comparisonCellInverse (B.pattern v) block false h ξ j.1 *
            comparisonCellInverse (B.pattern v) block true h ξ j.2) *
          comparisonCellCorrelation (B.pattern v) block h j χA χB
            x Z a₁ a₂ E H Ψ k s := by
  unfold residualStrippedLift
  rw [sum_freeDraw_by_comparisonCells (B.pattern v) block h]
  apply Finset.sum_congr rfl
  intro j hj
  let U := Finset.univ.filter (fun u : FreeDraw (B.pattern v) =>
    comparisonCellPair (B.pattern v) block h u = j)
  have he : (∑ u ∈ U, (freeDrawLaw (B.pattern v) u : ℂ) *
      ∑ n ∈ s u, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
        (freeDrawProduct (B.pattern v) u) *
        strippedMarkedRow (B.pattern v) n
          ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
          (residualUnsharedCoefficient B v z u)) =
      ∑ u ∈ U, ∑ χA ∈ primitiveCharacters Q, ∑ χB ∈ primitiveCharacters Q,
        (comparisonSign (B.pattern v) *
          comparisonCellInverse (B.pattern v) block false h ξ j.1 *
          comparisonCellInverse (B.pattern v) block true h ξ j.2) *
        ((freeDrawLaw (B.pattern v) u : ℂ) *
          star (charValue χA (comparisonFreeProduct (B.pattern v) block false u)) *
          star (charValue χB (comparisonFreeProduct (B.pattern v) block true u)) *
          ∑ n ∈ s u, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
            ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat
            (freeDrawProduct (B.pattern v) u) *
            (comparisonMarkedEndpoint (B.pattern v) block true h j.2 χB n *
              comparisonMarkedEndpoint (B.pattern v) block false h j.1 χA
                ((n : ℤ) + k * (freeDrawProduct (B.pattern v) u : ℤ)).toNat)) := by
    apply Finset.sum_congr rfl
    intro u hu
    have hp := (Finset.mem_filter.mp hu).2
    have hA := congrArg Prod.fst hp
    have hB := congrArg Prod.snd hp
    dsimp only [comparisonCellPair] at hA hB
    simp_rw [strippedMarkedRow_comparison_expansion B v block Q h ξ hc z u j.1 j.2 hA hB]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χA hχA
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χB hχB
    apply Finset.sum_congr rfl
    intro n hn
    ring
  change (∑ u ∈ U, _) = _
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χA hχA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χB hχB
  rw [← Finset.mul_sum]
  rfl

end Erdos821.P5Core
