import Erdos821.P5.ComparisonMarkedSeparation

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

def comparisonSign {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) : ℂ := -((-1 : ℂ) ^ (∑ g, (ν.changed g).card))

theorem comparisonSign_norm {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) : ‖comparisonSign ν‖ = 1 := by
  simp [comparisonSign, norm_pow]

/-- The literal comparison coefficient, with the two block roles retained. -/
def HasComparisonCoefficient {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G J ell m) (block : G.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ) : Prop :=
  ∀ a b u, ν.coefficient a b u = comparisonSign ν *
    selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
      (selectedEndpoint ν block false b) *
    selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
      (selectedEndpoint ν block true a)

theorem residual_comparison_coefficients {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family F G J m) (hB : B.Residual Q h ξ) :
    ∃ raw : Fin B.count, ∃ block : G.BigGroup → Bool,
      (∀ g, (B.pattern raw).changed g = ∅) ∧
      (∀ a b u, (B.pattern raw).coefficient a b u = 1) ∧
      ∀ v, v ≠ raw →
        (∀ g i, i ∈ (B.pattern v).changed g → i.val < m) ∧
        (∀ side : Bool, ∃ g : G.BigGroup,
          block g = side ∧ ((B.pattern v).changed g.val).Nonempty) ∧
        HasComparisonCoefficient (B.pattern v) block Q h ξ := by
  obtain ⟨raw, block, he, hc, hv⟩ := hB
  exact ⟨raw, block, he, hc, fun v hvr => hv v hvr⟩

theorem residualUnsharedCoefficient_cell_expansion {F : FixedData}
    {G : Blueprint.Graph.PrimeGroups} {J m : ℕ}
    (B : Family F G J m) (v : Fin B.count) (block : G.BigGroup → Bool)
    (Q : ℕ) (h ξ : ℝ) (hc : HasComparisonCoefficient (B.pattern v) block Q h ξ)
    (z : SharedDraw (B.pattern v)) (u : FreeDraw (B.pattern v))
    (jA jB : ℤ)
    (hA : cell h (comparisonFreeProduct (B.pattern v) block false u) = jA)
    (hB : cell h (comparisonFreeProduct (B.pattern v) block true u) = jB)
    (r s : UnsharedDraw (B.pattern v)) :
    residualUnsharedCoefficient B v z u r s =
      ∑ χA ∈ primitiveCharacters Q, ∑ χB ∈ primitiveCharacters Q,
        (comparisonSign (B.pattern v) *
          comparisonCellInverse (B.pattern v) block false h ξ jA *
          comparisonCellInverse (B.pattern v) block true h ξ jB *
          star (charValue χA (comparisonFreeProduct (B.pattern v) block false u)) *
          star (charValue χB (comparisonFreeProduct (B.pattern v) block true u))) *
        (comparisonMarkTest (B.pattern v) block true h jB χB r *
          comparisonMarkTest (B.pattern v) block false h jA χA s) := by
  unfold residualUnsharedCoefficient
  rw [hc]
  simp_rw [selectedProduct_assembleAux, selectedEndpoint_assembleLabels]
  rw [selectedKernel_cell_expansion _ block false Q h ξ jA _ _ hA,
    selectedKernel_cell_expansion _ block true Q h ξ jB _ _ hB]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χA hχA
  apply Finset.sum_congr rfl
  intro χB hχB
  dsimp only [comparisonMarkTest]
  ring

/-- Exact cell/character separation of the actual stripped row. The two
marked endpoint functions no longer have any free-label argument. -/
theorem strippedMarkedRow_comparison_expansion {P : Geometry} {G : PrimeGroups}
    {J m : ℕ} (B : Family P.graph G.graph J m) (v : Fin B.count)
    (block : G.graph.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (hc : HasComparisonCoefficient (B.pattern v) block Q h ξ)
    (z : SharedDraw (B.pattern v)) (u : FreeDraw (B.pattern v))
    (jA jB : ℤ)
    (hA : cell h (comparisonFreeProduct (B.pattern v) block false u) = jA)
    (hB : cell h (comparisonFreeProduct (B.pattern v) block true u) = jB)
    (n n' : ℕ) :
    strippedMarkedRow (B.pattern v) n n' (residualUnsharedCoefficient B v z u) =
      ∑ χA ∈ primitiveCharacters Q, ∑ χB ∈ primitiveCharacters Q,
        (comparisonSign (B.pattern v) *
          comparisonCellInverse (B.pattern v) block false h ξ jA *
          comparisonCellInverse (B.pattern v) block true h ξ jB *
          star (charValue χA (comparisonFreeProduct (B.pattern v) block false u)) *
          star (charValue χB (comparisonFreeProduct (B.pattern v) block true u))) *
        (comparisonMarkedEndpoint (B.pattern v) block true h jB χB n *
          comparisonMarkedEndpoint (B.pattern v) block false h jA χA n') := by
  have he := funext fun r => funext fun s =>
    residualUnsharedCoefficient_cell_expansion B v block Q h ξ hc z u jA jB hA hB r s
  rw [he, strippedMarkedRow_sum]
  apply Finset.sum_congr rfl
  intro χA hχA
  rw [strippedMarkedRow_sum]
  apply Finset.sum_congr rfl
  intro χB hχB
  rw [strippedMarkedRow_smul, strippedMarkedRow_mul]
  rfl

end Erdos821.P5Core
