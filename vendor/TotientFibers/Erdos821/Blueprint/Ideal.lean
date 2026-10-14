import Erdos821.Blueprint.Transference

/-! P4: an actual raw-plus-comparison model, independent of θ and ζ. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint.Graph

structure Family (F : FixedData) (P : PrimeGroups) (J m : ℕ) where
  count : ℕ
  pattern : Fin count → Pattern P J F.ell m

def Family.model {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (B : Family F P J m) (k : ℤ) (ζ : ℝ) : Model F P J m :=
  { patternCount := B.count, pattern := B.pattern, k := k, zeta := ζ }

def intervalBigGroups (P : PrimeGroups) : Prop :=
  ∀ g : P.BigGroup, ∃ lo hi : ℝ, ∀ p : ℕ,
    p ∈ P.primes g.val ↔ p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi

def selectedProduct {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (u : P.BigAux J) : ℕ :=
  ∏ g : P.BigGroup, ∏ i : Fin J,
    if block g = side ∧ i ∈ ν.changed g.val then (u g i).val else 1

def selectedEndpoint {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (a : P.BigLabels (J + ell)) : ℕ :=
  ∏ g : P.BigGroup, ∏ i : Fin J,
    if block g = side ∧ i ∈ ν.changed g.val then (a g (ν.slot i)).val else 1

def selectedCellMass {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (h : ℝ) (j : ℤ) : ℝ :=
  ∑ u : P.BigAux J, if Analytic.cell h (selectedProduct ν block side u) = j
    then ν.bigAuxMass u else 0

def selectedKernel {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (Q : ℕ) (h ξ : ℝ) (D X : ℕ) : ℂ :=
  let v := selectedCellMass ν block side h (Analytic.cell h X)
  if Analytic.cell h D = Analytic.cell h X ∧ ξ ≤ v then
    (v : ℂ)⁻¹ * ∑ χ ∈ Analytic.primitiveCharacters Q,
      star (Analytic.charValue χ D) * Analytic.charValue χ X
  else 0

/-- Explicit shape of all signed comparison coefficients; two nonempty blocks. -/
def Family.Residual {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (B : Family F P J m) (Q : ℕ) (h ξ : ℝ) : Prop :=
  ∃ raw : Fin B.count, ∃ block : P.BigGroup → Bool,
    (∀ g, (B.pattern raw).changed g = ∅) ∧
    (∀ a b u, (B.pattern raw).coefficient a b u = 1) ∧
    (∀ v, v ≠ raw →
      (∀ g i, i ∈ (B.pattern v).changed g → i.val < m) ∧
      (∀ side : Bool, ∃ g : P.BigGroup,
        block g = side ∧ ((B.pattern v).changed g.val).Nonempty) ∧
      ∀ a b u,
        let ν := B.pattern v
        ν.coefficient a b u =
          -((-1 : ℂ) ^ (∑ g, (ν.changed g).card)) *
          selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
            (selectedEndpoint ν block false b) *
          selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
            (selectedEndpoint ν block true a))

def IdealConstruction : Prop :=
  ∀ F : FixedData, ∀ E C₄ : ℝ, 0 < E → 0 ≤ C₄ →
    ∃ m J₀ : ℕ, ∃ C₁ qexp hexp ξexp : ℝ,
      0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ J : ℕ, J₀ ≤ J → ∀ᶠ x : ℝ in atTop,
        ∀ P : PrimeGroups, P.Admissible F x → intervalBigGroups P →
          ∃ B : Family F P J m,
            B.Residual ⌊L x ^ qexp⌋₊ (L x ^ (-hexp)) (L x ^ (-ξexp)) ∧
            (B.model 1 0).patternMass ≤ L x ^ C₁ ∧
            ∀ θ ζ : ℝ, |ζ| ≤ L x ^ C₄ →
              NormBound (P.idealMass (M := J + F.ell))
                ((B.model 1 ζ).idealKernel θ) (L x ^ (-E))

end Erdos821.Blueprint.Graph
namespace Erdos821.Blueprint

def ComparisonEstimate : Prop :=
  ∀ (P : Analytic.Geometry) (m : ℕ) (A C₄ : ℝ), 0 < A → 0 ≤ C₄ →
    ∃ qexp hexp ξexp : ℝ, 0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ᶠ x in atTop, ∀ G : Analytic.PrimeGroups, Analytic.Admissible P x G →
        ∀ a b, Analytic.bigSlots G a m → Analytic.bigSlots G b m →
          ∀ (α ζ : ℝ) (f : Analytic.Tuple G b → ℂ) (g : Analytic.Tuple G a → ℂ),
            |ζ| ≤ Analytic.L x ^ C₄ →
            ‖Analytic.comparisonError G a b ⌊Analytic.L x ^ qexp⌋₊
                (Analytic.L x ^ (-hexp)) (Analytic.L x ^ (-ξexp)) α ζ f g‖ ≤
              Analytic.L x ^ (-A) * Analytic.tupleNorm G b f * Analytic.tupleNorm G a g

structure IdealInputs : Prop where
  comparison : ComparisonEstimate
  construction : Graph.IdealConstruction

/-- P4 boundary: integer bilinear, character cells, tuple collapse and probe decomposition. -/
abbrev ideal_inputs_statement : Prop :=
  ∀ (_hc : ClassicalInputs),
    IdealInputs
end Erdos821.Blueprint
