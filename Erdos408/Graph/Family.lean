module

public import Erdos408.Graph.Reindex

/-!
# The family conclusion of `GraphTransference`

`FamilyBound` is the conclusion of `GraphTransference` for given groups at
scale `x`: a family of comparison patterns with the transferred pairing
bound. It transports along a reindexing of the groups (`FamilyBound.reindex`),
so it suffices to construct it for groups indexed by `Fin n`.
-/

@[expose] public section

namespace Erdos408.Graph

/-- The conclusion of `GraphTransference` for the groups `P` with big groups
`big`, at scale `x`. -/
def FamilyBound (q₀ : ℝ) (m₀ J : ℕ) (C₁ C E C₃ C₄ x : ℝ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι) : Prop :=
  ∃ (N : ℕ) (A B : Fin N → ι → Finset (Fin J)) (β : Fin N → ℂ)
    (φ φ' ψ ψ' : Fin N → ℕ → ℂ) (U U' : Fin N → ℝ),
    -- the comparison patterns
    (∀ ν g, Disjoint (A ν g) (B ν g) ∧ (A ν g ∪ B ν g).card ≤ m₀) ∧
    (∀ ν, ∀ g ∉ big, A ν g = ∅ ∧ B ν g = ∅) ∧
    (∀ ν, (∃ g, (A ν g).Nonempty) ∧ ∃ g, (B ν g).Nonempty) ∧
    (∀ ν n, ‖φ ν n‖ ≤ 1 ∧ ‖φ' ν n‖ ≤ 1 ∧ ‖ψ ν n‖ ≤ 1 ∧ ‖ψ' ν n‖ ≤ 1) ∧
    (∀ ν n, φ ν n ≠ 0 → U ν ≤ n ∧ n ≤ Real.exp 1 * U ν) ∧
    (∀ ν n, φ' ν n ≠ 0 → U' ν ≤ n ∧ n ≤ Real.exp 1 * U' ν) ∧
    ∑ ν, ‖β ν‖ ≤ Real.log x ^ C₁ ∧
    -- the transferred pairing
    ∀ ζ : ℝ, |ζ| ≤ Real.log x ^ C₄ → ∀ X : ℝ, √x ≤ X → X ≤ x ^ 2 →
      ∀ (S S' : Finset ℕ) (f g : ℕ → ℂ), (∀ n ∈ S, X ≤ n ∧ (n : ℝ) < 2 * X) →
        (∀ n, ‖f n‖ ≤ 1) → (∀ n ∉ S', g n = 0) →
        physicalNormSq P (J + 1) S f ≤ X * Real.log x ^ (2 * C₃) →
        physicalNormSq P (J + 1) S' g ≤ X * Real.log x ^ (2 * C₃) →
        ‖patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) ζ S f g +
            ∑ ν, patternPairing P q₀ (fun h => A ν h ∪ B ν h)
              (fun p p' a => β ν * φ ν (slotProduct (A ν) a) * φ' ν (slotProduct (B ν) a) *
                ψ ν (slotProduct (A ν) fun h i => p' h i.castSucc) *
                ψ' ν (slotProduct (B ν) fun h i => p h i.castSucc)) ζ S f g‖ ≤
          C * X * Real.log x ^ (-E + 2 * C₃)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The slot product of transported slots and labels. -/
lemma slotProduct_reindex (e : ι ≃ κ) {J : ℕ} (A : κ → Finset (Fin J)) (a : ι → Fin J → ℕ) :
    slotProduct (fun g => A (e g)) a = slotProduct A fun k => a (e.symm k) := by
  unfold slotProduct
  rw [← Equiv.prod_comp e]
  simp only [Equiv.symm_apply_apply]

/-- `FamilyBound` for the reindexed groups gives it for the original ones. -/
lemma FamilyBound.reindex (e : ι ≃ κ) {q₀ : ℝ} {m₀ J : ℕ} {C₁ C E C₃ C₄ x : ℝ}
    {P : ι → Finset ℕ} {big : Finset ι}
    (h : FamilyBound q₀ m₀ J C₁ C E C₃ C₄ x (fun k => P (e.symm k)) (big.map e.toEmbedding)) :
    FamilyBound q₀ m₀ J C₁ C E C₃ C₄ x P big := by
  obtain ⟨N, A, B, β, φ, φ', ψ, ψ', U, U', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
  refine ⟨N, fun ν g => A ν (e g), fun ν g => B ν (e g), β, φ, φ', ψ, ψ', U, U',
    fun ν g => h₁ ν (e g), fun ν g hg => h₂ ν (e g) (by simpa using hg), fun ν => ?_,
    h₄, h₅, h₆, h₇, ?_⟩
  · obtain ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩ := h₃ ν
    exact ⟨⟨e.symm g, by simpa using hg⟩, ⟨e.symm g', by simpa using hg'⟩⟩
  intro ζ hζ X hX₁ hX₂ S S' f g hS hf hg hnf hng
  have := h₈ ζ hζ X hX₁ hX₂ S S' f g hS hf hg (by rwa [physicalNormSq_reindex])
    (by rwa [physicalNormSq_reindex])
  have hraw := patternPairing_reindex e P q₀ (fun _ => (∅ : Finset (Fin J)))
    (fun _ _ _ => 1) ζ S f g
  rw [← hraw]
  convert this using 4 with ν
  rw [← patternPairing_reindex e]
  simp only [Equiv.apply_symm_apply, slotProduct_reindex]

end Erdos408.Graph
