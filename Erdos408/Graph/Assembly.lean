import Erdos408.Graph.Comparison
import Erdos408.Graph.Pairing

/-!
# The expanded family

From an upstream family in residual form, with raw pattern `raw` and blocks
`block`, the comparison patterns of `GraphTransference` are the terms of its
other patterns (`famIndex`, enumerated by `famPoint`). Upstream's pairing of
endpoints of the position alone is the raw pattern pairing plus the term
pairings (`pairing_eq_family`), and the term weights sum to at most
`ξ⁻² Q⁴` times the pattern mass (`sum_norm_termWeight_family_le`).
-/

namespace Erdos408.Graph

open Erdos821.Blueprint.Graph
open Erdos821.Blueprint.Analytic (cell charValue primitiveCharacters CharacterIndex)
open scoped Classical

variable {G : PrimeGroups} {J m : ℕ}
  {q₀ c₀ C₀ vlo vhi : ℝ} {hq₀ : 0 < q₀} {hq₁ : q₀ < 1} {hc₀ : 0 < c₀} {hvlo : 0 < vlo}

section

variable (B : Family (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo) G J m) (raw : Fin B.count)
  (block : G.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)

/-- The terms of all comparison patterns. -/
noncomputable def famIndex :
    Finset (Σ _ : Fin B.count, ℤ × CharacterIndex Q × ℤ × CharacterIndex Q) :=
  (Finset.univ.erase raw).sigma fun v => terms (B.pattern v) block Q h ξ

/-- The `ν`-th term of the comparison patterns. -/
noncomputable def famPoint (ν : Fin (famIndex B raw block Q h ξ).card) :
    Σ _ : Fin B.count, ℤ × CharacterIndex Q × ℤ × CharacterIndex Q :=
  ((famIndex B raw block Q h ξ).equivFin.symm ν).val

/-- Summing over the enumerated terms is summing over the comparison patterns
and their terms. -/
lemma sum_famPoint {R : Type*} [AddCommMonoid R]
    (Φ : (Σ _ : Fin B.count, ℤ × CharacterIndex Q × ℤ × CharacterIndex Q) → R) :
    ∑ ν, Φ (famPoint B raw block Q h ξ ν) =
      ∑ v ∈ Finset.univ.erase raw, ∑ τ ∈ terms (B.pattern v) block Q h ξ, Φ ⟨v, τ⟩ := by
  unfold famPoint
  rw [Equiv.sum_comp (famIndex B raw block Q h ξ).equivFin.symm fun σ => Φ σ.val,
    Finset.sum_coe_sort (famIndex B raw block Q h ξ) Φ, famIndex, Finset.sum_sigma]

end

/-- Upstream's pairing of endpoints of the position alone is the raw pattern
pairing plus the pairings of all terms of the comparison patterns. -/
theorem pairing_eq_family (B : Family (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo) G J m)
    (raw : Fin B.count) (block : G.BigGroup → Bool) (Q : ℕ) {h ξ : ℝ} (hξ : 0 < ξ)
    (hraw : ∀ g, (B.pattern raw).changed g = ∅)
    (hraw' : ∀ a b u, (B.pattern raw).coefficient a b u = 1)
    (hcoef : ∀ v, v ≠ raw → ∀ a b u, (B.pattern v).coefficient a b u =
      -((-1 : ℂ) ^ (∑ g, ((B.pattern v).changed g).card)) *
        selectedKernel (B.pattern v) block false Q h ξ
          (selectedProduct (B.pattern v) block false u)
          (selectedEndpoint (B.pattern v) block false b) *
        selectedKernel (B.pattern v) block true Q h ξ
          (selectedProduct (B.pattern v) block true u)
          (selectedEndpoint (B.pattern v) block true a))
    (hV : ∀ g, G.V g ≠ 0) (ζ X : ℝ) (S S' : Finset ℕ) (f g : ℕ → ℂ)
    (hS : ∀ n ∈ S, X ≤ n ∧ (n : ℝ) < 2 * X) (hg : ∀ n ∉ S', g n = 0) :
    (B.model 1 ζ).pairing X (targets (B.model 1 ζ) S') (extend S f) (fun z => g z.1.toNat) =
      patternPairing G.primes q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) ζ S f g +
        ∑ ν, patternPairing G.primes q₀
          (fun g => blockSlots (B.pattern (famPoint B raw block Q h ξ ν).1) block false g ∪
            blockSlots (B.pattern (famPoint B raw block Q h ξ ν).1) block true g)
          (termKernel (B.pattern (famPoint B raw block Q h ξ ν).1) block h
            (famPoint B raw block Q h ξ ν).2) ζ S f g := by
  rw [pairing_eq_sum _ X S S' f g hS]
  change ∑ v : Fin B.count, rawPairing (B.model 1 ζ) v S S' f g = _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ raw)]
  congr 1
  · rw [rawPairing_eq B ζ raw (fun _ _ _ => 1) (fun a b u => hraw' _ _ _) hV S S' f g hg]
    congr 1
    exact funext hraw
  · rw [sum_famPoint B raw block Q h ξ fun σ => patternPairing G.primes q₀
      (fun g => blockSlots (B.pattern σ.1) block false g ∪ blockSlots (B.pattern σ.1) block true g)
      (termKernel (B.pattern σ.1) block h σ.2) ζ S f g]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [rawPairing_comparison B ζ v block Q hξ (hcoef v (Finset.ne_of_mem_erase hv)) hV S S' f g
      hg]
    refine Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    exact funext fun g => (blockSlots_disjoint_union _ block g).2.symm

/-- The term weights of all comparison patterns sum to at most `ξ⁻² Q⁴` times
the pattern mass. -/
lemma sum_norm_termWeight_family_le
    (B : Family (fixedData q₀ c₀ C₀ vlo vhi hq₀ hq₁ hc₀ hvlo) G J m)
    (raw : Fin B.count) (block : G.BigGroup → Bool) (Q : ℕ) {h ξ : ℝ} (hξ : 0 < ξ)
    (hcoef : ∀ v, v ≠ raw → ∀ a b u, (B.pattern v).coefficient a b u =
      -((-1 : ℂ) ^ (∑ g, ((B.pattern v).changed g).card)) *
        selectedKernel (B.pattern v) block false Q h ξ
          (selectedProduct (B.pattern v) block false u)
          (selectedEndpoint (B.pattern v) block false b) *
        selectedKernel (B.pattern v) block true Q h ξ
          (selectedProduct (B.pattern v) block true u)
          (selectedEndpoint (B.pattern v) block true a))
    (hne : ∀ v, v ≠ raw → ∃ g, ((B.pattern v).changed g).Nonempty) (hV : ∀ g, G.V g ≠ 0) :
    ∑ ν, ‖termWeight (B.pattern (famPoint B raw block Q h ξ ν).1) block h
        (famPoint B raw block Q h ξ ν).2‖ ≤
      ξ⁻¹ ^ 2 * (Q : ℝ) ^ 4 * (B.model 1 0).patternMass := by
  rw [sum_famPoint B raw block Q h ξ fun σ => ‖termWeight (B.pattern σ.1) block h σ.2‖]
  have hle : ∀ v ∈ Finset.univ.erase raw,
      ∑ τ ∈ terms (B.pattern v) block Q h ξ, ‖termWeight (B.pattern v) block h τ‖ ≤
        ξ⁻¹ ^ 2 * (Q : ℝ) ^ 4 *
          sSup (Set.range fun z : G.BigLabels (J + 1) × G.BigLabels (J + 1) × G.BigAux J =>
            ‖(B.pattern v).coefficient z.1 z.2.1 z.2.2‖) := by
    intro v hv
    have hv' := Finset.ne_of_mem_erase hv
    obtain ⟨g, i, -⟩ := hne v hv'
    exact sum_norm_termWeight_le (B.pattern v) block hξ hV (Fin.pos i) (hcoef v hv')
  refine (Finset.sum_le_sum hle).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun v _ _ => sSup_norm_nonneg (B.pattern v)

end Erdos408.Graph
