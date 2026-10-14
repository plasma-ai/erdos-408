import Erdos408.OneSided.Moment.Chain
import Erdos408.OneSided.Moment.Edge
import Erdos408.OneSided.Moment.Phased.Edge
import Erdos408.OneSided.Moment.Phased.Ghost
import Erdos408.OneSided.Moment.Phased.HighRank
import Erdos408.OneSided.Moment.Phased.History

/-!
# Phased chains and the operator bounds

The ingredients of M10 (`blueprint/one_sided_type_ii.md` §13). A *phase* `ψ` assigns to each
birth address a multiplier `ψ_a : Option ℕ → ℂ` of its birth (`none` when the address is
not performed). The phased operators carry these multipliers in their coefficients, at the
operation that creates each birth, so they are still choice operators on the chain states.

* `phasedProduct_eq_sum_history`: the phased product expands into histories with weight
  `w(s, h) ∏_a ψ_a(β_a(s, h))`.
* `exists_phasedGhost_normLe` (M4): every phased ghost has norm at most `C₀`.
* `exists_phasedEdge_normLe` (M4, crude): every phased edge has norm at most `L^{C_e}`.
* `eventually_chainEdge_normLe` (M9): the plain edge has norm at most `L^{-G}`.
* `exists_realized_history_le` (M10, high rank): the absolute history sum constrained by a
  block system of rank `r` is at most `L^{C₁(N+1)} (C₁ exp(-L^{α₋}))^r`.

The norms are `NormLe` for the chain measure at both ends, with a cap `B ≤ L³`.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Phased

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- The phased ghost coefficient: the ghost coefficient times `∏_k ψ_k(k-th batch prime)`. -/
def phasedGhostCoef (N j : ℕ) (ψ : Fin B → Option ℕ → ℂ) (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) : ℂ :=
  chainGhostCoef q x d Y d₀ u v r B N j s c * ∏ k : Fin B, ψ k (batchPrimes x d c.2)[k.1]?

/-- The phased ghost `𝒢^ψ_j`. -/
def phasedGhost (N j : ℕ) (ψ : Fin B → Option ℕ → ℂ) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (multBox B ×ˢ multBox B) (phasedGhostCoef q x d Y d₀ u v r B N j ψ)
    (chainGhostOut x d Y d₀ u v r B)

/-- The phased edge coefficient: the edge coefficient times `∏_i ψ_i(fresh label of group i)`,
with `none` for a promoted label. -/
def phasedEdgeCoef (N : ℕ) (ψ : Fin K → Option ℕ → ℂ) (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) : ℂ :=
  chainEdgeCoef q A₀ x d Y d₀ u v r B N s c *
    ∏ i, ψ i (if (c.2.2.2.1 i).2 then none else some (c.2.2.2.1 i).1)

/-- The phased edge `ℰ^ψ`. -/
def phasedEdge (N : ℕ) (ψ : Fin K → Option ℕ → ℂ) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (edgeChoices x d Y d₀ u v r) (phasedEdgeCoef q A₀ x d Y d₀ u v r B N ψ)
    (chainEdgeOut x d Y d₀ u v r B)

/-- `𝒢^ψ₀ ℰ^ψ 𝒢^ψ₁ ⋯ ℰ^ψ 𝒢^ψ_N` applied to `f`, each operation with the phases of its own
addresses. -/
def phasedProduct (N : ℕ) (ψ : BirthAddr (K := K) x B N → Option ℕ → ℂ)
    (f : ChainState x d Y d₀ u v r B → ℂ) : ChainState x d Y d₀ u v r B → ℂ :=
  (List.finRange N).foldr
    (fun (j : Fin N) g =>
      phasedGhost q x d Y d₀ u v r B N j (fun k => ψ (.inr (.inr (j.castSucc, k))))
        (phasedEdge q A₀ x d Y d₀ u v r B N (fun i => ψ (.inr (.inl (j, i)))) g))
    (phasedGhost q x d Y d₀ u v r B N N (fun k => ψ (.inr (.inr (Fin.last N, k)))) f)

/-- The phased history expansion:
`𝒢^ψ₀ ℰ^ψ ⋯ 𝒢^ψ_N f (s) = ∑_h w(s, h) ∏_{a not initial} ψ_a(β_a(s, h)) f(end(s, h))`. The
initial addresses carry no operation; their phases multiply the initial vector. -/
theorem phasedProduct_eq_sum_history (N : ℕ) (ψ : BirthAddr (K := K) x B N → Option ℕ → ℂ)
    (f : ChainState x d Y d₀ u v r B → ℂ) (s : ChainState x d Y d₀ u v r B) :
    phasedProduct q A₀ x d Y d₀ u v r B N ψ f s =
      ∑ h ∈ histories x d Y d₀ u v r B N, chainWeight q A₀ s h *
        (∏ a : (Fin N × Fin K) ⊕ (Fin (N + 1) × Fin B), ψ (.inr a) (births s h (.inr a))) *
          f (chainEnd s h) := by
  -- expand with the phased coefficients at each visit and edge, then collect the phases
  refine (foldr_finRange_eq_sum_history f N
    (fun j => phasedGhostCoef q x d Y d₀ u v r B N j fun k => ψ (.inr (.inr (j, k))))
    (fun j => phasedEdgeCoef q A₀ x d Y d₀ u v r B N fun i => ψ (.inr (.inl (j, i)))) s).trans ?_
  refine sum_congr rfl fun h _ => ?_
  simp only [phasedGhostCoef, phasedEdgeCoef, prod_mul_distrib, Fintype.prod_sum_type,
    Fintype.prod_prod_type, births, chainWeight]
  ring

end Phased

/-- M4, the ghost: for `B ≤ L³`, every phased ghost with multipliers of modulus at most one
has norm at most `C₀` for the chain measure. -/
theorem exists_phasedGhost_normLe {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ (Y d₀ u v r : ℝ) (B N j : ℕ), (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
      ∀ ψ : Fin B → Option ℕ → ℂ, (∀ k o, ‖ψ k o‖ ≤ 1) →
        NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
          (fun s => chainMeasure q x d Y d₀ u v r B N s)
          (phasedGhost q x d Y d₀ u v r B N j ψ) C₀ := by
  obtain ⟨C₀, hC₀⟩ := exists_ghostChoiceOp_normLe (K := K) (C := C) (CX := CX) (ahi := ahi)
    (g := g) hq hq₁ halo
  refine ⟨C₀, ?_⟩
  filter_upwards [hC₀] with x hx d hd Y d₀ u v r B N j _ hN ψ hψ
  subst hN
  -- the multipliers have modulus at most one, so the phased coefficients are dominated
  refine hx d hd Y d₀ u v r B j _ fun s c => ?_
  rw [phasedGhostCoef, norm_mul, norm_prod]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (prod_le_one₀ (fun k _ => norm_nonneg _) fun k _ => hψ k _)

/-- M4, the crude edge: for `B ≤ L³`, every phased edge with multipliers of modulus at most
one has norm at most `L^{C_e}` for the chain measure, uniformly in the root box. -/
theorem exists_phasedEdge_normLe {q C CX alo ahi g A₀ : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) (hg : 0 < g) :
    ∃ Ce : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
      ∀ ψ : Fin K → Option ℕ → ℂ, (∀ i o, ‖ψ i o‖ ≤ 1) →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (phasedEdge q A₀ x d (2 ^ j) (2 ^ k) u v r B N ψ) (Real.log x ^ Ce) := by
  obtain ⟨Ce, hCe⟩ := exists_edgeChoiceOp_normLe (K := K) (C := C) (CX := CX) (ahi := ahi)
    A₀ hq hq₁ halo hg
  refine ⟨Ce, ?_⟩
  filter_upwards [hCe] with x hx d hd j k u v r _ _ _ _ _ _ B N hB hN ψ hψ
  subst hN
  -- the multipliers have modulus at most one, so the phased coefficients are dominated
  refine hx d hd (2 ^ j) (2 ^ k) u v r B (one_le_pow₀ (by norm_num)) (by positivity) hB _
    fun s c => ?_
  rw [phasedEdgeCoef, norm_mul, norm_prod]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => hψ i _)

/-- M9, the signed edge: for `K ≥ K₀` and `B ≤ L³`, the edge has norm at most `L^{-G}` for the
chain measure, uniformly in the root box. -/
theorem eventually_chainEdge_normLe {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hC : 0 < C) (hD : 0 < Dstar) (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5)
    (hK : bandThreshold Dstar C ≤ K) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (chainEdge q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N)
          (Real.log x ^ (-edgePrec Dstar C)) :=
  eventually_chainEdge_normLe_of_parts hq hq₁ hC hD hCX halo hahi hK hg

open scoped Classical in
/-- M10, high rank: for `B ≤ L³`, the absolute history sum constrained by a block system of
rank `r` is at most `L^{C₁(N+1)} (C₁ exp(-L^{α₋}))^r`. -/
theorem exists_realized_history_le {q C CX alo ahi g A₀ : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) :
    ∃ C₁ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
      ∀ 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N),
        ∑ s, chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s *
            ‖chainInit x d (2 ^ j) (2 ^ k) u v r B s‖ *
          ∑ h ∈ histories x d (2 ^ j) (2 ^ k) u v r B N,
            ‖chainWeight q A₀ s h‖ * ‖chainInit x d (2 ^ j) (2 ^ k) u v r B (chainEnd s h)‖ *
              ∏ C ∈ 𝒞, (if BlockRealized (births s h) C then 1 else 0) ≤
          Real.log x ^ (C₁ * (N + 1)) *
            (C₁ * Real.exp (-Real.log x ^ alo)) ^ blockRank 𝒞 :=
  exists_realized_history_le_aux hq hq₁ halo

end Erdos408.OneSided
