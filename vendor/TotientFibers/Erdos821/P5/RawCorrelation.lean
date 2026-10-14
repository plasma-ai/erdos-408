import Erdos821.P5.FullResidualStripping

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem freeDrawProduct_eq_one_of_empty {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (hν : ∀ g, ν.changed g = ∅)
    (u : FreeDraw ν) : freeDrawProduct ν u = 1 := by
  unfold freeDrawProduct
  apply Finset.prod_eq_one
  intro i hi
  have hmem := i.2.property
  have hf : False := by simpa [hν i.1] using hmem
  exact False.elim hf

theorem raw_pattern_t {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (hν : ∀ g, ν.changed g = ∅) :
    ν.t = fun _ => ell := by
  funext g
  simp [Blueprint.Graph.Pattern.t, hν g]

theorem raw_residual_coefficient {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (raw : Fin B.count)
    (hc : ∀ a b u, (B.pattern raw).coefficient a b u = 1)
    (z₀ : SharedDraw (B.pattern raw)) (u : FreeDraw (B.pattern raw)) :
    residualUnsharedCoefficient B raw z₀ u = fun _ _ => 1 := by
  funext r s
  exact hc _ _ _

theorem raw_stripped_marked_row {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (raw : Fin B.count)
    (he : ∀ g, (B.pattern raw).changed g = ∅)
    (hc : ∀ a b u, (B.pattern raw).coefficient a b u = 1)
    (z₀ : SharedDraw (B.pattern raw)) (u : FreeDraw (B.pattern raw)) (n n' : ℕ) :
    strippedMarkedRow (B.pattern raw) n n' (residualUnsharedCoefficient B raw z₀ u) =
      ((markWeight G P.q (fun _ => P.ell) n * markWeight G P.q (fun _ => P.ell) n' : ℝ) : ℂ) := by
  rw [raw_residual_coefficient B raw hc z₀ u]
  unfold strippedMarkedRow
  simpa only [raw_pattern_t (B.pattern raw) he, mul_one] using
    unshared_marked_constant_row P (B.pattern raw) n n' (1 : ℂ)

/-- Exact identification of the raw stripped pattern with the frozen
shiftCorrelation, retaining its real interval endpoints and signed shift. -/
theorem raw_stripped_lift_eq_shiftCorrelation {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (raw : Fin B.count)
    (he : ∀ g, (B.pattern raw).changed g = ∅)
    (hc : ∀ a b u, (B.pattern raw).coefficient a b u = 1)
    (hV : ∀ g, G.graph.V g ≠ 0) (z₀ : SharedDraw (B.pattern raw))
    (x Z a₁ a₂ lo hi : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hX : 1 ≤ lo * Z) (hk : |(k : ℝ)| ≤ lo * Z / 2) :
    residualStrippedLift B raw x Z a₁ a₂ E H Ψ k z₀
      (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern raw) u)) =
      shiftCorrelation P G x Z a₁ a₂ k E H Ψ lo hi := by
  unfold residualStrippedLift
  simp_rw [freeDrawProduct_eq_one_of_empty (B.pattern raw) he,
    raw_stripped_marked_row B raw he hc z₀,
    Nat.cast_one, mul_one]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, freeDrawLaw_sum (B.pattern raw) hV,
    Complex.ofReal_one, one_mul]
  unfold shiftCorrelation
  simp only [cutoffRoots, Nat.cast_one, mul_one]
  apply Finset.sum_congr rfl
  intro n hn
  have hncut : n ∈ cutoffRoots lo hi Z 1 := by
    simpa only [cutoffRoots, Nat.cast_one, mul_one] using hn
  have hX' : 1 ≤ lo * Z * (1 : ℕ) := by simpa using hX
  obtain ⟨hn1, hnlo, hnhi, hn'pos, hn'hi⟩ :=
    cutoffRoots_ranges lo hi Z 1 k hlo hhi hZ (by norm_num) hX' hk n hncut
  simp only [Nat.cast_one, mul_one] at hn'pos
  have hnpos : 0 < n := by omega
  rw [if_pos ⟨hnpos, hn'pos⟩]
  have hshift : (((n : ℤ) + k).toNat : ℝ) = (n : ℝ) + (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn'pos.le
  simp only [strippedLiftScalar, harmonicCutoff, Nat.cast_one, mul_one, div_one,
    Int.cast_natCast, Int.cast_add, hshift, Complex.ofReal_mul]
  ring

end Erdos821.P5Core
