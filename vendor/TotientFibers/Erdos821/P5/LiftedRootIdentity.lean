import Erdos821.P5.LiftedPatternRow

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

theorem patternTarget_shared_int {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (A : Model F G J m) (ν : Pattern G J F.ell m)
    (z : SharedDraw ν) (r : UnsharedDraw ν) (u : G.Aux J) (w : ℤ) :
    patternTarget A ν u ((sharedDrawProduct ν z : ℤ) * w) (assembleLabels ν z r) =
      (sharedDrawProduct ν z : ℤ) * (w + A.k * (freeProduct ν u : ℤ)) := by
  rw [patternTarget, pattern_D_split, sharedProduct_assemble, Nat.cast_mul]
  ring

/-- Exact finite-root identity for an actual physical pattern with the
harmonic cutoff inserted. Every source/target support condition remains;
no shared or free overlap is discarded. -/
theorem lifted_pattern_root_identity {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (A : Model P.graph G.graph J m) (ν : Pattern G.graph J P.ell m)
    (u : G.graph.Aux J) (hV : ∀ g, G.graph.V g ≠ 0) (S T : Finset ℤ)
    (hS : ∀ n ∈ S, 0 < n) (hT : ∀ n ∈ T, 0 < n)
    (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (hζ : A.zeta = -a₁ - a₂) :
    (∑ n ∈ S, ∑ a : A.Labels, ∑ b : A.Labels,
      gatedPatternTerm A ν u T (liftedEndpoint A x E (-a₁)) (liftedEndpoint A x H a₂)
        (harmonicCutoff Ψ Z) n a b) =
      ∑ z : SharedDraw ν, ∑ w ∈ strippedRoots S (sharedDrawProduct ν z),
        if 0 < w + A.k * (freeProduct ν u : ℤ) then
          if (sharedDrawProduct ν z : ℤ) * (w + A.k * (freeProduct ν u : ℤ)) ∈ T then
            (sharedDrawLaw ν z : ℂ) *
              strippedLiftScalar G x Z a₁ a₂ E H Ψ w.toNat
                (w + A.k * (freeProduct ν u : ℤ)).toNat (freeProduct ν u) *
              physicalSharedRow A ν z w.toNat (w + A.k * (freeProduct ν u : ℤ)).toNat
                (bannedPatternCoefficient A ν u z)
          else 0
        else 0 := by
  rw [sum_shared_pattern_roots A ν u S T (fun n hn => (hS n hn).le)]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hwS
  have hw := strippedRoots_positive (sharedDrawProduct_pos ν z) hS hwS
  by_cases hw' : 0 < w + A.k * (freeProduct ν u : ℤ)
  · rw [if_pos hw']
    have hwn : 0 < w.toNat := by omega
    have hw'n : 0 < (w + A.k * (freeProduct ν u : ℤ)).toNat := by omega
    have hshift : ((w + A.k * (freeProduct ν u : ℤ)).toNat : ℤ) =
        (w.toNat : ℤ) + A.k * (freeProduct ν u : ℤ) := by
      simp only [Int.toNat_of_nonneg hw.le, Int.toNat_of_nonneg hw'.le]
    simpa only [Nat.cast_mul, Int.toNat_of_nonneg hw.le, Int.toNat_of_nonneg hw'.le] using
      sum_lifted_shared_row A ν z u hV T x Z a₁ a₂ E H Ψ
        w.toNat (w + A.k * (freeProduct ν u : ℤ)).toNat hwn hw'n hshift hζ
  · rw [if_neg hw']
    have hnotT : (sharedDrawProduct ν z : ℤ) * (w + A.k * (freeProduct ν u : ℤ)) ∉ T := by
      intro ht
      have hp := hT _ ht
      have hDR : (0 : ℤ) < sharedDrawProduct ν z := by exact_mod_cast sharedDrawProduct_pos ν z
      exact hw' ((mul_pos_iff_of_pos_left hDR).mp hp)
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro s hs
    simp only [gatedPatternTerm, patternTarget_shared_int, hnotT, if_false, mul_zero]

end Erdos821.P5Core
