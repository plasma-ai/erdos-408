import Erdos821.P5.FullRootGates

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- The actual residual family on full finite positive root ranges, with
the cutoff inserted before any transference or Fourier separation. -/
def fullResidualLift {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (x Y Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v)) : ℂ :=
  ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v), (freeDrawLaw (B.pattern v) u : ℂ) *
    ∑ n ∈ positiveRoots Y, ∑ a : (B.model k ζ).Labels, ∑ b : (B.model k ζ).Labels,
      gatedPatternTerm (B.model k ζ) (B.pattern v) (assembleAux (B.pattern v) u (unused v))
        (positiveRoots Y) (liftedEndpoint (B.model k ζ) x E (-a₁))
        (liftedEndpoint (B.model k ζ) x H a₂) (harmonicCutoff Ψ Z) n a b

theorem full_residual_lift_eq_averaged {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Blueprint.Graph.Family P.graph G.graph J m) (x Y Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v)) (lo hi : ℝ)
    (hV : ∀ g, G.graph.V g ≠ 0) (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hΨ : Function.support Ψ ⊆ Set.Icc lo hi)
    (hX : ∀ v u, 1 ≤ lo * Z * freeDrawProduct (B.pattern v) u)
    (hk : ∀ v (u : FreeDraw (B.pattern v)), |(k : ℝ)| ≤ lo * Z / 2)
    (hY : ∀ v u z, (sharedDrawProduct (B.pattern v) z : ℝ) *
      ((hi + lo) * Z * freeDrawProduct (B.pattern v) u) ≤ Y)
    (hζ : ζ = -a₁ - a₂) :
    fullResidualLift B x Y Z a₁ a₂ E H Ψ k ζ unused =
      ∑ v : Fin B.count, residualAveragedLift B v x Z a₁ a₂ E H Ψ k ζ (unused v)
        (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u)) := by
  unfold fullResidualLift residualAveragedLift
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  exact lifted_pattern_full_roots (B.model k ζ) (B.pattern v) u (unused v) hV
    x lo hi Z Y a₁ a₂ E H Ψ hlo hhi hZ hΨ (hX v u) (hk v u) (hY v u) hζ

/-- The hypotheses for eliminating the actual finite source/target gates
follow uniformly from the given Z/k bounds and fixed cutoff support. -/
theorem eventual_full_residual_lift_eq_averaged (P : Geometry) (J m : ℕ)
    (C lo hi : ℝ) (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (B : Blueprint.Graph.Family P.graph G.graph J m)
        (Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
        (unused : (v : Fin B.count) → SharedDraw (B.pattern v)),
        Admissible P x G → |(k : ℝ)| ≤ L x ^ C →
        x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
        Function.support Ψ ⊆ Set.Icc lo hi → ζ = -a₁ - a₂ →
        fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused =
          ∑ v : Fin B.count, residualAveragedLift B v x Z a₁ a₂ E H Ψ k ζ (unused v)
            (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u)) := by
  filter_upwards [eventual_cutoff_draw_ranges P J P.ell m C lo hi hC hlo hhi,
    eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
    with x hx hxx hL
  change 1 ≤ L x at hL
  have hLpos : 0 < L x := by linarith
  have hxpos : 0 < x := by linarith
  intro G B Z a₁ a₂ E H Ψ k ζ unused hG hk hZlo hZhi hΨ hζ
  have hZpos : 0 < Z := (mul_pos hxpos (Real.rpow_pos_of_pos hLpos (-C))).trans_le hZlo
  have hV (g : Fin G.size) : G.graph.V g ≠ 0 := by
    rw [graph_mass]
    exact (P.positive.2.2.1.trans_le (hG.2.2.1 g).1).ne'
  apply full_residual_lift_eq_averaged B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused
    lo hi hV hlo hhi hZpos hΨ
  · intro v u
    exact (hx G (B.pattern v) u Z k hG hk hZlo hZhi).2.1
  · intro v u
    exact (hx G (B.pattern v) u Z k hG hk hZlo hZhi).2.2.1
  · intro v u z
    exact (hx G (B.pattern v) u Z k hG hk hZlo hZhi).2.2.2.2.2 z
  · exact hζ

/-- The full physical residual family differs from its stripped form by
arbitrary log saving. All support and range obligations are discharged;
only residual-family structure and its actual mass bound are assumed. -/
theorem full_residual_stripping_negligible (P : Geometry) (J m : ℕ)
    (A C C₁ τ η lo hi : ℝ) (bounds : ℕ → ℝ)
    (hC : 0 < C) (hlo : 0 < lo) (hhi : lo < hi) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (G : PrimeGroups) (Q : ℕ) (h ξ : ℝ)
        (B : Blueprint.Graph.Family P.graph G.graph J m)
        (Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
        (z₀ unused : (v : Fin B.count) → SharedDraw (B.pattern v)),
        Admissible P x G → B.Residual Q h ξ →
        EndpointBound x C τ η E → EndpointBound x C τ η H →
        (B.model k ζ).patternMass ≤ L x ^ C₁ →
        |(k : ℝ)| ≤ L x ^ C → x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
        CutoffBound x C lo hi Ψ bounds → ζ = -a₁ - a₂ →
        ‖fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused -
          ∑ v : Fin B.count, residualStrippedLift B v x Z a₁ a₂ E H Ψ k (z₀ v)
            (fun u => cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u))‖ ≤ L x ^ (-A) := by
  let R := (hi + lo) / lo
  have hR : 0 < R := div_pos (by linarith) hlo
  filter_upwards [eventual_full_residual_lift_eq_averaged P J m C lo hi hC hlo hhi,
    eventual_cutoff_draw_ranges P J P.ell m C lo hi hC hlo hhi,
    eventual_cutoff_sup C lo hi bounds,
    residual_family_stripping_negligible P J m A C (C + 1) C₁ τ η R hR]
    with x hfull hrange hsup hstrip
  intro G Q h ξ B Z a₁ a₂ E H Ψ k ζ z₀ unused hG hB hE hH hmass hk hZlo hZhi hΨ hζ
  rw [hfull G B Z a₁ a₂ E H Ψ k ζ unused hG hk hZlo hZhi hΨ.2.1 hζ]
  let X := fun (v : Fin B.count) (u : FreeDraw (B.pattern v)) =>
    lo * Z * freeDrawProduct (B.pattern v) u
  let Y := fun (v : Fin B.count) (u : FreeDraw (B.pattern v)) =>
    (hi + lo) * Z * freeDrawProduct (B.pattern v) u
  let s := fun (v : Fin B.count) (u : FreeDraw (B.pattern v)) =>
    cutoffRoots lo hi Z (freeDrawProduct (B.pattern v) u)
  apply hstrip G Q h ξ B Z a₁ a₂ E H Ψ k ζ z₀ unused X Y s hG hB hE hH hmass
  · intro v u
    exact (hrange G (B.pattern v) u Z k hG hk hZlo hZhi).2.2.2.1
  · intro v u
    obtain ⟨hZpos, hX1, hkhalf, hDCx, hYx, hshared⟩ :=
      hrange G (B.pattern v) u Z k hG hk hZlo hZhi
    have hDpos : 0 < (freeDrawProduct (B.pattern v) u : ℝ) := by
      exact_mod_cast freeDrawProduct_pos (B.pattern v) u
    have hhiPos : 0 < hi := hlo.trans hhi
    have hXpos : 0 < X v u := lt_of_lt_of_le zero_lt_one hX1
    have hY1 : 1 ≤ Y v u := by
      dsimp [Y]
      nlinarith [mul_pos (mul_pos hhiPos hZpos) hDpos]
    have hYX : Y v u = R * X v u := by
      dsimp [X, Y, R]
      field_simp
    refine ⟨hXpos, hY1, hYx, hYX.le, ?_, ?_⟩
    · intro n hn
      exact (cutoffRoots_ranges lo hi Z _ k hlo hhi hZpos (freeDrawProduct_pos _ u)
        hX1 hkhalf n hn).2.1
    · intro n hn
      obtain ⟨hn1, hnlo, hnhi, hn'pos, hn'hi⟩ :=
        cutoffRoots_ranges lo hi Z _ k hlo hhi hZpos (freeDrawProduct_pos _ u)
          hX1 hkhalf n hn
      exact ⟨hn1, hnhi, hn'pos, hn'hi⟩
  · intro v u n hn
    exact hsup Ψ hΨ _

end Erdos821.P5Core
