import Erdos821.P5.DyadicSourcePartition
import Erdos821.P5.RootMaskAlgebra

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem gatedFamilySum_source_dyadic {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (k : ℤ) (ζ Y : ℝ) (T : Finset ℤ)
    (f g : ℤ → ℂ) (w : ℤ → ℕ → ℂ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v)) :
    gatedFamilySum B k ζ (positiveRoots Y) T f g w unused =
      ∑ i ∈ Finset.range (sourceDyadicCount Y),
        gatedFamilySum B k ζ (dyad ((2 : ℝ) ^ i)) T
          (rootMask (positiveRoots Y) f) g w unused := by
  simp_rw [← gatedFamilySum_rootMask]
  unfold gatedFamilySum
  let Q : (v : Fin B.count) → FreeDraw (B.pattern v) → ℕ → ℂ := fun v u i =>
    (freeDrawLaw (B.pattern v) u : ℂ) *
      ∑ n ∈ positiveRoots Y ∩ dyad ((2 : ℝ) ^ i),
        ∑ a : G.Labels (J + F.ell), ∑ b : G.Labels (J + F.ell),
          gatedPatternTerm (B.model k ζ) (B.pattern v)
            (assembleAux (B.pattern v) u (unused v)) T f g w n a b
  calc
    _ = ∑ v : Fin B.count, ∑ u : FreeDraw (B.pattern v),
        ∑ i ∈ Finset.range (sourceDyadicCount Y), Q v u i := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      rw [sum_positiveRoots_dyadic, Finset.mul_sum]
    _ = ∑ v : Fin B.count, ∑ i ∈ Finset.range (sourceDyadicCount Y),
        ∑ u : FreeDraw (B.pattern v), Q v u i := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def retainedSourceDyads (x τ : ℝ) : Finset ℕ :=
  (Finset.range (sourceDyadicCount (x ^ (2 : ℕ)))).filter
    (fun i => x ^ (τ / 2) ≤ (2 : ℝ) ^ i ∧ (2 : ℝ) ^ i ≤ x ^ (2 : ℕ))

theorem mem_retainedSourceDyads (x τ : ℝ) (i : ℕ) :
    i ∈ retainedSourceDyads x τ ↔
      i < sourceDyadicCount (x ^ (2 : ℕ)) ∧
        x ^ (τ / 2) ≤ (2 : ℝ) ^ i ∧ (2 : ℝ) ^ i ≤ x ^ (2 : ℕ) := by
  simp [retainedSourceDyads]

theorem retainedSourceDyads_card_le (x τ : ℝ) :
    (retainedSourceDyads x τ).card ≤ sourceDyadicCount (x ^ (2 : ℕ)) := by
  unfold retainedSourceDyads
  simpa only [Finset.card_range] using Finset.card_le_card
    (Finset.filter_subset (fun i => x ^ (τ / 2) ≤ (2 : ℝ) ^ i ∧
      (2 : ℝ) ^ i ≤ x ^ (2 : ℕ)) (Finset.range (sourceDyadicCount (x ^ (2 : ℕ)))))

theorem retainedSourceDyads_transfer_range (x τ : ℝ) (hx : 1 ≤ x)
    (hτ : 0 < τ) (hτhi : τ ≤ 1) (i : ℕ) (hi : i ∈ retainedSourceDyads x τ) :
    x ^ (τ / 2) ≤ (2 : ℝ) ^ i ∧ (2 : ℝ) ^ i ≤ x ^ (τ / 2)⁻¹ := by
  obtain ⟨hirange, hilo, hihi⟩ := (mem_retainedSourceDyads x τ i).mp hi
  refine ⟨hilo, hihi.trans ?_⟩
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hx
  have hpos : 0 < τ / 2 := by linarith
  have hinv : (τ / 2) * (τ / 2)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hinvpos : 0 < (τ / 2)⁻¹ := inv_pos.mpr hpos
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem rootMask_liftedEndpoint_zero_on_low_dyad {P : Geometry} {G : PrimeGroups}
    {J m : ℕ} (A : Model P.graph G.graph J m) (x C τ η X : ℝ) (E : Endpoint)
    (hE : EndpointBound x C τ η E) (t : ℝ) (S : Finset ℤ)
    (hX : 0 < X) (hlo : X < x ^ (τ / 2))
    (hsmall : 2 * x ^ (τ / 2) ≤ x ^ τ) :
    ∀ n ∈ dyad X, rootMask S (liftedEndpoint A x E t) n = 0 := by
  intro n hn
  obtain ⟨hnlo, hnhi⟩ := (mem_graph_dyad X n).mp hn
  have hnpos : 0 < n := by exact_mod_cast hX.trans_le hnlo
  have hnscale : (n : ℝ) < x ^ τ := by linarith
  have hzero := liftedEndpoint_eq_zero_below_scale A x C τ η E hE t n hnpos hnscale
  simp [rootMask, hzero]

theorem rootMask_positiveRoots_zero_on_high_dyad (Y X : ℝ) (f : ℤ → ℂ)
    (hhi : Y < X) : ∀ n ∈ dyad X, rootMask (positiveRoots Y) f n = 0 := by
  intro n hn
  have hnlo := ((mem_graph_dyad X n).mp hn).1
  have hnot : n ∉ positiveRoots Y := by
    intro h
    have hnhi := ((mem_positiveRoots Y n).mp h).2
    linarith
  simp [rootMask, hnot]

/-- The original finite root mask is retained on the last partial dyad.
The discarded low dyads vanish by the actual endpoint support. -/
theorem fullResidualLift_eq_retained_dyadic {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (B : Family P.graph G.graph J m) (x Z a₁ a₂ C τ η : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ) (ζ : ℝ)
    (unused : (v : Fin B.count) → SharedDraw (B.pattern v))
    (hE : EndpointBound x C τ η E) (hsmall : 2 * x ^ (τ / 2) ≤ x ^ τ) :
    fullResidualLift B x (x ^ (2 : ℕ)) Z a₁ a₂ E H Ψ k ζ unused =
      ∑ i ∈ retainedSourceDyads x τ,
        gatedFamilySum B k ζ (dyad ((2 : ℝ) ^ i)) (positiveRoots (x ^ (2 : ℕ)))
          (rootMask (positiveRoots (x ^ (2 : ℕ)))
            (liftedEndpoint (B.model k ζ) x E (-a₁)))
          (liftedEndpoint (B.model k ζ) x H a₂) (harmonicCutoff Ψ Z) unused := by
  rw [fullResidualLift_eq_gatedFamilySum, gatedFamilySum_source_dyadic]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hfail : ¬(x ^ (τ / 2) ≤ (2 : ℝ) ^ i ∧ (2 : ℝ) ^ i ≤ x ^ (2 : ℕ)) := by
    intro h
    exact hnot (Finset.mem_filter.mpr ⟨hi, h⟩)
  apply gatedFamilySum_eq_zero_source
  by_cases hlo : x ^ (τ / 2) ≤ (2 : ℝ) ^ i
  · have hhi : x ^ (2 : ℕ) < (2 : ℝ) ^ i := lt_of_not_ge (fun h => hfail ⟨hlo, h⟩)
    exact rootMask_positiveRoots_zero_on_high_dyad _ _ _ hhi
  · exact rootMask_liftedEndpoint_zero_on_low_dyad (B.model k ζ) x C τ η _ E hE
      (-a₁) _ (pow_pos (by norm_num) _) (lt_of_not_ge hlo) hsmall

theorem eventual_low_dyad_separation (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 2 * x ^ (τ / 2) ≤ x ^ τ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by linarith : 0 < τ / 2)).eventually_ge_atTop (2 : ℝ)]
    with x hx hhalf
  refine ⟨hx, ?_⟩
  have hpow : x ^ (τ / 2) * x ^ (τ / 2) = x ^ τ := by
    rw [← Real.rpow_add (by linarith : 0 < x)]
    congr 1
    ring
  rw [← hpow]
  exact mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg (by linarith) _)

end Erdos821.P5Core
