import Erdos821.P5.CutoffSupport
import Erdos821.P5.LiftedRootIdentity
import Erdos821.P5.ResidualStripping

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- On cutoff support, both original roots are in the full positive range.
This applies to every shared draw, including repetitions and overlaps. -/
theorem cutoffRoots_shared_gates {G : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Blueprint.Graph.Pattern G J ell m) (u : FreeDraw ν) (z : SharedDraw ν)
    (lo hi Z Y : ℝ) (k : ℤ) (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hX : 1 ≤ lo * Z * freeDrawProduct ν u) (hk : |(k : ℝ)| ≤ lo * Z / 2)
    (hY : (sharedDrawProduct ν z : ℝ) * ((hi + lo) * Z * freeDrawProduct ν u) ≤ Y)
    (n : ℕ) (hn : n ∈ cutoffRoots lo hi Z (freeDrawProduct ν u)) :
    (n : ℤ) ∈ strippedRoots (positiveRoots Y) (sharedDrawProduct ν z) ∧
      0 < (n : ℤ) + k * (freeDrawProduct ν u : ℤ) ∧
      (sharedDrawProduct ν z : ℤ) * ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)) ∈
        positiveRoots Y := by
  obtain ⟨hn1, hnlo, hnhi, hn'pos, hn'hi⟩ :=
    cutoffRoots_ranges lo hi Z _ k hlo hhi hZ (freeDrawProduct_pos ν u) hX hk n hn
  have hDR : (0 : ℤ) < sharedDrawProduct ν z := by
    exact_mod_cast sharedDrawProduct_pos ν z
  have hnpos : (0 : ℤ) < n := by omega
  have hRnonneg : 0 ≤ (sharedDrawProduct ν z : ℝ) := Nat.cast_nonneg _
  have hnY : (sharedDrawProduct ν z : ℝ) * (n : ℝ) ≤ Y :=
    (mul_le_mul_of_nonneg_left hnhi hRnonneg).trans hY
  have hshiftR : (((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat : ℝ) =
      ((n : ℤ) + k * (freeDrawProduct ν u : ℤ) : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg hn'pos.le
  push_cast at hshiftR
  have hn'Y : ((sharedDrawProduct ν z : ℤ) *
      ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)) : ℤ) ≤ (Y : ℝ) := by
    push_cast
    rw [← hshiftR]
    exact (mul_le_mul_of_nonneg_left hn'hi hRnonneg).trans hY
  refine ⟨(mem_strippedRoots (sharedDrawProduct_pos ν z).ne' _).mpr ?_, hn'pos, ?_⟩
  · apply (mem_positiveRoots Y _).mpr
    exact ⟨mul_pos hDR hnpos, by simpa only [Int.cast_mul, Int.cast_natCast] using hnY⟩
  · exact (mem_positiveRoots Y _).mpr ⟨mul_pos hDR hn'pos, hn'Y⟩

/-- Exact extension to the common natural-number cutoff interval. The
source and target gates disappear only after their membership is proved. -/
theorem sum_full_shared_roots {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (u : FreeDraw ν)
    (unused z : SharedDraw ν) (x lo hi Z Y a₁ a₂ : ℝ) (E H : Endpoint)
    (Ψ : ℝ → ℂ) (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hs : Function.support Ψ ⊆ Set.Icc lo hi)
    (hX : 1 ≤ lo * Z * freeDrawProduct ν u) (hk : |(A.k : ℝ)| ≤ lo * Z / 2)
    (hY : (sharedDrawProduct ν z : ℝ) * ((hi + lo) * Z * freeDrawProduct ν u) ≤ Y) :
    (∑ w ∈ strippedRoots (positiveRoots Y) (sharedDrawProduct ν z),
      if 0 < w + A.k * (freeDrawProduct ν u : ℤ) then
        if (sharedDrawProduct ν z : ℤ) * (w + A.k * (freeDrawProduct ν u : ℤ)) ∈ positiveRoots Y then
          (sharedDrawLaw ν z : ℂ) *
            strippedLiftScalar G x Z a₁ a₂ E H Ψ w.toNat
              (w + A.k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
            physicalSharedRow A ν z w.toNat (w + A.k * (freeDrawProduct ν u : ℤ)).toNat
              (bannedPatternCoefficient A ν (assembleAux ν u unused) z)
        else 0
      else 0) =
    ∑ n ∈ cutoffRoots lo hi Z (freeDrawProduct ν u),
      (sharedDrawLaw ν z : ℂ) *
        strippedLiftScalar G x Z a₁ a₂ E H Ψ n
          ((n : ℤ) + A.k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        physicalSharedRow A ν z n ((n : ℤ) + A.k * (freeDrawProduct ν u : ℤ)).toNat
          (bannedPatternCoefficient A ν (assembleAux ν u unused) z) := by
  let S := cutoffRoots lo hi Z (freeDrawProduct ν u)
  let f := fun w : ℤ =>
    if 0 < w + A.k * (freeDrawProduct ν u : ℤ) then
      if (sharedDrawProduct ν z : ℤ) * (w + A.k * (freeDrawProduct ν u : ℤ)) ∈ positiveRoots Y then
        (sharedDrawLaw ν z : ℂ) *
          strippedLiftScalar G x Z a₁ a₂ E H Ψ w.toNat
            (w + A.k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
          physicalSharedRow A ν z w.toNat (w + A.k * (freeDrawProduct ν u : ℤ)).toNat
            (bannedPatternCoefficient A ν (assembleAux ν u unused) z)
      else 0
    else 0
  have hsub : S.image (fun n : ℕ => (n : ℤ)) ⊆
      strippedRoots (positiveRoots Y) (sharedDrawProduct ν z) := by
    intro w hw
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
    exact (cutoffRoots_shared_gates ν u z lo hi Z Y A.k hlo hhi hZ hX hk hY n hn).1
  have hzero (w : ℤ) (hw : w ∈ strippedRoots (positiveRoots Y) (sharedDrawProduct ν z))
      (hnot : w ∉ S.image (fun n : ℕ => (n : ℤ))) : f w = 0 := by
    have hwpos := strippedRoots_positive (sharedDrawProduct_pos ν z)
      (fun n hn => ((mem_positiveRoots Y n).mp hn).1) hw
    have hwnot : w.toNat ∉ S := by
      intro hn
      apply hnot
      exact Finset.mem_image.mpr ⟨w.toNat, hn, Int.toNat_of_nonneg hwpos.le⟩
    have hscalar := strippedLiftScalar_zero_outside G x lo hi Z a₁ a₂ E H Ψ
      (freeDrawProduct ν u) w.toNat (w + A.k * (freeDrawProduct ν u : ℤ)).toNat
      hZ (freeDrawProduct_pos ν u) (hlo.trans hhi) hs hwnot
    simp only [f, hscalar, mul_zero, zero_mul, ite_self]
  change (∑ w ∈ strippedRoots (positiveRoots Y) (sharedDrawProduct ν z), f w) = _
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_image (fun n hn r hr heq => by exact_mod_cast heq)]
  apply Finset.sum_congr rfl
  intro n hn
  have hg := cutoffRoots_shared_gates ν u z lo hi Z Y A.k hlo hhi hZ hX hk hY n hn
  simp only [f, hg.2.1, hg.2.2, if_true, Int.toNat_natCast]

/-- A full positive-root physical pattern equals its unrestricted shared
harmonic average on the common cutoff interval. No draws are discarded. -/
theorem lifted_pattern_full_roots {P : Geometry} {G : PrimeGroups} {J m : ℕ}
    (A : Blueprint.Graph.Model P.graph G.graph J m)
    (ν : Blueprint.Graph.Pattern G.graph J P.ell m) (u : FreeDraw ν) (unused : SharedDraw ν)
    (hV : ∀ g, G.graph.V g ≠ 0) (x lo hi Z Y a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z) (hs : Function.support Ψ ⊆ Set.Icc lo hi)
    (hX : 1 ≤ lo * Z * freeDrawProduct ν u) (hk : |(A.k : ℝ)| ≤ lo * Z / 2)
    (hY : ∀ z : SharedDraw ν,
      (sharedDrawProduct ν z : ℝ) * ((hi + lo) * Z * freeDrawProduct ν u) ≤ Y)
    (hζ : A.zeta = -a₁ - a₂) :
    (∑ n ∈ positiveRoots Y, ∑ a : A.Labels, ∑ b : A.Labels,
      gatedPatternTerm A ν (assembleAux ν u unused) (positiveRoots Y)
        (liftedEndpoint A x E (-a₁)) (liftedEndpoint A x H a₂) (harmonicCutoff Ψ Z) n a b) =
    ∑ n ∈ cutoffRoots lo hi Z (freeDrawProduct ν u),
      strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + A.k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        ∑ z : SharedDraw ν, (sharedDrawLaw ν z : ℂ) *
          physicalSharedRow A ν z n ((n : ℤ) + A.k * (freeDrawProduct ν u : ℤ)).toNat
            (bannedPatternCoefficient A ν (assembleAux ν u unused) z) := by
  rw [lifted_pattern_root_identity A ν (assembleAux ν u unused) hV
    (positiveRoots Y) (positiveRoots Y)
    (fun n hn => ((mem_positiveRoots Y n).mp hn).1)
    (fun n hn => ((mem_positiveRoots Y n).mp hn).1) x Z a₁ a₂ E H Ψ hζ]
  simp_rw [freeProduct_assembleAux]
  have hrows (z : SharedDraw ν) := sum_full_shared_roots A ν u unused z x lo hi Z Y a₁ a₂
    E H Ψ hlo hhi hZ hs hX hk (hY z)
  simp_rw [hrows]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

end Erdos821.P5Core
