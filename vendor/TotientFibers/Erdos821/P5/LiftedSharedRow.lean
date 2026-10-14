import Erdos821.P5.SharedRootPairing
import Erdos821.P5.MellinVectors

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

def harmonicCutoff (Ψ : ℝ → ℂ) (Z : ℝ) (n : ℤ) (D : ℕ) : ℂ :=
  Ψ ((n : ℝ) / (Z * (D : ℝ))) / (n : ℂ)

def strippedLiftScalar (G : Blueprint.Analytic.PrimeGroups) (x Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (w w' D : ℕ) : ℂ :=
  harmonicCutoff Ψ Z (w : ℤ) D * mellin ((w : ℝ) / D) a₁ *
    mellin ((w' : ℝ) / D) a₂ * star (endpoint G x E w) * endpoint G x H w'

theorem sharedDrawProduct_primeFactors {P : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) :
    (sharedDrawProduct ν z).primeFactors ⊆ P.allPrimes := by
  apply primeFactors_prod_supported
  · intro i hi
    exact (P.prime i.1 _ (z i).property).pos
  · intro i hi
    rw [(P.prime i.1 _ (z i).property).primeFactors, Finset.singleton_subset_iff]
    exact Finset.mem_biUnion.mpr ⟨i.1, Finset.mem_univ _, (z i).property⟩

theorem endpoint_sharedDrawProduct {G : Blueprint.Analytic.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern G.graph J ell m) (z : SharedDraw ν) (x : ℝ) (E : Endpoint) (n : ℕ) :
    endpoint G x E (sharedDrawProduct ν z * n) = endpoint G x E n :=
  endpoint_mul_supported G x E _ n (sharedDrawProduct_pos ν z).ne'
    (sharedDrawProduct_primeFactors ν z)

theorem harmonicCutoff_shared (Ψ : ℝ → ℂ) (Z : ℝ) (DR DC w : ℕ) (hDR : DR ≠ 0) :
    harmonicCutoff Ψ Z ((DR * w : ℕ) : ℤ) (DR * DC) =
      (DR : ℂ)⁻¹ * harmonicCutoff Ψ Z (w : ℤ) DC := by
  have hDRR : (DR : ℝ) ≠ 0 := by exact_mod_cast hDR
  simpa only [harmonicCutoff, Int.cast_natCast, Nat.cast_mul, Int.cast_mul,
    Complex.ofReal_mul, Complex.ofReal_natCast] using
    shared_cutoff_reindex Ψ DR DC Z w hDRR

theorem patternTarget_shared {F : FixedData} {P : Blueprint.Graph.PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (z : SharedDraw ν)
    (r : UnsharedDraw ν) (u : P.Aux J) (w w' : ℕ)
    (hshift : (w' : ℤ) = (w : ℤ) + A.k * (freeProduct ν u : ℤ)) :
    patternTarget A ν u ((sharedDrawProduct ν z * w : ℕ) : ℤ) (assembleLabels ν z r) =
      ((sharedDrawProduct ν z * w' : ℕ) : ℤ) := by
  rw [patternTarget, pattern_D_split, sharedProduct_assemble]
  push_cast
  rw [hshift]
  ring

theorem sharedDraw_harmonic_normalization {P : Blueprint.Graph.PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (z : SharedDraw ν) (r : UnsharedDraw ν)
    (hV : ∀ g, P.V g ≠ 0) :
    (P.markMass (J + ell) : ℂ) * (ν.physicalTargetMass : ℂ) / (sharedDrawProduct ν z : ℂ) =
      (sharedDrawLaw ν z : ℂ) * (ν.physicalTargetMass : ℂ) ^ 2 := by
  have h := shared_harmonic_normalization ν (assembleLabels ν z r) hV
  rw [sharedProduct_assemble, ← sharedDrawLaw_restriction, sharedRestriction_assemble] at h
  exact_mod_cast h

/-- The actual lifted integrand has the full damping squares. Removing its
shared product converts the mark mass exactly to the shared harmonic law. -/
theorem lifted_shared_integrand {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (A : Model P.graph G.graph J m) (ν : Pattern G.graph J P.ell m)
    (z : SharedDraw ν) (r : UnsharedDraw ν) (u : G.graph.Aux J)
    (hV : ∀ g, G.graph.V g ≠ 0) (x Z a₁ a₂ : ℝ) (E H : Endpoint)
    (Ψ : ℝ → ℂ) (w w' : ℕ) (hw : 0 < w) (hw' : 0 < w')
    (hζ : A.zeta = -a₁ - a₂) :
    harmonicCutoff Ψ Z ((sharedDrawProduct ν z * w : ℕ) : ℤ)
        (sharedDrawProduct ν z * freeProduct ν u) *
      star (liftedEndpoint A x E (-a₁) ((sharedDrawProduct ν z * w : ℕ) : ℤ)) *
      liftedEndpoint A x H a₂ ((sharedDrawProduct ν z * w' : ℕ) : ℤ) *
      (G.graph.markMass (J + P.ell) : ℂ) *
      ((ν.physicalTargetMass * A.damping ((sharedDrawProduct ν z * w : ℕ) : ℤ) *
        A.damping ((sharedDrawProduct ν z * w' : ℕ) : ℤ) : ℝ) : ℂ) *
      imaginaryPower (sharedDrawProduct ν z * freeProduct ν u) A.zeta =
        (sharedDrawLaw ν z : ℂ) * strippedLiftScalar G x Z a₁ a₂ E H Ψ w w'
          (freeProduct ν u) *
          ((ν.physicalTargetMass ^ 2 * A.damping ((sharedDrawProduct ν z * w : ℕ) : ℤ) ^ 2 *
            A.damping ((sharedDrawProduct ν z * w' : ℕ) : ℤ) ^ 2 : ℝ) : ℂ) := by
  have hDR : 0 < (sharedDrawProduct ν z : ℝ) := by exact_mod_cast sharedDrawProduct_pos ν z
  have hDC : 0 < (freeProduct ν u : ℝ) := by exact_mod_cast freeProduct_pos ν u
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hw'R : (0 : ℝ) < w' := by exact_mod_cast hw'
  have hphase := shared_mellin_cancellation (sharedDrawProduct ν z) (freeProduct ν u)
    w w' a₁ a₂ hDR hDC hwR hw'R
  have hnorm := sharedDraw_harmonic_normalization ν z r hV
  rw [div_eq_mul_inv] at hnorm
  have hstar (d : ℝ) : star (d : ℂ) = (d : ℂ) := by simp
  have hip (D : ℕ) : imaginaryPower D A.zeta = mellin D (-a₁ - a₂) := by
    rw [hζ]
    simp only [imaginaryPower, Blueprint.Analytic.mellin]
    congr 1
    ring
  simp only [liftedEndpoint, star_mul, star_mellin, neg_neg, hstar,
    Int.toNat_natCast, endpoint_sharedDrawProduct, hip,
    harmonicCutoff_shared Ψ Z _ _ _ (sharedDrawProduct_pos ν z).ne',
    Complex.ofReal_mul, Complex.ofReal_pow, strippedLiftScalar]
  have hphase' : mellin ((sharedDrawProduct ν z * w : ℕ) : ℤ) a₁ *
      mellin ((sharedDrawProduct ν z * w' : ℕ) : ℤ) a₂ *
      mellin (sharedDrawProduct ν z * freeProduct ν u : ℕ) (-a₁ - a₂) =
        mellin ((w : ℝ) / freeProduct ν u) a₁ * mellin ((w' : ℝ) / freeProduct ν u) a₂ := by
    simpa only [Int.cast_natCast, Nat.cast_mul, Int.cast_mul] using hphase
  calc
    _ = harmonicCutoff Ψ Z (w : ℤ) (freeProduct ν u) *
        (mellin ((sharedDrawProduct ν z * w : ℕ) : ℤ) a₁ *
          mellin ((sharedDrawProduct ν z * w' : ℕ) : ℤ) a₂ *
          mellin (sharedDrawProduct ν z * freeProduct ν u : ℕ) (-a₁ - a₂)) *
        star (endpoint G x E w) * endpoint G x H w' *
        ((G.graph.markMass (J + P.ell) : ℂ) * (ν.physicalTargetMass : ℂ) *
          (sharedDrawProduct ν z : ℂ)⁻¹) *
        (A.damping ((sharedDrawProduct ν z * w : ℕ) : ℤ) : ℂ) ^ 2 *
        (A.damping ((sharedDrawProduct ν z * w' : ℕ) : ℤ) : ℂ) ^ 2 := by ring
    _ = _ := by rw [hphase', hnorm]; ring

end Erdos821.P5Core
