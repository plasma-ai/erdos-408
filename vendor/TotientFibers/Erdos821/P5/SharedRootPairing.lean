import Erdos821.P5.RootShift
import Erdos821.P5.RootMultiples
import Erdos821.P5.SharedRowBound
import Erdos821.P5.PhysicalNormTheorem

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Graph

/-- A scalar may still depend on the original source root and full edge
product. The cutoff will only be separated after this exact reindexing. -/
def gatedPatternTerm {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (T : Finset ℤ) (f g : ℤ → ℂ) (weight : ℤ → ℕ → ℂ)
    (n : ℤ) (a b : A.Labels) : ℂ :=
  weight n (ν.D a u) * star (f n) * (P.markMass (J + F.ell) : ℂ) *
    (if patternTarget A ν u n a ∈ T then
      g (patternTarget A ν u n a) *
        physicalPatternBody A ν u n (patternTarget A ν u n a) a b else 0)

theorem gatedPatternTerm_zero_incompatible {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (T : Finset ℤ) (f g : ℤ → ℂ) (weight : ℤ → ℕ → ℂ)
    (n : ℤ) (a b : A.Labels) (h : ¬ν.compatible a b) :
    gatedPatternTerm A ν u T f g weight n a b = 0 := by
  simp [gatedPatternTerm, physicalPatternBody, h]

theorem sum_gatedPatternTerm_labels {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (T : Finset ℤ) (f g : ℤ → ℂ) (weight : ℤ → ℕ → ℂ) (n : ℤ) :
    (∑ a : A.Labels, ∑ b : A.Labels, gatedPatternTerm A ν u T f g weight n a b) =
      ∑ z : SharedDraw ν, ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
        gatedPatternTerm A ν u T f g weight n
          (assembleLabels ν z r) (assembleLabels ν z s) := by
  rw [← sum_compatible_labels]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hc : ν.compatible a b
  · simp only [hc, if_true]
  · simp only [hc, if_false, gatedPatternTerm_zero_incompatible A ν u T f g weight n a b hc]

theorem gatedPatternTerm_zero_not_shared_multiple {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (T : Finset ℤ) (f g : ℤ → ℂ) (weight : ℤ → ℕ → ℂ)
    (n : ℤ) (hn : 0 ≤ n) (z : SharedDraw ν) (r s : UnsharedDraw ν)
    (hd : ¬(sharedDrawProduct ν z : ℤ) ∣ n) :
    gatedPatternTerm A ν u T f g weight n
      (assembleLabels ν z r) (assembleLabels ν z s) = 0 := by
  have hp : ¬P.physical (J + F.ell) n (assembleLabels ν z r) := by
    intro hp
    have hdiv := physical_sharedProduct_dvd ν (assembleLabels ν z r) hn hp
    rw [sharedProduct_assemble] at hdiv
    apply hd
    have hdivZ := Int.natCast_dvd_natCast.mpr hdiv
    simpa only [Int.toNat_of_nonneg hn] using hdivZ
  simp [gatedPatternTerm, physicalPatternBody, hp]

/-- Compatible lists force the source root to be divisible by their shared
product. This is an exact finite sum, with no discarded configurations. -/
theorem sum_shared_pattern_roots {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (S T : Finset ℤ) (hS : ∀ n ∈ S, 0 ≤ n)
    (f g : ℤ → ℂ) (weight : ℤ → ℕ → ℂ) :
    (∑ n ∈ S, ∑ a : A.Labels, ∑ b : A.Labels,
      gatedPatternTerm A ν u T f g weight n a b) =
      ∑ z : SharedDraw ν, ∑ w ∈ strippedRoots S (sharedDrawProduct ν z),
        ∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
          gatedPatternTerm A ν u T f g weight ((sharedDrawProduct ν z : ℤ) * w)
            (assembleLabels ν z r) (assembleLabels ν z s) := by
  simp_rw [sum_gatedPatternTerm_labels]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  apply sum_strip_multiples S (sharedDrawProduct ν z) (sharedDrawProduct_pos ν z).ne'
  intro n hn hnd
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro s hs
  exact gatedPatternTerm_zero_not_shared_multiple A ν u T f g weight n (hS n hn) z r s hnd

/-- The actual graph pairing has now been reindexed by the shared harmonic
coordinates and exact divided source roots. A scalar cutoff can be inserted
in gatedPatternTerm before its logarithmic Fourier separation. -/
theorem pairing_shared_root_expansion {P : Blueprint.Analytic.Geometry}
    {G : Blueprint.Analytic.PrimeGroups} {J m : ℕ}
    (A : Model P.graph G.graph J m) (hV : ∀ g, G.graph.V g ≠ 0)
    (X : ℝ) (hX : 1 ≤ X) (T : Finset ℤ) (f g : ℤ → ℂ) :
    A.pairing X (T.product Finset.univ) f (fun z => g z.1) =
      ∑ v : Fin A.patternCount, ∑ u : FreeDraw (A.pattern v),
        (freeDrawLaw (A.pattern v) u : ℂ) *
          ∑ z : SharedDraw (A.pattern v),
            ∑ w ∈ strippedRoots (dyad X) (sharedDrawProduct (A.pattern v) z),
              ∑ r : UnsharedDraw (A.pattern v), ∑ s : UnsharedDraw (A.pattern v),
                gatedPatternTerm A (A.pattern v)
                  (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV))
                  T f g (fun _ _ => 1) ((sharedDrawProduct (A.pattern v) z : ℤ) * w)
                  (assembleLabels (A.pattern v) z r) (assembleLabels (A.pattern v) z s) := by
  rw [pairing_shift_expansion A hV X T f g]
  have hraw : (∑ n ∈ dyad X, ∑ v : Fin A.patternCount,
      ∑ u : FreeDraw (A.pattern v), ∑ a : A.Labels, ∑ b : A.Labels,
        (freeDrawLaw (A.pattern v) u : ℂ) * star (f n) *
          (G.graph.markMass (J + P.ell) : ℂ) *
            (if patternTarget A (A.pattern v)
              (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n a ∈ T
            then g (patternTarget A (A.pattern v)
              (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n a) *
              physicalPatternBody A (A.pattern v)
                (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n
                (patternTarget A (A.pattern v)
                  (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) n a) a b
            else 0)) =
        ∑ n ∈ dyad X, ∑ v : Fin A.patternCount, ∑ u : FreeDraw (A.pattern v),
          (freeDrawLaw (A.pattern v) u : ℂ) *
            ∑ a : A.Labels, ∑ b : A.Labels,
              gatedPatternTerm A (A.pattern v)
                (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV))
                T f g (fun _ _ => 1) n a b := by
    simp only [gatedPatternTerm, one_mul, Finset.mul_sum, mul_assoc]
  rw [hraw, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Finset.mul_sum]
  congr 1
  exact sum_shared_pattern_roots A (A.pattern v)
    (assembleAux (A.pattern v) u (unusedAuxDraw (A.pattern v) hV)) (dyad X) T
    (fun n hn => (graph_dyad_positive hX hn).le) f g (fun _ _ => 1)

end Erdos821.P5Core
