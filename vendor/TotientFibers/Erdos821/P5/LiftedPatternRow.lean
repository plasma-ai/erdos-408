import Erdos821.P5.LiftedSharedRow

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

def bannedPatternCoefficient {F : FixedData} {G : Blueprint.Graph.PrimeGroups} {J m : ℕ}
    (A : Model F G J m) (ν : Pattern G J F.ell m) (u : G.Aux J)
    (z : SharedDraw ν) (r s : UnsharedDraw ν) : ℂ :=
  if ν.ban (assembleLabels ν z r) (assembleLabels ν z s) u then
    ν.coefficient (G.restrictBig (assembleLabels ν z r))
      (G.restrictBig (assembleLabels ν z s)) (fun g => u g.val) else 0

theorem gated_lifted_shared_term {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (A : Model P.graph G.graph J m) (ν : Pattern G.graph J P.ell m)
    (z : SharedDraw ν) (r s : UnsharedDraw ν) (u : G.graph.Aux J)
    (hV : ∀ g, G.graph.V g ≠ 0) (T : Finset ℤ) (x Z a₁ a₂ : ℝ) (E H : Endpoint)
    (Ψ : ℝ → ℂ) (w w' : ℕ) (hw : 0 < w) (hw' : 0 < w')
    (hshift : (w' : ℤ) = (w : ℤ) + A.k * (freeProduct ν u : ℤ))
    (hζ : A.zeta = -a₁ - a₂) :
    gatedPatternTerm A ν u T (liftedEndpoint A x E (-a₁)) (liftedEndpoint A x H a₂)
        (harmonicCutoff Ψ Z) ((sharedDrawProduct ν z * w : ℕ) : ℤ)
        (assembleLabels ν z r) (assembleLabels ν z s) =
      if ((sharedDrawProduct ν z * w' : ℕ) : ℤ) ∈ T then
        (sharedDrawLaw ν z : ℂ) * strippedLiftScalar G x Z a₁ a₂ E H Ψ w w'
          (freeProduct ν u) *
          ((ν.physicalTargetMass ^ 2 * A.damping ((sharedDrawProduct ν z * w : ℕ) : ℤ) ^ 2 *
            A.damping ((sharedDrawProduct ν z * w' : ℕ) : ℤ) ^ 2 : ℝ) : ℂ) *
          (if G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * w : ℕ) : ℤ)
              (assembleLabels ν z r) ∧
            G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * w' : ℕ) : ℤ)
              (assembleLabels ν z s)
          then bannedPatternCoefficient A ν u z r s else 0)
      else 0 := by
  have hD : ν.D (assembleLabels ν z r) u = sharedDrawProduct ν z * freeProduct ν u := by
    rw [pattern_D_split, sharedProduct_assemble]
  have ht := patternTarget_shared A ν z r u w w' hshift
  have hcomp : ν.compatible (assembleLabels ν z r) (assembleLabels ν z s) :=
    (compatible_assemble_iff ν z z r s).mpr rfl
  have hfull : ((sharedDrawProduct ν z * w' : ℕ) : ℤ) =
      ((sharedDrawProduct ν z * w : ℕ) : ℤ) +
        A.k * ((sharedDrawProduct ν z * freeProduct ν u : ℕ) : ℤ) := by
    simpa only [patternTarget, hD] using ht.symm
  unfold gatedPatternTerm
  rw [hD, ht]
  by_cases hT : ((sharedDrawProduct ν z * w' : ℕ) : ℤ) ∈ T
  · simp only [hT, if_true]
    by_cases hp : G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * w : ℕ) : ℤ)
        (assembleLabels ν z r) ∧
      G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * w' : ℕ) : ℤ)
        (assembleLabels ν z s)
    · by_cases hb : ν.ban (assembleLabels ν z r) (assembleLabels ν z s) u
      · have hcond : (G.graph.physical (J + P.ell)
              ((sharedDrawProduct ν z * w : ℕ) : ℤ) (assembleLabels ν z r) ∧
            G.graph.physical (J + P.ell) ((sharedDrawProduct ν z * w' : ℕ) : ℤ)
              (assembleLabels ν z s)) ∧
            ν.compatible (assembleLabels ν z r) (assembleLabels ν z s) ∧
            ν.ban (assembleLabels ν z r) (assembleLabels ν z s) u ∧
            ((sharedDrawProduct ν z * w' : ℕ) : ℤ) =
              ((sharedDrawProduct ν z * w : ℕ) : ℤ) +
                A.k * (ν.D (assembleLabels ν z r) u : ℤ) :=
          ⟨hp, hcomp, hb, by rwa [hD]⟩
        rw [physicalPatternBody, if_pos hcond, if_pos hp,
          bannedPatternCoefficient, if_pos hb, hD]
        have hi := lifted_shared_integrand A ν z r u hV x Z a₁ a₂ E H Ψ w w' hw hw' hζ
        calc
          _ = (harmonicCutoff Ψ Z ((sharedDrawProduct ν z * w : ℕ) : ℤ)
              (sharedDrawProduct ν z * freeProduct ν u) *
            star (liftedEndpoint A x E (-a₁) ((sharedDrawProduct ν z * w : ℕ) : ℤ)) *
            liftedEndpoint A x H a₂ ((sharedDrawProduct ν z * w' : ℕ) : ℤ) *
            (G.graph.markMass (J + P.ell) : ℂ) *
            ((ν.physicalTargetMass * A.damping ((sharedDrawProduct ν z * w : ℕ) : ℤ) *
              A.damping ((sharedDrawProduct ν z * w' : ℕ) : ℤ) : ℝ) : ℂ) *
            imaginaryPower (sharedDrawProduct ν z * freeProduct ν u) A.zeta) *
              ν.coefficient (G.graph.restrictBig (assembleLabels ν z r))
                (G.graph.restrictBig (assembleLabels ν z s)) (fun g => u g.val) := by ring
          _ = _ := by rw [hi]
      · have hbody : physicalPatternBody A ν u ((sharedDrawProduct ν z * w : ℕ) : ℤ)
            ((sharedDrawProduct ν z * w' : ℕ) : ℤ)
            (assembleLabels ν z r) (assembleLabels ν z s) = 0 := by
          unfold physicalPatternBody
          exact if_neg (fun h => hb h.2.2.1)
        simp only [hbody, mul_zero, hp, if_true, bannedPatternCoefficient, hb, if_false, ite_self]
    · have hbody : physicalPatternBody A ν u ((sharedDrawProduct ν z * w : ℕ) : ℤ)
          ((sharedDrawProduct ν z * w' : ℕ) : ℤ)
          (assembleLabels ν z r) (assembleLabels ν z s) = 0 := by
        unfold physicalPatternBody
        exact if_neg (fun h => hp h.1)
      simp only [hbody, mul_zero, hp, if_false]
  · simp only [hT, if_false, mul_zero]

/-- The reindexed actual lift is the existing physicalSharedRow times its
harmonic law and stripped scalar. This includes bad draws and the full ban. -/
theorem sum_lifted_shared_row {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m : ℕ} (A : Model P.graph G.graph J m) (ν : Pattern G.graph J P.ell m)
    (z : SharedDraw ν) (u : G.graph.Aux J) (hV : ∀ g, G.graph.V g ≠ 0)
    (T : Finset ℤ) (x Z a₁ a₂ : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ)
    (w w' : ℕ) (hw : 0 < w) (hw' : 0 < w')
    (hshift : (w' : ℤ) = (w : ℤ) + A.k * (freeProduct ν u : ℤ))
    (hζ : A.zeta = -a₁ - a₂) :
    (∑ r : UnsharedDraw ν, ∑ s : UnsharedDraw ν,
      gatedPatternTerm A ν u T (liftedEndpoint A x E (-a₁)) (liftedEndpoint A x H a₂)
        (harmonicCutoff Ψ Z) ((sharedDrawProduct ν z * w : ℕ) : ℤ)
        (assembleLabels ν z r) (assembleLabels ν z s)) =
      if ((sharedDrawProduct ν z * w' : ℕ) : ℤ) ∈ T then
        (sharedDrawLaw ν z : ℂ) * strippedLiftScalar G x Z a₁ a₂ E H Ψ w w'
          (freeProduct ν u) *
          physicalSharedRow A ν z w w' (bannedPatternCoefficient A ν u z) else 0 := by
  simp_rw [gated_lifted_shared_term A ν z _ _ u hV T x Z a₁ a₂ E H Ψ w w' hw hw' hshift hζ]
  by_cases hT : ((sharedDrawProduct ν z * w' : ℕ) : ℤ) ∈ T
  · simp only [hT, if_true, physicalSharedRow, Finset.mul_sum, mul_assoc]
  · simp only [hT, if_false, Finset.sum_const_zero]

end Erdos821.P5Core
