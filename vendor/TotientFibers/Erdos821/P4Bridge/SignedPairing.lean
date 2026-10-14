import Erdos821.P4Bridge.UnsignedKernel

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

lemma unsignedFullPair_states (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g) (Q : ℕ) (h ξ θ ζ : ℝ)
    (f g : P.BigLabels (J + ell) → ℂ) :
    idealFullPair (unsignedKernel ν block Q h ξ θ ζ) f g =
      ∑ s : SharedRows ν, ∑ a : SideTuple ν block false, ∑ b : SideTuple ν block true,
        ∑ t : P.BigLabels ell, ∑ a' : SideTuple ν block false,
        ∑ b' : SideTuple ν block true, ∑ t' : P.BigLabels ell,
          ((rowWeight (sharedRows ν) s *
            Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a *
            Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b *
            P.idealMass t *
            Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a' *
            Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b' *
            P.idealMass t' : ℝ) : ℂ) *
          star (f (labelJoin ν block s a b t)) * g (labelJoin ν block s a' b' t') *
          Blueprint.Analytic.mellin (rowProduct (sharedRows ν) s) ζ *
          auxCorrection ν block Q h ξ θ ζ (rowProduct (sharedRows ν) s) a' b := by
  unfold idealFullPair
  rw [sum_labels ν block]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro t _
  rw [sum_labels ν block]
  simp only [unsignedKernel_join ν block hV, idealMass_labelJoin,
    mul_ite, ite_mul, mul_zero, zero_mul]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  apply Finset.sum_congr rfl
  intro a' _
  apply Finset.sum_congr rfl
  intro b' _
  apply Finset.sum_congr rfl
  intro t' _
  simp only [Complex.ofReal_mul]
  ring

lemma unsignedFullPair_conditional (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g) (Q : ℕ) (h ξ θ ζ : ℝ)
    (f g : P.BigLabels (J + ell) → ℂ) :
    idealFullPair (unsignedKernel ν block Q h ξ θ ζ) f g =
      ∑ s : SharedRows ν, (rowWeight (sharedRows ν) s : ℂ) *
        Blueprint.Analytic.mellin (rowProduct (sharedRows ν) s) ζ *
        correctionConditional ν block Q h ξ θ ζ (rowProduct (sharedRows ν) s)
          (conditionalF ν block f s) (conditionalG ν block g s) := by
  rw [unsignedFullPair_states ν block hV]
  apply Finset.sum_congr rfl
  intro s _
  rw [sum_six_permute]
  unfold correctionConditional Blueprint.Analytic.expect
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a' _
  let wx := Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false)
  let wy := Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true)
  let K : ℂ := ((rowWeight (sharedRows ν) s * wy b * wx a' : ℝ) : ℂ) *
    Blueprint.Analytic.mellin (rowProduct (sharedRows ν) s) ζ *
    auxCorrection ν block Q h ξ θ ζ (rowProduct (sharedRows ν) s) a' b
  calc
    _ = ∑ a, ∑ t : P.BigLabels ell, ∑ b', ∑ t' : P.BigLabels ell,
        ((wx a * P.idealMass t * wy b' * P.idealMass t' : ℝ) : ℂ) *
          star (f (labelJoin ν block s a b t)) * g (labelJoin ν block s a' b' t') * K := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro b' _
      apply Finset.sum_congr rfl
      intro t' _
      dsimp only [K, wx, wy]
      simp only [Complex.ofReal_mul]
      ring
    _ = star (conditionalF ν block f s b) * conditionalG ν block g s a' * K :=
      sum_four_factor wx (P.idealMass (M := ell)) wy (P.idealMass (M := ell))
        (fun a t => f (labelJoin ν block s a b t))
        (fun b' t' => g (labelJoin ν block s a' b' t')) K
    _ = _ := by
      dsimp only [K, wx, wy]
      simp only [Complex.ofReal_mul]
      ring

end
end Erdos821.P4Bridge
