import Erdos821.P4Bridge.SignedPairing

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

lemma signedRaw_eq (hj : m ≤ J) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ θ ζ : ℝ) (c : ProbeChoice P m block)
    (a b : P.BigLabels (J + F.ell)) :
    (((onePatternFamily F P J m (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ) a b =
      -((-1 : ℂ) ^ (∑ j, ((choiceBase hj c.val : Pattern P J F.ell m).changed j).card)) *
      unsignedKernel (choiceBase hj c.val : Pattern P J F.ell m) block Q h ξ θ ζ a b := by
  dsimp only [onePatternFamily, Family.model, Model.idealRaw]
  simp only [Fin.sum_univ_one]
  unfold unsignedKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  let ν : Pattern P J F.ell m := choiceBase hj c.val
  change (if ν.matchesBig a b then
    ((ν.bigAuxMass u * ν.freshMass b : ℝ) : ℂ) *
      (-((-1 : ℂ) ^ (∑ j, (ν.changed j).card)) *
        selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
          (selectedEndpoint ν block false b) *
        selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
          (selectedEndpoint ν block true a)) * imaginaryPower (ν.DBig a u) ζ *
        phase (θ * ν.DBig a u) else 0) = _
  by_cases hm : ν.matchesBig a b
  · dsimp only [ν] at hm ⊢
    simp only [hm, ite_true]
    ring
  · dsimp only [ν] at hm ⊢
    simp only [hm, ite_false, mul_zero]

lemma signedFullPair_eq (hj : m ≤ J) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ θ ζ : ℝ) (c : ProbeChoice P m block)
    (f g : P.BigLabels (J + F.ell) → ℂ) :
    idealFullPair (((onePatternFamily F P J m (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ) f g =
      -((-1 : ℂ) ^ (∑ j, ((choiceBase hj c.val : Pattern P J F.ell m).changed j).card)) *
        idealFullPair (unsignedKernel (choiceBase hj c.val : Pattern P J F.ell m)
          block Q h ξ θ ζ) f g := by
  unfold idealFullPair
  simp_rw [signedRaw_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma analytic_mellin_norm (n ζ : ℝ) : ‖Blueprint.Analytic.mellin n ζ‖ = 1 := by
  simp [Blueprint.Analytic.mellin, Complex.norm_exp]

end
end Erdos821.P4Bridge

namespace Erdos821.P4Probe
open Blueprint.Graph Erdos821.P4Bridge
noncomputable section

theorem PatternComparisonBridgeTask_proof : PatternComparisonBridgeTask := by
  intro F P J m hj block Q h ξ θ ζ ε c hV hε hLC f g
  dsimp only
  let ν : Pattern P J F.ell m := choiceBase hj c.val
  let sigma : ℂ := (-1 : ℂ) ^ (∑ j, (ν.changed j).card)
  let fA := bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block false) f
  let gB := bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block true) g
  have hmarg := Erdos821.P4Marg.PatternAveragingTask_proof
    F P J m hj block Q h ξ θ ζ c hV f g
  change idealFullPair (((onePatternFamily F P J m
      (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ) f g =
    idealFullPair (((onePatternFamily F P J m
      (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ) fA gB at hmarg
  change ‖idealFullPair (((onePatternFamily F P J m
      (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ) f g +
    sigma * idealFullPair (((rawFamily F P J m).model 1 ζ).idealRaw θ) fA gB‖ ≤ _
  rw [hmarg, signedFullPair_eq]
  have hrawK : (((rawFamily F P J m).model 1 ζ).idealRaw θ) =
      rawPrefixKernel P J F.ell θ ζ := by
    funext a b
    exact rawModel_idealRaw_eq F P J m hV θ ζ a b
  rw [hrawK]
  change ‖-sigma * idealFullPair (unsignedKernel ν block Q h ξ θ ζ) fA gB +
    sigma * idealFullPair (rawPrefixKernel P J F.ell θ ζ) fA gB‖ ≤ _
  have halg : -sigma * idealFullPair (unsignedKernel ν block Q h ξ θ ζ) fA gB +
      sigma * idealFullPair (rawPrefixKernel P J F.ell θ ζ) fA gB =
      sigma * (idealFullPair (rawPrefixKernel P J F.ell θ ζ) fA gB -
        idealFullPair (unsignedKernel ν block Q h ξ θ ζ) fA gB) := by ring
  have hsigma : ‖sigma‖ = 1 := by simp [sigma]
  rw [halg, norm_mul, hsigma, one_mul]
  have hF : ∀ s a a' b t, fA (labelJoin ν block s a b t) = fA (labelJoin ν block s a' b t) :=
    bigAverage_join_false ν block f
  have hG : ∀ s a b b' t, gB (labelJoin ν block s a b t) = gB (labelJoin ν block s a b' t) :=
    bigAverage_join_true ν block g
  have herror : idealFullPair (rawPrefixKernel P J F.ell θ ζ) fA gB -
      idealFullPair (unsignedKernel ν block Q h ξ θ ζ) fA gB =
      ∑ s : SharedRows ν, (rowWeight (sharedRows ν) s : ℂ) *
        Blueprint.Analytic.mellin (rowProduct (sharedRows ν) s) ζ *
        Blueprint.Analytic.comparisonError (analyticGroups P)
          (sideCounts ν block false) (sideCounts ν block true) Q h ξ
          (θ * rowProduct (sharedRows ν) s) ζ
          (conditionalF ν block fA s) (conditionalG ν block gB s) := by
    rw [rawFullPair_conditional ν block hV θ ζ fA gB hF hG,
      unsignedFullPair_conditional ν block hV, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [analyticError_eq]
    ring
  rw [herror]
  obtain ⟨gF, hgF, hneF⟩ := c.property false
  obtain ⟨gT, hgT, hneT⟩ := c.property true
  have hkF : Blueprint.Analytic.bigSlots (analyticGroups P) (sideCounts ν block false) m := by
    change Blueprint.Analytic.bigSlots (analyticGroups P)
      (selectedCounts (patternAuxCoordinates ν block false)) m
    rw [sideCounts_false_eq]
    exact kFalse_bigSlots hj block c gF hgF hneF
  have hkT : Blueprint.Analytic.bigSlots (analyticGroups P) (sideCounts ν block true) m := by
    change Blueprint.Analytic.bigSlots (analyticGroups P)
      (selectedCounts (patternAuxCoordinates ν block true)) m
    rw [sideCounts_true_eq]
    exact kTrue_bigSlots hj block c gT hgT hneT
  let a : SharedRows ν → ℝ := fun s => ∑ y,
    Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) y *
      ‖conditionalF ν block fA s y‖ ^ 2
  let b : SharedRows ν → ℝ := fun s => ∑ x,
    Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) x *
      ‖conditionalG ν block gB s x‖ ^ 2
  have ha : ∀ s, 0 ≤ a s := fun s => Finset.sum_nonneg (fun y _ =>
    mul_nonneg (sideWeight_pos hV _ y).le (sq_nonneg _))
  have hb : ∀ s, 0 ≤ b s := fun s => Finset.sum_nonneg (fun x _ =>
    mul_nonneg (sideWeight_pos hV _ x).le (sq_nonneg _))
  have he : ∀ s, ‖Blueprint.Analytic.comparisonError (analyticGroups P)
      (sideCounts ν block false) (sideCounts ν block true) Q h ξ
      (θ * rowProduct (sharedRows ν) s) ζ
      (conditionalF ν block fA s) (conditionalG ν block gB s)‖ ≤
      ε * Real.sqrt (a s) * Real.sqrt (b s) := fun s =>
    hLC _ _ hkF hkT _ _ _
  have hbound := weighted_error_sum_bound (rowWeight (sharedRows ν)) a b
    (fun s => Blueprint.Analytic.mellin (rowProduct (sharedRows ν) s) ζ)
    (fun s => Blueprint.Analytic.comparisonError (analyticGroups P)
      (sideCounts ν block false) (sideCounts ν block true) Q h ξ
      (θ * rowProduct (sharedRows ν) s) ζ
      (conditionalF ν block fA s) (conditionalG ν block gB s)) ε
    (fun s => (rowWeight_pos hV _ s).le) ha hb
    (fun s => (analytic_mellin_norm _ _).le) hε he
  have hEf : (∑ s, rowWeight (sharedRows ν) s * a s) ≤ ∑ x, P.idealMass x * ‖f x‖ ^ 2 :=
    (conditionalF_energy_le ν block hV fA).trans
      (bigCoordinateAverage_sqNorm_le P (J + F.ell) hV (patternSideCoordinates ν block false) f)
  have hEg : (∑ s, rowWeight (sharedRows ν) s * b s) ≤ ∑ x, P.idealMass x * ‖g x‖ ^ 2 :=
    (conditionalG_energy_le ν block hV gB).trans
      (bigCoordinateAverage_sqNorm_le P (J + F.ell) hV (patternSideCoordinates ν block true) g)
  apply hbound.trans
  unfold idealVectorNorm
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEf) hε)
    (Real.sqrt_le_sqrt hEg) (Real.sqrt_nonneg _) (mul_nonneg hε (Real.sqrt_nonneg _))

example : PatternComparisonBridgeTask := PatternComparisonBridgeTask_proof

end
end Erdos821.P4Probe
