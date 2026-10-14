import Erdos821.P4Bridge.RawPairing
import Erdos821.P4Probe.AuxTupleLaw

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Erdos821.P4Bridge
open Blueprint.Graph P4Probe
noncomputable section
variable {P : PrimeGroups} {J ell m : ℕ}

def tupleMultiplier (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (C : ℕ) (θ ζ : ℝ) (a : SideTuple ν block false) (b : SideTuple ν block true) : ℂ :=
  Blueprint.Analytic.mellin
    ((Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a : ℝ) *
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b) ζ *
    Blueprint.Analytic.e ((θ * C) *
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a *
      Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b)

def auxCorrection (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ θ ζ : ℝ) (C : ℕ)
    (a : SideTuple ν block false) (b : SideTuple ν block true) : ℂ :=
  Blueprint.Analytic.expect (analyticGroups P) (sideCounts ν block false) fun dA =>
    Blueprint.Analytic.expect (analyticGroups P) (sideCounts ν block true) fun dB =>
      Blueprint.Analytic.cellKernel (analyticGroups P) (sideCounts ν block false) Q h ξ
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) dA)
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a) *
      Blueprint.Analytic.cellKernel (analyticGroups P) (sideCounts ν block true) Q h ξ
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) dB)
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b) *
      tupleMultiplier ν block C θ ζ dA dB

def correctionConditional (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ θ ζ : ℝ) (C : ℕ)
    (f : SideTuple ν block true → ℂ) (g : SideTuple ν block false → ℂ) : ℂ :=
  Blueprint.Analytic.expect (analyticGroups P) (sideCounts ν block true) fun b =>
    Blueprint.Analytic.expect (analyticGroups P) (sideCounts ν block false) fun a =>
      star (f b) * g a * auxCorrection ν block Q h ξ θ ζ C a b

def unsignedKernel (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ θ ζ : ℝ) (a b : P.BigLabels (J + ell)) : ℂ :=
  ∑ u : P.BigAux J, if ν.matchesBig a b then
    ((ν.bigAuxMass u * ν.freshMass b : ℝ) : ℂ) *
    (selectedKernel ν block false Q h ξ
      (selectedProduct ν block false u) (selectedEndpoint ν block false b) *
    selectedKernel ν block true Q h ξ
      (selectedProduct ν block true u) (selectedEndpoint ν block true a)) *
    imaginaryPower (ν.DBig a u) ζ * phase (θ * ν.DBig a u)
  else 0

lemma unsignedKernel_join (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (hV : ∀ g, 0 < P.V g) (Q : ℕ) (h ξ θ ζ : ℝ)
    (s s' : SharedRows ν) (a a' : SideTuple ν block false) (b b' : SideTuple ν block true)
    (t t' : P.BigLabels ell) :
    unsignedKernel ν block Q h ξ θ ζ (labelJoin ν block s a b t) (labelJoin ν block s' a' b' t') =
      if s = s' then
        ((Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block false) a' *
          Blueprint.Analytic.tupleWeight (analyticGroups P) (sideCounts ν block true) b' *
          P.idealMass t' : ℝ) : ℂ) *
        Blueprint.Analytic.mellin (rowProduct (sharedRows ν) s) ζ *
        auxCorrection ν block Q h ξ θ ζ (rowProduct (sharedRows ν) s) a' b
      else 0 := by
  unfold unsignedKernel
  by_cases hs : s = s'
  · subst s'
    simp only [matchesBig_join, ite_true]
    let C := rowProduct (sharedRows ν) s
    let H : SideTuple ν block false → SideTuple ν block true → ℂ := fun dA dB =>
      Blueprint.Analytic.cellKernel (analyticGroups P) (sideCounts ν block false) Q h ξ
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) dA)
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block false) a') *
      Blueprint.Analytic.cellKernel (analyticGroups P) (sideCounts ν block true) Q h ξ
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) dB)
        (Blueprint.Analytic.product (analyticGroups P) (sideCounts ν block true) b) *
      tupleMultiplier ν block C θ ζ dA dB
    have ht (u : P.BigAux J) :
        ((ν.bigAuxMass u * ν.freshMass (labelJoin ν block s a' b' t') : ℝ) : ℂ) *
        (selectedKernel ν block false Q h ξ (selectedProduct ν block false u)
          (selectedEndpoint ν block false (labelJoin ν block s a' b' t')) *
        selectedKernel ν block true Q h ξ (selectedProduct ν block true u)
          (selectedEndpoint ν block true (labelJoin ν block s a b t))) *
        imaginaryPower (ν.DBig (labelJoin ν block s a b t) u) ζ *
        phase (θ * ν.DBig (labelJoin ν block s a b t) u) =
        (ν.freshMass (labelJoin ν block s a' b' t') : ℂ) * Blueprint.Analytic.mellin C ζ *
          ((ν.bigAuxMass u : ℂ) *
            H (selectedAuxTuple ν block false u) (selectedAuxTuple ν block true u)) := by
      rw [DBig_split ν block, sharedPrefixProduct_join_rows,
        selectedEndpoint_join_false, selectedEndpoint_join_true,
        selectedKernel_eq ν block false hV, selectedKernel_eq ν block true hV]
      have hm := multiplier_factor C (selectedProduct ν block false u)
        (selectedProduct ν block true u) (rowProduct_pos _ s)
        (selectedProduct_pos ν block false u) (selectedProduct_pos ν block true u) θ ζ
      dsimp only [C] at hm
      dsimp only [H, tupleMultiplier, C, sideCounts]
      simp only [selectedAuxTuple_product, Complex.ofReal_mul, Nat.cast_mul, mul_assoc]
      simp only [mul_assoc] at hm
      linear_combination ((ν.bigAuxMass u : ℂ) *
        (ν.freshMass (labelJoin ν block s a' b' t') : ℂ) *
        (Blueprint.Analytic.cellKernel (analyticGroups P)
          (selectedCounts (patternAuxCoordinates ν block false)) Q h ξ
          (selectedProduct ν block false u)
          (Blueprint.Analytic.product (analyticGroups P)
            (selectedCounts (patternAuxCoordinates ν block false)) a') *
        Blueprint.Analytic.cellKernel (analyticGroups P)
          (selectedCounts (patternAuxCoordinates ν block true)) Q h ξ
          (selectedProduct ν block true u)
          (Blueprint.Analytic.product (analyticGroups P)
            (selectedCounts (patternAuxCoordinates ν block true)) b))) * hm
    simp_rw [ht]
    rw [← Finset.mul_sum, bigAux_selected_pair_expect ν block hV H,
      freshMass_join ν block hV]
    unfold auxCorrection Blueprint.Analytic.expect
    dsimp only [H]
    simp only [Finset.mul_sum, Complex.ofReal_mul, mul_assoc]
    rfl
  · simp [matchesBig_join, hs]

lemma analyticError_eq (ν : Pattern P J ell m) (block : P.BigGroup → Bool)
    (Q : ℕ) (h ξ θ ζ : ℝ) (C : ℕ)
    (f : SideTuple ν block true → ℂ) (g : SideTuple ν block false → ℂ) :
    Blueprint.Analytic.comparisonError (analyticGroups P)
      (sideCounts ν block false) (sideCounts ν block true) Q h ξ (θ * C) ζ f g =
      rawConditional ν block C θ ζ f g - correctionConditional ν block Q h ξ θ ζ C f g := by
  unfold Blueprint.Analytic.comparisonError rawConditional correctionConditional
    auxCorrection tupleMultiplier Blueprint.Analytic.expect
  simp only [mul_sub, Finset.sum_sub_distrib, mul_assoc]

end
end Erdos821.P4Bridge
