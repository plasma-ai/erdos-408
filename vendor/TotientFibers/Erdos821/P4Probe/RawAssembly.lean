import Erdos821.P4Probe.PatternBridgeTasks

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Probe
open Blueprint.Graph

noncomputable section

lemma probeFamily_idealRaw_eq (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hj : m ≤ J) (block : P.BigGroup → Bool) (Q : ℕ) (h ξ θ ζ : ℝ)
    (a b : P.BigLabels (J + F.ell)) :
    ((probeFamily F P J m hj block Q h ξ).model 1 ζ).idealRaw θ a b =
      ((rawFamily F P J m).model 1 ζ).idealRaw θ a b +
      ∑ c : ProbeChoice P m block,
        ((onePatternFamily F P J m (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ a b := by
  let term : Pattern P J F.ell m → ℂ := fun ν =>
    ∑ u : P.BigAux J, if ν.matchesBig a b then
      ((ν.bigAuxMass u * ν.freshMass b : ℝ) : ℂ) * ν.coefficient a b u *
        imaginaryPower (ν.DBig a u) ζ * phase (θ * ν.DBig a u) else 0
  change (∑ v, term ((probeFamily F P J m hj block Q h ξ).pattern v)) = _
  calc
    _ = ∑ c : Option (ProbeChoice P m block), term (match c with
        | none => rawPattern P J F.ell m
        | some c => signedPattern hj block Q h ξ c) := by
      apply Fintype.sum_equiv (Fintype.equivFin (Option (ProbeChoice P m block))).symm
      intro v
      rfl
    _ = _ := by
      rw [Fintype.sum_option]
      change term (rawPattern P J F.ell m) + ∑ c, term (signedPattern hj block Q h ξ c) =
        (∑ _v : Fin 1, term (rawPattern P J F.ell m)) +
        ∑ c, ∑ _v : Fin 1, term (signedPattern hj block Q h ξ c)
      simp only [Fin.sum_univ_one]

lemma idealFullPair_add {P : PrimeGroups} {M : ℕ}
    (K H : P.BigLabels M → P.BigLabels M → ℂ) (f g : P.BigLabels M → ℂ) :
    idealFullPair (fun a b => K a b + H a b) f g =
      idealFullPair K f g + idealFullPair H f g := by
  simp [idealFullPair, mul_add, add_mul, Finset.sum_add_distrib]

lemma idealFullPair_sum {P : PrimeGroups} {M : ℕ} {ι : Type*} [Fintype ι]
    (K : ι → P.BigLabels M → P.BigLabels M → ℂ) (f g : P.BigLabels M → ℂ) :
    idealFullPair (fun a b => ∑ i, K i a b) f g =
      ∑ i, idealFullPair (K i) f g := by
  simp only [idealFullPair, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ a, ∑ i, ∑ b, (P.idealMass a : ℂ) * star (f a) * K i a b * g b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma rawFullPair_bound (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hV : ∀ j, 0 < P.V j) (θ ζ : ℝ) (f g : P.BigLabels (J + F.ell) → ℂ) :
    ‖idealFullPair (((rawFamily F P J m).model 1 ζ).idealRaw θ) f g‖ ≤
      idealVectorNorm P (J + F.ell) f * idealVectorNorm P (J + F.ell) g := by
  simpa [idealFullPair, idealVectorNorm] using
    rawModel_normBound F P J m hV θ ζ Finset.univ Finset.univ f g

lemma probeFamily_fullPair_eq (F : FixedData) (P : PrimeGroups) (J m : ℕ)
    (hj : m ≤ J) (block : P.BigGroup → Bool) (Q : ℕ) (h ξ θ ζ : ℝ)
    (f g : P.BigLabels (J + F.ell) → ℂ) :
    idealFullPair (((probeFamily F P J m hj block Q h ξ).model 1 ζ).idealRaw θ) f g =
      idealFullPair (((rawFamily F P J m).model 1 ζ).idealRaw θ) f g +
      ∑ c : ProbeChoice P m block,
        idealFullPair (((onePatternFamily F P J m
          (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ) f g := by
  have hk : ((probeFamily F P J m hj block Q h ξ).model 1 ζ).idealRaw θ =
      fun a b => ((rawFamily F P J m).model 1 ζ).idealRaw θ a b +
        ∑ c : ProbeChoice P m block, ((onePatternFamily F P J m
          (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ a b := by
    funext a b
    exact probeFamily_idealRaw_eq F P J m hj block Q h ξ θ ζ a b
  rw [hk, idealFullPair_add, idealFullPair_sum]

lemma probeFamily_comparison_bound (hbridge : PatternComparisonBridgeTask)
    (F : FixedData) (P : PrimeGroups) (J m : ℕ) (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ θ ζ ε : ℝ)
    (hV : ∀ j, 0 < P.V j) (hε : 0 ≤ ε) (hLC : LocalComparison P m Q h ξ ζ ε)
    (f g : P.BigLabels (J + F.ell) → ℂ) :
    let R := ((rawFamily F P J m).model 1 ζ).idealRaw θ
    let correction := fun c : ProbeChoice P m block =>
      let ν : Pattern P J F.ell m := signedPattern hj block Q h ξ c
      (-1 : ℂ) ^ (∑ j, (ν.changed j).card) * idealFullPair R
        (bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block false) f)
        (bigCoordinateAverage P (J + F.ell) (patternSideCoordinates ν block true) g)
    ‖idealFullPair (((probeFamily F P J m hj block Q h ξ).model 1 ζ).idealRaw θ) f g -
      idealFullPair R f g + ∑ c, correction c‖ ≤
      (Fintype.card (ProbeChoice P m block) : ℝ) * ε *
        idealVectorNorm P (J + F.ell) f * idealVectorNorm P (J + F.ell) g := by
  dsimp only
  rw [probeFamily_fullPair_eq]
  simp only [add_sub_cancel_left]
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ c : ProbeChoice P m block,
        ‖idealFullPair (((onePatternFamily F P J m
          (signedPattern hj block Q h ξ c)).model 1 ζ).idealRaw θ) f g +
          (-1 : ℂ) ^ (∑ j, ((signedPattern hj block Q h ξ c : Pattern P J F.ell m).changed j).card) *
            idealFullPair (((rawFamily F P J m).model 1 ζ).idealRaw θ)
              (bigCoordinateAverage P (J + F.ell)
                (patternSideCoordinates (signedPattern hj block Q h ξ c) block false) f)
              (bigCoordinateAverage P (J + F.ell)
                (patternSideCoordinates (signedPattern hj block Q h ξ c) block true) g)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c : ProbeChoice P m block,
        ε * idealVectorNorm P (J + F.ell) f * idealVectorNorm P (J + F.ell) g := by
      apply Finset.sum_le_sum
      intro c _
      exact hbridge F P J m hj block Q h ξ θ ζ ε c hV hε hLC f g
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end
end Erdos821.P4Probe
