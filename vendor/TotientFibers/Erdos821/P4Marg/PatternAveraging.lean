import Erdos821.P4Probe.PatternAveragingTask
import Erdos821.P4Probe.PatternMasses
import Erdos821.P4Probe.BigDuality

set_option autoImplicit false
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P4Marg
open Blueprint.Graph P4Probe

noncomputable section

variable {P : PrimeGroups} {J ell m : ℕ}

def replaceBigLabels {P : PrimeGroups} {M : ℕ}
    (S : P.BigGroup → Finset (Fin M)) (a y : P.BigLabels M) : P.BigLabels M :=
  fun g i => if i ∈ S g then y g i else a g i

lemma slot_injective (ν : Pattern P J ell m) : Function.Injective ν.slot := by
  intro i j hij
  apply Fin.ext
  simpa [Pattern.slot] using congrArg Fin.val hij

lemma slot_not_mem_patternSideCoordinates (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (g : P.BigGroup) (i : Fin J)
    (hi : i ∉ ν.changed g.val) :
    ν.slot i ∉ patternSideCoordinates ν block side g := by
  intro hmem
  by_cases hb : block g = side
  · simp only [patternSideCoordinates, hb, ite_true] at hmem
    obtain ⟨j, hj, hslot⟩ := Finset.mem_image.mp hmem
    have hji : j = i := slot_injective ν hslot
    exact hi (hji ▸ hj)
  · simp [patternSideCoordinates, hb] at hmem

lemma shared_not_mem_patternSideCoordinates (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool) (g : P.BigGroup)
    (i : Fin (J + ell)) (hi : ν.shared g.val i) :
    i ∉ patternSideCoordinates ν block side g := by
  intro hmem
  by_cases hb : block g = side
  · simp only [patternSideCoordinates, hb, ite_true] at hmem
    obtain ⟨j, hj, hslot⟩ := Finset.mem_image.mp hmem
    obtain ⟨j', hshared, hnot⟩ := hi
    have hji : j' = j := slot_injective ν (hshared.trans hslot.symm)
    exact hnot (hji ▸ hj)
  · simp [patternSideCoordinates, hb] at hmem

lemma sharedLabelMass_replace_eq (ν : Pattern P J ell m)
    (S : P.BigGroup → Finset (Fin (J + ell)))
    (hS : ∀ g i, ν.shared g.val i → i ∉ S g)
    (a y : P.BigLabels (J + ell)) :
    sharedLabelMass ν (replaceBigLabels S a y) = sharedLabelMass ν a := by
  unfold sharedLabelMass
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : ν.shared g.val i
  · simp [hi, replaceBigLabels, hS g i hi]
  · simp [hi]

lemma matchesBig_replace_left (ν : Pattern P J ell m)
    (S : P.BigGroup → Finset (Fin (J + ell)))
    (hS : ∀ g i, ν.shared g.val i → i ∉ S g)
    (a y b : P.BigLabels (J + ell)) :
    ν.matchesBig (replaceBigLabels S a y) b ↔ ν.matchesBig a b := by
  constructor
  · intro h g i hi
    have hnot := hS g i hi
    simpa [replaceBigLabels, hnot] using h g i hi
  · intro h g i hi
    have hnot := hS g i hi
    simpa [replaceBigLabels, hnot] using h g i hi

lemma matchesBig_replace_right (ν : Pattern P J ell m)
    (S : P.BigGroup → Finset (Fin (J + ell)))
    (hS : ∀ g i, ν.shared g.val i → i ∉ S g)
    (a b y : P.BigLabels (J + ell)) :
    ν.matchesBig a (replaceBigLabels S b y) ↔ ν.matchesBig a b := by
  constructor
  · intro h g i hi
    have hnot := hS g i hi
    simpa [replaceBigLabels, hnot] using h g i hi
  · intro h g i hi
    have hnot := hS g i hi
    simpa [replaceBigLabels, hnot] using h g i hi

lemma sharedPrefixProduct_replace_eq (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool)
    (a y : P.BigLabels (J + ell)) :
    sharedPrefixProduct ν (replaceBigLabels (patternSideCoordinates ν block side) a y) =
      sharedPrefixProduct ν a := by
  unfold sharedPrefixProduct
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ν.changed g.val
  · simp [hi]
  · simp [hi, replaceBigLabels,
      slot_not_mem_patternSideCoordinates ν block side g i hi]

lemma DBig_replace_side_eq (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool)
    (a y : P.BigLabels (J + ell)) (u : P.BigAux J) :
    ν.DBig (replaceBigLabels (patternSideCoordinates ν block side) a y) u =
      ν.DBig a u := by
  rw [DBig_split ν block (replaceBigLabels (patternSideCoordinates ν block side) a y) u,
    DBig_split ν block a u,
    sharedPrefixProduct_replace_eq ν block side a y]

lemma selectedEndpoint_replace_other (ν : Pattern P J ell m)
    (block : P.BigGroup → Bool) (side : Bool)
    (a y : P.BigLabels (J + ell)) :
    selectedEndpoint ν block (!side)
      (replaceBigLabels (patternSideCoordinates ν block side) a y) =
    selectedEndpoint ν block (!side) a := by
  unfold selectedEndpoint
  apply Finset.prod_congr rfl
  intro g _
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : block g = !side ∧ i ∈ ν.changed g.val
  · have hb : block g ≠ side := by
      cases side <;> simp_all
    simp [h, replaceBigLabels, patternSideCoordinates]
  · simp [h]

def patternDensity (ν : Pattern P J ell m) (θ ζ : ℝ)
    (a b : P.BigLabels (J + ell)) : ℂ :=
  ∑ u : P.BigAux J,
    if ν.matchesBig a b then
      ((ν.bigAuxMass u / sharedLabelMass ν a : ℝ) * ν.coefficient a b u *
        imaginaryPower (ν.DBig a u) ζ * phase (θ * ν.DBig a u))
    else 0

def modelDensity {F : FixedData} (A : Model F P J m) (θ ζ : ℝ)
    (a b : P.BigLabels (J + F.ell)) : ℂ :=
  ∑ v, patternDensity (A.pattern v) θ ζ a b

lemma signedPattern_coefficient_source_mix (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (c : ProbeChoice P m block) (a y b : P.BigLabels (J + ell)) (u : P.BigAux J) :
    (signedPattern (ell := ell) hj block Q h ξ c).coefficient
        (replaceBigLabels
          (patternSideCoordinates (signedPattern (ell := ell) hj block Q h ξ c) block false) a y) b u =
      (signedPattern (ell := ell) hj block Q h ξ c).coefficient a b u := by
  have hcoords :
      patternSideCoordinates (signedPattern (ell := ell) hj block Q h ξ c) block false =
        patternSideCoordinates (choiceBase (ell := ell) hj c.val) block false := rfl
  rw [hcoords]
  simp only [signedPattern]
  have hendpoint :
      selectedEndpoint (choiceBase (ell := ell) hj c.val) block true
          (replaceBigLabels (patternSideCoordinates (choiceBase (ell := ell) hj c.val)
            block false) a y) =
        selectedEndpoint (choiceBase (ell := ell) hj c.val) block true a := by
    simpa using selectedEndpoint_replace_other
      (choiceBase (ell := ell) hj c.val) block false a y
  rw [hendpoint]

lemma signedPattern_coefficient_target_mix (hj : m ≤ J)
    (block : P.BigGroup → Bool) (Q : ℕ) (h ξ : ℝ)
    (c : ProbeChoice P m block) (a b y : P.BigLabels (J + ell)) (u : P.BigAux J) :
    (signedPattern (ell := ell) hj block Q h ξ c).coefficient a
        (replaceBigLabels
          (patternSideCoordinates (signedPattern (ell := ell) hj block Q h ξ c) block true) b y) u =
      (signedPattern (ell := ell) hj block Q h ξ c).coefficient a b u := by
  have hcoords :
      patternSideCoordinates (signedPattern (ell := ell) hj block Q h ξ c) block true =
        patternSideCoordinates (choiceBase (ell := ell) hj c.val) block true := rfl
  rw [hcoords]
  simp only [signedPattern]
  have hendpoint :
      selectedEndpoint (choiceBase (ell := ell) hj c.val) block false
          (replaceBigLabels (patternSideCoordinates (choiceBase (ell := ell) hj c.val)
            block true) b y) =
        selectedEndpoint (choiceBase (ell := ell) hj c.val) block false b := by
    simpa using selectedEndpoint_replace_other
      (choiceBase (ell := ell) hj c.val) block true b y
  rw [hendpoint]

lemma patternDensity_replace_left (ν : Pattern P J ell m)
    (S : P.BigGroup → Finset (Fin (J + ell)))
    (hS : ∀ g i, ν.shared g.val i → i ∉ S g)
    (θ ζ : ℝ) (a y b : P.BigLabels (J + ell))
    (hcoef : ∀ u, ν.coefficient (replaceBigLabels S a y) b u = ν.coefficient a b u)
    (hDBig : ∀ u, ν.DBig (replaceBigLabels S a y) u = ν.DBig a u) :
    patternDensity ν θ ζ (replaceBigLabels S a y) b = patternDensity ν θ ζ a b := by
  unfold patternDensity
  rw [matchesBig_replace_left ν S hS a y b]
  by_cases hm : ν.matchesBig a b
  · simp only [if_pos hm]
    rw [sharedLabelMass_replace_eq ν S hS a y]
    apply Finset.sum_congr rfl
    intro u _
    rw [hcoef u, hDBig u]
  · simp only [if_neg hm]

lemma patternDensity_replace_right (ν : Pattern P J ell m)
    (S : P.BigGroup → Finset (Fin (J + ell)))
    (hS : ∀ g i, ν.shared g.val i → i ∉ S g)
    (θ ζ : ℝ) (a b y : P.BigLabels (J + ell))
    (hcoef : ∀ u, ν.coefficient a (replaceBigLabels S b y) u = ν.coefficient a b u) :
    patternDensity ν θ ζ a (replaceBigLabels S b y) = patternDensity ν θ ζ a b := by
  unfold patternDensity
  rw [matchesBig_replace_right ν S hS a b y]
  by_cases hm : ν.matchesBig a b
  · simp only [if_pos hm]
    apply Finset.sum_congr rfl
    intro u _
    rw [hcoef u]
  · simp only [if_neg hm]

lemma onePattern_idealRaw_eq_density (F : FixedData)
    (ν : Pattern P J F.ell m) (hV : ∀ g, 0 < P.V g) (θ ζ : ℝ)
    (a b : P.BigLabels (J + F.ell)) :
    ((onePatternFamily F P J m ν).model 1 ζ).idealRaw θ a b =
      (P.idealMass b : ℂ) *
        modelDensity ((onePatternFamily F P J m ν).model 1 ζ) θ ζ a b := by
  simpa [modelDensity, patternDensity, onePatternFamily, Family.model] using
    idealRaw_eq_targetMass
      (A := (onePatternFamily F P J m ν).model 1 ζ) hV θ a b

lemma modelDensity_replace_left {F : FixedData} (A : Model F P J m)
    (S : P.BigGroup → Finset (Fin (J + F.ell)))
    (hS : ∀ v g i, (A.pattern v).shared g.val i → i ∉ S g)
    (θ ζ : ℝ) (a y b : P.BigLabels (J + F.ell))
    (hcoef : ∀ v u,
      (A.pattern v).coefficient (replaceBigLabels S a y) b u =
        (A.pattern v).coefficient a b u)
    (hDBig : ∀ v u,
      (A.pattern v).DBig (replaceBigLabels S a y) u = (A.pattern v).DBig a u) :
    modelDensity A θ ζ (replaceBigLabels S a y) b = modelDensity A θ ζ a b := by
  unfold modelDensity
  apply Finset.sum_congr rfl
  intro v _
  exact patternDensity_replace_left (A.pattern v) S (hS v) θ ζ a y b (hcoef v) (hDBig v)

lemma modelDensity_replace_right {F : FixedData} (A : Model F P J m)
    (S : P.BigGroup → Finset (Fin (J + F.ell)))
    (hS : ∀ v g i, (A.pattern v).shared g.val i → i ∉ S g)
    (θ ζ : ℝ) (a b y : P.BigLabels (J + F.ell))
    (hcoef : ∀ v u,
      (A.pattern v).coefficient a (replaceBigLabels S b y) u =
        (A.pattern v).coefficient a b u) :
    modelDensity A θ ζ a (replaceBigLabels S b y) = modelDensity A θ ζ a b := by
  unfold modelDensity
  apply Finset.sum_congr rfl
  intro v _
  exact patternDensity_replace_right (A.pattern v) S (hS v) θ ζ a b y (hcoef v)

lemma bigCoordinateAverage_eq_self_of_replace_invariant (P : PrimeGroups) (M : ℕ)
    (hV : ∀ g, 0 < P.V g) (S : P.BigGroup → Finset (Fin M))
    (f : P.BigLabels M → ℂ)
    (hinv : ∀ a y, f (replaceBigLabels S a y) = f a) :
    bigCoordinateAverage P M S f = f := by
  funext a
  unfold bigCoordinateAverage
  have htotal : (∑ y : P.BigLabels M, (P.idealMass y : ℂ)) = 1 := by
    exact_mod_cast idealMass_sum P M hV
  calc
    (∑ y, (P.idealMass y : ℂ) * f (replaceBigLabels S a y)) =
        ∑ y, (P.idealMass y : ℂ) * f a := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hinv]
    _ = f a := by rw [← Finset.sum_mul, htotal]; simp

theorem PatternAveragingTask_proof : P4Probe.PatternAveragingTask := by
  intro F P J m hj block Q h ξ θ ζ c hV f g
  let ν : Pattern P J F.ell m := signedPattern hj block Q h ξ c
  let A : Model F P J m := (onePatternFamily F P J m ν).model 1 ζ
  let S₀ : P.BigGroup → Finset (Fin (J + F.ell)) :=
    patternSideCoordinates ν block false
  let S₁ : P.BigGroup → Finset (Fin (J + F.ell)) :=
    patternSideCoordinates ν block true
  let H : P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → ℂ :=
    modelDensity A θ ζ
  let K : P.BigLabels (J + F.ell) → P.BigLabels (J + F.ell) → ℂ :=
    A.idealRaw θ
  let fA := bigCoordinateAverage P (J + F.ell) S₀ f
  let gB := bigCoordinateAverage P (J + F.ell) S₁ g
  change idealFullPair K f g = idealFullPair K fA gB
  have hK : K = fun a b => (P.idealMass b : ℂ) * H a b := by
    funext a b
    exact onePattern_idealRaw_eq_density F ν hV θ ζ a b
  have hS₀ : ∀ v g i, (A.pattern v).shared g.val i → i ∉ S₀ g := by
    intro v g i hi
    change ν.shared g.val i at hi
    change i ∉ patternSideCoordinates ν block false g
    exact shared_not_mem_patternSideCoordinates ν block false g i hi
  have hS₁ : ∀ v g i, (A.pattern v).shared g.val i → i ∉ S₁ g := by
    intro v g i hi
    change ν.shared g.val i at hi
    change i ∉ patternSideCoordinates ν block true g
    exact shared_not_mem_patternSideCoordinates ν block true g i hi
  have hKfixed : ∀ b,
      bigCoordinateAverage P (J + F.ell) S₀ (fun a => K a b) = fun a => K a b := by
    intro b
    apply bigCoordinateAverage_eq_self_of_replace_invariant P (J + F.ell) hV S₀
      (fun a => K a b)
    intro a y
    have hcoef : ∀ v u,
        (A.pattern v).coefficient (replaceBigLabels S₀ a y) b u =
          (A.pattern v).coefficient a b u := by
      intro v u
      change ν.coefficient (replaceBigLabels S₀ a y) b u = ν.coefficient a b u
      exact signedPattern_coefficient_source_mix (ell := F.ell) hj block Q h ξ c a y b u
    have hDBig : ∀ v u,
        (A.pattern v).DBig (replaceBigLabels S₀ a y) u = (A.pattern v).DBig a u := by
      intro v u
      change ν.DBig (replaceBigLabels S₀ a y) u = ν.DBig a u
      exact DBig_replace_side_eq ν block false a y u
    have hdensity := modelDensity_replace_left A S₀ hS₀ θ ζ a y b hcoef hDBig
    calc
      K (replaceBigLabels S₀ a y) b = (P.idealMass b : ℂ) * H (replaceBigLabels S₀ a y) b := by
        rw [hK]
      _ = (P.idealMass b : ℂ) * H a b := by
        exact congrArg (fun z => (P.idealMass b : ℂ) * z) hdensity
      _ = K a b := by rw [hK]
  have hHfixed : ∀ a,
      bigCoordinateAverage P (J + F.ell) S₁ (fun b => H a b) = fun b => H a b := by
    intro a
    apply bigCoordinateAverage_eq_self_of_replace_invariant P (J + F.ell) hV S₁
      (fun b => H a b)
    intro b y
    have hcoef : ∀ v u,
        (A.pattern v).coefficient a (replaceBigLabels S₁ b y) u =
          (A.pattern v).coefficient a b u := by
      intro v u
      change ν.coefficient a (replaceBigLabels S₁ b y) u = ν.coefficient a b u
      exact signedPattern_coefficient_target_mix (ell := F.ell) hj block Q h ξ c a b y u
    exact modelDensity_replace_right A S₁ hS₁ θ ζ a b y hcoef
  have hsource := idealFullPair_source_average
    P (J + F.ell) S₀ K hKfixed f g
  have hsource' :
      idealFullPair (fun a b => (P.idealMass b : ℂ) * H a b) fA g =
        idealFullPair (fun a b => (P.idealMass b : ℂ) * H a b) f g := by
    simpa only [hK] using hsource
  have htarget := idealFullPair_target_average
    P (J + F.ell) S₁ H hHfixed fA g
  calc
    idealFullPair K f g =
        idealFullPair (fun a b => (P.idealMass b : ℂ) * H a b) f g := by rw [hK]
    _ = idealFullPair (fun a b => (P.idealMass b : ℂ) * H a b) fA g := hsource'.symm
    _ = idealFullPair (fun a b => (P.idealMass b : ℂ) * H a b) fA gB := htarget.symm
    _ = idealFullPair K fA gB := by rw [hK]

end
end Erdos821.P4Marg

example : Erdos821.P4Probe.PatternAveragingTask :=
  Erdos821.P4Marg.PatternAveragingTask_proof

