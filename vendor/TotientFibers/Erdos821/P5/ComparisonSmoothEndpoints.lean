import Erdos821.P5.PositiveSizeCutoffs
import Erdos821.P5.ComparisonMellinAlgebra
import Erdos821.P5.MarkedEnergyTask

noncomputable section
open scoped BigOperators Classical ContDiff

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem star_weightedMarks (G : PrimeGroups) (q : ℝ) (t : Fin G.size → ℕ)
    (b : Tuple G t → ℂ) (n : ℕ) :
    star (weightedMarks G q t b n) = weightedMarks G q t (fun z => star (b z)) n := by
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  have hsum : (∑ z : Tuple G t, star (if admissibleMarks G t n z then b z else 0)) =
      ∑ z : Tuple G t, if admissibleMarks G t n z then star (b z) else 0 := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hp : admissibleMarks G t n z <;> simp [hp]
  unfold weightedMarks
  simp only [star_mul, star_sum, hreal]
  rw [hsum]
  ring

def comparisonEnergyMark {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (z : Tuple G ν.t) : ℂ :=
  star (comparisonMarkTest ν block side h j χ ((unsharedTupleEquiv ν).symm z))

theorem comparisonEnergyMark_norm_le {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (z : Tuple G ν.t) :
    ‖comparisonEnergyMark ν block side h j χ z‖ ≤ 1 := by
  simpa only [comparisonEnergyMark, norm_star] using comparisonMarkTest_norm_le ν block side h j χ _

theorem comparisonEnergyMark_big_ext {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (z z' : Tuple G ν.t)
    (hzz : ∀ g, g ∈ G.big → z g = z' g) :
    comparisonEnergyMark ν block side h j χ z = comparisonEnergyMark ν block side h j χ z' := by
  apply congrArg star
  apply comparisonMarkTest_big_ext
  intro g
  funext i
  change z g.val _ = z' g.val _
  have hnot : g.val ∉ G.small := of_decide_eq_true g.property
  rw [hzz g.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)]

theorem star_comparisonMarkedEndpoint {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (n : ℕ) :
    star (comparisonMarkedEndpoint ν block side h j χ n) =
      weightedMarks G P.q ν.t (comparisonEnergyMark ν block side h j χ) n := by
  unfold comparisonMarkedEndpoint
  rw [unsharedMarkedFunction_eq_weightedMarks, star_weightedMarks]
  rfl

def comparisonSmoothSource (G : PrimeGroups) (x Y a v lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (E : Endpoint) (mark : ℕ → ℂ) (n : ℕ) : ℂ :=
  (comparisonSourceSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ) *
    comparisonMellinSource G x Y a v E mark n

def comparisonSmoothTarget (G : PrimeGroups) (x Y a lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (E : Endpoint) (mark : ℕ → ℂ) (n : ℕ) : ℂ :=
  (comparisonTargetSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ) *
    comparisonMellinTarget G x a E mark n

theorem comparisonSmoothSource_eq_markedEnergy {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool) (side : Bool)
    (h : ℝ) (j : ℤ) (χ : CharacterIndex Q) (x Y a v lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (hY : 0 < Y) (E : Endpoint) (n : ℕ) (hn : 0 < n) :
    comparisonSmoothSource G x Y a v lo hi hlo hhi E
      (comparisonMarkedEndpoint ν block side h j χ) n =
      mellin Y v * markedEnergyCoefficient P G x Y (-a - v) E ν.t
        (comparisonEnergyMark ν block side h j χ) (comparisonHarmonicSizeCutoff lo hi hlo hhi) n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold comparisonSmoothSource comparisonMellinSource markedEnergyCoefficient comparisonHarmonicSizeCutoff
  rw [star_comparisonMarkedEndpoint, mellin_div _ _ _ hnR hY]
  have hphase : mellin n (-a) * mellin n (-v) = mellin n (-a - v) := by
    rw [← mellin_add]
    congr 1
  rw [show -(-v) = v by ring]
  push_cast
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hNC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hYC, hNC]
  linear_combination hphase * Blueprint.Analytic.mellin Y v * endpoint G x E n *
    weightedMarks G P.q ν.t (comparisonEnergyMark ν block side h j χ) n *
    (comparisonSourceSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ)

theorem comparisonSmoothSource_zero_outside (G : PrimeGroups) (x Y a v lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (hY : 0 < Y) (E : Endpoint) (mark : ℕ → ℂ)
    (n : ℕ) (hn : n ∉ comparisonCommonRoots lo hi Y) :
    comparisonSmoothSource G x Y a v lo hi hlo hhi E mark n = 0 := by
  have hz : comparisonSourceSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) = 0 := by
    by_contra hne
    have hp := comparisonSourceSizeCutoff_support lo hi hlo hhi (Function.mem_support.mpr hne)
    apply hn
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.ceil_le.mpr ((le_div_iff₀ hY).mp hp.1)
    · exact Nat.le_floor ((div_le_iff₀ hY).mp hp.2)
  simp [comparisonSmoothSource, hz]

end Erdos821.P5Core
