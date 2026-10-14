import Erdos821.P5.ComparisonSupport

noncomputable section
open scoped BigOperators Classical ContDiff Topology
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def comparisonSourceSizeBump (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    ContDiffBump (hi + 3 * lo / 4) where
  rIn := hi
  rOut := hi + lo / 4
  rIn_pos := hlo.trans hhi
  rIn_lt_rOut := by linarith

def comparisonTargetSizeBump (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    ContDiffBump (hi + 3 * lo / 4) where
  rIn := hi + lo / 4
  rOut := hi + lo / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def comparisonSourceSizeCutoff (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (y : ℝ) : ℝ :=
  comparisonSourceSizeBump lo hi hlo hhi y

def comparisonTargetSizeCutoff (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (y : ℝ) : ℝ :=
  comparisonTargetSizeBump lo hi hlo hhi y

theorem comparisonSourceSizeCutoff_one (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (y : ℝ) (hy : y ∈ Set.Icc lo (2 * hi)) :
    comparisonSourceSizeCutoff lo hi hlo hhi y = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  dsimp [comparisonSourceSizeBump]
  constructor <;> linarith [hy.1, hy.2]

theorem comparisonTargetSizeCutoff_one (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (y : ℝ) (hy : y ∈ Set.Icc (lo / 2) (2 * hi + lo)) :
    comparisonTargetSizeCutoff lo hi hlo hhi y = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  dsimp [comparisonTargetSizeBump]
  constructor <;> linarith [hy.1, hy.2]

theorem comparisonSourceSizeCutoff_support (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    Function.support (comparisonSourceSizeCutoff lo hi hlo hhi) ⊆
      Set.Icc (lo / 2) (2 * hi + lo) := by
  intro y hy
  have hb : y ∈ Metric.ball (hi + 3 * lo / 4) (hi + lo / 4) := by
    change y ∈ Function.support (comparisonSourceSizeBump lo hi hlo hhi) at hy
    rw [ContDiffBump.support_eq] at hy
    exact hy
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hb
  constructor <;> linarith [hb.1, hb.2]

theorem comparisonTargetSizeCutoff_support (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    Function.support (comparisonTargetSizeCutoff lo hi hlo hhi) ⊆
      Set.Icc (lo / 4) (2 * hi + 5 * lo / 4) := by
  intro y hy
  have hb : y ∈ Metric.ball (hi + 3 * lo / 4) (hi + lo / 2) := by
    change y ∈ Function.support (comparisonTargetSizeBump lo hi hlo hhi) at hy
    rw [ContDiffBump.support_eq] at hy
    exact hy
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hb
  constructor <;> linarith [hb.1, hb.2]

theorem comparisonSourceSizeCutoff_norm_le (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (y : ℝ) : ‖comparisonSourceSizeCutoff lo hi hlo hhi y‖ ≤ 1 := by
  rw [comparisonSourceSizeCutoff, Real.norm_eq_abs,
    abs_of_nonneg (ContDiffBump.nonneg _)]
  exact ContDiffBump.le_one _

theorem comparisonTargetSizeCutoff_norm_le (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (y : ℝ) : ‖comparisonTargetSizeCutoff lo hi hlo hhi y‖ ≤ 1 := by
  rw [comparisonTargetSizeCutoff, Real.norm_eq_abs,
    abs_of_nonneg (ContDiffBump.nonneg _)]
  exact ContDiffBump.le_one _

def comparisonHarmonicSizeCutoff (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) (y : ℝ) : ℂ :=
  (comparisonSourceSizeCutoff lo hi hlo hhi y : ℂ) / (y : ℂ)

theorem comparisonHarmonicSizeCutoff_support (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    Function.support (comparisonHarmonicSizeCutoff lo hi hlo hhi) ⊆
      Set.Icc (lo / 2) (2 * hi + lo) := by
  intro y hy
  apply comparisonSourceSizeCutoff_support lo hi hlo hhi
  apply Function.mem_support.mpr
  intro hz
  have hne := Function.mem_support.mp hy
  exact hne (by simp [comparisonHarmonicSizeCutoff, hz])

theorem comparisonHarmonicSizeCutoff_contDiff (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    ContDiff ℝ ∞ (comparisonHarmonicSizeCutoff lo hi hlo hhi) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y = 0
  · subst y
    have hz : comparisonHarmonicSizeCutoff lo hi hlo hhi =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds (by linarith : (0 : ℝ) < lo / 2)] with y hy
      have hs : comparisonSourceSizeCutoff lo hi hlo hhi y = 0 := by
        by_contra hne
        have hp := comparisonSourceSizeCutoff_support lo hi hlo hhi (Function.mem_support.mpr hne)
        linarith [hp.1]
      simp [comparisonHarmonicSizeCutoff, hs]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · have hr : ContDiffAt ℝ ∞
        (fun y => comparisonSourceSizeCutoff lo hi hlo hhi y / y) y :=
      (comparisonSourceSizeBump lo hi hlo hhi).contDiffAt.div contDiffAt_id hy
    change ContDiffAt ℝ ∞ (fun y : ℝ =>
      (comparisonSourceSizeCutoff lo hi hlo hhi y : ℂ) / (y : ℂ)) y
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_div] using
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hr


/-- A fixed smooth positive-interval cutoff has fixed derivative constants.
These constants are independent of x, the lift depth and all free draws. -/
theorem fixed_positive_cutoff_bounds (f : ℝ → ℂ) (lo hi : ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : Function.support f ⊆ Set.Icc lo hi) :
    ∃ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) ∧
      ∀ x C : ℝ, 1 ≤ L x → 0 ≤ C → CutoffBound x C lo hi f bounds := by
  have hc : HasCompactSupport f := by
    change IsCompact (closure (Function.support f))
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  have hder : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖iteratedDeriv j f y‖ ≤ C := by
    intro j
    obtain ⟨C, hC, hd⟩ := hc.exists_bound_iteratedFDeriv hf j
    refine ⟨C, hC, ?_⟩
    intro y
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hd j le_rfl y
  choose bounds hb hd using hder
  refine ⟨bounds, hb, ?_⟩
  intro x C hL hC
  refine ⟨hf, hs, ?_⟩
  intro j y
  exact (hd j y).trans (le_mul_of_one_le_right (hb j)
    (Real.one_le_rpow hL (by positivity)))

theorem comparisonHarmonicSizeCutoff_bounds (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    ∃ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) ∧
      ∀ x C : ℝ, 1 ≤ L x → 0 ≤ C →
        CutoffBound x C (lo / 2) (2 * hi + lo)
          (comparisonHarmonicSizeCutoff lo hi hlo hhi) bounds :=
  fixed_positive_cutoff_bounds _ _ _ (comparisonHarmonicSizeCutoff_contDiff lo hi hlo hhi)
    (comparisonHarmonicSizeCutoff_support lo hi hlo hhi)

theorem comparisonTargetSizeCutoff_bounds (lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi) :
    ∃ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) ∧
      ∀ x C : ℝ, 1 ≤ L x → 0 ≤ C →
        CutoffBound x C (lo / 4) (2 * hi + 5 * lo / 4)
          (fun y => (comparisonTargetSizeCutoff lo hi hlo hhi y : ℂ)) bounds :=
  fixed_positive_cutoff_bounds _ _ _
    (Complex.ofRealCLM.contDiff.comp (comparisonTargetSizeBump lo hi hlo hhi).contDiff)
    (by
      intro y hy
      apply comparisonTargetSizeCutoff_support lo hi hlo hhi
      simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hy)

end Erdos821.P5Core
