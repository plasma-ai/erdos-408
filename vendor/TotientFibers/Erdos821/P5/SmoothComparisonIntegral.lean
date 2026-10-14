import Erdos821.P5.ComparisonSmoothEndpoints
import Erdos821.P5.ComparisonCutoffSeparation

noncomputable section
open scoped BigOperators Classical
open MeasureTheory

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

def smoothComparisonTerm (G : PrimeGroups) (x Y UA UB a₁ a₂ v lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (E H : Endpoint)
    (mark₁ mark₂ : ℕ → ℂ) (w w' DA DB : ℕ) : ℂ :=
  (Y : ℂ)⁻¹ * comparisonMellinTest UA a₁ a₂ v DA * comparisonMellinTest UB a₁ a₂ v DB *
    star (comparisonSmoothSource G x Y a₁ v lo hi hlo hhi E mark₁ w) *
    comparisonSmoothTarget G x Y a₂ lo hi hlo hhi H mark₂ w'

theorem smoothComparisonTerm_factor (G : PrimeGroups) (x Y UA UB a₁ a₂ v lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (E H : Endpoint)
    (mark₁ mark₂ : ℕ → ℂ) (w w' DA DB : ℕ) :
    smoothComparisonTerm G x Y UA UB a₁ a₂ v lo hi hlo hhi E H mark₁ mark₂ w w' DA DB =
      ((comparisonSourceSizeCutoff lo hi hlo hhi ((w : ℝ) / Y) : ℂ) *
        (comparisonTargetSizeCutoff lo hi hlo hhi ((w' : ℝ) / Y) : ℂ)) *
      separatedComparisonTerm G x Y UA UB a₁ a₂ v E H mark₁ mark₂ w w' DA DB := by
  unfold smoothComparisonTerm comparisonSmoothSource comparisonSmoothTarget separatedComparisonTerm
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  rw [star_mul, hreal]
  ring

theorem smoothComparisonTerm_integrable (G : PrimeGroups) (x Y UA UB a₁ a₂ lo hi : ℝ)
    (hlo : 0 < lo) (hhi : lo < hi) (E H : Endpoint) (mark₁ mark₂ : ℕ → ℂ)
    (w w' DA DB : ℕ) (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α) :
    Integrable (fun ξ => α ξ * smoothComparisonTerm G x Y UA UB a₁ a₂
      (mellinFrequency ξ) lo hi hlo hhi E H mark₁ mark₂ w w' DA DB) := by
  let c : ℂ := (comparisonSourceSizeCutoff lo hi hlo hhi ((w : ℝ) / Y) : ℂ) *
    (comparisonTargetSizeCutoff lo hi hlo hhi ((w' : ℝ) / Y) : ℂ)
  convert (separatedComparisonTerm_integrable G x Y UA UB a₁ a₂ E H mark₁ mark₂
    w w' DA DB α hα).const_mul c using 1
  funext ξ
  rw [smoothComparisonTerm_factor]
  dsimp only [c]
  ring

def smoothComparisonCellCorrelation {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (j : ℤ × ℤ) (χA χB : CharacterIndex Q)
    (x Y a₁ a₂ v lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (E H : Endpoint) (k : ℤ) : ℂ :=
  ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j,
    (freeDrawLaw ν u : ℂ) *
      star (charValue χA (comparisonFreeProduct ν block false u)) *
      star (charValue χB (comparisonFreeProduct ν block true u)) *
      ∑ n ∈ comparisonCommonRoots lo hi Y,
        smoothComparisonTerm G x Y (comparisonCellScale h j.1) (comparisonCellScale h j.2)
          a₁ a₂ v lo hi hlo hhi E H
          (comparisonMarkedEndpoint ν block true h j.2 χB)
          (comparisonMarkedEndpoint ν block false h j.1 χA) n
          ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
          (comparisonFreeProduct ν block false u) (comparisonFreeProduct ν block true u)

/-- Fixed source/target smooth cutoffs are inserted before inversion.
They equal one on the original cutoff support, and the smoothed source
vanishes outside the common roots. The endpoint sequences are now the
actual smooth coefficients required by the major-arc energy task. -/
theorem comparisonCellCorrelation_eq_smooth_integral
    {P : Geometry} {G : PrimeGroups} {J m Q : ℕ}
    (ν : Pattern G.graph J P.ell m) (block : G.graph.BigGroup → Bool)
    (h : ℝ) (hh : 0 < h) (hwidth : Real.exp (2 * h) ≤ 2)
    (j : ℤ × ℤ) (χA χB : CharacterIndex Q) (z : SharedDraw ν)
    (x Z a₁ a₂ lo hi : ℝ) (E H : Endpoint) (Ψ : ℝ → ℂ) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z)
    (hk : |(k : ℝ)| ≤ lo * Z / 8) (hs : Function.support Ψ ⊆ Set.Icc lo hi)
    (α : (Fin 1 → ℝ) → ℂ) (hα : Integrable α)
    (hrep : ∀ y : ℝ, 0 < y → Ψ y = ∫ ξ, α ξ * mellin y (mellinFrequency ξ)) :
    comparisonCellCorrelation ν block h j χA χB x Z a₁ a₂ E H Ψ k
      (fun u => cutoffRoots lo hi Z (freeDrawProduct ν u)) =
      ∫ ξ, α ξ * smoothComparisonCellCorrelation ν block h j χA χB
        x (Z * comparisonJointScale h j) a₁ a₂ (mellinFrequency ξ) lo hi hlo hhi E H k := by
  let Y := Z * comparisonJointScale h j
  have hY : 0 < Y := mul_pos hZ (comparisonJointScale_pos h j)
  let f := fun (u : FreeDraw ν) (n : ℕ) (ξ : Fin 1 → ℝ) =>
    smoothComparisonTerm G x Y (comparisonCellScale h j.1) (comparisonCellScale h j.2)
      a₁ a₂ (mellinFrequency ξ) lo hi hlo hhi E H
      (comparisonMarkedEndpoint ν block true h j.2 χB)
      (comparisonMarkedEndpoint ν block false h j.1 χA) n
      ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
      (comparisonFreeProduct ν block false u) (comparisonFreeProduct ν block true u)
  have hiF (u : FreeDraw ν) (n : ℕ) : Integrable (fun ξ => α ξ * f u n ξ) :=
    smoothComparisonTerm_integrable G x Y _ _ a₁ a₂ lo hi hlo hhi E H _ _ n _ _ _ α hα
  have hterm (u : FreeDraw ν) (hu : comparisonCellPair ν block h u = j)
      (n : ℕ) (hn : n ∈ comparisonCommonRoots lo hi Y) :
      strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat) = ∫ ξ, α ξ * f u n ξ := by
    let n' := ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat
    let c : ℂ := (comparisonSourceSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ) *
      (comparisonTargetSizeCutoff lo hi hlo hhi ((n' : ℝ) / Y) : ℂ)
    have hpos := comparison_common_root_positivity ν block h hh hwidth j u z hu
      lo hi Z k hlo hZ hk n hn
    have hscaled : c * (strippedLiftScalar G x Z a₁ a₂ E H Ψ n n' (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA n')) =
        strippedLiftScalar G x Z a₁ a₂ E H Ψ n n' (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA n') := by
      by_cases hΨ : Ψ ((n : ℝ) / (Z * freeDrawProduct ν u)) = 0
      · simp [strippedLiftScalar, harmonicCutoff, hΨ]
      · have hroot := cutoffRoots_of_nonzero lo hi Z _ n Ψ hZ (freeDrawProduct_pos ν u)
          (hlo.trans hhi) hs hΨ
        have hr := comparison_cutoff_source_target_ranges ν block h hh hwidth j u z hu
          lo hi Z k hlo hhi hZ (by nlinarith [mul_pos hlo hZ]) n hroot
        have hcs := comparisonSourceSizeCutoff_one lo hi hlo hhi ((n : ℝ) / Y)
          ⟨(le_div_iff₀ hY).mpr hr.1, (div_le_iff₀ hY).mpr hr.2.1⟩
        have hct := comparisonTargetSizeCutoff_one lo hi hlo hhi ((n' : ℝ) / Y)
          ⟨(le_div_iff₀ hY).mpr hr.2.2.2.1, (div_le_iff₀ hY).mpr hr.2.2.2.2⟩
        simp only [c, hcs, hct, Complex.ofReal_one, one_mul]
    have hre : strippedLiftScalar G x Z a₁ a₂ E H Ψ n n' (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA n') =
        ∫ ξ, α ξ * separatedComparisonTerm G x Y (comparisonCellScale h j.1)
          (comparisonCellScale h j.2) a₁ a₂ (mellinFrequency ξ) E H
          (comparisonMarkedEndpoint ν block true h j.2 χB)
          (comparisonMarkedEndpoint ν block false h j.1 χA) n n'
          (comparisonFreeProduct ν block false u) (comparisonFreeProduct ν block true u) := by
      rw [freeDrawProduct_eq_comparisonProducts ν block u z]
      apply stripped_scalar_eq_separated_integral G x Z _ _ a₁ a₂ E H _ _ n n' _ _ hZ
        (comparisonCellScale_pos _ _) (comparisonCellScale_pos _ _) hpos.1
        (by dsimp [n']; omega) (comparisonFreeProduct_pos _ _ _ _)
        (comparisonFreeProduct_pos _ _ _ _) Ψ α hrep
    change _ = ∫ ξ, α ξ * f u n ξ
    rw [← hscaled, hre, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    dsimp only [f]
    rw [smoothComparisonTerm_factor]
    dsimp only [c, n']
    ring
  rw [comparisonCellCorrelation_eq_common_roots ν block h hh hwidth j χA χB z
    x Z a₁ a₂ lo hi E H Ψ k hlo hhi hZ hs]
  unfold comparisonCellCorrelation
  let c := fun u : FreeDraw ν => (freeDrawLaw ν u : ℂ) *
    star (charValue χA (comparisonFreeProduct ν block false u)) *
    star (charValue χB (comparisonFreeProduct ν block true u))
  have hrow (u : FreeDraw ν) (hu : comparisonCellPair ν block h u = j) :
      (∑ n ∈ comparisonCommonRoots lo hi Y, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat)) =
      ∫ ξ, ∑ n ∈ comparisonCommonRoots lo hi Y, α ξ * f u n ξ := by
    rw [integral_finsetSum _ (fun n hn => hiF u n)]
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm u hu n hn
  have heq : (∑ u : FreeDraw ν with comparisonCellPair ν block h u = j, c u * ∑ n ∈
      comparisonCommonRoots lo hi Y, strippedLiftScalar G x Z a₁ a₂ E H Ψ n
        ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat (freeDrawProduct ν u) *
        (comparisonMarkedEndpoint ν block true h j.2 χB n *
          comparisonMarkedEndpoint ν block false h j.1 χA
            ((n : ℤ) + k * (freeDrawProduct ν u : ℤ)).toNat)) =
      ∑ u : FreeDraw ν with comparisonCellPair ν block h u = j,
        c u * ∫ ξ, ∑ n ∈ comparisonCommonRoots lo hi Y, α ξ * f u n ξ := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hrow u (Finset.mem_filter.mp hu).2]
  change (∑ u : FreeDraw ν with comparisonCellPair ν block h u = j, c u * _) = _
  rw [heq]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun u hu =>
    (integrable_finsetSum _ (fun n hn => hiF u n)).const_mul (c u))]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold smoothComparisonCellCorrelation
  simp only [c, f, Y]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro n hn
  ring

end Erdos821.P5Core
