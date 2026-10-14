module

public import Erdos408.OneSided.Moment.RootReplacement.Boundary
public import Erdos408.OneSided.Moment.RootReplacement.Mass

/-!
# Assembly of the root replacement

Steps 1 and 5 of the assembly in `blueprint/one_sided_type_ii.md` §15. By RR1
(`detMoment_eq_sum_rootMoment`) and RR2 over configurations (`rootMoment_eq_sum_conf`), the
normalized moment minus the Riemann sum is `∑_ω c(ω) D(ω)`, where `D(ω)` is the
per-configuration difference of `norm_sum_positions_sub_le`. Only live configurations have
`D(ω) ≠ 0`, since the roots and the cube corners lie in the root box. So the difference is at
most the live coefficient mass times the largest per-configuration error.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

/-- The line average is additive over finite sums. -/
theorem lineAverage_sum (x : ℝ) (d : Data K) {ι : Type*} (s : Finset ι)
    (F : ι → (ℕ → ℕ) → ℂ) :
    lineAverage x d (fun ℓ => ∑ i ∈ s, F i ℓ) = ∑ i ∈ s, lineAverage x d (F i) := by
  simp only [lineAverage, mul_sum]
  rw [sum_comm]

/-- The line average commutes with constant factors. -/
theorem lineAverage_const_mul (x : ℝ) (d : Data K) (c : ℂ) (F : (ℕ → ℕ) → ℂ) :
    lineAverage x d (fun ℓ => c * F ℓ) = c * lineAverage x d F := by
  simp only [lineAverage, ← mul_sum]
  ring

/-- The per-configuration difference `D(ω)`: the normalized root sum of `A(ω, ·) F_ω` over
the positions, minus `c₂` times its Riemann sum at the cube corners. -/
def confDiff (q x : ℝ) (d : Data K) (Y d₀ : ℝ) (n : ℕ) (ω : Conf x d Y d₀) : ℂ :=
  ((d₀ * Y * d.Hm * d.Hn : ℝ) : ℂ)⁻¹ * ∑ P₀ ∈ positions d Y d₀,
      (confInd x d Y d₀ ω P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
        ∏ p ∈ bandPrimes x d, (confLineFactor q p ω (rootLines P₀ p) : ℂ) -
    (primitiveDensity : ℂ) * (((n : ℂ) ^ 3)⁻¹ * ∑ i ∈ cubeIndices n,
      (confInd x d Y d₀ ω (d₀ * Y * d.Hm * (1 + i.1 / n)) (d.Hn * (1 + i.2.1 / n))
        (i.2.2 / n) : ℂ) *
        lineAverage x d (fun ℓ => ∏ p ∈ bandPrimes x d, (confLineFactor q p ω (ℓ p) : ℂ)))

/-- The normalized moment minus the Riemann sum is `∑_ω c(ω) D(ω)`. -/
theorem sub_eq_sum_confDiff {q A₀ x : ℝ} (hq : 0 < q) {d : Data K} {Y d₀ : ℝ}
    (hU : 0 < d₀ * Y * d.Hm) (hV : 0 ≤ d.Hn) (hR : 0 < momentPower x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (n : ℕ) :
    ((d₀ * Y * d.Hm * d.Hn : ℝ) : ℂ)⁻¹ * detMoment q A₀ x d Y d₀ -
        (primitiveDensity : ℂ) * (((n : ℂ) ^ 3)⁻¹ * ∑ i ∈ cubeIndices n,
          lineAverage x d fun ℓ => rootMoment q A₀ x d Y d₀ (d₀ * Y * d.Hm * (1 + i.1 / n))
            (d.Hn * (1 + i.2.1 / n)) (i.2.2 / n) ℓ) =
      ∑ ω : Conf x d Y d₀, confCoeff A₀ x d Y d₀ ω * confDiff q x d Y d₀ n ω := by
  -- step: expand every root moment over the configurations
  rw [detMoment_eq_sum_rootMoment q A₀ x hU hV]
  simp only [rootMoment_eq_sum_conf hq hR hdisj, lineAverage_sum, lineAverage_const_mul]
  -- step: swap the sums over the configurations outside
  simp only [confDiff, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  · rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  · rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

/-- A configuration that is not live has `D(ω) = 0`: the roots of the positions and the cube
corners lie in the root box. -/
theorem confDiff_eq_zero_of_not_live (q x : ℝ) (d : Data K) {Y d₀ : ℝ}
    (hU : 0 < d₀ * Y * d.Hm) (hV : 0 < d.Hn) {n : ℕ} (hn : 1 ≤ n) (ω : Conf x d Y d₀)
    (hω : ¬ ConfLive ω) : confDiff q x d Y d₀ n ω = 0 := by
  simp only [ConfLive, not_exists, not_and, not_not] at hω
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hn
  -- step: the integer roots of the positions lie in the root box
  have hpos : ∀ P₀ ∈ positions d Y d₀,
      (confInd x d Y d₀ ω P₀.1 P₀.2 ((rootC P₀.1 P₀.2 : ℝ) / P₀.1) : ℂ) *
        ∏ p ∈ bandPrimes x d, (confLineFactor q p ω (rootLines P₀ p) : ℂ) = 0 := by
    intro P₀ hP₀
    obtain ⟨-, hP₁, hP₁', hP₂, hP₂'⟩ := (Reindex.mem_positions_iff hU hV.le).1 hP₀
    have hu : (0 : ℝ) < P₀.1 := by exact_mod_cast Reindex.pos_of_mem hU hV.le hP₀
    have hc : (rootC P₀.1 P₀.2 : ℝ) < P₀.1 := by
      exact_mod_cast RootResidue.rootC_lt (Reindex.pos_of_mem hU hV.le hP₀) P₀.2
    rw [hω _ _ _ hP₁ hP₁' hP₂ hP₂' (by positivity) ((div_le_one hu).2 hc.le),
      Complex.ofReal_zero, zero_mul]
  -- step: the cube corners lie in the root box
  have hcube : ∀ i ∈ cubeIndices n,
      (confInd x d Y d₀ ω (d₀ * Y * d.Hm * (1 + i.1 / n)) (d.Hn * (1 + i.2.1 / n))
        (i.2.2 / n) : ℂ) *
        lineAverage x d (fun ℓ => ∏ p ∈ bandPrimes x d, (confLineFactor q p ω (ℓ p) : ℂ)) =
        0 := by
    intro i hi
    obtain ⟨hi₁, hi₂, hi₃⟩ : i.1 < 15 * n ∧ i.2.1 < n ∧ i.2.2 < n := by
      simpa [cubeIndices] using hi
    have h₁ : (i.1 : ℝ) / n ≤ 15 := (div_le_iff₀ hn₀).2 (by exact_mod_cast hi₁.le)
    have h₂ : (i.2.1 : ℝ) / n ≤ 1 := (div_le_one hn₀).2 (by exact_mod_cast hi₂.le)
    have h₃ : (i.2.2 : ℝ) / n ≤ 1 := (div_le_one hn₀).2 (by exact_mod_cast hi₃.le)
    have h₁₀ : (0 : ℝ) ≤ i.1 / n := by positivity
    have h₂₀ : (0 : ℝ) ≤ i.2.1 / n := by positivity
    rw [hω _ _ _ (le_mul_of_one_le_right hU.le (by linarith))
      (by rw [mul_comm 16]; exact mul_le_mul_of_nonneg_left (by linarith) hU.le)
      (le_mul_of_one_le_right hV.le (by linarith))
      (by rw [mul_comm 2]; exact mul_le_mul_of_nonneg_left (by linarith) hV.le)
      (by positivity) h₃, Complex.ofReal_zero, zero_mul]
  rw [confDiff, sum_eq_zero hpos, sum_eq_zero hcube, mul_zero, mul_zero, mul_zero, sub_zero]

open scoped Classical in
/-- **Assembly**: if the live coefficients have mass at most `M` and every live configuration
with `c(ω) ≠ 0` has per-configuration error at most `ε`, then the normalized moment is within
`M ε` of `c₂` times the Riemann sum. -/
theorem norm_sub_le_of_conf {q A₀ x : ℝ} (hq : 0 < q) {d : Data K} {Y d₀ : ℝ}
    (hU : 0 < d₀ * Y * d.Hm) (hV : 0 < d.Hn) (hR : 0 < momentPower x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {n : ℕ} (hn : 1 ≤ n)
    {M ε : ℝ} (hε : 0 ≤ ε)
    (hM : ∑ ω ∈ univ.filter (fun ω : Conf x d Y d₀ => ConfLive ω),
      ‖confCoeff A₀ x d Y d₀ ω‖ ≤ M)
    (hD : ∀ ω : Conf x d Y d₀, ConfLive ω → confCoeff A₀ x d Y d₀ ω ≠ 0 →
      ‖confDiff q x d Y d₀ n ω‖ ≤ ε) :
    ‖((d₀ * Y * d.Hm * d.Hn : ℝ) : ℂ)⁻¹ * detMoment q A₀ x d Y d₀ -
        (primitiveDensity : ℂ) * (((n : ℂ) ^ 3)⁻¹ * ∑ i ∈ cubeIndices n,
          lineAverage x d fun ℓ => rootMoment q A₀ x d Y d₀ (d₀ * Y * d.Hm * (1 + i.1 / n))
            (d.Hn * (1 + i.2.1 / n)) (i.2.2 / n) ℓ)‖ ≤ M * ε := by
  rw [sub_eq_sum_confDiff hq hU hV.le hR hdisj n]
  calc ‖∑ ω : Conf x d Y d₀, confCoeff A₀ x d Y d₀ ω * confDiff q x d Y d₀ n ω‖
      ≤ ∑ ω : Conf x d Y d₀, ‖confCoeff A₀ x d Y d₀ ω‖ * ‖confDiff q x d Y d₀ n ω‖ :=
        (norm_sum_le _ _).trans_eq (sum_congr rfl fun ω _ => norm_mul _ _)
    _ = ∑ ω ∈ univ.filter (fun ω : Conf x d Y d₀ => ConfLive ω),
          ‖confCoeff A₀ x d Y d₀ ω‖ * ‖confDiff q x d Y d₀ n ω‖ := by
        -- step: the configurations that are not live contribute nothing
        rw [sum_filter]
        refine sum_congr rfl fun ω _ => ?_
        split_ifs with hω
        · rfl
        · rw [confDiff_eq_zero_of_not_live q x d hU hV hn ω hω, norm_zero, mul_zero]
    _ ≤ ∑ ω ∈ univ.filter (fun ω : Conf x d Y d₀ => ConfLive ω),
          ‖confCoeff A₀ x d Y d₀ ω‖ * ε := by
        refine sum_le_sum fun ω hω => ?_
        by_cases hc : confCoeff A₀ x d Y d₀ ω = 0
        · rw [hc, norm_zero, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hD ω (mem_filter.1 hω).2 hc) (norm_nonneg _)
    _ ≤ M * ε := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right hM hε

end Erdos408.OneSided
