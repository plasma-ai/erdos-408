import Erdos821.P5.LongRoughReduction
import Erdos821.P5.LongScales
import Erdos821.P5.LongFrequency

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem long_rough_polynomial_of_inputs (hsieve : Blueprint.RoughPolynomial)
    (hlog : LogPhaseSumTask) (τ η C A : ℝ) (hτ : 0 < τ) (_hη : η < 1 / 4)
    (hC : 0 < C) (hA : 0 < A) :
    ∃ B₀ K : ℝ, 0 < B₀ ∧ 0 < K ∧ ∀ᶠ x in atTop,
      ∀ (P lo hi σ t : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r),
        x ^ τ / 2 ≤ P → P ≤ x ^ η → P ≤ lo → lo ≤ hi → hi ≤ 2 * P →
        1 ≤ r → (r : ℝ) ≤ L x ^ C → |σ| ≤ L x ^ C →
        L x ^ B₀ ≤ |t| → |t + σ| ≤ x ^ (2 : ℕ) →
        ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough (W x)),
          χ (n : ZMod r) * mellin n (t + σ) / (n : ℂ)‖ ≤ K * L x ^ (-A) := by
  obtain ⟨Ks, δ, K, hKs, hδ, hK, h₀, hevent⟩ := rough_long_reduction hsieve hlog τ hτ
  let B₀ := max (A + 2) (C + 2)
  let K₀ := Ks * (6 * K + 5)
  have hB₀ : 0 < B₀ := (by linarith : (0 : ℝ) < A + 2).trans_le (le_max_left _ _)
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  have hBA : A + 2 ≤ B₀ := le_max_left _ _
  have hBC : C + 2 ≤ B₀ := le_max_right _ _
  have hB2 : 2 ≤ B₀ := by linarith
  have hL2 := Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)
  refine ⟨B₀, K₀, hB₀, hK₀, ?_⟩
  filter_upwards [hevent, eventual_rough_geometry h₀ τ C hτ hC,
    eventual_rough_depth_error h₀ A hA,
    eventual_negative_power_le_log_power (3 * τ / 4) A (by positivity),
    eventual_negative_power_le_log_power (τ * δ / 2) (A + 1) (by positivity),
    eventual_negative_power_le_log_power (τ / 2) (A + 1) (by positivity), hL2]
    with x he hgeom hdepth hlevel hdelta hinv hL2
  intro P lo hi σ t r χ hP _hPupper hPlo hlohi hhi hr hrbound hσ ht hux
  have hxpos : 0 < x := by linarith [hgeom.1]
  have hLpos : 0 < L x := by linarith [hgeom.2.1]
  obtain ⟨hP1, hX1, hscale, hDP⟩ := hgeom.2.2.2 P r hP hrbound
  have hfreq := shifted_frequency_bound (L x) B₀ C t σ hL2 hBC hB2 hσ ht
  have hfreq' : |t + σ|⁻¹ ≤ 2 * L x ^ (-(A + 1)) := by
    apply hfreq.2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hgeom.2.1 (by linarith)) (by norm_num)
  have hXdelta : (x ^ (τ / 2)) ^ (-δ) ≤ L x ^ (-(A + 1)) := by
    rw [← Real.rpow_mul hxpos.le]
    convert hdelta.2.2 using 1 <;> ring
  have hXinv : (x ^ (τ / 2))⁻¹ ≤ L x ^ (-(A + 1)) := by
    rw [← Real.rpow_neg hxpos.le]
    exact hinv.2.2
  have hDP' : W x ^ (4 * roughDepth h₀ x + 2) / P ≤ 2 * L x ^ (-A) :=
    hDP.trans (mul_le_mul_of_nonneg_left hlevel.2.2 (by norm_num))
  have hlog : 0 ≤ Real.log (2 * W x) := Real.log_nonneg (by linarith [hgeom.2.2.1])
  have hsum : K * (|t + σ|⁻¹ + (x ^ (τ / 2)) ^ (-δ)) + (x ^ (τ / 2))⁻¹ ≤
      (3 * K + 1) * L x ^ (-(A + 1)) := by
    have h := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hfreq' hXdelta) hK.le) hXinv
    nlinarith
  have hHL : L x ^ (-(A + 1)) * L x = L x ^ (-A) := by
    calc
      _ = L x ^ (-(A + 1)) * L x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = L x ^ (-(A + 1) + 1) := (Real.rpow_add hLpos _ _).symm
      _ = _ := by congr 1; ring
  have hosc : (K * (|t + σ|⁻¹ + (x ^ (τ / 2)) ^ (-δ)) + (x ^ (τ / 2))⁻¹) *
      Real.log (2 * W x) ≤ (6 * K + 2) * L x ^ (-A) := by
    calc
      _ ≤ ((3 * K + 1) * L x ^ (-(A + 1))) * Real.log (2 * W x) :=
        mul_le_mul_of_nonneg_right hsum hlog
      _ ≤ ((3 * K + 1) * L x ^ (-(A + 1))) * (2 * L x) :=
        mul_le_mul_of_nonneg_left (log_two_W_le x hgeom.2.1) (by positivity)
      _ = (6 * K + 2) * (L x ^ (-(A + 1)) * L x) := by ring
      _ = _ := by rw [hHL]
  have hraw := he (roughDepth h₀ x) (roughDepth_ge h₀ x) (roughDepth_even h₀ x)
    (W x) hgeom.2.2.1 P lo hi (t + σ) (x ^ (τ / 2)) r χ hP1 hPlo hlohi hhi hr
    hX1 le_rfl hscale hfreq.1 hux
  calc
    _ ≤ Ks * (Real.exp (-(roughDepth h₀ x : ℝ)) +
        W x ^ (4 * roughDepth h₀ x + 2) / P +
        (K * (|t + σ|⁻¹ + (x ^ (τ / 2)) ^ (-δ)) + (x ^ (τ / 2))⁻¹) *
          Real.log (2 * W x)) := hraw
    _ ≤ Ks * (L x ^ (-A) + 2 * L x ^ (-A) + (6 * K + 2) * L x ^ (-A)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hdepth.2 hDP') hosc) hKs.le
    _ = K₀ * L x ^ (-A) := by dsimp [K₀]; ring

example (hsieve : Blueprint.RoughPolynomial) (hlog : LogPhaseSumTask) :
    Erdos821.Blueprint.Analytic.long_rough_polynomial_statement := @long_rough_polynomial_of_inputs hsieve hlog

end Erdos821.P5Core
