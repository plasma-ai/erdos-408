import Erdos821.P5.LongProgressions
import Erdos821.P5.LongSieveEstimate

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- All finite and oscillatory steps of the long rough-integer estimate.
The explicit scale condition `D*q*X ≤ P` makes every divisor progression
long enough, including the one-integer residue boundary correction. -/
theorem rough_long_reduction (hsieve : Blueprint.RoughPolynomial)
    (hlog : LogPhaseSumTask) (τ : ℝ) (hτ : 0 < τ) :
    ∃ Ks δ K : ℝ, 0 < Ks ∧ 0 < δ ∧ 0 < K ∧
      ∃ h₀ : ℕ, ∀ᶠ x : ℝ in atTop,
        ∀ h : ℕ, h₀ ≤ h → Even h → ∀ z : ℝ, 2 ≤ z →
          ∀ (P lo hi u X : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q),
            1 ≤ P → P ≤ lo → lo ≤ hi → hi ≤ 2 * P →
            1 ≤ q → 1 ≤ X → x ^ (τ / 2) ≤ X →
            z ^ (4 * h + 2) * q * X ≤ P →
            1 ≤ |u| → |u| ≤ x ^ (2 : ℕ) →
            ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough z),
              χ (n : ZMod q) * mellin n u / (n : ℂ)‖ ≤
                Ks * (Real.exp (-(h : ℝ)) + z ^ (4 * h + 2) / P +
                  (K * (|u|⁻¹ + X ^ (-δ)) + X⁻¹) * Real.log (2 * z)) := by
  obtain ⟨Ks, hKs, h₀, hsieve⟩ := rough_sieve_cancellation hsieve
  obtain ⟨δ, K, hδ, hK, hevent⟩ := long_progression_of_log_task hlog τ hτ
  refine ⟨Ks, δ, K, hKs, hδ, hK, h₀, hevent.mono ?_⟩
  intro x hx h hh he z hz P lo hi u X q χ hP1 hPlo hlohi hhi hq hX1 hXx hscale hu hux
  obtain ⟨lam, _hcoeff, _hsupport, hsievebound⟩ := hsieve h hh he z hz
  have hPpos : 0 < P := by linarith
  have hXpos : 0 < X := by linarith
  have hqpos : 0 < q := by omega
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hD : 0 ≤ z ^ (4 * h + 2) := by positivity
  let B := K * (|u|⁻¹ + X ^ (-δ)) + X⁻¹
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply hsievebound P lo hi u B q χ hPpos (by linarith) hPlo hlohi hhi hB
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hdpos : 0 < d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hdD : (d : ℝ) ≤ z ^ (4 * h + 2) :=
    (Nat.le_floor_iff hD).mp (Finset.mem_Icc.mp hd).2
  have hmul : (d : ℝ) * q * X ≤ P := by
    apply le_trans _ hscale
    gcongr
  have hXN : X ≤ P / ((d : ℝ) * q) := (le_div_iff₀ (mul_pos hdR hqR)).mpr (by nlinarith [hmul])
  have hNpos : 0 < P / ((d : ℝ) * q) := hXpos.trans_le hXN
  have hpower : (P / ((d : ℝ) * q)) ^ (-δ) ≤ X ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hXpos hXN (by linarith)
  have hinv : (P / ((d : ℝ) * q))⁻¹ ≤ X⁻¹ := inv_anti₀ hXpos hXN
  have h := hx P lo hi u d q χ hd1 hq (hX1.trans hXN) (hXx.trans hXN)
    hPlo hlohi hhi hu hux
  apply h.trans
  apply div_le_div_of_nonneg_right _ hdR.le
  dsimp [B]
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hpower) hK.le) hinv

end Erdos821.P5Core
