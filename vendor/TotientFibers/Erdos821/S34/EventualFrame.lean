import Erdos821.S34.CharacterCellTasks
import Erdos821.S34.KernelTransport

set_option autoImplicit false
open scoped BigOperators Classical
open Filter

namespace Erdos821.S34Core
noncomputable section
open Blueprint Blueprint.Analytic

theorem gram_factor_le_two (L q ξexp K : ℝ) (Q : ℕ)
    (hL : 1 ≤ L) (hK : 0 ≤ K) (hKL : K ≤ L ^ (2 : ℕ))
    (hQ : (Q : ℝ) ≤ L ^ q) :
    1 + (Q : ℝ) ^ 2 * (K * L ^ (-(2 * q + ξexp + 2))) / L ^ (-ξexp) ≤ 2 := by
  have hLpos : 0 < L := by linarith
  have hξpos : 0 < L ^ (-ξexp) := Real.rpow_pos_of_pos hLpos _
  have hδ : 0 ≤ K * L ^ (-(2 * q + ξexp + 2)) := mul_nonneg hK (Real.rpow_nonneg hLpos.le _)
  have hQsq : (Q : ℝ) ^ 2 ≤ L ^ (2 * q) := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2
    have he : (L ^ q) ^ (2 : ℕ) = L ^ (2 * q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
      congr 1
      norm_num
      ring
    rwa [he] at hs
  have hb : (Q : ℝ) ^ 2 * (K * L ^ (-(2 * q + ξexp + 2))) ≤ L ^ (-ξexp) := by
    calc
      _ ≤ L ^ (2 * q) * (K * L ^ (-(2 * q + ξexp + 2))) :=
        mul_le_mul_of_nonneg_right hQsq hδ
      _ = K * L ^ (-ξexp - 2) := by
        rw [mul_left_comm, ← Real.rpow_add hLpos]
        congr 1
        ring
      _ = L ^ (-ξexp) * (K / L ^ (2 : ℕ)) := by
        rw [show -ξexp - 2 = -ξexp + (-2) by ring, Real.rpow_add hLpos,
          Real.rpow_neg hLpos.le (2 : ℝ), Real.rpow_two]
        ring
      _ ≤ L ^ (-ξexp) * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one₀ (by positivity : (0 : ℝ) < L ^ (2 : ℕ))).mpr hKL) hξpos.le
      _ = _ := mul_one _
  have hd := (div_le_one₀ hξpos).mpr hb
  linarith

theorem eventually_cell_operator_norm (hchar : CharacterCellTask) (hc : HarmonicCharacters)
    (P : Geometry) (m : ℕ) (qexp ξexp : ℝ) (hq : 0 < qexp) (hξexp : 0 < ξexp) :
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ k, bigSlots G k m → ∀ (Q : ℕ) (h : ℝ), (Q : ℝ) ≤ L x ^ qexp → 0 < h →
      ∀ f : Tuple G k → ℂ,
        tupleNorm G k (cellApply G k Q h (L x ^ (-ξexp)) f) ≤ 2 * tupleNorm G k f ∧
        tupleNorm G k (cellTransposeApply G k Q h (L x ^ (-ξexp)) f) ≤ 2 * tupleNorm G k f := by
  let D := 2 * qexp + ξexp + 2
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨K, hK, hcell⟩ := hchar hc P m qexp D hq hD
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hcell, hL.eventually_ge_atTop (max 1 K)] with x hx hLx
  have hL1 : 1 ≤ L x := (le_max_left 1 K).trans hLx
  have hLpos : 0 < L x := by linarith
  have hKL : K ≤ L x ^ (2 : ℕ) := by
    have hkL := (le_max_right 1 K).trans hLx
    nlinarith
  intro G hG k hk Q h hQ hh f
  let δ := K * L x ^ (-D)
  have hδ : 0 ≤ δ := mul_nonneg hK.le (Real.rpow_nonneg hLpos.le _)
  have hξ : 0 < L x ^ (-ξexp) := Real.rpow_pos_of_pos hLpos _
  have hgram (j : ℤ) (_hj : L x ^ (-ξexp) ≤ cellMass G k h j)
      (χ : CharacterIndex Q) (hχ : χ ∈ primitiveCharacters Q)
      (ψ : CharacterIndex Q) (hψ : ψ ∈ primitiveCharacters Q) (hne : χ ≠ ψ) :
      ‖expect G k (fun z => if cell h (product G k z) = j then
        star (charValue χ (product G k z)) * charValue ψ (product G k z) else 0)‖ ≤ δ :=
    hx G hG k hk Q h j χ ψ hQ hh hχ hψ hne
  have hfac := gram_factor_le_two (L x) qexp ξexp K Q hL1 hK.le hKL hQ
  have hnorm := mul_le_mul_of_nonneg_right hfac
    (Real.sqrt_nonneg (∑ z, tupleWeight G k z * ‖f z‖ ^ 2))
  constructor
  · exact (cell_operator_norm G k Q h (L x ^ (-ξexp)) δ hξ hδ hgram f).trans hnorm
  · exact (cell_transpose_operator_norm G k Q h (L x ^ (-ξexp)) δ hξ hδ hgram f).trans hnorm

end
end Erdos821.S34Core
