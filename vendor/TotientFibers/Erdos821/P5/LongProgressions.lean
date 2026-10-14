import Erdos821.P5.ProgressionIntervals
import Erdos821.P5.LogBoundary
import Erdos821.P5.LongSieve

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

theorem characterMellinTerm_residue_factor (d q a y : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℝ) (hd : 0 < d) (hv : 0 < q * y + a) :
    characterMellinTerm χ u (d * (q * y + a)) =
      (χ (d : ZMod q) * χ (a : ZMod q) * mellin d u / (d : ℂ)) *
        (mellin (q * y + a) u / ((q * y + a : ℕ) : ℂ)) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hvR : 0 < ((q * y + a : ℕ) : ℝ) := by exact_mod_cast hv
  have hchar : χ ((q * y + a : ℕ) : ZMod q) = χ (a : ZMod q) := by
    simp
  unfold characterMellinTerm
  simp only [Nat.cast_mul, map_mul]
  rw [mellin_mul _ _ _ hdR hvR, hchar]
  simp only [div_eq_mul_inv, mul_inv_rev]
  push_cast
  ring

theorem residue_factor_norm_le (d q a : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) :
    ‖χ (d : ZMod q) * χ (a : ZMod q) * mellin d u / (d : ℂ)‖ ≤ (d : ℝ)⁻¹ := by
  rw [norm_div, norm_mul, norm_mul, norm_mellin, mul_one, Complex.norm_natCast]
  have hprod : ‖χ (d : ZMod q)‖ * ‖χ (a : ZMod q)‖ ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul (χ.norm_le_one _) (χ.norm_le_one _) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  simpa only [one_div] using div_le_div_of_nonneg_right hprod (Nat.cast_nonneg d)

/-- §4 divisor progression cancellation after character-class splitting.
The boundary correction remains `1/N`, with N=P/(d*q), and all constants
are independent of d, q and the chosen character. -/
theorem long_progression_of_log_task (hlog : LogPhaseSumTask) (τ : ℝ) (hτ : 0 < τ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (P lo hi u : ℝ) (d q : ℕ) (χ : DirichletCharacter ℂ q),
        1 ≤ d → 1 ≤ q → 1 ≤ P / ((d : ℝ) * q) →
        x ^ (τ / 2) ≤ P / ((d : ℝ) * q) →
        P ≤ lo → lo ≤ hi → hi ≤ 2 * P →
        1 ≤ |u| → |u| ≤ x ^ (2 : ℕ) →
        ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun n => d ∣ n),
          characterMellinTerm χ u n‖ ≤
            (K * (|u|⁻¹ + (P / ((d : ℝ) * q)) ^ (-δ)) +
              (P / ((d : ℝ) * q))⁻¹) / d := by
  classical
  obtain ⟨δ, K, hδ, hK, hevent⟩ := weighted_log_phase_extended_of_task hlog τ hτ
  refine ⟨δ, K, hδ, hK, hevent.mono ?_⟩
  intro x hx P lo hi u d q χ hd hq hN1 hNx hPlo hlohi hhi hu hux
  have hdpos : 0 < d := by omega
  have hqpos : 0 < q := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqpos
  let N := P / ((d : ℝ) * q)
  let E := |u|⁻¹ + N ^ (-δ)
  let R := (K / q) * E + ((q : ℝ) * N)⁻¹
  have hNpos : 0 < N := by dsimp [N]; linarith
  have hPpos : 0 < P := by
    have h := (le_div_iff₀ (mul_pos hdR hqR)).mp hN1
    nlinarith [mul_pos hdR hqR]
  have hlo0 : 0 ≤ lo := (hPpos.trans_le hPlo).le
  have hNrel : (q : ℝ) * N = P / d := by dsimp [N]; field_simp
  have hqlo : (q : ℝ) ≤ lo / d := by
    have h := mul_le_mul_of_nonneg_left hN1 hqR.le
    have hPle : P / (d : ℝ) ≤ lo / d := div_le_div_of_nonneg_right hPlo hdR.le
    dsimp [N] at hNrel
    nlinarith [hNrel]
  have hlohiD : lo / (d : ℝ) ≤ hi / d := div_le_div_of_nonneg_right hlohi hdR.le
  have hsum : (∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (fun n => d ∣ n),
      characterMellinTerm χ u n) =
      ∑ a ∈ Finset.range q,
        ∑ y ∈ Finset.Icc ⌈(lo / d - a) / (q : ℝ)⌉ ⌊(hi / d - a) / (q : ℝ)⌋,
          characterMellinTerm χ u (d * (q * y.toNat + a)) := by
    rw [sum_interval_multiples lo hi d _ hlo0 hlohi hdpos,
      sum_interval_residues (lo / d) (hi / d) q _ hqpos hqlo hlohiD]
  have hclass (a : ℕ) (ha : a ∈ Finset.range q) :
      ‖∑ y ∈ Finset.Icc ⌈(lo / d - a) / (q : ℝ)⌉ ⌊(hi / d - a) / (q : ℝ)⌋,
        characterMellinTerm χ u (d * (q * y.toNat + a))‖ ≤ (d : ℝ)⁻¹ * R := by
    have haq := Finset.mem_range.mp ha
    have haR : (a : ℝ) < q := by exact_mod_cast haq
    let α := (lo / d - a) / (q : ℝ)
    let β := (hi / d - a) / (q : ℝ)
    have hα : (q : ℝ) * α + a = lo / d := by dsimp [α]; field_simp; ring
    have hβ : (q : ℝ) * β + a = hi / d := by dsimp [β]; field_simp; ring
    have hαlow : N - 1 ≤ α := by
      have h := div_le_div_of_nonneg_right hPlo hdR.le
      nlinarith [hNrel]
    have hαβ : α ≤ β := by dsimp [α, β]; gcongr
    have hβhigh : β ≤ 2 * N := by
      have h := div_le_div_of_nonneg_right hhi hdR.le
      rw [mul_div_assoc] at h
      nlinarith [hNrel]
    have hbase : (q : ℝ) * N ≤ q * α + a := by
      rw [hα, hNrel]
      exact div_le_div_of_nonneg_right hPlo hdR.le
    have hphase : ‖∑ y ∈ Finset.Icc ⌈α⌉ ⌊β⌋,
        mellin (q * (y : ℝ) + a) u / ((q * (y : ℝ) + a : ℝ) : ℂ)‖ ≤ R :=
      hx N α β u q a hNpos hNx hαlow hαβ hβhigh hq haq hbase hu hux
    have hy0 (y : ℤ) (hy : y ∈ Finset.Icc ⌈α⌉ ⌊β⌋) : 0 ≤ y := by
      have hylo := Int.ceil_le.mp (Finset.mem_Icc.mp hy).1
      have hαpos : 0 < α := by
        apply (lt_div_iff₀ hqR).mpr
        nlinarith [hqlo]
      have : 0 ≤ (y : ℝ) := (hαpos.trans_le hylo).le
      exact_mod_cast this
    have hfactor : (∑ y ∈ Finset.Icc ⌈α⌉ ⌊β⌋,
        characterMellinTerm χ u (d * (q * y.toNat + a))) =
        (χ (d : ZMod q) * χ (a : ZMod q) * mellin d u / (d : ℂ)) *
          ∑ y ∈ Finset.Icc ⌈α⌉ ⌊β⌋,
            mellin (q * (y : ℝ) + a) u / ((q * (y : ℝ) + a : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hyR : (y.toNat : ℝ) = (y : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (hy0 y hy)
      have hyC : (y.toNat : ℂ) = (y : ℂ) := by exact_mod_cast Int.toNat_of_nonneg (hy0 y hy)
      have hvpos : 0 < q * y.toNat + a := by
        have hylo := Int.ceil_le.mp (Finset.mem_Icc.mp hy).1
        have hden : 0 < (q : ℝ) * y + a := by nlinarith [hqlo]
        have hvR : 0 < ((q * y.toNat + a : ℕ) : ℝ) := by push_cast; rwa [hyR]
        exact_mod_cast hvR
      rw [characterMellinTerm_residue_factor d q a y.toNat χ u hdpos hvpos]
      congr 1
      push_cast
      rw [hyR, hyC]
    rw [hfactor, norm_mul]
    exact mul_le_mul (residue_factor_norm_le d q a χ u) hphase
      (norm_nonneg _) (inv_nonneg.mpr hdR.le)
  rw [hsum]
  calc
    _ ≤ ∑ a ∈ Finset.range q,
        ‖∑ y ∈ Finset.Icc ⌈(lo / d - a) / (q : ℝ)⌉ ⌊(hi / d - a) / (q : ℝ)⌋,
          characterMellinTerm χ u (d * (q * y.toNat + a))‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Finset.range q, (d : ℝ)⁻¹ * R := Finset.sum_le_sum hclass
    _ = (q : ℝ) * ((d : ℝ)⁻¹ * R) := by simp
    _ = (K * E + N⁻¹) / d := by dsimp [R]; field_simp
    _ = _ := rfl

end Erdos821.P5Core
