import Erdos821.P5.DrawProductScales
import Erdos821.P5.ProgressionIntervals
import Erdos821.P5.LiftedSharedRow

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic

def positiveRoots (Y : ℝ) : Finset ℤ := Finset.Icc 1 ⌊Y⌋

theorem mem_positiveRoots (Y : ℝ) (n : ℤ) :
    n ∈ positiveRoots Y ↔ 0 < n ∧ (n : ℝ) ≤ Y := by
  simp only [positiveRoots, Finset.mem_Icc, Int.le_floor]
  constructor <;> intro h <;> exact ⟨by omega, h.2⟩

def cutoffRoots (lo hi Z : ℝ) (D : ℕ) : Finset ℕ :=
  Finset.Icc ⌈lo * Z * D⌉₊ ⌊hi * Z * D⌋₊

theorem mem_cutoffRoots (lo hi Z : ℝ) (D n : ℕ) (hhi : 0 ≤ hi * Z * D) :
    n ∈ cutoffRoots lo hi Z D ↔ lo * Z * D ≤ (n : ℝ) ∧ (n : ℝ) ≤ hi * Z * D :=
  nat_interval_mem_iff _ _ _ hhi

theorem cutoffRoots_ranges (lo hi Z : ℝ) (D : ℕ) (k : ℤ)
    (hlo : 0 < lo) (hhi : lo < hi) (hZ : 0 < Z) (hD : 0 < D)
    (hX : 1 ≤ lo * Z * D) (hk : |(k : ℝ)| ≤ lo * Z / 2)
    (n : ℕ) (hn : n ∈ cutoffRoots lo hi Z D) :
    1 ≤ n ∧ lo * Z * D ≤ (n : ℝ) ∧ (n : ℝ) ≤ (hi + lo) * Z * D ∧
      0 < (n : ℤ) + k * (D : ℤ) ∧
      (((n : ℤ) + k * (D : ℤ)).toNat : ℝ) ≤ (hi + lo) * Z * D := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hhipos : 0 < hi := hlo.trans hhi
  obtain ⟨hnlo, hnhi⟩ := (mem_cutoffRoots lo hi Z D n (by positivity)).mp hn
  have hn1 : 1 ≤ n := by exact_mod_cast hX.trans hnlo
  have hkD := mul_le_mul_of_nonneg_right hk hDR.le
  have hneg := neg_abs_le (k : ℝ)
  have hposR : 0 < (n : ℝ) + (k : ℝ) * D := by
    have hnegD := mul_le_mul_of_nonneg_right hneg hDR.le
    nlinarith [mul_pos (mul_pos hlo hZ) hDR]
  have hpos : 0 < (n : ℤ) + k * (D : ℤ) := by exact_mod_cast hposR
  have hshiftR : (((n : ℤ) + k * (D : ℤ)).toNat : ℝ) =
      (n : ℝ) + (k : ℝ) * D := by
    exact_mod_cast Int.toNat_of_nonneg hpos.le
  refine ⟨hn1, hnlo, ?_, hpos, ?_⟩
  · nlinarith [mul_pos (mul_pos hlo hZ) hDR]
  · rw [hshiftR]
    have hposD := mul_le_mul_of_nonneg_right (le_abs_self (k : ℝ)) hDR.le
    nlinarith [mul_pos (mul_pos hlo hZ) hDR]

theorem cutoffRoots_of_nonzero (lo hi Z : ℝ) (D n : ℕ) (Ψ : ℝ → ℂ)
    (hZ : 0 < Z) (hD : 0 < D) (hhi : 0 < hi)
    (hs : Function.support Ψ ⊆ Set.Icc lo hi) (hΨ : Ψ ((n : ℝ) / (Z * D)) ≠ 0) :
    n ∈ cutoffRoots lo hi Z D := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  have harg : (n : ℝ) / (Z * D) ∈ Set.Icc lo hi := hs (Function.mem_support.mpr hΨ)
  apply (mem_cutoffRoots lo hi Z D n (by positivity)).mpr
  constructor
  · simpa only [mul_assoc] using (le_div_iff₀ (mul_pos hZ hDR)).mp harg.1
  · simpa only [mul_assoc] using (div_le_iff₀ (mul_pos hZ hDR)).mp harg.2

theorem strippedLiftScalar_zero_outside (G : PrimeGroups) (x lo hi Z a₁ a₂ : ℝ)
    (E H : Endpoint) (Ψ : ℝ → ℂ) (D n n' : ℕ)
    (hZ : 0 < Z) (hD : 0 < D) (hhi : 0 < hi)
    (hs : Function.support Ψ ⊆ Set.Icc lo hi) (hn : n ∉ cutoffRoots lo hi Z D) :
    strippedLiftScalar G x Z a₁ a₂ E H Ψ n n' D = 0 := by
  have hΨ : Ψ ((n : ℝ) / (Z * D)) = 0 := by
    by_contra h
    exact hn (cutoffRoots_of_nonzero lo hi Z D n Ψ hZ hD hhi hs h)
  simp [strippedLiftScalar, harmonicCutoff, hΨ]

theorem eventual_cutoff_sup (C lo hi : ℝ) (bounds : ℕ → ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (Ψ : ℝ → ℂ), CutoffBound x C lo hi Ψ bounds →
      ∀ y : ℝ, ‖Ψ y‖ ≤ L x ^ (C + 1) := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (bounds 0))]
    with x hx
  change max 1 (bounds 0) ≤ L x at hx
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hx)
  intro Ψ hΨ y
  have hzero : ‖Ψ y‖ ≤ bounds 0 * L x ^ C := by
    simpa only [iteratedDeriv_zero, Nat.cast_zero, zero_add, mul_one] using hΨ.2.2 0 y
  calc
    _ ≤ bounds 0 * L x ^ C := hzero
    _ ≤ L x * L x ^ C := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hx)
      (Real.rpow_nonneg hLpos.le _)
    _ = _ := by rw [Real.rpow_add hLpos, Real.rpow_one]; ring

end Erdos821.P5Core
