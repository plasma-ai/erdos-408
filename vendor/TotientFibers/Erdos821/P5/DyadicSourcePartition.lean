import Erdos821.P5.ComparableTargets
import Mathlib.Data.Nat.Log

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T

def sourceDyadicCount (Y : ℝ) : ℕ := Nat.log 2 ⌊Y⌋₊ + 1

theorem mem_power_dyad_iff (i : ℕ) (n : ℤ) :
    n ∈ dyad ((2 : ℝ) ^ i) ↔ 0 < n ∧ Nat.log 2 n.toNat = i := by
  rw [mem_graph_dyad]
  constructor
  · intro h
    have hpos : 0 < (n : ℝ) := (pow_pos (by norm_num) i).trans_le h.1
    have hn : 0 < n := by exact_mod_cast hpos
    have hcast : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn.le
    have hlo : 2 ^ i ≤ n.toNat := by exact_mod_cast (hcast.symm ▸ h.1)
    have hhi : n.toNat < 2 ^ (i + 1) := by
      have : (n.toNat : ℝ) < (2 : ℝ) ^ (i + 1) := by
        rw [hcast, pow_succ]
        nlinarith [h.2]
      exact_mod_cast this
    exact ⟨hn, Nat.log_eq_of_pow_le_of_lt_pow hlo hhi⟩
  · rintro ⟨hn, hi⟩
    have hnN : n.toNat ≠ 0 := by omega
    have hcast : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hn.le
    have hlo := Nat.pow_log_le_self 2 hnN
    have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n.toNat
    rw [hi] at hlo hhi
    constructor
    · rw [← hcast]
      exact_mod_cast hlo
    · have : (n.toNat : ℝ) < (2 : ℝ) ^ (i + 1) := by exact_mod_cast hhi
      rw [hcast, pow_succ] at this
      nlinarith

theorem power_dyads_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyad ((2 : ℝ) ^ i)) (dyad ((2 : ℝ) ^ j)) := by
  apply Finset.disjoint_left.mpr
  intro n hi hj
  exact hij (((mem_power_dyad_iff i n).mp hi).2.symm.trans
    ((mem_power_dyad_iff j n).mp hj).2)

theorem positiveRoots_eq_dyadic_union (Y : ℝ) :
    positiveRoots Y = (Finset.range (sourceDyadicCount Y)).biUnion
      (fun i => positiveRoots Y ∩ dyad ((2 : ℝ) ^ i)) := by
  ext n
  constructor
  · intro hn
    obtain ⟨hnpos, hnY⟩ := (mem_positiveRoots Y n).mp hn
    have hcast : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnpos.le
    have hfloor : n.toNat ≤ ⌊Y⌋₊ := Nat.le_floor (hcast.symm ▸ hnY)
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 n.toNat, ?_, Finset.mem_inter.mpr ⟨hn, ?_⟩⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hfloor))
    · exact (mem_power_dyad_iff _ n).mpr ⟨hnpos, rfl⟩
  · intro hn
    obtain ⟨i, hi, hn⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_inter.mp hn).1

theorem sum_positiveRoots_dyadic (Y : ℝ) (f : ℤ → ℂ) :
    (∑ n ∈ positiveRoots Y, f n) =
      ∑ i ∈ Finset.range (sourceDyadicCount Y),
        ∑ n ∈ positiveRoots Y ∩ dyad ((2 : ℝ) ^ i), f n := by
  conv_lhs => rw [positiveRoots_eq_dyadic_union Y]
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact (power_dyads_disjoint hij).mono Finset.inter_subset_right Finset.inter_subset_right

/-- A logarithmic bound for the number of source dyads, including the
last partial dyad. No estimate is inferred from a sampled range. -/
theorem sourceDyadicCount_le_log (Y : ℝ) (hY : 1 ≤ Y) :
    (sourceDyadicCount Y : ℝ) ≤ Real.log Y / Real.log 2 + 1 := by
  have hfloor : ⌊Y⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by simpa using hY)
    omega
  have hpow : (2 : ℝ) ^ Nat.log 2 ⌊Y⌋₊ ≤ Y := by
    exact (by exact_mod_cast Nat.pow_log_le_self 2 hfloor :
      (2 : ℝ) ^ Nat.log 2 ⌊Y⌋₊ ≤ (⌊Y⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
  have hlog := Real.log_le_log (pow_pos (by norm_num) _) hpow
  rw [Real.log_pow] at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := (le_div_iff₀ hlog2).mpr hlog
  dsimp only [sourceDyadicCount]
  push_cast
  linarith

theorem sourceDyadicCount_square_le (x : ℝ) (hx : 1 ≤ x) (hL : 1 ≤ L x) :
    (sourceDyadicCount (x ^ (2 : ℕ)) : ℝ) ≤ (2 / Real.log 2 + 1) * L x := by
  have h := sourceDyadicCount_le_log (x ^ (2 : ℕ)) (by nlinarith)
  rw [Real.log_pow] at h
  have halg : (2 : ℝ) * Real.log x / Real.log 2 = (2 / Real.log 2) * Real.log x := by ring
  norm_num only [Nat.cast_ofNat] at h
  rw [halg] at h
  change (sourceDyadicCount (x ^ (2 : ℕ)) : ℝ) ≤ (2 / Real.log 2 + 1) * Real.log x
  change 1 ≤ Real.log x at hL
  nlinarith

end Erdos821.P5Core
