import Erdos821.P5.Basic

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core

/-- An integer distance has at most two preimages, including distance zero. -/
theorem distance_fiber_card (E : Finset ℤ) (j : ℤ) (n : ℕ) :
    (E.filter (fun k => (j - k).natAbs = n)).card ≤ 2 := by
  calc
    _ ≤ ({j - n, j + n} : Finset ℤ).card := by
      apply Finset.card_le_card
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      have h' : (j - k).natAbs = (n : ℤ).natAbs := by simpa using h
      have hsign := Int.natAbs_eq_natAbs_iff.mp h'
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    _ ≤ _ := Finset.card_le_two

/-- The reciprocal integer-distance row is a harmonic sum with multiplicity at most two. -/
theorem integer_harmonic_row (E : Finset ℤ) (j : ℤ) (N : ℕ)
    (hN : ∀ k ∈ E, (j - k).natAbs ≤ N) :
    (∑ k ∈ E, 1 / (1 + (|(j : ℝ) - k|))) ≤ 2 * (harmonic (N + 1) : ℝ) := by
  classical
  have hparts : ∑ n ∈ Finset.range (N + 1),
      ∑ k ∈ E.filter (fun k => (j - k).natAbs = n), 1 / (1 + (n : ℝ)) =
      ∑ k ∈ E, 1 / (1 + ((j - k).natAbs : ℝ)) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (s := E) (t := Finset.range (N + 1)) (g := fun k => (j - k).natAbs)
      (fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN k hk)))
      (fun k => 1 / (1 + ((j - k).natAbs : ℝ)))
    rw [← h]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  calc
    _ = ∑ k ∈ E, 1 / (1 + ((j - k).natAbs : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (j - k)).symm
      simpa only [Int.cast_abs, Int.cast_sub, Int.cast_natCast] using h
    _ = _ := hparts.symm
    _ ≤ ∑ n ∈ Finset.range (N + 1), 2 / (1 + (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((E.filter (fun k => (j - k).natAbs = n)).card : ℝ) ≤ 2 := by
        exact_mod_cast distance_fiber_card E j n
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right hcard
        (show 0 ≤ 1 / (1 + (n : ℝ)) by positivity)
    _ = _ := by
      simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv,
        Finset.mul_sum, add_comm]

/-- Bounded integer cells give a logarithmic reciprocal row bound. -/
theorem integer_harmonic_row_log (E : Finset ℤ) (j : ℤ) (Y : ℝ)
    (hY : Real.exp 1 ≤ Y) (hj : |(j : ℝ)| ≤ Y)
    (hE : ∀ k ∈ E, |(k : ℝ)| ≤ Y) :
    (∑ k ∈ E, 1 / (1 + |(j : ℝ) - k|)) ≤ 8 * Real.log (2 * Y) := by
  have hY1 : 1 ≤ Y := by
    have h : (1 : ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    exact h.trans hY
  have hYpos : 0 < Y := by linarith
  have hlogY : 1 ≤ Real.log Y := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hY
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2Y : 1 ≤ Real.log (2 * Y) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hYpos.ne']
    linarith
  have hlogY2Y : Real.log Y ≤ Real.log (2 * Y) :=
    Real.log_le_log hYpos (by linarith)
  let N := ⌊2 * Y⌋₊
  have hN (k : ℤ) (hk : k ∈ E) : (j - k).natAbs ≤ N := by
    apply Nat.le_floor
    have hdist : |(j : ℝ) - k| ≤ |(j : ℝ)| + |(k : ℝ)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (j : ℝ) (-(k : ℝ))
    have hcast : ((j - k).natAbs : ℝ) = |(j : ℝ) - k| := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
    rw [hcast]
    linarith [hE k hk]
  have hN3Y : ((N + 1 : ℕ) : ℝ) ≤ 3 * Y := by
    have hfloor := Nat.floor_le (show 0 ≤ 2 * Y by positivity)
    dsimp [N]
    push_cast
    linarith
  have hlogN : Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log 3 + Real.log Y := by
    have h := Real.log_le_log (show (0 : ℝ) < (N + 1 : ℕ) by positivity) hN3Y
    rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hYpos.ne'] at h
  have hlog3 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  have h := integer_harmonic_row E j N hN
  have hH := harmonic_le_one_add_log (N + 1)
  nlinarith only [h, hH, hlogN, hlog3, hlogY2Y, hlog2Y]

/-- Moving the sample within its unit cell changes the reciprocal row by a factor ≤2. -/
theorem reciprocal_cell_distance (j k : ℤ) (t : ℤ → ℝ)
    (hj : (j : ℝ) ≤ t j ∧ t j ≤ (j : ℝ) + 1)
    (hk : (k : ℝ) ≤ t k ∧ t k ≤ (k : ℝ) + 1) :
    1 / (1 + |t j - t k|) ≤ 2 / (1 + |(j : ℝ) - k|) := by
  have hdiff : |(j : ℝ) - k| ≤ 1 + |t j - t k| := by
    apply abs_le.mpr
    have hleft := neg_abs_le (t j - t k)
    have hright := le_abs_self (t j - t k)
    constructor <;> linarith
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + |t j - t k|)
    (by positivity : 0 < 1 + |(j : ℝ) - k|)).mpr
  linarith [abs_nonneg (t j - t k)]

end Erdos821.P5Core
