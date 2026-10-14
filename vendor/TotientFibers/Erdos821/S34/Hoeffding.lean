import Mathlib

set_option autoImplicit false

open scoped BigOperators

namespace Erdos821.S34.Proofs

/-- The fraction of cardinality-j subsets containing m probes and omitting ell
coordinates. All divisions are real divisions. -/
theorem hoeffding_fraction (M m ell j : ℕ) (hml : m + ell ≤ M)
    (hmj : m ≤ j) (hje : j + ell ≤ M) :
    (Nat.choose (M - m - ell) (j - m) : ℝ) / Nat.choose M j =
      ((Nat.descFactorial j m : ℝ) * Nat.descFactorial (M - j) ell) /
        Nat.descFactorial M (m + ell) := by
  have hjM : j ≤ M := by omega
  have he : ell ≤ M - j := by omega
  have hsub : j - m ≤ M - m - ell := by omega
  have hdiff : M - m - ell - (j - m) = M - j - ell := by omega
  have hdiff' : M - (m + ell) = M - m - ell := by omega
  have hc := Nat.choose_mul_factorial_mul_factorial hsub
  rw [hdiff] at hc
  have hM := Nat.factorial_mul_descFactorial hml
  rw [hdiff'] at hM
  have hj := Nat.factorial_mul_descFactorial hmj
  have hl := Nat.factorial_mul_descFactorial he
  have hcM := Nat.choose_mul_factorial_mul_factorial hjM
  have hcross :
      Nat.choose (M - m - ell) (j - m) * Nat.descFactorial M (m + ell) =
        Nat.choose M j * Nat.descFactorial j m * Nat.descFactorial (M - j) ell := by
    apply Nat.mul_right_cancel
      (Nat.mul_pos (Nat.factorial_pos (j - m)) (Nat.factorial_pos (M - j - ell)))
    calc
      _ = Nat.descFactorial M (m + ell) *
          (Nat.choose (M - m - ell) (j - m) *
            Nat.factorial (j - m) * Nat.factorial (M - j - ell)) := by ring
      _ = Nat.descFactorial M (m + ell) * Nat.factorial (M - m - ell) := by rw [hc]
      _ = Nat.factorial M := by simpa [Nat.mul_comm] using hM
      _ = Nat.choose M j * (Nat.factorial (j - m) * Nat.descFactorial j m) *
          (Nat.factorial (M - j - ell) * Nat.descFactorial (M - j) ell) := by
        rw [hj, hl]
        exact hcM.symm
      _ = _ := by ring
  have hchoose : (Nat.choose M j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjM).ne'
  have hfall : (Nat.descFactorial M (m + ell) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hml).ne'
  apply (div_eq_div_iff hchoose hfall).mpr
  have hcross' :
      (Nat.choose (M - m - ell) (j - m) : ℝ) * Nat.descFactorial M (m + ell) =
        Nat.choose M j * Nat.descFactorial j m * Nat.descFactorial (M - j) ell := by
    exact_mod_cast hcross
  calc
    _ = _ := hcross'
    _ = _ := by ring

private theorem prod_one_sub_lower {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (h₀ : ∀ i ∈ s, 0 ≤ a i)
    (h₁ : ∀ i ∈ s, a i ≤ 1) :
    1 - (∑ i ∈ s, a i) ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    have hx₀ := h₀ x (Finset.mem_insert_self x s)
    have hx₁ := h₁ x (Finset.mem_insert_self x s)
    have hs₀ : ∀ i ∈ s, 0 ≤ a i := fun i hi => h₀ i (Finset.mem_insert_of_mem hi)
    have hs₁ : ∀ i ∈ s, a i ≤ 1 := fun i hi => h₁ i (Finset.mem_insert_of_mem hi)
    have hs := Finset.sum_nonneg hs₀
    have hi := ih hs₀ hs₁
    simp only [Finset.sum_insert hx, Finset.prod_insert hx]
    calc
      1 - (a x + ∑ i ∈ s, a i) ≤ (1 - a x) * (1 - ∑ i ∈ s, a i) := by
        nlinarith
      _ ≤ (1 - a x) * ∏ i ∈ s, (1 - a i) :=
        mul_le_mul_of_nonneg_left hi (by linarith)

/-- Half of M^k is a lower bound for the falling factorial when the total
excluded fraction is at most one half. -/
theorem descFactorial_half (M k : ℕ) (hk : 2 ≤ k) (hM : k * (k - 1) ≤ M) :
    (M : ℝ) ^ k / 2 ≤ (Nat.descFactorial M k : ℝ) := by
  have hkM : k ≤ M := calc
    k = k * 1 := by simp
    _ ≤ k * (k - 1) := Nat.mul_le_mul_left k (by omega)
    _ ≤ M := hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hsum : (∑ i ∈ Finset.range k, (i : ℝ)) * 2 =
      (k : ℝ) * (k - 1 : ℕ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Finset.sum_range_id_mul_two k)
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum] using h
  have hM' : (k : ℝ) * (k - 1 : ℕ) ≤ M := by exact_mod_cast hM
  have hsum_div : (∑ i ∈ Finset.range k, (i : ℝ) / M) ≤ 1 / 2 := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hMpos).mpr
    nlinarith
  have hprod : (1 / 2 : ℝ) ≤ ∏ i ∈ Finset.range k, (1 - (i : ℝ) / M) := by
    have hp := prod_one_sub_lower (Finset.range k) (fun i => (i : ℝ) / M)
      (fun i _ => by positivity) (fun i hi => (div_le_one hMpos).mpr (by
        exact_mod_cast (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hkM)))
    linarith
  have hfall : (Nat.descFactorial M k : ℝ) =
      (M : ℝ) ^ k * ∏ i ∈ Finset.range k, (1 - (i : ℝ) / M) := by
    calc
      _ = ∏ i ∈ Finset.range k, ((M : ℝ) - i) := by
        simp only [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
        apply Finset.prod_congr rfl
        intro i hi
        exact Nat.cast_sub (Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hkM)
      _ = ∏ i ∈ Finset.range k, ((M : ℝ) * (1 - (i : ℝ) / M)) := by
        apply Finset.prod_congr rfl
        intro i _
        field_simp
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  calc
    (M : ℝ) ^ k / 2 = (M : ℝ) ^ k * (1 / 2) := by ring
    _ ≤ (M : ℝ) ^ k * ∏ i ∈ Finset.range k, (1 - (i : ℝ) / M) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := hfall.symm

private theorem rpow_weight_pow (p w : ℝ) (hp : 0 ≤ p) (k j : ℕ)
    (he : w * (k : ℝ) = j) : (p ^ w) ^ k = p ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp, he, Real.rpow_natCast]

/-- The elementary beta-function maximum needed for probe suppression,
obtained from weighted AM–GM. -/
theorem beta_power_bound (m ell : ℕ) (hm : 1 ≤ m) (he : 1 ≤ ell)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    t ^ m * (1 - t) ^ ell ≤ (ell : ℝ) ^ ell / (m : ℝ) ^ ell := by
  let S : ℝ := (m : ℝ) + ell
  let wm : ℝ := (m : ℝ) / S
  let we : ℝ := (ell : ℝ) / S
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hepos : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have hSpos : 0 < S := by dsimp [S]; positivity
  have hwmpos : 0 < wm := div_pos hmpos hSpos
  have hwepos : 0 < we := div_pos hepos hSpos
  have hw : wm + we = 1 := by
    dsimp [wm, we]
    rw [← add_div]
    exact div_self (ne_of_gt hSpos)
  have hp₁ : 0 ≤ t / wm := div_nonneg ht₀ hwmpos.le
  have hp₂ : 0 ≤ (1 - t) / we := div_nonneg (by linarith) hwepos.le
  have harith : wm * (t / wm) + we * ((1 - t) / we) = 1 := by
    field_simp [ne_of_gt hwmpos, ne_of_gt hwepos]
    <;> ring
  have ham : (t / wm) ^ wm * ((1 - t) / we) ^ we ≤ 1 :=
    (Real.geom_mean_le_arith_mean2_weighted hwmpos.le hwepos.le hp₁ hp₂ hw).trans_eq harith
  have hexpm : wm * ((m + ell : ℕ) : ℝ) = m := by
    simp only [Nat.cast_add]
    change ((m : ℝ) / S) * S = m
    exact div_mul_cancel₀ _ (ne_of_gt hSpos)
  have hexpe : we * ((m + ell : ℕ) : ℝ) = ell := by
    simp only [Nat.cast_add]
    change ((ell : ℝ) / S) * S = ell
    exact div_mul_cancel₀ _ (ne_of_gt hSpos)
  have hpow := pow_le_pow_left₀
    (mul_nonneg (Real.rpow_nonneg hp₁ wm) (Real.rpow_nonneg hp₂ we)) ham (m + ell)
  rw [mul_pow, rpow_weight_pow _ _ hp₁ _ _ hexpm,
    rpow_weight_pow _ _ hp₂ _ _ hexpe, one_pow] at hpow
  rw [div_pow t wm m, div_pow (1 - t) we ell, div_mul_div_comm] at hpow
  have hbeta : t ^ m * (1 - t) ^ ell ≤ wm ^ m * we ^ ell :=
    (div_le_one (mul_pos (pow_pos hwmpos m) (pow_pos hwepos ell))).mp hpow
  have hwm : wm ≤ 1 := (div_le_one hSpos).mpr (by dsimp [S]; linarith)
  have hwe : we ≤ (ell : ℝ) / m :=
    div_le_div_of_nonneg_left hepos.le hmpos (by dsimp [S]; linarith)
  have hbound := mul_le_mul (pow_le_one₀ (n := m) hwmpos.le hwm)
    (pow_le_pow_left₀ hwepos.le hwe ell) (pow_nonneg hwepos.le ell) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul, div_pow] using hbeta.trans hbound

/-- The suppression bound for a symmetric component containing all m probes
and excluding all ell averaged coordinates. -/
theorem hoeffding_fraction_bound (M m ell j : ℕ) (hm : 1 ≤ m) (he : 1 ≤ ell)
    (hM : (m + ell) * (m + ell - 1) ≤ M) (hj : j ≤ M) :
    ((Nat.descFactorial j m : ℝ) * Nat.descFactorial (M - j) ell) /
      Nat.descFactorial M (m + ell) ≤ 2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell := by
  have hk : 2 ≤ m + ell := by omega
  have hkM : m + ell ≤ M := calc
    m + ell = (m + ell) * 1 := by simp
    _ ≤ (m + ell) * (m + ell - 1) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ M := hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hdpos : 0 < (Nat.descFactorial M (m + ell) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hkM
  let c : ℝ := (ell : ℝ) ^ ell / (m : ℝ) ^ ell
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb := beta_power_bound m ell hm he ((j : ℝ) / M)
    (by positivity) ((div_le_one hMpos).mpr (by exact_mod_cast hj))
  have hscale : ((j : ℝ) / M) ^ m * (1 - (j : ℝ) / M) ^ ell =
      ((j : ℝ) ^ m * (M - j : ℕ) ^ ell) / (M : ℝ) ^ (m + ell) := by
    rw [Nat.cast_sub hj, pow_add]
    have hsub : 1 - (j : ℝ) / M = ((M : ℝ) - j) / M := by
      field_simp
    rw [hsub, div_pow, div_pow, div_mul_div_comm]
  rw [hscale] at hb
  have hnpow : (j : ℝ) ^ m * (M - j : ℕ) ^ ell ≤ c * (M : ℝ) ^ (m + ell) :=
    (div_le_iff₀ (pow_pos hMpos (m + ell))).mp hb
  have hjpow : (Nat.descFactorial j m : ℝ) ≤ (j : ℝ) ^ m := by
    exact_mod_cast Nat.descFactorial_le_pow j m
  have hepow : (Nat.descFactorial (M - j) ell : ℝ) ≤ (M - j : ℕ) ^ ell := by
    exact_mod_cast Nat.descFactorial_le_pow (M - j) ell
  have hnum := mul_le_mul hjpow hepow (by positivity) (by positivity)
  have hn := hnum.trans hnpow
  have hd := mul_le_mul_of_nonneg_left (descFactorial_half M (m + ell) hk hM) hc
  apply (div_le_iff₀ hdpos).mpr
  have hfinal : (Nat.descFactorial j m : ℝ) * Nat.descFactorial (M - j) ell ≤
      2 * c * Nat.descFactorial M (m + ell) := by
    nlinarith [hn, hd]
  simpa only [c, div_eq_mul_inv, mul_assoc] using hfinal

end Erdos821.S34.Proofs
