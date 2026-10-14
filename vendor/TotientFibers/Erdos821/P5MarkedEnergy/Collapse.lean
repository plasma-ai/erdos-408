import Erdos821.P5.Basic
import Erdos821.Classical.DivisorMoments

/-! Dyadic harmonic Dirichlet polynomials and their products. A product of
`k` dyadic polynomials is one Dirichlet polynomial whose coefficient square sum
is controlled by a fixed divisor moment. -/

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- The dyad `[2^i, 2^(i+1))`. -/
def dyad (i : ℕ) : Finset ℕ := Finset.Ico (2 ^ i) (2 ^ (i + 1))

theorem mem_dyad {i m : ℕ} : m ∈ dyad i ↔ 2 ^ i ≤ m ∧ m < 2 ^ (i + 1) := Finset.mem_Ico

theorem dyad_pos {i m : ℕ} (hm : m ∈ dyad i) : 0 < m :=
  lt_of_lt_of_le (Nat.two_pow_pos i) (mem_dyad.mp hm).1

/-- The harmonic dyadic polynomial `∑_{m ∈ dyad i} f(m) m^{-1+it}`. -/
def hpoly (f : ℕ → ℂ) (i : ℕ) (t : ℝ) : ℂ := dp (dyad i) (fun m => f m / m) t

theorem continuous_hpoly (f : ℕ → ℂ) (i : ℕ) : Continuous (hpoly f i) :=
  P5Core.continuous_dp _ _

theorem card_dyad (i : ℕ) : (dyad i).card = 2 ^ i := by
  simp only [dyad, Nat.card_Ico, pow_succ]; omega

/-- A dyadic polynomial is bounded by the coefficient bound. -/
theorem norm_hpoly_le (f : ℕ → ℂ) (i : ℕ) (B : ℝ) (hB : ∀ m ∈ dyad i, ‖f m‖ ≤ B) (t : ℝ) :
    ‖hpoly f i t‖ ≤ B := by
  have hB0 : 0 ≤ B := by
    have h := hB (2 ^ i) (mem_dyad.mpr ⟨le_rfl, Nat.pow_lt_pow_right (by norm_num) (by omega)⟩)
    exact (norm_nonneg _).trans h
  unfold hpoly dp
  calc ‖∑ m ∈ dyad i, f m / m * mellin m t‖ ≤ ∑ m ∈ dyad i, ‖f m / m * mellin m t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ dyad i, B / 2 ^ i := by
        apply Finset.sum_le_sum
        intro m hm
        have hm1 := (mem_dyad.mp hm).1
        have hmpos : (0 : ℝ) < m := by exact_mod_cast dyad_pos hm
        have hm2 : (2 : ℝ) ^ i ≤ m := by exact_mod_cast hm1
        rw [norm_mul, P5Core.norm_mellin, mul_one, norm_div, Complex.norm_natCast]
        calc ‖f m‖ / m ≤ B / m := div_le_div_of_nonneg_right (hB m hm) hmpos.le
          _ ≤ B / 2 ^ i := div_le_div_of_nonneg_left hB0 (by positivity) hm2
    _ = B := by
        rw [Finset.sum_const, card_dyad, nsmul_eq_mul]
        push_cast
        field_simp

/-! ### Boxes of `k` dyads -/

/-- The box of tuples. -/
def boxSet {k : ℕ} (i : Fin k → ℕ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset fun j => dyad (i j)

/-- The collapsed coefficient of a product of dyadic polynomials. -/
def coll {k : ℕ} (f : Fin k → ℕ → ℂ) (i : Fin k → ℕ) (n : ℕ) : ℂ :=
  (∑ z ∈ (boxSet i).filter (fun z => ∏ j, z j = n), ∏ j, f j (z j)) / n

theorem box_prod_bounds {k : ℕ} (i : Fin k → ℕ) (z : Fin k → ℕ) (hz : z ∈ boxSet i) :
    2 ^ (∑ j, i j) ≤ ∏ j, z j ∧ ∏ j, z j ≤ 2 ^ (∑ j, i j + k) := by
  have hz' : ∀ j, z j ∈ dyad (i j) := fun j => Fintype.mem_piFinset.mp hz j
  constructor
  · rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod fun j _ => (mem_dyad.mp (hz' j)).1
  · have : 2 ^ (∑ j, i j + k) = ∏ j : Fin k, 2 ^ (i j + 1) := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
      simp
    rw [this]
    exact Finset.prod_le_prod fun j _ => (mem_dyad.mp (hz' j)).2.le

/-- Product of `k` dyadic polynomials as one Dirichlet polynomial. -/
theorem prod_hpoly_eq {k : ℕ} (f : Fin k → ℕ → ℂ) (i : Fin k → ℕ) (t : ℝ) :
    ∏ j, hpoly (f j) (i j) t = dp (Finset.Icc 1 (2 ^ (∑ j, i j + k))) (coll f i) t := by
  classical
  have hzpos : ∀ z ∈ boxSet i, ∀ j, 0 < z j := fun z hz j =>
    dyad_pos (Fintype.mem_piFinset.mp hz j)
  unfold hpoly dp
  rw [Finset.prod_univ_sum]
  have hterm : ∀ z ∈ boxSet i, (∏ j, f j (z j) / (z j : ℕ) * mellin (z j : ℕ) t) =
      (∏ j, f j (z j)) / ((∏ j, z j : ℕ) : ℂ) * mellin ((∏ j, z j : ℕ) : ℕ) t := by
    intro z hz
    rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]
    congr 1
    · push_cast; rfl
    · push_cast
      rw [P5Core.mellin_prod _ _ _ (fun j _ => by exact_mod_cast hzpos z hz j)]
  change ∑ z ∈ boxSet i, ∏ j, f j (z j) / (z j : ℕ) * mellin (z j : ℕ) t = _
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun z => ∏ j, z j)
    (t := Finset.Icc 1 (2 ^ (∑ j, i j + k)))]
  · apply Finset.sum_congr rfl
    intro n _
    unfold coll
    rw [Finset.sum_div, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  · intro z hz
    have hb := box_prod_bounds i z hz
    have h1 : 1 ≤ ∏ j, z j := le_trans (Nat.one_le_two_pow) hb.1
    exact Finset.mem_Icc.mpr ⟨h1, hb.2⟩

/-- Fiber count: tuples with a given product are tuples of divisors. -/
theorem box_fiber_card_le {k : ℕ} (i : Fin k → ℕ) (n : ℕ) (hn : 0 < n) :
    ((boxSet i).filter (fun z => ∏ j, z j = n)).card ≤ n.divisors.card ^ k := by
  classical
  have hsub : (boxSet i).filter (fun z => ∏ j, z j = n) ⊆
      Fintype.piFinset (fun _ : Fin k => n.divisors) := by
    intro z hz
    obtain ⟨_, hprod⟩ := Finset.mem_filter.mp hz
    apply Fintype.mem_piFinset.mpr
    intro j
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn.ne'⟩
    rw [← hprod]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  calc _ ≤ (Fintype.piFinset (fun _ : Fin k => n.divisors)).card := Finset.card_le_card hsub
    _ = n.divisors.card ^ k := by simp [Fintype.card_piFinset]

theorem norm_coll_le {k : ℕ} (f : Fin k → ℕ → ℂ) (i : Fin k → ℕ) (B : Fin k → ℝ)
    (hB0 : ∀ j, 0 ≤ B j) (hB : ∀ j, ∀ m ∈ dyad (i j), ‖f j m‖ ≤ B j) (n : ℕ) (hn : 0 < n) :
    ‖coll f i n‖ ≤ (n.divisors.card : ℝ) ^ k * (∏ j, B j) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold coll
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ hnpos.le
  calc ‖∑ z ∈ (boxSet i).filter (fun z => ∏ j, z j = n), ∏ j, f j (z j)‖
      ≤ ∑ z ∈ (boxSet i).filter (fun z => ∏ j, z j = n), ‖∏ j, f j (z j)‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ (boxSet i).filter (fun z => ∏ j, z j = n), ∏ j, B j := by
        apply Finset.sum_le_sum
        intro z hz
        rw [norm_prod]
        apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
        intro j _
        exact hB j _ (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hz).1 j)
    _ = ((boxSet i).filter (fun z => ∏ j, z j = n)).card * ∏ j, B j := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n.divisors.card : ℝ) ^ k * ∏ j, B j := by
        have hBnn : 0 ≤ ∏ j, B j := Finset.prod_nonneg fun j _ => hB0 j
        apply mul_le_mul_of_nonneg_right _ hBnn
        exact_mod_cast box_fiber_card_le i n hn

theorem divisor_pow_count (k : ℕ) :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧ ∀ Y : ℝ, 1 ≤ Y →
      (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k) ≤ K * Y * Real.log (2 * Y) ^ c := by
  obtain ⟨c₀, K, hK, hm⟩ := Blueprint.DivisorMoments_proof k
  let c := max c₀ 0
  let M := max 1 (Real.log 2 ^ c₀)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by linarith
  refine ⟨c, K * M, le_max_right _ _, mul_pos hK hMpos, ?_⟩
  intro Y hY
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log (2 * Y) := Real.log_le_log (by norm_num) (by linarith)
  have hlogpos : 0 < Real.log (2 * Y) := hlog2.trans_le hlog
  have hpow : Real.log (2 * Y) ^ c₀ ≤ M * Real.log (2 * Y) ^ c := by
    by_cases hc : 0 ≤ c₀
    · have heq : c = c₀ := max_eq_left hc
      rw [heq]
      exact le_mul_of_one_le_left (Real.rpow_nonneg hlogpos.le _) hM1
    · have hc₀ : c₀ ≤ 0 := le_of_not_ge hc
      have heq : c = 0 := max_eq_right hc₀
      rw [heq, Real.rpow_zero, mul_one]
      exact (Real.rpow_le_rpow_of_nonpos hlog2 hlog hc₀).trans (le_max_right _ _)
  calc
    _ ≤ K * Y * Real.log (2 * Y) ^ c₀ := (hm Y hY).2
    _ ≤ K * Y * (M * Real.log (2 * Y) ^ c) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- Coefficient square sum of a collapsed box product. -/
theorem sqNorm_coll_le (k : ℕ) : ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
    ∀ (f : Fin k → ℕ → ℂ) (i : Fin k → ℕ) (B : Fin k → ℝ),
      (∀ j, 0 ≤ B j) → (∀ j, ∀ m ∈ dyad (i j), ‖f j m‖ ≤ B j) →
      sqNorm (Finset.Icc 1 (2 ^ (∑ j, i j + k))) (coll f i) ≤
        K * (∏ j, B j) ^ 2 * Real.log (2 * 2 ^ (∑ j, i j + k)) ^ c / 2 ^ (∑ j, i j) := by
  obtain ⟨c, K, hc, hK, hcount⟩ := divisor_pow_count (2 * k)
  refine ⟨c, K * 2 ^ k, hc, by positivity, ?_⟩
  intro f i B hB0 hB
  set N : ℕ := 2 ^ (∑ j, i j + k) with hN
  set S : ℕ := ∑ j, i j with hS
  have hBnn : 0 ≤ ∏ j, B j := Finset.prod_nonneg fun j _ => hB0 j
  have hpt : ∀ n ∈ Finset.Icc 1 N, ‖coll f i n‖ ^ 2 ≤
      ((n.divisors.card : ℝ) ^ (2 * k)) * ((∏ j, B j) ^ 2 / (2 ^ S) ^ 2) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hne : ((boxSet i).filter (fun z => ∏ j, z j = n)).Nonempty
    · obtain ⟨z, hz⟩ := hne
      obtain ⟨hzbox, hzprod⟩ := Finset.mem_filter.mp hz
      have hlo : 2 ^ S ≤ n := hzprod ▸ (box_prod_bounds i z hzbox).1
      have hloR : (2 : ℝ) ^ S ≤ n := by exact_mod_cast hlo
      have h1 := norm_coll_le f i B hB0 hB n (by omega)
      have h2 : (n.divisors.card : ℝ) ^ k * (∏ j, B j) / n ≤
          (n.divisors.card : ℝ) ^ k * (∏ j, B j) / 2 ^ S :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hloR
      calc ‖coll f i n‖ ^ 2 ≤ ((n.divisors.card : ℝ) ^ k * (∏ j, B j) / 2 ^ S) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
        _ = _ := by rw [pow_mul]; ring
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : coll f i n = 0 := by simp [coll, hne]
      rw [this, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_two_pow
  calc sqNorm (Finset.Icc 1 N) (coll f i)
      ≤ ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ (2 * k)) *
          ((∏ j, B j) ^ 2 / (2 ^ S) ^ 2) := Finset.sum_le_sum hpt
    _ = (∑ n ∈ Finset.Icc 1 ⌊(N : ℝ)⌋₊, (n.divisors.card : ℝ) ^ (2 * k)) *
          ((∏ j, B j) ^ 2 / (2 ^ S) ^ 2) := by
        rw [Finset.sum_mul, Nat.floor_natCast]
    _ ≤ (K * N * Real.log (2 * N) ^ c) * ((∏ j, B j) ^ 2 / (2 ^ S) ^ 2) :=
        mul_le_mul_of_nonneg_right (hcount N hNR) (by positivity)
    _ = K * 2 ^ k * (∏ j, B j) ^ 2 * Real.log (2 * 2 ^ (S + k)) ^ c / 2 ^ S := by
        rw [hN]
        push_cast
        rw [pow_add]
        field_simp

theorem coll_eq_zero_of_lt {k : ℕ} (f : Fin k → ℕ → ℂ) (i : Fin k → ℕ) (n : ℕ)
    (hn : n < 2 ^ (∑ j, i j)) : coll f i n = 0 := by
  unfold coll
  have : (boxSet i).filter (fun z => ∏ j, z j = n) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro z hz hprod
    have := (box_prod_bounds i z hz).1
    omega
  rw [this, Finset.sum_empty, zero_div]

end Erdos821.P5Marked
