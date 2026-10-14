import Erdos821.P5MarkedEnergy.Factorization
import Erdos821.P5.EndpointMean

/-! The square-multiple error of small-mark removal (paper §4): the endpoint
square sum over multiples of `p_s^2`, summed over the removed group. -/

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

theorem sum_biUnion_le_of_nonneg {ι : Type*} (s : Finset ι) (t : ι → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) : ∑ n ∈ s.biUnion t, f n ≤ ∑ i ∈ s, ∑ n ∈ t i, f n := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ n ∈ t i ∩ s.biUnion t, f n := Finset.sum_nonneg fun n _ => hf n
    linarith

/-- The number of distinct primes of a finite set dividing `n`. -/
theorem card_primes_dvd_le (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (n : ℕ) (hn : 1 ≤ n)
    (hdvd : ∀ p ∈ T, p ∣ n) : (T.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have hsub : T ⊆ n.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨hT p hp, hdvd p hp, by omega⟩
  have hprod : ∏ p ∈ T, p ∣ n :=
    (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd n)
  have hpow : 2 ^ T.card ≤ ∏ p ∈ T, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (hT p hp).two_le)
  have hle : 2 ^ T.card ≤ n := hpow.trans (Nat.le_of_dvd (by omega) hprod)
  have hleR : (2 : ℝ) ^ T.card ≤ n := by exact_mod_cast hle
  have hlog := Real.log_le_log (by positivity) hleR
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  exact hlog

/-- Covering a size range by dyadic intervals. -/
theorem exists_dyadic_index (lo Y : ℝ) (hlo : 0 < lo) (hY : 0 < Y) (J0 : ℕ) (hi : ℝ)
    (hJ : hi ≤ lo * 2 ^ J0) (n : ℕ) (hn1 : lo * Y ≤ n) (hn2 : (n : ℝ) ≤ hi * Y) :
    ∃ j ∈ Finset.range (J0 + 1), n ∈ Finset.Icc ⌈lo * Y * 2 ^ j⌉₊ ⌊2 * (lo * Y * 2 ^ j)⌋₊ := by
  have hX : 0 < lo * Y := by positivity
  set z := (n : ℝ) / (lo * Y) with hz
  have hz1 : 1 ≤ z := by rw [hz, le_div_iff₀ hX]; linarith
  set j := Nat.log 2 ⌊z⌋₊ with hj
  have hf1 : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz1)
  have hjlo : 2 ^ j ≤ ⌊z⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have hjhi : ⌊z⌋₊ < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hjloR : (2 : ℝ) ^ j ≤ z := by
    have : ((2 ^ j : ℕ) : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hjlo
    push_cast at this
    exact this.trans (Nat.floor_le (by linarith))
  have hjhiR : z < (2 : ℝ) ^ (j + 1) := by
    have : (⌊z⌋₊ + 1 : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hjhi
    push_cast at this
    linarith [Nat.lt_floor_add_one z]
  refine ⟨j, ?_, ?_⟩
  · apply Finset.mem_range.mpr
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : (2 : ℝ) ^ (J0 + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hcon
    have h2 : z ≤ hi / lo := by
      rw [hz, div_le_div_iff₀ hX hlo]; nlinarith
    have h3 : hi / lo ≤ 2 ^ J0 := by rw [div_le_iff₀ hlo]; linarith
    have : (2 : ℝ) ^ (J0 + 1) = 2 * 2 ^ J0 := by ring
    have h4 : (0 : ℝ) < 2 ^ J0 := by positivity
    linarith
  · apply Finset.mem_Icc.mpr
    constructor
    · apply Nat.ceil_le.mpr
      have := hjloR
      rw [hz, le_div_iff₀ hX] at this
      linarith
    · apply Nat.le_floor
      have := hjhiR.le
      rw [hz, div_le_iff₀ hX] at this
      have e : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [e] at this
      linarith

/-- The endpoint square sum over all multiples of squares of the removed primes. -/
theorem bad_endpoint_sum :
    ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
      ∀ (G : PrimeGroups) (x C τ η lo hi Y : ℝ) (E : Endpoint) (J0 : ℕ) (Pset : Finset ℕ),
        1 ≤ L x → EndpointBound x C τ η E → 0 < lo → 0 < Y → hi ≤ lo * 2 ^ J0 →
        (∀ p ∈ Pset, p.Prime ∧ p ∈ Finset.univ.biUnion G.primes ∧ ((p ^ 2 : ℕ) : ℝ) ≤ lo * Y) →
        (∑ n ∈ (Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊).filter (fun n => ∃ p ∈ Pset, p ^ 2 ∣ n),
          ‖endpoint G x E n‖ ^ 2) ≤
          (J0 + 1) * K * (lo * Y * 2 ^ J0) * L x ^ (4 * C) *
            Real.log (4 * (lo * Y * 2 ^ J0)) ^ c * ∑ p ∈ Pset, 1 / ((p : ℝ) ^ 2) := by
  obtain ⟨c, K, hc, hK, hmult⟩ := P5Core.endpoint_square_sum_multiples
  refine ⟨c, K, hc, hK, ?_⟩
  intro G x C τ η lo hi Y E J0 Pset hL hE hlo hY hJ hP
  set S := Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊ with hS
  set X : ℕ → ℝ := fun j => lo * Y * 2 ^ j with hXdef
  set Xs := lo * Y * 2 ^ J0 with hXs
  have hX0 : 0 < lo * Y := by positivity
  have hLpos : 0 < L x := by linarith
  have hf : ∀ n, 0 ≤ ‖endpoint G x E n‖ ^ 2 := fun n => by positivity
  -- union bound over the removed primes
  have hsub : S.filter (fun n => ∃ p ∈ Pset, p ^ 2 ∣ n) ⊆
      Pset.biUnion (fun p => S.filter (fun n => p ^ 2 ∣ n)) := by
    intro n hn
    obtain ⟨hnS, p, hp, hpn⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hnS, hpn⟩⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)).trans ?_
  refine (sum_biUnion_le_of_nonneg _ _ _ hf).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpprime, hpG, hpsq⟩ := hP p hp
  set D := p ^ 2 with hD
  have hD1 : 1 ≤ D := Nat.one_le_pow _ _ hpprime.pos
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  have hDprime : D.primeFactors ⊆ Finset.univ.biUnion G.primes := by
    rw [hD, Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors hpprime]
    intro q hq; rw [Finset.mem_singleton.mp hq]; exact hpG
  -- dyadic cover of the size range
  have hcover : S.filter (fun n => D ∣ n) ⊆ (Finset.range (J0 + 1)).biUnion
      (fun j => (Finset.Icc ⌈X j⌉₊ ⌊2 * X j⌋₊).filter (fun n => D ∣ n)) := by
    intro n hn
    obtain ⟨hnS, hDn⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hnS
    have hn1 : lo * Y ≤ n := Nat.ceil_le.mp h1
    have hn0 : n ≠ 0 := by
      intro h; rw [h] at hn1; push_cast at hn1; linarith
    have hn2 : (n : ℝ) ≤ hi * Y := (Nat.le_floor_iff' hn0).mp h2
    obtain ⟨j, hj, hnj⟩ := exists_dyadic_index lo Y hlo hY J0 hi hJ n hn1 hn2
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hnj, hDn⟩⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => hf n)).trans ?_
  refine (sum_biUnion_le_of_nonneg _ _ _ hf).trans ?_
  have hpiece : ∀ j ∈ Finset.range (J0 + 1),
      ∑ n ∈ (Finset.Icc ⌈X j⌉₊ ⌊2 * X j⌋₊).filter (fun n => D ∣ n), ‖endpoint G x E n‖ ^ 2 ≤
        K * Xs * L x ^ (4 * C) * Real.log (4 * Xs) ^ c * (1 / ((p : ℝ) ^ 2)) := by
    intro j hj
    have hjle : j ≤ J0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hXj : lo * Y ≤ X j := by
      simp only [hXdef]; exact le_mul_of_one_le_right hX0.le (one_le_pow₀ (by norm_num))
    have hXjs : X j ≤ Xs := by
      simp only [hXdef, hXs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hjle) hX0.le
    have hDX : (D : ℝ) ≤ X j := by
      have : ((D : ℕ) : ℝ) = ((p ^ 2 : ℕ) : ℝ) := rfl
      linarith
    have h := hmult G x C τ η (X j) E D hL hE hD1 hDX hDprime
    refine h.trans ?_
    have hXjpos : 0 < X j := lt_of_lt_of_le hX0 hXj
    have hDpos : (0 : ℝ) < D := by linarith
    have hlogpos : 0 ≤ Real.log (4 * X j / D) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hDpos]; linarith
    have hlog : Real.log (4 * X j / D) ≤ Real.log (4 * Xs) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hDpos]; nlinarith
    have hpow : Real.log (4 * X j / D) ^ c ≤ Real.log (4 * Xs) ^ c :=
      Real.rpow_le_rpow hlogpos hlog hc
    have hDp : (D : ℝ) = (p : ℝ) ^ 2 := by rw [hD]; push_cast; ring
    have hLc : 0 ≤ L x ^ (4 * C) := Real.rpow_nonneg hLpos.le _
    calc K * (X j / D) * L x ^ (4 * C) * Real.log (4 * X j / D) ^ c
        ≤ K * (Xs / D) * L x ^ (4 * C) * Real.log (4 * Xs) ^ c := by
          gcongr
      _ = K * Xs * L x ^ (4 * C) * Real.log (4 * Xs) ^ c * (1 / ((p : ℝ) ^ 2)) := by
          rw [hDp]; ring
  refine (Finset.sum_le_sum hpiece).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  rfl

end Erdos821.P5Marked
