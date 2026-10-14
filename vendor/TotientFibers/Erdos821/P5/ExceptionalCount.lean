import Erdos821.P5.Exceptional
import Erdos821.P5.DiscreteMoments
import Erdos821.P5.CoefficientSquare

noncomputable section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

/-- A separated-point estimate loses at most three when sampling closed integer cells. -/
theorem three_class_sum_bound (E : Finset ℤ) (t : ℤ → ℝ) (v : ℝ → ℝ) (M : ℝ)
    (hcell : ∀ k ∈ E, (k : ℝ) ≤ t k ∧ t k ≤ (k : ℝ) + 1)
    (hbound : ∀ J : Finset ℤ, J ⊆ E →
      (∀ k ∈ J, ∀ l ∈ J, k ≠ l → 1 ≤ |t k - t l|) →
      ∑ k ∈ J, v (t k) ≤ M) :
    ∑ k ∈ E, v (t k) ≤ 3 * M := by
  classical
  have hparts : ∑ i ∈ Finset.Ico (0 : ℤ) 3,
      ∑ k ∈ E.filter (fun k => k % 3 = i), v (t k) = ∑ k ∈ E, v (t k) := by
    apply Finset.sum_fiberwise_of_maps_to
    intro k _
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  rw [← hparts]
  calc
    _ ≤ ∑ _i ∈ Finset.Ico (0 : ℤ) 3, M := by
      apply Finset.sum_le_sum
      intro i _
      apply hbound _ (Finset.filter_subset _ _)
      intro k hk l hl hkl
      obtain ⟨hkE, hkmod⟩ := Finset.mem_filter.mp hk
      obtain ⟨hlE, hlmod⟩ := Finset.mem_filter.mp hl
      exact cell_times_separated t k l (hcell k hkE) (hcell l hlE) hkl
        (hkmod.trans hlmod.symm)
    _ = _ := by norm_num

/-- The finite high-moment bound underlying the exceptional-times lemma.
The power m is arbitrary, and the P1 mean-square constant is uniform in m. -/
theorem occupied_moment_bound
    (hm : Blueprint.MeanSquares := Erdos821.Classical.blueprint_meanSquares) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s : Finset ℕ) (b : ℕ → ℂ) (m : ℕ) (δ Tmax : ℝ),
      (∀ p ∈ s, p.Prime) → 0 ≤ δ → 0 ≤ Tmax →
      ((occupied s b δ Tmax).ncard : ℝ) * δ ^ (2 * m) ≤
        3 * K * (2 * Tmax + 1 + ((s.sup id) ^ m : ℕ) *
          Real.log (2 * ((s.sup id) ^ m : ℕ))) *
          Real.log (2 * ((s.sup id) ^ m : ℕ)) ^ 2 *
          Nat.factorial m * (∑ p ∈ s, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) ^ m := by
  classical
  obtain ⟨K, hK, hmean⟩ := discrete_prime_polynomial_moment hm
  refine ⟨K, hK, ?_⟩
  intro s b m δ Tmax hprime hδ hT
  let hfinite := occupied_finite s b δ Tmax
  let E := hfinite.toFinset
  obtain ⟨t, ht⟩ := occupied_witnesses s b δ Tmax
  have htE (k : ℤ) (hk : k ∈ E) := ht k (by simpa [E] using hk)
  let M := K * (2 * Tmax + 1 + ((s.sup id) ^ m : ℕ) *
      Real.log (2 * ((s.sup id) ^ m : ℕ))) *
      Real.log (2 * ((s.sup id) ^ m : ℕ)) ^ 2 *
      Nat.factorial m * (∑ p ∈ s, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) ^ m
  have hsample : ∑ k ∈ E, ‖primePolynomial s b (t k)‖ ^ (2 * m) ≤ 3 * M := by
    apply three_class_sum_bound E t (fun u => ‖primePolynomial s b u‖ ^ (2 * m)) M
      (fun k hk => ⟨(htE k hk).1, (htE k hk).2.1⟩)
    intro J hJE hsep
    have hinj : Set.InjOn t (J : Set ℤ) := by
      intro k hk l hl hkl
      by_contra hne
      have h := hsep k hk l hl hne
      rw [hkl, sub_self, abs_zero] at h
      norm_num at h
    have htime : ∀ u ∈ J.image t, -Tmax ≤ u ∧ u ≤ Tmax := by
      intro u hu
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
      exact abs_le.mp (htE k (hJE hk)).2.2.1
    have hsep' : ∀ u ∈ J.image t, ∀ v ∈ J.image t, u ≠ v → 1 ≤ |u - v| := by
      intro u hu v hv hne
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hv
      exact hsep k hk l hl (fun h => hne (congrArg t h))
    have h := hmean s b m (-Tmax) Tmax (J.image t) hprime (by linarith) htime hsep'
    rw [Finset.sum_image hinj] at h
    simpa only [M, sub_neg_eq_add, ← two_mul] using h
  have hcard : (E.card : ℝ) * δ ^ (2 * m) ≤
      ∑ k ∈ E, ‖primePolynomial s b (t k)‖ ^ (2 * m) := by
    calc
      _ = ∑ _k ∈ E, δ ^ (2 * m) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun k hk =>
        pow_le_pow_left₀ hδ (htE k hk).2.2.2.le _)
  have h := hcard.trans hsample
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  simpa only [E, M, mul_assoc] using h

theorem nat_log_two_nonneg (N : ℕ) : 0 ≤ Real.log (2 * N) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    exact Real.log_nonneg (by linarith)

/-- The quantitative bound before selecting the growing power.
It uses only the prime dyad, bounded coefficients, and polynomial length ≤Y. -/
theorem occupied_count_bound
    (hm : Blueprint.MeanSquares := Erdos821.Classical.blueprint_meanSquares) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (b : ℕ → ℂ) (m : ℕ)
      (P δ Tmax Y : ℝ),
      1 ≤ P → 0 < δ → 0 ≤ Tmax → Tmax ≤ Y → 1 ≤ Y →
      (((s.sup id) ^ m : ℕ) : ℝ) ≤ Y →
      (∀ p ∈ s, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
      (∀ p ∈ s, ‖b p‖ ≤ 1) →
      ((occupied s b δ Tmax).ncard : ℝ) ≤
        C * Y * (1 + Real.log (2 * Y)) ^ 3 *
          Nat.factorial m * (3 / P) ^ m / δ ^ (2 * m) := by
  classical
  obtain ⟨K, hK, hcount⟩ := occupied_moment_bound hm
  refine ⟨9 * K, by positivity, ?_⟩
  intro s b m P δ Tmax Y hP hδ hT hTY hY hNY hs hb
  let N := (s.sup id) ^ m
  let B := 1 + Real.log (2 * Y)
  have hlogY : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hlogN : 0 ≤ Real.log (2 * N) := nat_log_two_nonneg N
  have hlogNY : Real.log (2 * N) ≤ Real.log (2 * Y) := by
    by_cases hN : N = 0
    · simpa [hN] using hlogY
    · apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left hNY (by norm_num)
  have hbase : 2 * Tmax + 1 + N * Real.log (2 * N) ≤ 3 * Y * B := by
    have hprod := mul_le_mul hNY hlogNY hlogN (by linarith : 0 ≤ Y)
    dsimp [B]
    nlinarith
  have hsq : Real.log (2 * N) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hlogN (by dsimp [B]; linarith) 2
  have hpoly : (∑ p ∈ s, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) ^ m ≤ (3 / P) ^ m :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun p _ => by positivity))
      (harmonic_coefficient_square s b P hP (fun p hp => (hs p hp).2) hb) m
  have hscale :
      3 * K * (2 * Tmax + 1 + N * Real.log (2 * N)) * Real.log (2 * N) ^ 2 *
        Nat.factorial m * (∑ p ∈ s, ‖b p‖ ^ 2 / (p : ℝ) ^ 2) ^ m ≤
      (9 * K) * Y * B ^ 3 * Nat.factorial m * (3 / P) ^ m := by
    calc
      _ ≤ 3 * K * (3 * Y * B) * B ^ 2 *
          Nat.factorial m * (3 / P) ^ m := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hbase (by positivity)
          · exact hsq
          · positivity
          · positivity
        · exact hpoly
        · positivity
        · positivity
      _ = _ := by ring
  apply (le_div_iff₀ (pow_pos hδ (2 * m))).mpr
  exact (hcount s b m δ Tmax (fun p hp => (hs p hp).1) hδ.le hT).trans hscale

end Erdos821.P5Core
