import Erdos821.P5MarkedEnergy.FinalPiece

/-! The two square sums of the final assembly: the square-multiple error and
the coefficient square sum of one piece. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic P5Core

/-- The square-multiple error sum. -/
theorem error_total : ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
    ∀ (P : Geometry) (G : PrimeGroups) (x C τ η Y v lo hi M0 Mw : ℝ) (E : Endpoint)
      (t : Fin G.size → ℕ) (b : Tuple G t → ℂ) (Ψ : ℝ → ℂ) (gs : Fin G.size) (ls : Fin (t gs))
      (r : ℕ) (u : ℤ) (J0 : ℕ),
      1 ≤ L x → EndpointBound x C τ η E → 0 < lo → 0 < Y → hi ≤ lo * 2 ^ J0 →
      gs ∈ G.small → 0 < mass G gs →
      (∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z') →
      (∀ p ∈ G.primes gs, ((p ^ 2 : ℕ) : ℝ) ≤ lo * Y) →
      (∀ y, ‖Ψ y‖ ≤ M0) →
      (∀ n ∈ Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊,
        ‖weightedMarks G P.q t b n - Wtil G gs (Wres G t gs ls P.q b) n‖ ≤ Mw) →
      (∑ n ∈ Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊,
          ‖epsf P G x Y v E t b Ψ gs (Wres G t gs ls P.q b) r u n‖ ^ 2) ≤
        (M0 * Mw) ^ 2 * ((J0 + 1) * K * (lo * Y * 2 ^ J0) * L x ^ (4 * C) *
          Real.log (4 * (lo * Y * 2 ^ J0)) ^ c * ∑ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2)) := by
  obtain ⟨c, K, hc, hK, hbad⟩ := bad_endpoint_sum
  refine ⟨c, K, hc, hK, ?_⟩
  intro P G x C τ η Y v lo hi M0 Mw E t b Ψ gs ls r u J0 hL hE hlo hY hJ0 hgs hmass hb hp2 hM0 hMw
  set S := Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊ with hS
  have hM00 : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  have hpt : ∀ n ∈ S, ‖epsf P G x Y v E t b Ψ gs (Wres G t gs ls P.q b) r u n‖ ^ 2 ≤
      (if ∃ p ∈ G.primes gs, p ^ 2 ∣ n then (M0 * Mw) ^ 2 * ‖endpoint G x E n‖ ^ 2 else 0) := by
    intro n hn
    split_ifs with hbadn
    · unfold epsf
      rw [norm_mul, norm_mul, norm_mul, norm_mul, P5Core.norm_mellin, mul_one]
      have he : ‖e (u * n / r)‖ = 1 := norm_e _
      rw [he, mul_one]
      have h1 := hM0 (n / Y)
      have h2 := hMw n hn
      have hMw0 : 0 ≤ Mw := (norm_nonneg _).trans h2
      calc (‖Ψ (n / Y)‖ * ‖endpoint G x E n‖ *
            ‖weightedMarks G P.q t b n - Wtil G gs (Wres G t gs ls P.q b) n‖) ^ 2
          ≤ (M0 * ‖endpoint G x E n‖ * Mw) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) h2 (norm_nonneg _)
              (by positivity)
        _ = (M0 * Mw) ^ 2 * ‖endpoint G x E n‖ ^ 2 := by ring
    · push_neg at hbadn
      rw [epsf_eq_zero_of_good P G x Y v E t b Ψ gs ls r u hgs hb hmass n hbadn]
      simp
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply hbad G x C τ η lo hi Y E J0 (G.primes gs) hL hE hlo hY hJ0
  intro p hp
  exact ⟨G.prime gs p hp, Finset.mem_biUnion.mpr ⟨gs, Finset.mem_univ _, hp⟩, hp2 p hp⟩

/-- The coefficient square sum of one piece. -/
theorem sq_total : ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧
    ∀ (G : PrimeGroups) (x Y v lo hi M0 B1 B2 B3 B4 : ℝ) (E : Endpoint) (Ψ : ℝ → ℂ)
      (gs : Fin G.size) (Wr : ℕ → ℂ) (r : ℕ) (u : ℤ) (i : ℕ) (χ : DirichletCharacter ℂ r),
      0 < lo → 0 < Y → 1 ≤ hi * Y → (∀ y, ‖Ψ y‖ ≤ M0) →
      (∀ m, ‖cf1 E r χ m‖ ≤ B1) → (∀ m, ‖cf2 G gs r χ m‖ ≤ B2) →
      (∀ m, ‖cf3 E x r χ m‖ ≤ B3) → (∀ m, ‖cf4 G E Wr r u χ m‖ ≤ B4) →
      sqNorm (spiece lo hi Y i) (bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ i χ) ≤
        M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 * (K * (hi * Y) * Real.log (2 * (hi * Y)) ^ c) := by
  obtain ⟨c, K, hc, hK, hcount⟩ := divisor_pow_count 6
  refine ⟨c, K, hc, hK, ?_⟩
  intro G x Y v lo hi M0 B1 B2 B3 B4 E Ψ gs Wr r u i χ hlo hY hhiY hM0 h1 h2 h3 h4
  set N := ⌊hi * Y⌋₊ with hN
  have hM00 : 0 ≤ M0 := (norm_nonneg _).trans (hM0 0)
  have hBB : 0 ≤ B1 * B2 * B3 * B4 := by
    have b1 := (norm_nonneg _).trans (h1 0); have b2 := (norm_nonneg _).trans (h2 0)
    have b3 := (norm_nonneg _).trans (h3 0); have b4 := (norm_nonneg _).trans (h4 0)
    positivity
  have hsub : spiece lo hi Y i ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨a1, a2⟩ := Finset.mem_Icc.mp hn1
    have : 0 < ⌈lo * Y⌉₊ := Nat.ceil_pos.mpr (by positivity)
    exact Finset.mem_Icc.mpr ⟨by omega, a2⟩
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ‖bpiece G x Y v lo E Ψ gs Wr r u N i χ n‖ ^ 2 ≤
        M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 * (n.divisors.card : ℝ) ^ 6 := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    unfold bpiece
    rw [norm_mul, norm_mul, norm_mul, P5Core.norm_mellin, mul_one, Complex.norm_real]
    have hpsi : ‖psi lo i (n / Y)‖ ≤ 1 := by
      unfold psi gstep
      rw [Real.norm_eq_abs, abs_le]
      have a1 := Real.smoothTransition.nonneg ((n / Y - ptA lo i) / (ptA lo (i + 1) - ptA lo i))
      have a2 := Real.smoothTransition.le_one ((n / Y - ptA lo i) / (ptA lo (i + 1) - ptA lo i))
      have a3 := Real.smoothTransition.nonneg
        ((n / Y - ptA lo (i + 1)) / (ptA lo (i + 1 + 1) - ptA lo (i + 1)))
      have a4 := Real.smoothTransition.le_one
        ((n / Y - ptA lo (i + 1)) / (ptA lo (i + 1 + 1) - ptA lo (i + 1)))
      constructor <;> linarith
    have hq := norm_quad_le (cf1 E r χ) (cf2 G gs r χ) (cf3 E x r χ) (cf4 G E Wr r u χ)
      B1 B2 B3 B4 h1 h2 h3 h4 N n hn1
    have hΨ := hM0 (n / Y)
    calc (‖Ψ (n / Y)‖ * ‖psi lo i (n / Y)‖ *
          ‖quad (cf1 E r χ) (cf2 G gs r χ) (cf3 E x r χ) (cf4 G E Wr r u χ) N n‖) ^ 2
        ≤ (M0 * 1 * ((n.divisors.card : ℝ) ^ 3 * (B1 * B2 * B3 * B4))) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul (mul_le_mul hΨ hpsi (norm_nonneg _) hM00) hq (norm_nonneg _)
            (by positivity)
      _ = M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 * (n.divisors.card : ℝ) ^ 6 := by ring
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.le_floor (by exact_mod_cast hhiY)
  calc sqNorm (spiece lo hi Y i) (bpiece G x Y v lo E Ψ gs Wr r u N i χ)
      ≤ sqNorm (Finset.Icc 1 N) (bpiece G x Y v lo E Ψ gs Wr r u N i χ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ n ∈ Finset.Icc 1 N, M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 * (n.divisors.card : ℝ) ^ 6 :=
        Finset.sum_le_sum hpt
    _ = M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 *
          ∑ n ∈ Finset.Icc 1 ⌊(N : ℝ)⌋₊, (n.divisors.card : ℝ) ^ 6 := by
        rw [Finset.mul_sum, Nat.floor_natCast]
    _ ≤ M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 * (K * N * Real.log (2 * N) ^ c) :=
        mul_le_mul_of_nonneg_left (hcount N hN1) (by positivity)
    _ ≤ M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 * (K * (hi * Y) * Real.log (2 * (hi * Y)) ^ c) := by
        have hNle : (N : ℝ) ≤ hi * Y := Nat.floor_le (by linarith)
        have hlog0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
        have hlog : Real.log (2 * N) ≤ Real.log (2 * (hi * Y)) :=
          Real.log_le_log (by linarith) (by linarith)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul (mul_le_mul_of_nonneg_left hNle hK.le) (Real.rpow_le_rpow hlog0 hlog hc)
          (Real.rpow_nonneg hlog0 _) (by positivity)

def ErrorSpec (c K : ℝ) : Prop :=
    ∀ (P : Geometry) (G : PrimeGroups) (x C τ η Y v lo hi M0 Mw : ℝ) (E : Endpoint)
      (t : Fin G.size → ℕ) (b : Tuple G t → ℂ) (Ψ : ℝ → ℂ) (gs : Fin G.size) (ls : Fin (t gs))
      (r : ℕ) (u : ℤ) (J0 : ℕ),
      1 ≤ L x → EndpointBound x C τ η E → 0 < lo → 0 < Y → hi ≤ lo * 2 ^ J0 →
      gs ∈ G.small → 0 < mass G gs →
      (∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z') →
      (∀ p ∈ G.primes gs, ((p ^ 2 : ℕ) : ℝ) ≤ lo * Y) →
      (∀ y, ‖Ψ y‖ ≤ M0) →
      (∀ n ∈ Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊,
        ‖weightedMarks G P.q t b n - Wtil G gs (Wres G t gs ls P.q b) n‖ ≤ Mw) →
      (∑ n ∈ Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊,
          ‖epsf P G x Y v E t b Ψ gs (Wres G t gs ls P.q b) r u n‖ ^ 2) ≤
        (M0 * Mw) ^ 2 * ((J0 + 1) * K * (lo * Y * 2 ^ J0) * L x ^ (4 * C) *
          Real.log (4 * (lo * Y * 2 ^ J0)) ^ c * ∑ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2))

theorem error_total' : ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧ ErrorSpec c K := error_total

def SqSpec (c K : ℝ) : Prop :=
    ∀ (G : PrimeGroups) (x Y v lo hi M0 B1 B2 B3 B4 : ℝ) (E : Endpoint) (Ψ : ℝ → ℂ)
      (gs : Fin G.size) (Wr : ℕ → ℂ) (r : ℕ) (u : ℤ) (i : ℕ) (χ : DirichletCharacter ℂ r),
      0 < lo → 0 < Y → 1 ≤ hi * Y → (∀ y, ‖Ψ y‖ ≤ M0) →
      (∀ m, ‖cf1 E r χ m‖ ≤ B1) → (∀ m, ‖cf2 G gs r χ m‖ ≤ B2) →
      (∀ m, ‖cf3 E x r χ m‖ ≤ B3) → (∀ m, ‖cf4 G E Wr r u χ m‖ ≤ B4) →
      sqNorm (spiece lo hi Y i) (bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ i χ) ≤
        M0 ^ 2 * (B1 * B2 * B3 * B4) ^ 2 * (K * (hi * Y) * Real.log (2 * (hi * Y)) ^ c)

theorem sq_total' : ∃ c K : ℝ, 0 ≤ c ∧ 0 < K ∧ SqSpec c K := sq_total

end Erdos821.P5Marked
