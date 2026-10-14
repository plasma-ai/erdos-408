import Erdos408.TwoSided.Setup
import Erdos821.P5Energy.Final
import Erdos821.P5FourierArcProof.FourierArc
import Erdos821.P5MarkedEnergy.Weights

/-!
# Fourier identities and the arc energy

The finite Fourier analysis behind S8–S10 of `blueprint/two_sided_correlation.md` §§5.3–5.4,
for additive polynomials `∑_{n ∈ s} a_n e(θn)` over `ℕ` (upstream's
`localAdditivePolynomial`).

* `integral_norm_localAdditivePolynomial_sq`, `integral_star_mul_mul_sum`: Parseval and the
  shift identity
  `∫₀¹ star(∑ star(f_n) e(θn)) (∑ g_m e(θm)) ∑_l c_l e(-θD_l) = ∑_l c_l ∑_n f_n g_{n + D_l}`.
* `exists_integral_norm_localAdditivePolynomial_le`: the local Mellin energy (PD Lemma 6.4,
  upstream `LocalMellinEnergyTask_proof`) at the centre `c`, with the weighted tail over
  `|t| > T₀` bounded by the weighted mean value (upstream `weighted_mean_value`).
* `norm_sum_star_mul_cpow`: the Mellin side is `Y` times a twisted polynomial (6.24).
-/

namespace Erdos408.TwoSided.Arcs

open MeasureTheory
open Erdos821.Blueprint.Analytic (e dp mellin sqNorm)
open Erdos821.P5Core (localAdditivePolynomial integerAdditivePolynomial)

/-- An additive polynomial over `ℕ` is the integer one over the image of `s`. -/
private theorem localAdditivePolynomial_eq_int (s : Finset ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    localAdditivePolynomial s a θ =
      integerAdditivePolynomial (s.map Nat.castEmbedding) (fun z => a z.toNat) θ := by
  simp [localAdditivePolynomial, integerAdditivePolynomial, Finset.sum_map]

/-- Additive polynomials are continuous. -/
theorem continuous_localAdditivePolynomial (s : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (localAdditivePolynomial s a) := by
  unfold localAdditivePolynomial
  fun_prop

/-- Parseval: `∫₀¹ |∑ a_n e(θn)|² = ∑ |a_n|²`. -/
theorem integral_norm_localAdditivePolynomial_sq (s : Finset ℕ) (a : ℕ → ℂ) :
    ∫ θ in (0 : ℝ)..1, ‖localAdditivePolynomial s a θ‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  simp_rw [localAdditivePolynomial_eq_int]
  rw [Erdos821.P5Core.FourierArcTask_proof.2.1, Finset.sum_map]
  simp

/-- The shift identity for one shift `d`. -/
private theorem integral_star_mul_mul_e (s s' : Finset ℕ) (f g : ℕ → ℂ) (d : ℕ) :
    ∫ θ in (0 : ℝ)..1, star (localAdditivePolynomial s (fun n => star (f n)) θ) *
        localAdditivePolynomial s' g θ * e (-θ * d) =
      ∑ n ∈ s, if n + d ∈ s' then f n * g (n + d) else 0 := by
  simp_rw [localAdditivePolynomial_eq_int]
  have h := Erdos821.P5Core.FourierArcTask_proof.1 (s.map Nat.castEmbedding)
    (s'.map Nat.castEmbedding) (fun z => star (f z.toNat)) (fun z => g z.toNat) d
  simp only [Int.cast_natCast] at h
  rw [← h, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_map]
  simp only [Nat.castEmbedding_apply, Int.toNat_natCast, star_star]
  have hc : ∀ m : ℕ, ((m : ℤ) = (n : ℤ) + (d : ℤ)) ↔ m = n + d := fun m => by omega
  simp only [hc]
  rw [Finset.sum_ite_eq']

/-- **The shift identity.** If every `n + D_l` with `c_l ≠ 0` and `n ∈ s` lies in `s'`, then
`∫₀¹ star(∑ star(f_n) e(θn)) (∑ g_m e(θm)) ∑_l c_l e(-θ D_l) = ∑_l c_l ∑_n f_n g_{n + D_l}`. -/
theorem integral_star_mul_mul_sum {Λ : Type*} (Ls : Finset Λ) (c : Λ → ℂ) (D : Λ → ℕ)
    (s s' : Finset ℕ) (f g : ℕ → ℂ) (hD : ∀ l ∈ Ls, c l ≠ 0 → ∀ n ∈ s, n + D l ∈ s') :
    ∫ θ in (0 : ℝ)..1, star (localAdditivePolynomial s (fun n => star (f n)) θ) *
        localAdditivePolynomial s' g θ * ∑ l ∈ Ls, c l * e (-θ * D l) =
      ∑ l ∈ Ls, c l * ∑ n ∈ s, f n * g (n + D l) := by
  have hi : ∀ l ∈ Ls, IntervalIntegrable (fun θ => c l *
      (star (localAdditivePolynomial s (fun n => star (f n)) θ) *
        localAdditivePolynomial s' g θ * e (-θ * D l))) volume 0 1 := fun l _ =>
    Continuous.intervalIntegrable (by
      have := continuous_localAdditivePolynomial s fun n => star (f n)
      have := continuous_localAdditivePolynomial s' g
      fun_prop) _ _
  have hcongr : ∫ θ in (0 : ℝ)..1, star (localAdditivePolynomial s (fun n => star (f n)) θ) *
        localAdditivePolynomial s' g θ * ∑ l ∈ Ls, c l * e (-θ * D l) =
      ∫ θ in (0 : ℝ)..1, ∑ l ∈ Ls, c l *
        (star (localAdditivePolynomial s (fun n => star (f n)) θ) *
          localAdditivePolynomial s' g θ * e (-θ * D l)) := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hcongr, intervalIntegral.integral_finsetSum hi]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [intervalIntegral.integral_const_mul, integral_star_mul_mul_e, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hc : c l = 0
  · simp [hc]
  · rw [ite_eq_left (hD l hl hc n hn)]

/-- `|e(t)| = 1`. -/
theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  rw [e, show 2 * (Real.pi : ℂ) * t * Complex.I = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `star(n^{it}) = n^{-it}` for `n ≥ 1`. -/
private theorem star_natCast_cpow {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    star ((n : ℂ) ^ ((t : ℂ) * Complex.I)) = (n : ℂ) ^ (((-t : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log, Complex.star_def,
    ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring_nf

/-- `n^{it} = mellin(n, t)` for `n ≥ 1`. -/
private theorem natCast_cpow_eq_mellin {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ ((t : ℂ) * Complex.I) = mellin n t := by
  unfold Erdos821.Blueprint.Analytic.mellin
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log]
  ring_nf

/-- **The Mellin side as a twisted polynomial.** On `s = [⌈Y⌉, ⌊2Y⌋]`,
`|∑ star(f_n) e(un/r) n^{it}| = Y |Y⁻¹ ∑ f_n e(-un/r) n^{-it}|`. -/
theorem norm_sum_star_mul_cpow {Y : ℝ} (hY : 0 < Y) (f : ℕ → ℂ) (u : ℤ) (r : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
        star (f n) * e ((u : ℝ) / r * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ =
      Y * ‖twistedPoly Y f (-u) r (-t)‖ := by
  rw [twistedPoly, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hY.le,
    mul_inv_cancel_left₀ hY.ne', ← norm_star, star_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (Nat.ceil_pos.2 hY) (Finset.mem_Icc.1 hn).1).ne'
  rw [star_mul', star_mul', star_star, star_natCast_cpow hn0, Erdos821.P5FourierArcProof.star_e,
    e]
  congr 2
  push_cast
  ring_nf

/-- **The arc energy (PD Lemma 6.4 with the tail).** For `j ≥ 4` there is `K > 0` such that
for `10 ≤ Y`, `1 ≤ H ≤ Y/10`, `2Y ≤ T₀ H` and coefficients supported in `[Y, 2Y]`, the energy
of `∑ a_n e(θn)` on the arc `|θ - c| ≤ 1/H` is at most
`K/Y ∫_{-T₀}^{T₀} |∑ a_n e(cn) n^{it}|² + K (1 + T₀H/(2Y))^{4-j} (1/H + 2 log 4Y) ∑ |a_n|²
  + K (H/Y)² ∑ |a_n|²`,
by upstream's `LocalMellinEnergyTask_proof`, with the weighted tail split off by
`wj_integral_split` and bounded by `weighted_mean_value`. -/
theorem exists_integral_norm_localAdditivePolynomial_le (j : ℕ) (hj : 4 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Y H T₀ c : ℝ) (s : Finset ℕ) (a : ℕ → ℂ),
      10 ≤ Y → 1 ≤ H → H ≤ Y / 10 → (∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y) →
      2 * Y ≤ T₀ * H →
      ∫ θ in (c - 1 / H)..(c + 1 / H), ‖localAdditivePolynomial s a θ‖ ^ 2 ≤
        K / Y * (∫ t in (-T₀)..T₀,
          ‖∑ n ∈ s, a n * e (c * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) +
        K * ((1 + T₀ * H / (2 * Y)) ^ (j - 4))⁻¹ * (1 / H + 2 * Real.log (4 * Y)) *
          ∑ n ∈ s, ‖a n‖ ^ 2 +
        K * (H / Y) ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  obtain ⟨K₃, hK₃, hLME⟩ := Erdos821.P5Core.LocalMellinEnergyTask_proof j (by omega)
  obtain ⟨KW, hKW, hWMV⟩ := Erdos821.P5Marked.weighted_mean_value
  refine ⟨K₃ * (KW + 1), by positivity, fun Y H T₀ c s a hY hH hHY hs hT₀ => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  set a' : ℕ → ℂ := fun n => a n * e (c * n) with ha'
  set S : ℝ := ∑ n ∈ s, ‖a n‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => by positivity
  have hsq : sqNorm s a' = S := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ha', norm_mul, norm_e, mul_one]
  -- centre the arc at `0`
  have hshift : ∫ θ in (c - 1 / H)..(c + 1 / H), ‖localAdditivePolynomial s a θ‖ ^ 2 =
      ∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial s a' θ‖ ^ 2 := by
    rw [sub_eq_add_neg, ← neg_div, ← intervalIntegral.integral_comp_add_left _ c]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [localAdditivePolynomial, ha']
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, ← Erdos821.P5FourierArcProof.e_add]
    congr 2
    ring
  -- the Mellin side
  set F : ℝ → ℂ := dp s a' with hF
  have hFcont : Continuous F := Erdos821.P5Core.continuous_dp s a'
  have hFeq : ∀ t, F t = ∑ n ∈ s, a n * e (c * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro t
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by
      have := (hs n hn).1
      rintro rfl
      norm_num at this
      linarith
    rw [natCast_cpow_eq_mellin hn0]
  -- `F` as a polynomial over `[1, N]`, `N = ⌊2Y⌋`
  set N : ℕ := ⌊2 * Y⌋₊ with hN
  set g : ℕ → ℂ := fun n => if n ∈ s then a' n else 0 with hg
  have hsub : s ⊆ Finset.Icc 1 N := by
    intro n hn
    have h₁ := (hs n hn).1
    have h₂ := (hs n hn).2
    refine Finset.mem_Icc.2 ⟨?_, Nat.le_floor h₂⟩
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hdpg : ∀ t, dp (Finset.Icc 1 N) g t = F t := by
    intro t
    simp only [dp, hF, hg, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  have hsqg : sqNorm (Finset.Icc 1 N) g = S := by
    have hg2 : ∀ n, ‖g n‖ ^ 2 = if n ∈ s then ‖a' n‖ ^ 2 else 0 := fun n => by
      simp only [hg]
      split_ifs <;> simp
    rw [← hsq]
    simp only [sqNorm, hg2]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
  set h : ℝ := H / Y with hh
  have hh0 : 0 < h := div_pos hH0 hY0
  set ℓ : ℝ := T₀ * H / (2 * Y) with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ, le_div_iff₀ (by positivity)]; linarith
  have h2ℓ : 2 * ℓ / h = T₀ := by
    rw [hℓ, hh]
    field_simp
  obtain ⟨hint, hwmv⟩ := hWMV N g h 0 hh0
  simp only [add_zero, hdpg, hsqg] at hint hwmv
  have hsplit := Erdos821.P5Marked.wj_integral_split hj hh0 hℓ1
    (by rw [abs_zero]; positivity) F hFcont hint
  simp only [add_zero, h2ℓ] at hsplit
  -- `N log 2N ≤ 2Y log 4Y`
  have hNlog : (N : ℝ) * Real.log (2 * N) ≤ 2 * Y * Real.log (4 * Y) := by
    have hN2 : (N : ℝ) ≤ 2 * Y := Nat.floor_le (by positivity)
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0]
      simp only [Nat.cast_zero, zero_mul]
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h0
    exact mul_le_mul hN2 (Real.log_le_log (by positivity) (by linarith))
      (Real.log_nonneg (by linarith)) (by positivity)
  have hlog0 : 0 ≤ Real.log (4 * Y) := Real.log_nonneg (by linarith)
  have hwt : ∫ t, Erdos821.P5Marked.wt h t * ‖F t‖ ^ 2 ≤
      KW * Y * (1 / H + 2 * Real.log (4 * Y)) * S := by
    refine hwmv.trans ?_
    have : 1 / h + N * Real.log (2 * N) ≤ Y * (1 / H + 2 * Real.log (4 * Y)) := by
      rw [hh, one_div_div]
      have : Y / H = Y * (1 / H) := by ring
      nlinarith
    calc KW * (1 / h + N * Real.log (2 * N)) * S
        ≤ KW * (Y * (1 / H + 2 * Real.log (4 * Y))) * S := by gcongr
      _ = KW * Y * (1 / H + 2 * Real.log (4 * Y)) * S := by ring
  have hLME' := hLME Y H s a' hY hH hHY hs
  rw [hsq] at hLME'
  have hwj : ∫ t : ℝ, (1 + |H / Y * t|) ^ (-(j : ℤ)) * ‖dp s a' t‖ ^ 2 ≤
      (∫ t in (-T₀)..T₀, ‖F t‖ ^ 2) +
        ((1 + ℓ) ^ (j - 4))⁻¹ * (KW * Y * (1 / H + 2 * Real.log (4 * Y)) * S) := by
    refine hsplit.trans (add_le_add (le_of_eq ?_) ?_)
    · congr 1
    · exact mul_le_mul_of_nonneg_left hwt (by positivity)
  have hmain0 : 0 ≤ ∫ t in (-T₀)..T₀, ‖F t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by nlinarith) fun t _ => by positivity
  simp_rw [hFeq] at hwj hmain0
  rw [hshift]
  refine hLME'.trans ?_
  have hpos : 0 ≤ ((1 + ℓ) ^ (j - 4))⁻¹ := by positivity
  have hK₁ : K₃ ≤ K₃ * (KW + 1) := le_mul_of_one_le_right hK₃.le (by linarith)
  have hK₂ : K₃ * KW ≤ K₃ * (KW + 1) := by nlinarith
  calc K₃ / Y * (∫ t : ℝ, (1 + |H / Y * t|) ^ (-(j : ℤ)) * ‖dp s a' t‖ ^ 2) +
        K₃ * (H / Y) ^ 2 * S
      ≤ K₃ / Y * ((∫ t in (-T₀)..T₀,
          ‖∑ n ∈ s, a n * e (c * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) +
          ((1 + ℓ) ^ (j - 4))⁻¹ * (KW * Y * (1 / H + 2 * Real.log (4 * Y)) * S)) +
        K₃ * (H / Y) ^ 2 * S := by gcongr
    _ = K₃ / Y * (∫ t in (-T₀)..T₀,
          ‖∑ n ∈ s, a n * e (c * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) +
        K₃ * KW * ((1 + ℓ) ^ (j - 4))⁻¹ * (1 / H + 2 * Real.log (4 * Y)) * S +
        K₃ * (H / Y) ^ 2 * S := by
          generalize (∫ t in (-T₀)..T₀,
            ‖∑ n ∈ s, a n * e (c * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) = Mn
          field_simp
    _ ≤ K₃ * (KW + 1) / Y * (∫ t in (-T₀)..T₀,
          ‖∑ n ∈ s, a n * e (c * n) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) +
        K₃ * (KW + 1) * ((1 + ℓ) ^ (j - 4))⁻¹ * (1 / H + 2 * Real.log (4 * Y)) * S +
        K₃ * (KW + 1) * (H / Y) ^ 2 * S := by
          gcongr

end Erdos408.TwoSided.Arcs
