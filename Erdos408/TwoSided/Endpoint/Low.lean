module

public import Erdos408.TwoSided.Endpoint.DivisorModel
public import Erdos408.TwoSided.Endpoint.Low.Facts

/-!
# Low frequencies

S12 of `blueprint/two_sided_correlation.md` §6.2 (PD (6.28)–(6.29); X1, O2). For
`|t| ≤ L^{B'}`, write `f_B H_m = ∑_Q B(init Q) ∑_{w = l_Q n} H_m(n)` (U8), replace `H_m` by
its divisor model (E1, at the scales `Y/l_Q` and `Y`), and compare each progression sum with
`κ_{h,k} m⁻¹` times the full sum `∑_{w ≤ 2Y} ψ₁(w/Y) w^{iτ}`. The main terms cancel exactly
against `C_B`, which is literally `∑_Q B(init Q)/l_Q` over the same tuples (X1); no comparison
with an integral is needed. The pieces are in `Low/`.

* Lemma E2 (`exists_norm_lowFrequency_le`): the pointwise bound
  `6 M₁(0) C_N^{1/2} L^{-N/2} (T + E₀)^{d+1} + exp(-cL/(2T²⁰))`.
* `exists_integral_lowFrequency_le`: with `N ≥ A₀ + B' + 2`, the part of the mean square
  (6.24) over `|t| ≤ L^{B'}` is `O(L^{-A₀})`.
-/

@[expose] public section

namespace Erdos408.TwoSided

open Filter

/-- **Lemma E2 (low frequencies).** For the fixed data, `C_m`, `M₁`, `B'`, `C₈`, `N` and
`C_N` there is `E₀` (Mertens' constant) such that, eventually, for groups as in (6.1), all
bands, slots and `|B| ≤ 1`, every pattern `C`, test `b`, piece `ψ₁` supported in `[1, 2]`,
scale `Y`, twist `|σ| ≤ L^{C_m}` and modulus `k ≤ L^{C_m}`, and every divisor model `A` of the
marks with constants `(C₈, C_N, N)`: for `|t| ≤ L^{B'}`,
`|Y⁻¹ ∑ 𝒰(w) e(hw/k) w^{it}| ≤ 6 M₁(0) C_N^{1/2} L^{-N/2} (T + E₀)^{d+1} + exp(-cL/(2T²⁰))`.
The model error is Cauchy plus E1(c) and `∑_Q 1/l_Q ≤ (T + E₀)^{d+1}` (U6), in total
`2√2 M₁(0) C_N^{1/2} L^{-N/2} (T + E₀)^{d+1}`; the progression errors are
`≤ k · 2(M₁(1) + |τ| M₁(0))` per modulus `l_Q d` coprime to `k` (U3), against the main term
`κ_{h,k} (l_Q d)⁻¹ ∑_w ψ₁(w/Y) w^{iτ}`; with `#slotTuples ≤ x^{1-ε}` and
`∑ |A_d| ≤ e^{2L^{0.47}} L^{C₈}` they total `≤ L^{O(1)} e^{2L^{0.47}} x^{-ε} ≤ exp(-cL/(2T²⁰))`
(O2). The progression comparison is `LowFreq.norm_sum_dvd_twist_sub_le`. -/
theorem exists_norm_lowFrequency_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ)
    (d : ℕ) (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c) (Cm : ℝ)
    (M₁ : ℕ → ℝ) (B' C₈ : ℝ) (N : ℕ) (CNN : ℝ) :
    ∃ E₀ : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
        ∀ (J : ℕ) (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ),
        ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
          (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) →
          (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
        ∀ (Y σ : ℝ) (k : ℕ) (h : ℤ),
          x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y →
          Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
          |σ| ≤ Real.log x ^ Cm → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
        ∀ A : ℕ → ℂ, DivisorModel x q q₀ a P (unsharedSlots C) b C₈ CNN N A →
        ∀ t : ℝ, |t| ≤ Real.log x ^ B' →
          ‖twistedPoly Y (endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ) h k t‖ ≤
            6 * M₁ 0 * Real.sqrt CNN * Real.log x ^ (-(N : ℝ) / 2) *
                (Real.log (Real.log x) + E₀) ^ (d + 1) +
              Real.exp (-(c / 2 * Real.log x / Real.log (Real.log x) ^ 20)) := by
  obtain ⟨E, -, hE⟩ := Sieve.abs_sum_inv_primes_sub_le
  refine ⟨E, ?_⟩
  set K : ℝ := 4 * (|M₁ 1| + 2 * |M₁ 0|) with hK
  set Cexp : ℝ := C₈ + Cm + (|Cm| + |B'|) with hCexp
  filter_upwards [eventually_ge_atTop 2, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    OneSided.eventually_rpow_lt_of_mem_band (show (0 : ℝ) < alo by linarith) Cm,
    LowFreq.eventually_rpow_lt_exp_rpow Cm (show (0 : ℝ) < 0.27 by norm_num),
    OneSided.eventually_two_mul_rpow_lt (show (0 : ℝ) < 0.27 - ahi by linarith),
    LowFreq.eventually_three_rpow_le hc, LowFreq.eventually_log_le_rpow c,
    LowFreq.eventually_mul_exp_le hc K Cexp, eventually_logLog_add_pow_le E (d + 1),
    Sieve.tendsto_logLog.eventually_ge_atTop 1]
    with x hx2 hL1 hband hCm htwo h3 hLx hfin hTE hT1
  intro ι _ _ P big hadm r a u v Bc hin hsl hBc J C b ψ₁ hψ hψs hψd Y σ k h hY₁ hY₂ hσ hk₁
    hk₂ A hA t ht
  set L := Real.log x with hL
  set T := Real.log L with hT
  simp only [logLog] at hT1
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  have hxY : x ≤ Y := le_trans (le_mul_of_one_le_right hx0.le (Real.one_le_exp (by positivity)))
    hY₁
  have hY1 : 1 ≤ Y := hx1.trans hxY
  have hk0 : 0 < k := hk₁
  have hM0 : 0 ≤ M₁ 0 := (norm_nonneg _).trans (hψd 0 0)
  have hM1 : 0 ≤ M₁ 1 := (norm_nonneg _).trans (hψd 1 0)
  obtain ⟨hPd, -, -, -, -, hVP, hsmall, hbig, -⟩ := hadm
  obtain ⟨-, ha, -⟩ := hin
  obtain ⟨hAs, hAm, hAms⟩ := hA
  set ε := c / T ^ 20 with hε
  -- the primes: active and band primes lie in `(L^{C_m}, exp(L^{0.46})]`, slot primes above
  have hgroup : ∀ g, ∀ p ∈ P g, p.Prime ∧ Real.exp (L ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) := by
    intro g p hp
    have h27 : L ^ (0.27 : ℝ) ≤ L ^ (0.39 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h36 : L ^ (0.36 : ℝ) ≤ L ^ (0.46 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    by_cases hg : g ∈ big
    · obtain ⟨h₁, h₂, h₃⟩ := mem_primesIcc.1 (hbig g hg hp)
      exact ⟨h₁, (Real.exp_le_exp.2 h27).trans h₂, h₃⟩
    · obtain ⟨h₁, h₂, h₃⟩ := mem_primesIcc.1 (hsmall g hg hp)
      exact ⟨h₁, h₂, h₃.trans (Real.exp_le_exp.2 h36)⟩
  have h2746 : Real.exp (L ^ (0.27 : ℝ)) ≤ Real.exp (L ^ (0.46 : ℝ)) :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have hbandle : ∀ i, ∀ p ∈ band x (a i), (p : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) := by
    intro i p hp
    have := Real.exp_lt_exp.2 (htwo (a i) 0.27 (by linarith [(ha i).2]))
    linarith [OneSided.le_exp_of_mem_band hp]
  have h46 : L ^ (0.46 : ℝ) < ε * L := by
    have h₁ : L ^ (0.46 : ℝ) ≤ L ^ (0.47 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h₂ : 0 < L ^ (0.47 : ℝ) := by positivity
    have h₃ : ε * L = 2 * (c / 2 * L / T ^ 20) := by rw [hε]; ring
    have h₄ : 0 ≤ c / 2 * L / T ^ 20 := by positivity
    linarith
  have hslot : ∀ Q ∈ slotTuples x u v, ∀ i, (Q i).Prime ∧
      Real.exp (L ^ (0.46 : ℝ)) < Q i := by
    intro Q hQ i
    obtain ⟨⟨-, hp, hlt⟩, -⟩ := (Sieve.mem_slotTuples.1 hQ).imp_left fun h => h i
    refine ⟨hp, lt_of_lt_of_le ?_ hlt.le⟩
    calc Real.exp (L ^ (0.46 : ℝ)) < Real.exp (ε * L) := Real.exp_lt_exp.2 h46
      _ = x ^ ε := by rw [Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ x ^ u i := Real.rpow_le_rpow_of_exponent_le hx1 (hsl.1 i)
  -- U8: slot primes are not active or band primes
  have hnd : ∀ Q ∈ slotTuples x u v, ∀ p : ℕ, p.Prime →
      (p : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) → ¬ p ∣ ∏ i, Q i := by
    intro Q hQ p hp hple hdvd
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp (hslot Q hQ i).1).1 hi
    rw [this] at hple
    linarith [(hslot Q hQ i).2]
  have hH : ∀ Q ∈ slotTuples x u v, ∀ n, LowFreq.marks x q q₀ a P C b ((∏ i, Q i) * n) =
      LowFreq.marks x q q₀ a P C b n := by
    intro Q hQ n
    have hiff : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) →
        (p ∣ (∏ i, Q i) * n ↔ p ∣ n) := fun p hp hple =>
      ⟨fun h => (hp.dvd_mul.1 h).resolve_left (hnd Q hQ p hp hple),
        fun h => dvd_mul_of_dvd_right h _⟩
    unfold LowFreq.marks
    rw [markedWeight_congr _ _ _ fun i _ p hp =>
        hiff p (TypeII.band_prime hp) (hbandle i p hp),
      markedListWeight_congr _ _ _ fun g p hp =>
        hiff p (hgroup g p hp).1 (hgroup g p hp).2.2]
  -- U3: every `m d` is coprime to `k`
  set X := ⌊Real.exp (2 * L ^ (0.47 : ℝ))⌋₊ with hX
  set D := Finset.Icc 1 X with hD
  have hAD : ∀ d, A d ≠ 0 → d ∈ D := by
    intro d hd
    obtain ⟨hsq, hle, -⟩ := hAs d hd
    exact Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 hsq.ne_zero, Nat.le_floor hle⟩
  have hkp : ∀ p : ℕ, L ^ Cm < p → ¬ p ∣ k := by
    intro p hp hdvd
    have : (p : ℝ) ≤ k := by exact_mod_cast Nat.le_of_dvd hk0 hdvd
    linarith
  have hcop : ∀ m : ℕ, (∀ p : ℕ, p.Prime → p ∣ m → L ^ Cm < p) →
      ∀ d ∈ D, A d ≠ 0 → Nat.Coprime (m * d) k := by
    intro m hm d _ hd
    refine Nat.coprime_of_dvd fun p hp hpd => hkp p ?_
    rcases hp.dvd_mul.1 hpd with h' | h'
    · exact hm p hp h'
    · have hd0 : d ≠ 0 := (hAs d hd).1.ne_zero
      rcases (hAs d hd).2.2 p (Nat.mem_primeFactors.2 ⟨hp, h', hd0⟩) with hg | ⟨i, hi⟩
      · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.1 hg
        linarith [hCm, (hgroup g p hg).2.1]
      · exact hband (a i) (ha i).1 p hi
  have hcopQ : ∀ Q ∈ slotTuples x u v, ∀ p : ℕ, p.Prime → p ∣ ∏ i, Q i → L ^ Cm < p := by
    intro Q hQ p hp hdvd
    by_contra hlt
    exact hnd Q hQ p hp (by linarith [not_lt.1 hlt, hCm]) hdvd
  -- steps 2–3 for every modulus
  set τ := σ + t with hτ
  set G := LowFreq.lowWeight ψ₁ Y τ with hG
  set H := LowFreq.marks x q q₀ a P C b with hHdef
  set Nw := ⌊2 * Y⌋₊ with hNw
  set ρ : ℝ := L ^ (-(N : ℝ)) with hρ
  set Θ := LowFreq.twistMean h k * (∑ w ∈ Finset.Icc 1 Nw, G w) * (∑ d ∈ D, A d / d) with hΘ
  set TV := ∑ w ∈ Finset.Icc 1 Nw, ‖G w - G (w - 1)‖ with hTV
  set α := M₁ 0 * (Real.sqrt 2 * Real.sqrt CNN * Real.sqrt ρ) with hα
  set β := (∑ d ∈ D, ‖A d‖) * (k * TV) with hβ
  have hψ1 := fun y => LowFreq.one_lt_of_ne_zero hψ.continuous hψs (y := y)
  have hG0 : G 0 = 0 := by
    have : ψ₁ 0 = 0 := by
      by_contra h'
      linarith [(hψs 0 h').1]
    simp [hG, LowFreq.lowWeight, this]
  have hΦ : ∀ w, ‖G w * LowFreq.addTwist h k w‖ ≤ M₁ 0 := by
    intro w
    rw [norm_mul, LowFreq.norm_addTwist, mul_one]
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · rw [hG0, norm_zero]; exact hM0
    · rw [hG, LowFreq.lowWeight, norm_mul, Complex.norm_natCast_cpow_of_pos hw]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, mul_one, sub_self, Real.rpow_zero, mul_one]
      exact hψd 0 _
  have hΦs : ∀ w : ℕ, G w * LowFreq.addTwist h k w ≠ 0 → Y < w := by
    intro w hw
    have : ψ₁ (w / Y) ≠ 0 := by
      intro h0
      exact hw (by simp [hG, LowFreq.lowWeight, h0])
    have := hψ1 _ this
    rwa [lt_div_iff₀ hY0, one_mul] at this
  have hρ0 : 0 ≤ ρ := by positivity
  have hstep : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Y → (∀ n, H (m * n) = H n) →
      (∀ p : ℕ, p.Prime → p ∣ m → L ^ Cm < p) →
      ‖LowFreq.progSum ψ₁ Y τ h k H m - Θ / (m : ℂ)‖ ≤ α * Y / m + β := by
    intro m hm hmY hHm hmp
    have hR : 1 ≤ Y / m := by
      rw [le_div_iff₀ (by exact_mod_cast hm), one_mul]; exact hmY
    have := LowFreq.norm_sum_dvd_sub_le hAD (fun d hd => (Finset.mem_Icc.1 hd).1) hM0 hρ0 hk0
      hG0 hΦ hΦs hm hmY hHm (hcop m hmp) (hAms (Y / m) hR)
    refine this.trans_eq ?_
    rw [hα, hβ, hTV]
    ring
  -- step 5: the cancellation
  rw [LowFreq.twistedPoly_eq x q q₀ a u v Bc P C b (fun y hy => (hψs y hy).1) hY1 σ h k t]
  set Ts := slotTuples x u v with hTs
  set Sinv := ∑ Q ∈ Ts, 1 / ∏ i, (Q i : ℝ) with hSinv
  have hε0 : 0 ≤ ε := by positivity
  have hv1 : ∑ i, v i ≤ 1 := by
    have := hsl.2
    simp only [logLog] at this
    linarith
  have hlpos : ∀ Q ∈ Ts, 0 < ∏ i, Q i := fun Q hQ =>
    Finset.prod_pos fun i _ => (hslot Q hQ i).1.pos
  have hlY : ∀ Q ∈ Ts, ((∏ i, Q i : ℕ) : ℝ) ≤ Y := by
    intro Q hQ
    have := Sieve.prod_le_of_mem_slotTuples hx0 hQ
    push_cast
    calc ∏ i, (Q i : ℝ) ≤ x ^ ∑ i, v i := this
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hv1
      _ = x := Real.rpow_one x
      _ ≤ Y := hxY
  have hΔ : ∀ Q ∈ Ts, ‖LowFreq.progSum ψ₁ Y τ h k H (∏ i, Q i) - Θ / ((∏ i, Q i : ℕ) : ℂ)‖ ≤
      α * Y / (∏ i, Q i : ℕ) + β := fun Q hQ =>
    hstep _ (hlpos Q hQ) (hlY Q hQ) (hH Q hQ) (hcopQ Q hQ)
  have hΔ₁ : ‖LowFreq.progSum ψ₁ Y τ h k H 1 - Θ‖ ≤ α * Y + β := by
    have := hstep 1 one_pos (by simpa using hY1) (fun n => by rw [one_mul])
      fun p hp hd => absurd (Nat.le_of_dvd one_pos hd) (by have := hp.two_le; omega)
    simpa using this
  have hcomb := LowFreq.norm_combine_le hBc hlpos hΔ hΔ₁
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hY0.le]
  refine (mul_le_mul_of_nonneg_left hcomb (inv_nonneg.2 hY0.le)).trans ?_
  -- the harmonic constant and the tuple count (U4–U6)
  have hSinv0 : 0 ≤ Sinv := Finset.sum_nonneg fun Q _ => by positivity
  have hSinvT : Sinv ≤ (T + E) ^ (d + 1) := by
    refine (Sieve.sum_inv_slotTuples_le (by linarith) hv1).trans ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => by positivity)
      (Sieve.sum_inv_primes_le_logLog hE hx2 le_rfl) _
  have hcard : (Ts.card : ℝ) ≤ x ^ (1 - ε) :=
    (Sieve.card_slotTuples_le hx0 u v).trans (Real.rpow_le_rpow_of_exponent_le hx1 hsl.2)
  have hβ0 : 0 ≤ β := by positivity
  have hα0 : 0 ≤ α := by positivity
  have hsplit : Y⁻¹ * (2 * α * Y * Sinv + β * (Ts.card + Sinv)) =
      2 * α * Sinv + β * ((Ts.card + Sinv) / Y) := by
    field_simp
  rw [hsplit]
  refine add_le_add ?_ ?_
  · -- the model error, step 2
    have hsqρ : Real.sqrt ρ = L ^ (-(N : ℝ) / 2) := by
      rw [hρ, Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
      ring_nf
    have hsq2 : Real.sqrt 2 ≤ 3 := by
      rw [show (3 : ℝ) = Real.sqrt (3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [hα, hsqρ]
    have h0 : 0 ≤ M₁ 0 * Real.sqrt CNN * L ^ (-(N : ℝ) / 2) := by positivity
    calc 2 * (M₁ 0 * (Real.sqrt 2 * Real.sqrt CNN * L ^ (-(N : ℝ) / 2))) * Sinv
        = 2 * Real.sqrt 2 * (M₁ 0 * Real.sqrt CNN * L ^ (-(N : ℝ) / 2)) * Sinv := by ring
      _ ≤ 6 * (M₁ 0 * Real.sqrt CNN * L ^ (-(N : ℝ) / 2)) * (T + E) ^ (d + 1) := by
          gcongr
          linarith
      _ = _ := by ring
  · -- the progression errors, step 4
    have hX0 : (0 : ℝ) < Real.exp (2 * L ^ (0.47 : ℝ)) := Real.exp_pos _
    have hAsum : ∑ d ∈ D, ‖A d‖ ≤ Real.exp (2 * L ^ (0.47 : ℝ)) * L ^ C₈ := by
      calc ∑ d ∈ D, ‖A d‖ ≤ ∑ d ∈ D, Real.exp (2 * L ^ (0.47 : ℝ)) * (‖A d‖ / d) := by
            refine Finset.sum_le_sum fun d hd => ?_
            obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.1 hd
            have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
            have hdle : (d : ℝ) ≤ Real.exp (2 * L ^ (0.47 : ℝ)) :=
              (Nat.cast_le.2 hdX).trans (Nat.floor_le hX0.le)
            rw [mul_div_assoc', le_div_iff₀ hd0]
            exact (mul_le_mul_of_nonneg_left hdle (norm_nonneg (A d))).trans_eq (mul_comm _ _)
        _ = Real.exp (2 * L ^ (0.47 : ℝ)) * ∑ d ∈ D, ‖A d‖ / d := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hAm hX0.le
    have hderiv : ∀ y, ‖deriv ψ₁ y‖ ≤ M₁ 1 := fun y => by
      have := hψd 1 y
      rwa [iteratedDeriv_one] at this
    have hval : ∀ y, ‖ψ₁ y‖ ≤ M₁ 0 := fun y => by
      have := hψd 0 y
      rwa [iteratedDeriv_zero] at this
    have hTVle : TV ≤ 2 * (M₁ 1 + |τ| * M₁ 0) := by
      have := LowFreq.sum_norm_sub_le (hψ.differentiable (by simp)) hval hderiv
        (fun y hy => (hψs y hy).1) hY0 τ Nw
      have hNw : (Nw : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
      have hS0 : 0 ≤ (M₁ 1 + |τ| * M₁ 0) / Y := by positivity
      calc TV ≤ Nw * ((M₁ 1 + |τ| * M₁ 0) / Y) := this
        _ ≤ 2 * Y * ((M₁ 1 + |τ| * M₁ 0) / Y) := mul_le_mul_of_nonneg_right hNw hS0
        _ = 2 * (M₁ 1 + |τ| * M₁ 0) := by field_simp
    set Lp := L ^ (|Cm| + |B'|) with hLp
    have hLp1 : 1 ≤ Lp := Real.one_le_rpow hL1 (by positivity)
    have hτle : |τ| ≤ 2 * Lp := by
      have h₁ : L ^ Cm ≤ Lp := Real.rpow_le_rpow_of_exponent_le hL1 (by
        linarith [le_abs_self Cm, abs_nonneg B'])
      have h₂ : L ^ B' ≤ Lp := Real.rpow_le_rpow_of_exponent_le hL1 (by
        linarith [le_abs_self B', abs_nonneg Cm])
      calc |τ| ≤ |σ| + |t| := abs_add_le σ t
        _ ≤ 2 * Lp := by linarith only [hσ, ht, h₁, h₂]
    have hM' : M₁ 1 + |τ| * M₁ 0 ≤ (|M₁ 1| + 2 * |M₁ 0|) * Lp := by
      rw [abs_of_nonneg hM0, abs_of_nonneg hM1]
      have h₁ : M₁ 1 ≤ M₁ 1 * Lp := le_mul_of_one_le_right hM1 hLp1
      have h₂ : |τ| * M₁ 0 ≤ 2 * Lp * M₁ 0 := mul_le_mul_of_nonneg_right hτle hM0
      calc M₁ 1 + |τ| * M₁ 0 ≤ M₁ 1 * Lp + 2 * Lp * M₁ 0 := add_le_add h₁ h₂
        _ = (M₁ 1 + 2 * M₁ 0) * Lp := by ring
    have hβle : β ≤ Real.exp (2 * L ^ (0.47 : ℝ)) * L ^ C₈ *
        (L ^ Cm * (2 * ((|M₁ 1| + 2 * |M₁ 0|) * Lp))) := by
      rw [hβ]
      refine mul_le_mul hAsum (mul_le_mul hk₂ (hTVle.trans
        (mul_le_mul_of_nonneg_left hM' (by norm_num))) (by positivity) (by positivity))
        (by positivity) (by positivity)
    -- `(#Q + ∑ 1/l_Q)/Y ≤ 2 x^{1-ε}/x = 2 e^{-εL}`
    have hrest : (Ts.card + Sinv) / Y ≤ 2 * Real.exp (-(ε * L)) := by
      have h₁ : (Ts.card : ℝ) + Sinv ≤ 2 * x ^ (1 - ε) := by
        rw [two_mul]
        exact add_le_add hcard ((hSinvT.trans hTE.2).trans hLx)
      have h₂ : x ^ (1 - ε) / x = Real.exp (-(ε * L)) := by
        rw [Real.rpow_def_of_pos hx0, div_eq_iff hx0.ne']
        conv_rhs => rw [← Real.exp_log hx0]
        rw [← Real.exp_add, hL]
        ring_nf
      calc (Ts.card + Sinv) / Y ≤ 2 * x ^ (1 - ε) / x :=
            div_le_div₀ (by positivity) h₁ hx0 hxY
        _ = 2 * Real.exp (-(ε * L)) := by rw [mul_div_assoc, h₂]
    have hεL : ε * L = 2 * (c / 2 * L / T ^ 20) := by rw [hε]; ring
    have hfin' : K * L ^ Cexp * Real.exp (2 * L ^ (0.47 : ℝ)) ≤
        Real.exp (c / 2 * L / T ^ 20) := hfin
    have hKL : Real.exp (2 * L ^ (0.47 : ℝ)) * L ^ C₈ *
        (L ^ Cm * (2 * ((|M₁ 1| + 2 * |M₁ 0|) * Lp))) * (2 * Real.exp (-(ε * L))) =
        K * L ^ Cexp * Real.exp (2 * L ^ (0.47 : ℝ)) * Real.exp (-(ε * L)) := by
      rw [hK, hCexp, Real.rpow_add hL0, Real.rpow_add hL0]
      ring
    calc β * ((Ts.card + Sinv) / Y)
        ≤ Real.exp (2 * L ^ (0.47 : ℝ)) * L ^ C₈ *
            (L ^ Cm * (2 * ((|M₁ 1| + 2 * |M₁ 0|) * Lp))) * (2 * Real.exp (-(ε * L))) :=
          mul_le_mul hβle hrest (div_nonneg (add_nonneg (Nat.cast_nonneg _) hSinv0) hY0.le)
            (hβ0.trans hβle)
      _ = K * L ^ Cexp * Real.exp (2 * L ^ (0.47 : ℝ)) * Real.exp (-(ε * L)) := hKL
      _ ≤ Real.exp (c / 2 * L / T ^ 20) * Real.exp (-(ε * L)) :=
          mul_le_mul_of_nonneg_right hfin' (Real.exp_pos (-(ε * L))).le
      _ = Real.exp (-(c / 2 * L / T ^ 20)) := by
          rw [← Real.exp_add, hεL]
          ring_nf

/-- **The low part of (6.24).** For every `B'` there is `C_L` such that, eventually, the part
of the endpoint mean square over `|t| ≤ L^{B'}` is at most `C_L L^{-A₀}`: E2 with the model
of E1 at precision `N = ⌈A₀ + B' + 2⌉`, using `(T + E₀)^{d+1} ≤ L` and
`exp(-cL/(2T²⁰)) ≤ L^{-(A₀ + B')/2}`. -/
theorem exists_integral_lowFrequency_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ)
    (CN c : ℝ) (d : ℕ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c)
    (m₀ : ℕ) (Cm A₀ : ℝ) (M₁ : ℕ → ℝ) (B' : ℝ) :
    ∃ CL : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
        ∀ (J : ℕ) (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ),
          (∀ g, (C g).card ≤ m₀) → (∀ p, ‖b p‖ ≤ 1) →
        ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
          (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) →
          (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
        ∀ (Y σ : ℝ) (k : ℕ) (h : ℤ),
          x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y →
          Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
          |σ| ≤ Real.log x ^ Cm → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
          ∫ t in -(Real.log x ^ B')..(Real.log x ^ B'),
              ‖twistedPoly Y (endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ) h k t‖ ^ 2 ≤
            CL * Real.log x ^ (-A₀) := by
  obtain ⟨C₈, hE1⟩ := exists_divisorModel q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN hq hq₁ hq₀ hq₀₁ hvlo
    halo hahi m₀
  set N : ℕ := ⌈A₀ + B' + 2⌉₊ with hN
  obtain ⟨CNN, hE1x⟩ := hE1 N
  obtain ⟨E₀, hE2⟩ := exists_norm_lowFrequency_le q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c d halo hal
    hahi hc Cm M₁ B' C₈ N CNN
  set K : ℝ := 6 * |M₁ 0| * Real.sqrt CNN + 1 with hK
  refine ⟨2 * K ^ 2, ?_⟩
  filter_upwards [hE1x, hE2, eventually_logLog_add_pow_le E₀ (d + 1),
    eventually_exp_neg_margin_le (half_pos hc) ((A₀ + B') / 2),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hE1x hE2 hT hmar hL
  intro ι _ _ P big hadm r a u v Bc hin hsl hBc J C b hC hb ψ₁ hψ hψs hψd Y σ k h hY₁ hY₂ hσ
    hk₁ hk₂
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  obtain ⟨Amod, hmod⟩ := hE1x P big hadm r a hin (J + 1) (unsharedSlots C) b
    (fun g => by rw [card_unsharedSlots]; exact Nat.add_le_add_right (hC g) 1) hb
  set D : ℝ := (A₀ + B') / 2 with hD
  -- the pointwise bound `K L^{-D}`
  have hND : -(N : ℝ) / 2 + 1 ≤ -D := by
    have := Nat.le_ceil (A₀ + B' + 2)
    rw [← hN] at this
    rw [hD]
    linarith
  have hpt : ∀ t : ℝ, |t| ≤ L ^ B' →
      ‖twistedPoly Y (endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ) h k t‖ ≤ K * L ^ (-D) := by
    intro t ht
    refine (hE2 P big hadm r a u v Bc hin hsl hBc J C b ψ₁ hψ hψs hψd Y σ k h hY₁ hY₂ hσ hk₁
      hk₂ Amod hmod t ht).trans ?_
    have hmar' : Real.exp (-(c / 2 * L / Real.log L ^ 20)) ≤ L ^ (-D) := hmar
    have hM : 6 * M₁ 0 * Real.sqrt CNN ≤ 6 * |M₁ 0| * Real.sqrt CNN := by
      gcongr
      exact le_abs_self _
    have hpow : L ^ (-(N : ℝ) / 2) * (Real.log L + E₀) ^ (d + 1) ≤ L ^ (-D) := by
      calc L ^ (-(N : ℝ) / 2) * (Real.log L + E₀) ^ (d + 1) ≤ L ^ (-(N : ℝ) / 2) * L :=
            mul_le_mul_of_nonneg_left hT.2 (by positivity)
        _ = L ^ (-(N : ℝ) / 2 + 1) := by rw [Real.rpow_add hL0, Real.rpow_one]
        _ ≤ L ^ (-D) := Real.rpow_le_rpow_of_exponent_le hL hND
    have hT0 : 0 ≤ (Real.log L + E₀) ^ (d + 1) := pow_nonneg hT.1 _
    calc 6 * M₁ 0 * Real.sqrt CNN * L ^ (-(N : ℝ) / 2) * (Real.log L + E₀) ^ (d + 1) +
          Real.exp (-(c / 2 * L / Real.log L ^ 20))
        ≤ 6 * |M₁ 0| * Real.sqrt CNN * (L ^ (-(N : ℝ) / 2) * (Real.log L + E₀) ^ (d + 1)) +
            L ^ (-D) := by
          rw [← mul_assoc]
          gcongr
      _ ≤ 6 * |M₁ 0| * Real.sqrt CNN * L ^ (-D) + L ^ (-D) := by gcongr
      _ = K * L ^ (-D) := by rw [hK]; ring
  have hK0 : 0 ≤ K := by positivity
  have hLB : 0 ≤ L ^ B' := by positivity
  calc ∫ t in -(L ^ B')..(L ^ B'),
        ‖twistedPoly Y (endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ) h k t‖ ^ 2
      ≤ ‖∫ t in -(L ^ B')..(L ^ B'),
          ‖twistedPoly Y (endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ) h k t‖ ^ 2‖ :=
        Real.le_norm_self _
    _ ≤ (K * L ^ (-D)) ^ 2 * |L ^ B' - -(L ^ B')| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
        rw [Real.norm_of_nonneg (by positivity)]
        have ht' : |t| ≤ L ^ B' := by
          rw [Set.uIoc_of_le (by linarith)] at ht
          exact abs_le.2 ⟨ht.1.le, ht.2⟩
        exact pow_le_pow_left₀ (norm_nonneg _) (hpt t ht') 2
    _ = 2 * K ^ 2 * ((L ^ (-D)) ^ 2 * L ^ B') := by
        rw [abs_of_nonneg (by linarith)]
        ring
    _ = 2 * K ^ 2 * L ^ (-A₀) := by
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul hL0.le, ← Real.rpow_add hL0, hD]
        congr 1
        ring

end Erdos408.TwoSided
