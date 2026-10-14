import Erdos408.OneSided.Major.Arcs
import Erdos408.OneSided.Major.Regions

/-!
# One arc term

`blueprint/one_sided_type_ii.md` §6.4, "One arc term". Fix the arc `h/k` and `θ = λ/Y`.
After the separation (`Major/Arcs.lean`) the arc term is `∫ K(q) G(q₁) \bar G(-q₂) dq` with
`|G(τ)| ≤ XY g(τ)`, `g = ∑_χ |Q_χ|` and `Q_χ = B_λ^{χ₁} M^{χ₂} N^{χ₃}`. The kernel bound
`|K(τ, σ)| ≤ C₀ Λ⁴ X⁻¹ (1 + |τ|/X)^{-2} (1 + |τ + σ|)^{-2}` and the three regions of
`Major/Regions.lean` bound it by the energy and the mean values of the `Q_χ`.

* `|B_λ| ≤ 4`: a label tuple `p` contributes at most `4Y/∏p_i`, since `η(a/Y) = 0` for
  `a ≥ 4Y`, and `∑_p 1/∏p_i = ∏ V_i`.
* `maj:product-mean`: `M N` is a Dirichlet polynomial of length `N ≤ 4X` whose coefficients
  are at most `L^{2C} τ(l)`, so PD Lemma 2.2 and `∑ τ(l)² ≤ N (1 + log N)³` give
  `∫_I |M N|² ≤ 2048 L^{C₄} (1 + |I|/X)` with `C₄ = 4C + 4`.
* `norm_arcTerm_le`: by Cauchy's inequality over the characters, `g²` has energy and mean
  values `|χ|²` times those of one `Q_χ`.
-/

noncomputable section

namespace Erdos408.OneSided

open MeasureTheory Finset Real

variable {K : ℕ}

/-! ### Sizes of the polynomials -/

/-- `|n^{iτ}| ≤ 1`. -/
private theorem norm_natCast_cpow_mul_I_le (n : ℕ) (τ : ℝ) :
    ‖(n : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · by_cases hτ : (τ : ℂ) * Complex.I = 0
    · simp [hτ]
    · simp [Complex.zero_cpow hτ]
  · rw [Complex.norm_natCast_cpow_of_pos hn]
    simp

/-- `η(a/Y) ≤ 4Y/a`, since `η(a/Y) = 0` unless `a < 4Y`. -/
private theorem dyadicBump_div_le {a Y : ℝ} (ha : 0 ≤ a) (hY : 0 < Y) :
    dyadicBump (a / Y) ≤ 4 * Y / a := by
  by_cases h : dyadicBump (a / Y) = 0
  · rw [h]
    positivity
  obtain ⟨h₁, h₂⟩ := lt_of_dyadicBump_ne_zero h
  have ha' : 0 < a := lt_of_le_of_ne ha fun h0 => by rw [← h0, zero_div] at h₁; linarith
  rw [div_lt_iff₀ hY] at h₂
  calc dyadicBump (a / Y) ≤ 1 := dyadicBump_le_one _
    _ ≤ 4 * Y / a := by rw [le_div_iff₀ ha']; linarith

/-- `∑_p 1/∏ p_i = ∏ V_i` over the label tuples. -/
private theorem sum_labels_inv (x : ℝ) (d : Data K) :
    ∑ p ∈ d.labels x, ((∏ i, p i : ℕ) : ℝ)⁻¹ = d.bandMass x := by
  unfold Data.bandMass Data.labels harmonicMass
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
  simp only [one_div]

/-- `|B_λ(τ)| ≤ 4`. -/
private theorem norm_labelPoly_le (x : ℝ) (d : Data K) {Y : ℝ} (hY : 0 < Y) (lam : ℝ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (τ : ℝ) : ‖labelPoly x d Y lam χ τ‖ ≤ 4 := by
  have hV : 0 ≤ d.bandMass x :=
    Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun p _ => by positivity
  unfold labelPoly
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hY.le]
  calc Y⁻¹ * ‖∑ p ∈ d.labels x, ((dyadicBump ((∏ i, p i : ℕ) / Y) * (d.bandMass x)⁻¹ : ℝ) : ℂ) *
          Complex.exp (-(2 * π * Complex.I * ((lam * (∏ i, p i : ℕ) / Y : ℝ) : ℂ))) *
          χ (∏ i, p i : ℕ) * ((∏ i, p i : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)‖
      ≤ Y⁻¹ * ∑ p ∈ d.labels x, 4 * Y * (d.bandMass x)⁻¹ * ((∏ i, p i : ℕ) : ℝ)⁻¹ := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        have hη := dyadicBump_div_le (Nat.cast_nonneg (∏ i, p i)) hY
        have hexp : ‖Complex.exp (-(2 * π * Complex.I *
            ((lam * (∏ i, p i : ℕ) / Y : ℝ) : ℂ)))‖ = 1 := by
          rw [show -(2 * π * Complex.I * ((lam * (∏ i, p i : ℕ) / Y : ℝ) : ℂ)) =
            ((-(2 * π * (lam * (∏ i, p i : ℕ) / Y)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I]
        rw [norm_mul, norm_mul, norm_mul, hexp, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (dyadicBump_nonneg _) (inv_nonneg.2 hV))]
        calc dyadicBump ((∏ i, p i : ℕ) / Y) * (d.bandMass x)⁻¹ * 1 * ‖χ (∏ i, p i : ℕ)‖ *
              ‖((∏ i, p i : ℕ) : ℂ) ^ ((τ : ℂ) * Complex.I)‖
            ≤ 4 * Y / (∏ i, p i : ℕ) * (d.bandMass x)⁻¹ * 1 * 1 * 1 := by
              gcongr
              · exact χ.norm_le_one _
              · exact norm_natCast_cpow_mul_I_le _ _
          _ = 4 * Y * (d.bandMass x)⁻¹ * ((∏ i, p i : ℕ) : ℝ)⁻¹ := by ring
    _ = 4 * ((d.bandMass x)⁻¹ * d.bandMass x) := by
        rw [← Finset.mul_sum, sum_labels_inv]
        field_simp
    _ ≤ 4 := by
        rcases hV.eq_or_lt with h | h
        · rw [← h, inv_zero, zero_mul]
          norm_num
        · rw [inv_mul_cancel₀ h.ne', mul_one]

/-- `B_λ` is continuous: the label products are nonzero. -/
private theorem continuous_labelPoly (x : ℝ) (d : Data K) (Y lam : ℝ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) : Continuous (labelPoly x d Y lam χ) := by
  unfold labelPoly
  refine continuous_const.mul (continuous_finsetSum _ fun p hp =>
    continuous_const.mul (continuous_natCast_cpow_mul_I ?_))
  rw [Finset.prod_ne_zero_iff]
  exact fun i _ => (TypeII.band_prime (Fintype.mem_piFinset.1 hp i)).ne_zero

/-- `|M_α(τ)| ≤ H_m⁻¹ ∑_m |α_m|`. -/
private theorem norm_markedPoly_le {d : Data K} (hHm : 0 < d.Hm) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (τ : ℝ) :
    ‖markedPoly d χ τ‖ ≤ d.Hm⁻¹ * ∑ m ∈ d.mRange, ‖d.α m‖ := by
  unfold markedPoly
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hHm.le]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [norm_mul, norm_mul]
  calc ‖d.α m‖ * ‖χ m‖ * ‖(m : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤ ‖d.α m‖ * 1 * 1 := by
        gcongr
        · exact χ.norm_le_one _
        · exact norm_natCast_cpow_mul_I_le _ _
    _ = ‖d.α m‖ := by ring

/-- `|N_β(τ)| ≤ H_n⁻¹ ∑_n |β_n|`. -/
private theorem norm_unmarkedPoly_le {d : Data K} (hHn : 0 < d.Hn) {k : ℕ}
    (ψ : DirichletCharacter ℂ k) (τ : ℝ) :
    ‖unmarkedPoly d ψ τ‖ ≤ d.Hn⁻¹ * ∑ n ∈ d.nRange, ‖d.β n‖ := by
  unfold unmarkedPoly
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hHn.le]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_mul]
  calc ‖d.β n‖ * ‖ψ n‖ * ‖(n : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤ ‖d.β n‖ * 1 * 1 := by
        gcongr
        · exact ψ.norm_le_one _
        · exact norm_natCast_cpow_mul_I_le _ _
    _ = ‖d.β n‖ := by ring

/-- `maj:product-mean` on any interval `[a, b]`:
`∫_a^b |B_λ M_α N_β|² ≤ 165888 L^{C₄} (1 + (b - a)/X)`, once `log 4X ≤ 2L`. With `|B_λ| ≤ 4`
it suffices to bound `M_α N_β`, whose coefficients are `X⁻¹ ∑_{mn = l} α_m χ(m) β_n ψ(n)`, of
length `N ≤ 4X`: `maj:product-mean` (`integral_norm_sum_mul_sum_sq_le`) gives
`X⁻² (b - a + 96 X L) L^{4C} (108 X L³)`. -/
theorem integral_norm_labelPoly_mul_sq_le {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hx : 1 ≤ x) (hL : 1 ≤ Real.log x)
    (hlog : Real.log (4 * d.X) ≤ 2 * Real.log x) {Y : ℝ} (hY : 0 < Y) (lam : ℝ) {k : ℕ}
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ k) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ in a..b, ‖labelPoly x d Y lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 ≤
      165888 * Real.log x ^ meanExp C * (1 + (b - a) / d.X) := by
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hγ : 0 ≤ d.γ := (Real.rpow_nonneg hL0.le _).trans hd.γ_ge
  have hHm : 1 ≤ d.Hm := (Real.one_le_rpow hx hγ).trans hd.Hm_ge
  have hHn : 1 ≤ d.Hn := (Real.one_le_rpow hx hγ).trans hd.Hn_ge
  have hX : 0 < d.X := mul_pos (by linarith) (by linarith)
  -- `|B_λ M_α N_β|² ≤ 16 |M_α N_β|²`
  have hc₁ : Continuous fun τ => markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ :=
    (continuous_markedPoly (by linarith) χ₂).mul (continuous_unmarkedPoly (by linarith) χ₃)
  have hc₂ : Continuous fun τ =>
      labelPoly x d Y lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ :=
    ((continuous_labelPoly x d Y lam χ₁).mul (continuous_markedPoly (by linarith) χ₂)).mul
      (continuous_unmarkedPoly (by linarith) χ₃)
  have h16 : ∫ τ in a..b, ‖labelPoly x d Y lam χ₁ τ * markedPoly d χ₂ τ *
      unmarkedPoly d χ₃ τ‖ ^ 2 ≤
        16 * ∫ τ in a..b, ‖markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hab ((hc₂.norm.pow 2).intervalIntegrable _ _)
      (((hc₁.norm.pow 2).const_mul _).intervalIntegrable _ _) fun τ _ => ?_
    rw [mul_assoc, norm_mul, mul_pow, show (16 : ℝ) = 4 ^ 2 by norm_num]
    gcongr
    exact norm_labelPoly_le x d hY lam χ₁ τ
  -- the coefficients are at most `L^C`
  have hLC : 0 ≤ L ^ C := Real.rpow_nonneg hL0.le _
  have hu : ∀ m ∈ d.mRange, ‖d.α m * χ₂ m‖ ≤ L ^ C := by
    intro m _
    rw [norm_mul]
    by_cases h : d.α m = 0
    · rw [h, norm_zero, zero_mul]
      exact hLC
    · calc ‖d.α m‖ * ‖χ₂ m‖ ≤ L ^ C * 1 :=
            mul_le_mul (hd.α_supp m h).2.2.2 (χ₂.norm_le_one _) (norm_nonneg _) hLC
        _ = L ^ C := mul_one _
  have hv : ∀ n ∈ d.nRange, ‖d.β n * χ₃ n‖ ≤ L ^ C := by
    intro n _
    rw [norm_mul]
    by_cases h : d.β n = 0
    · rw [h, norm_zero, zero_mul]
      exact hLC
    · calc ‖d.β n‖ * ‖χ₃ n‖ ≤ L ^ C * 1 :=
            mul_le_mul (hd.β_supp n h).2.2.2 (χ₃.norm_le_one _) (norm_nonneg _) hLC
        _ = L ^ C := mul_one _
  -- the ranges lie in `[1, ⌊2H_m⌋]` and `[1, ⌊2H_n⌋]`
  set N₁ := ⌊2 * d.Hm⌋₊
  set N₂ := ⌊2 * d.Hn⌋₊
  have hI₁ : ∀ m ∈ d.mRange, 1 ≤ m ∧ m ≤ N₁ := fun m hm => by
    rw [Data.mRange, Finset.mem_Icc] at hm
    exact ⟨(Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne').trans hm.1, hm.2⟩
  have hI₂ : ∀ n ∈ d.nRange, 1 ≤ n ∧ n ≤ N₂ := fun n hn => by
    rw [Data.nRange, Finset.mem_Icc] at hn
    exact ⟨(Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne').trans hn.1, hn.2⟩
  have hmean := integral_norm_sum_mul_sum_sq_le hI₁ hI₂ hLC hLC hu hv hab
  -- `M_α N_β = X⁻¹ (∑_m α_m χ(m) m^{iτ}) (∑_n β_n ψ(n) n^{iτ})`
  have hprod : ∀ τ : ℝ, ‖markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 = d.X⁻¹ ^ 2 *
      ‖(∑ m ∈ d.mRange, d.α m * χ₂ m * (m : ℂ) ^ ((τ : ℂ) * Complex.I)) *
        (∑ n ∈ d.nRange, d.β n * χ₃ n * (n : ℂ) ^ ((τ : ℂ) * Complex.I))‖ ^ 2 := by
    intro τ
    unfold markedPoly unmarkedPoly Data.X
    rw [mul_mul_mul_comm, norm_mul, mul_pow, ← mul_inv, ← Complex.ofReal_mul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  simp_rw [hprod] at h16
  rw [intervalIntegral.integral_const_mul] at h16
  -- the length `N = N₁ N₂` has `1 ≤ N ≤ 4X` and `1 + log N ≤ 3L`
  have hN₁ : (N₁ : ℝ) ≤ 2 * d.Hm := Nat.floor_le (by linarith)
  have hN₂ : (N₂ : ℝ) ≤ 2 * d.Hn := Nat.floor_le (by linarith)
  have hN₁' : 1 ≤ N₁ := Nat.le_floor (by push_cast; linarith)
  have hN₂' : 1 ≤ N₂ := Nat.le_floor (by push_cast; linarith)
  have hN : ((N₁ * N₂ : ℕ) : ℝ) ≤ 4 * d.X := by
    push_cast
    unfold Data.X
    calc (N₁ : ℝ) * N₂ ≤ (2 * d.Hm) * (2 * d.Hn) :=
          mul_le_mul hN₁ hN₂ (Nat.cast_nonneg _) (by linarith)
      _ = 4 * (d.Hm * d.Hn) := by ring
  have hN1 : (1 : ℝ) ≤ ((N₁ * N₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hlogN0 : 0 ≤ Real.log ((N₁ * N₂ : ℕ) : ℝ) := Real.log_nonneg hN1
  have hlogN : 1 + Real.log ((N₁ * N₂ : ℕ) : ℝ) ≤ 3 * L := by
    have := Real.log_le_log (by linarith) hN
    linarith
  have h₁ : b - a + 8 * ((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ≤
      b - a + 96 * d.X * L := by
    have h : 8 * ((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ≤
        8 * (4 * d.X) * (3 * L) := by gcongr
    linarith
  have h₂ : (L ^ C) ^ 2 * (L ^ C) ^ 2 *
      (((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ^ 3) ≤
      L ^ (4 * C) * (108 * d.X * L ^ 3) := by
    have e : (L ^ C) ^ 2 * (L ^ C) ^ 2 = L ^ (4 * C) := by
      rw [← pow_add, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      norm_num
      ring_nf
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((N₁ * N₂ : ℕ) : ℝ) * (1 + Real.log ((N₁ * N₂ : ℕ) : ℝ)) ^ 3
        ≤ (4 * d.X) * (3 * L) ^ 3 := by gcongr
      _ = 108 * d.X * L ^ 3 := by ring
  -- collect the powers of `L`
  set y := (b - a) / d.X with hy
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hX.le
  set P := L ^ (4 * C) * L ^ 3 with hP
  have hP0 : 0 ≤ P := by positivity
  have hPL : P * L = L ^ meanExp C := by
    rw [hP, meanExp, mul_assoc, ← pow_succ, ← Real.rpow_natCast, ← Real.rpow_add hL0]
    norm_num
  have hkey : P * (y + 96 * L) ≤ 96 * (P * L) * (1 + y) := by
    have h := mul_nonneg (mul_nonneg hP0 hy0) (show 0 ≤ 96 * L - 1 by linarith)
    have e : 96 * (P * L) * (1 + y) - P * (y + 96 * L) = P * y * (96 * L - 1) := by ring
    linarith
  calc ∫ τ in a..b, ‖labelPoly x d Y lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2
      ≤ 16 * (d.X⁻¹ ^ 2 * ((b - a + 96 * d.X * L) * (L ^ (4 * C) * (108 * d.X * L ^ 3)))) := by
        refine h16.trans ?_
        gcongr
        refine hmean.trans ?_
        have h96 : 0 < 96 * d.X * L := by positivity
        exact mul_le_mul h₁ h₂ (by positivity) (by linarith)
    _ = 1728 * (P * (y + 96 * L)) := by
        rw [hy, hP]
        field_simp
        ring
    _ ≤ 1728 * (96 * (P * L) * (1 + y)) := by gcongr
    _ = 165888 * L ^ meanExp C * (1 + y) := by rw [← hPL]; ring

/-- `∫_a^b (∑_i f_i)² ≤ |s| ∑_i ∫_a^b f_i²`, by Cauchy's inequality at each point. -/
private theorem intervalIntegral_sq_sum_le {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i, Continuous (f i)) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ in a..b, (∑ i ∈ s, f i τ) ^ 2 ≤ #s * ∑ i ∈ s, ∫ τ in a..b, f i τ ^ 2 := by
  have h₁ : Continuous fun τ => (∑ i ∈ s, f i τ) ^ 2 :=
    (continuous_finsetSum _ fun i _ => hf i).pow 2
  have h₂ : Continuous fun τ => (#s : ℝ) * ∑ i ∈ s, f i τ ^ 2 :=
    (continuous_finsetSum _ fun i _ => (hf i).pow 2).const_mul _
  calc ∫ τ in a..b, (∑ i ∈ s, f i τ) ^ 2 ≤ ∫ τ in a..b, (#s : ℝ) * ∑ i ∈ s, f i τ ^ 2 :=
        intervalIntegral.integral_mono_on hab (h₁.intervalIntegrable _ _)
          (h₂.intervalIntegrable _ _) fun τ _ => sq_sum_le_card_mul_sum_sq (s := s)
            (f := fun i => f i τ)
    _ = #s * ∑ i ∈ s, ∫ τ in a..b, f i τ ^ 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum (f := fun i τ => f i τ ^ 2) fun i _ =>
            ((hf i).pow 2).intervalIntegrable _ _]

/-! ### One arc term -/

/-- One arc term at `θ = λ/Y`. Let `K` separate `ψ_λ(X(w - w'))` with
`|K(τ, σ)| ≤ c (1 + |τ|/X)^{-2} (1 + |τ + σ|)^{-2}`, and let every `Q_χ = B_λ^{χ₁} M^{χ₂} N^{χ₃}`
have energy at most `E` on `[-T, T]` and mean values `M (1 + |I|/X)`. With `n` the number of
character triples, the arc term is at most
`c (XY)² π ((ε n² E + ε⁻¹ n² M (1 + 2T/X))/2 + 8 n² M X / T)`. -/
theorem norm_arcTerm_le {x Y : ℝ} {d : Data K} (hY : 0 < Y) (hHm : 0 < d.Hm) (hHn : 0 < d.Hn)
    (k h : ℕ) [NeZero k] (lam : ℝ) {Kf : ℝ × ℝ → ℂ} {c T M E ε : ℝ} (hKi : Integrable Kf)
    (hKb : ∀ τ σ : ℝ, ‖Kf (τ, σ)‖ ≤ c * ((1 + |τ| / d.X) ^ 2)⁻¹ * ((1 + |τ + σ|) ^ 2)⁻¹)
    (hK : ∀ w w' : ℝ, 1 ≤ w → w ≤ 16 → 1 ≤ w' → w' ≤ 16 →
      plateauTwist lam (d.X * (w - w')) =
        ∫ q : ℝ × ℝ, Kf q * (w : ℂ) ^ ((q.1 : ℂ) * Complex.I) *
          (w' : ℂ) ^ ((q.2 : ℂ) * Complex.I))
    (hsupp : ∀ u ∈ sideSet x d, sideCoeff x d Y u ≠ 0 →
      1 ≤ (sideProd u : ℝ) / (d.X * Y) ∧ (sideProd u : ℝ) / (d.X * Y) ≤ 16)
    (hpos : ∀ u ∈ sideSet x d, 0 < sideProd u)
    (hunit : ∀ u ∈ sideSet x d, sideCoeff x d Y u ≠ 0 →
      IsUnit (sideLabel u : ZMod k) ∧ IsUnit (u.2.1 : ZMod k) ∧ IsUnit (u.2.2 : ZMod k))
    (hXT : d.X ≤ T) (hε : 0 < ε)
    (hE : ∀ χ₁ χ₂ χ₃ : DirichletCharacter ℂ k, ∫ τ in (-T)..T,
      ‖labelPoly x d Y lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 ≤ E)
    (hM : ∀ χ₁ χ₂ χ₃ : DirichletCharacter ℂ k, ∀ a b : ℝ, a ≤ b → ∫ τ in a..b,
      ‖labelPoly x d Y lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 ≤
        M * (1 + (b - a) / d.X)) :
    ‖arcTerm x d Y k h (lam / Y)‖ ≤ c * (d.X * Y) ^ 2 *
      (π * ((ε * (((Fintype.card (DirichletCharacter ℂ k) : ℝ) ^ 3) ^ 2 * E) +
          ε⁻¹ * (((Fintype.card (DirichletCharacter ℂ k) : ℝ) ^ 3) ^ 2 * M *
            (1 + 2 * T / d.X))) / 2 +
        8 * (((Fintype.card (DirichletCharacter ℂ k) : ℝ) ^ 3) ^ 2 * M) * d.X / T)) := by
  have hX : 0 < d.X := mul_pos hHm hHn
  set n : ℝ := (Fintype.card (DirichletCharacter ℂ k) : ℝ) ^ 3 with hn
  -- `g = ∑_χ |Q_χ|` bounds the separated polynomial
  set Q : DirichletCharacter ℂ k × DirichletCharacter ℂ k × DirichletCharacter ℂ k → ℝ → ℂ :=
    fun χ τ => labelPoly x d Y lam χ.1 τ * markedPoly d χ.2.1 τ * unmarkedPoly d χ.2.2 τ
    with hQ
  set g : ℝ → ℝ := fun τ => ∑ χ, ‖Q χ τ‖ with hg
  have hQc : ∀ χ, Continuous (Q χ) := fun χ =>
    ((continuous_labelPoly x d Y lam χ.1).mul (continuous_markedPoly hHm χ.2.1)).mul
      (continuous_unmarkedPoly hHn χ.2.2)
  have hgc : Continuous g := continuous_finsetSum _ fun χ _ => (hQc χ).norm
  have hg0 : ∀ τ, 0 ≤ g τ := fun τ => Finset.sum_nonneg fun χ _ => norm_nonneg _
  have hgB : ∀ τ, g τ ≤ ∑ _χ : DirichletCharacter ℂ k × DirichletCharacter ℂ k ×
      DirichletCharacter ℂ k, 4 * (d.Hm⁻¹ * ∑ m ∈ d.mRange, ‖d.α m‖) *
        (d.Hn⁻¹ * ∑ n ∈ d.nRange, ‖d.β n‖) := fun τ =>
    Finset.sum_le_sum fun χ _ => by
      rw [hQ, norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (norm_labelPoly_le x d hY lam χ.1 τ)
        (norm_markedPoly_le hHm χ.2.1 τ) (norm_nonneg _) (by norm_num))
        (norm_unmarkedPoly_le hHn χ.2.2 τ) (norm_nonneg _) (by positivity)
  have hcard : (#(Finset.univ : Finset (DirichletCharacter ℂ k × DirichletCharacter ℂ k ×
      DirichletCharacter ℂ k)) : ℝ) = n := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, hn]
    push_cast
    ring
  have hn0 : 0 ≤ n := by positivity
  -- the energy and the mean values of `g²`
  have hEg : ∫ τ in (-T)..T, g τ ^ 2 ≤ n ^ 2 * E := by
    refine (intervalIntegral_sq_sum_le _ (fun χ => (hQc χ).norm) (by linarith)).trans ?_
    rw [hcard]
    calc n * ∑ χ : DirichletCharacter ℂ k × DirichletCharacter ℂ k × DirichletCharacter ℂ k,
          ∫ τ in (-T)..T, ‖Q χ τ‖ ^ 2
        ≤ n * ∑ _χ : DirichletCharacter ℂ k × DirichletCharacter ℂ k ×
            DirichletCharacter ℂ k, E := by
          gcongr with χ
          exact hE χ.1 χ.2.1 χ.2.2
      _ = n ^ 2 * E := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  have hMg : ∀ a b, a ≤ b → ∫ τ in a..b, g τ ^ 2 ≤ n ^ 2 * M * (1 + (b - a) / d.X) := by
    intro a b hab
    refine (intervalIntegral_sq_sum_le _ (fun χ => (hQc χ).norm) hab).trans ?_
    rw [hcard]
    calc n * ∑ χ : DirichletCharacter ℂ k × DirichletCharacter ℂ k × DirichletCharacter ℂ k,
          ∫ τ in a..b, ‖Q χ τ‖ ^ 2
        ≤ n * ∑ _χ : DirichletCharacter ℂ k × DirichletCharacter ℂ k ×
            DirichletCharacter ℂ k, M * (1 + (b - a) / d.X) := by
          gcongr with χ
          exact hM χ.1 χ.2.1 χ.2.2 a b hab
      _ = n ^ 2 * M * (1 + (b - a) / d.X) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
  obtain ⟨hInt, hBound⟩ := integral_kernel_mul_le hgc hg0 hgB hX hXT hε hEg hMg
  have hc0 : 0 ≤ c := by
    have h0 := (norm_nonneg _).trans (hKb 0 0)
    simpa using h0
  have hG : ∀ τ, ‖sidePoly x d Y lam k h τ‖ ≤ d.X * Y * g τ :=
    norm_sidePoly_le hY hHm hHn k h lam hunit hpos
  rw [arcTerm_eq_integral hY hX k h lam hKi hK hsupp hpos]
  calc ‖∫ q : ℝ × ℝ, Kf q * (sidePoly x d Y lam k h q.1 * star (sidePoly x d Y lam k h (-q.2)))‖
      ≤ ∫ q : ℝ × ℝ, ‖Kf q * (sidePoly x d Y lam k h q.1 *
          star (sidePoly x d Y lam k h (-q.2)))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ q : ℝ × ℝ, c * (d.X * Y) ^ 2 * (((1 + |q.1| / d.X) ^ 2)⁻¹ *
          ((1 + |q.1 + q.2|) ^ 2)⁻¹ * (g q.1 * g (-q.2))) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
          (hInt.const_mul _) (Filter.Eventually.of_forall fun q => ?_)
        obtain ⟨τ, σ⟩ := q
        dsimp only
        rw [norm_mul, norm_mul, norm_star]
        calc ‖Kf (τ, σ)‖ * (‖sidePoly x d Y lam k h τ‖ * ‖sidePoly x d Y lam k h (-σ)‖)
            ≤ (c * ((1 + |τ| / d.X) ^ 2)⁻¹ * ((1 + |τ + σ|) ^ 2)⁻¹) *
                ((d.X * Y * g τ) * (d.X * Y * g (-σ))) := by
              gcongr
              · exact hKb τ σ
              · exact hG τ
              · exact hG (-σ)
          _ = _ := by ring
    _ = c * (d.X * Y) ^ 2 * ∫ q : ℝ × ℝ, ((1 + |q.1| / d.X) ^ 2)⁻¹ *
          ((1 + |q.1 + q.2|) ^ 2)⁻¹ * (g q.1 * g (-q.2)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hBound (by positivity)

end Erdos408.OneSided
