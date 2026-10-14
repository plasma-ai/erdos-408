import Erdos408.TwoSided.Endpoint.Low.Progression

/-!
# One progression of the low-frequency sum

Steps 2–3 of Lemma E2 (`blueprint/two_sided_correlation.md` §6.2) for one modulus `m`
(`m = l_Q` for a slot tuple, or `m = 1` for the constant term). For marks `H` with
`H(mn) = H(n)` (U8) and a model `A` supported on `D`, with every `m d` coprime to `k` (U3),
the progression sum `P_m = ∑_{w ≤ N, m ∣ w} G(w) e(hw/k) H(w)` is
`κ_{h,k} S Ā / m`, with `S = ∑_{w ≤ N} G(w)` and `Ā = ∑_d A_d / d`, up to

* the model error `M₀ √2 √C_N (Y/m) ρ^{1/2}`, by Cauchy–Schwarz and E1(c) at the scale
  `R = Y/m` (`LowFreq.norm_sum_mul_sub_model_le`);
* the progression errors `(∑_d |A_d|) k TV(G)` (`LowFreq.norm_sum_dvd_sub_le`).
-/

namespace Erdos408.TwoSided.LowFreq

open Finset

/-- The divisor sum of a model supported on `D`, for `n ≠ 0`. -/
theorem sum_divisors_eq_sum_filter {A : ℕ → ℂ} {D : Finset ℕ} (hA : ∀ d, A d ≠ 0 → d ∈ D)
    {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, A d = ∑ d ∈ D, if d ∣ n then A d else 0 := by
  rw [← sum_filter]
  have h₁ : ∑ d ∈ n.divisors, A d = ∑ d ∈ n.divisors ∩ D, A d := by
    refine (sum_subset inter_subset_left fun d hd hd' => ?_).symm
    by_contra h
    exact hd' (mem_inter.2 ⟨hd, hA d h⟩)
  rw [h₁]
  congr 1
  ext d
  simp only [mem_inter, Nat.mem_divisors, mem_filter]
  tauto

/-- **Steps 2–3, the algebra.** For `H(mn) = H(n)` and a model supported on `D`,
`P_m = ∑_d A_d ∑_{w ≤ N, md ∣ w} Φ(w) + ∑_{w ≤ N, m ∣ w} Φ(w) (H - ∑_{d ∣ ·} A_d)(w/m)`. -/
theorem sum_dvd_eq {Φ H A : ℕ → ℂ} {D : Finset ℕ} (hA : ∀ d, A d ≠ 0 → d ∈ D) {m : ℕ}
    (hm : 0 < m) (hH : ∀ n, H (m * n) = H n) (Nw : ℕ) :
    ∑ w ∈ (Icc 1 Nw).filter (m ∣ ·), Φ w * H w =
      ∑ d ∈ D, A d * ∑ w ∈ (Icc 1 Nw).filter (m * d ∣ ·), Φ w +
        ∑ w ∈ (Icc 1 Nw).filter (m ∣ ·),
          Φ w * (H (w / m) - ∑ d ∈ (w / m).divisors, A d) := by
  have hw : ∀ w ∈ (Icc 1 Nw).filter (m ∣ ·), Φ w * H w =
      (∑ d ∈ D, A d * if m * d ∣ w then Φ w else 0) +
        Φ w * (H (w / m) - ∑ d ∈ (w / m).divisors, A d) := by
    intro w hw'
    obtain ⟨hw₁, hmw⟩ := mem_filter.1 hw'
    have hw0 : w ≠ 0 := by have := (mem_Icc.1 hw₁).1; omega
    have hq0 : w / m ≠ 0 := by
      intro h
      rw [Nat.div_eq_zero_iff_lt hm] at h
      exact hw0 (Nat.eq_zero_of_dvd_of_lt hmw h)
    have hHw : H w = H (w / m) := by rw [← hH (w / m), Nat.mul_div_cancel' hmw]
    rw [hHw, sum_divisors_eq_sum_filter hA hq0, mul_sub, mul_sum]
    have : ∀ d ∈ D, (Φ w * if d ∣ w / m then A d else 0) =
        A d * if m * d ∣ w then Φ w else 0 := by
      intro d _
      by_cases hd : m * d ∣ w
      · rw [ite_eq_left ((Nat.dvd_div_iff_mul_dvd hmw).2 hd), ite_eq_left hd]
        ring
      · rw [ite_eq_right fun h => hd ((Nat.dvd_div_iff_mul_dvd hmw).1 h), ite_eq_right hd]
        ring
    rw [sum_congr rfl this]
    ring
  rw [sum_congr rfl hw, sum_add_distrib, sum_comm]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  rw [← mul_sum, ← sum_filter, filter_filter]
  congr 2
  refine filter_congr fun w _ => ?_
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨(Dvd.intro d rfl).trans h, h⟩

/-- **Step 2, the model error.** If `|Φ| ≤ M₀`, `Φ(w) ≠ 0 → Y < w`, `m ≤ Y` and the model
error `E` has `∑_{R < n ≤ 2R} |E(n)|² ≤ C_N R ρ` at `R = Y/m`, then
`|∑_{w ≤ 2Y, m ∣ w} Φ(w) E(w/m)| ≤ M₀ √2 √C_N (Y/m) √ρ`. -/
theorem norm_sum_mul_sub_model_le {Φ E : ℕ → ℂ} {M₀ Y CNN ρ : ℝ} (hM₀ : 0 ≤ M₀)
    (hρ : 0 ≤ ρ) (hΦ : ∀ w, ‖Φ w‖ ≤ M₀) (hΦs : ∀ w : ℕ, Φ w ≠ 0 → Y < w) {m : ℕ}
    (hm : 0 < m) (hmY : (m : ℝ) ≤ Y)
    (hE : ∑ n ∈ Ioc ⌊Y / m⌋₊ ⌊2 * (Y / m)⌋₊, ‖E n‖ ^ 2 ≤ CNN * (Y / m) * ρ) :
    ‖∑ w ∈ (Icc 1 ⌊2 * Y⌋₊).filter (m ∣ ·), Φ w * E (w / m)‖ ≤
      M₀ * (Real.sqrt 2 * Real.sqrt CNN * (Y / m) * Real.sqrt ρ) := by
  set R := Y / m with hR
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hR1 : 1 ≤ R := by rw [hR, le_div_iff₀ hm', one_mul]; exact hmY
  set I := Ioc ⌊R⌋₊ ⌊2 * R⌋₊
  set F := ((Icc 1 ⌊2 * Y⌋₊).filter (m ∣ ·)).filter fun w : ℕ => Y < w
  -- only `Y < w ≤ 2Y` contribute, and `w ↦ w/m` maps them into `(R, 2R]`
  have h1 : ‖∑ w ∈ (Icc 1 ⌊2 * Y⌋₊).filter (m ∣ ·), Φ w * E (w / m)‖ ≤
      M₀ * ∑ w ∈ F, ‖E (w / m)‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [mul_sum, show (∑ w ∈ F, M₀ * ‖E (w / m)‖) = ∑ w ∈ (Icc 1 ⌊2 * Y⌋₊).filter (m ∣ ·),
      if Y < w then M₀ * ‖E (w / m)‖ else 0 from sum_filter _ _]
    refine sum_le_sum fun w _ => ?_
    split_ifs with hw
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hΦ w) (norm_nonneg _)
    · have : Φ w = 0 := by
        by_contra h
        exact hw (hΦs w h)
      rw [this, zero_mul, norm_zero]
  have hinj : Set.InjOn (· / m) (F : Set ℕ) := by
    intro w₁ hw₁ w₂ hw₂ h
    have h₁ := (mem_filter.1 (mem_filter.1 hw₁).1).2
    have h₂ := (mem_filter.1 (mem_filter.1 hw₂).1).2
    simp only at h
    rw [← Nat.mul_div_cancel' h₁, ← Nat.mul_div_cancel' h₂, h]
  have himg : F.image (· / m) ⊆ I := by
    intro n hn
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hn
    obtain ⟨⟨hw₁, hmw⟩, hYw⟩ := mem_filter.1 hw |>.imp_left mem_filter.1
    have hwN := (mem_Icc.1 hw₁).2
    have hcast : ((w / m : ℕ) : ℝ) = w / m := Nat.cast_div hmw hm'.ne'
    have hw2 : (w : ℝ) ≤ 2 * Y := (Nat.cast_le.2 hwN).trans (Nat.floor_le (by
      have : (0 : ℝ) ≤ m := hm'.le
      linarith))
    refine mem_Ioc.2 ⟨?_, ?_⟩
    · rw [← Nat.cast_lt (α := ℝ), hcast]
      refine (Nat.floor_le (by linarith)).trans_lt ?_
      rw [hR]
      exact div_lt_div_of_pos_right hYw hm'
    · refine Nat.le_floor ?_
      rw [hcast, hR, mul_div_assoc']
      exact div_le_div_of_nonneg_right hw2 hm'.le
  have h2 : ∑ w ∈ F, ‖E (w / m)‖ ≤ ∑ n ∈ I, ‖E n‖ := by
    rw [← sum_image (f := fun n => ‖E n‖) hinj]
    exact sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => norm_nonneg _
  -- Cauchy–Schwarz on `(R, 2R]`, which has at most `2R` points
  have hcard : (#I : ℝ) ≤ 2 * R := by
    rw [Nat.card_Ioc]
    have h₁ := Nat.floor_le (show 0 ≤ 2 * R by linarith)
    have h₂ := Nat.lt_floor_add_one R
    rw [Nat.cast_sub (Nat.floor_le_floor (by linarith))]
    linarith
  have h3 : (∑ n ∈ I, ‖E n‖) ^ 2 ≤ 2 * R * (CNN * R * ρ) := by
    have := sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) fun n => ‖E n‖
    simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at this
    refine this.trans ?_
    exact mul_le_mul hcard hE (sum_nonneg fun _ _ => by positivity) (by linarith)
  have h4 : ∑ n ∈ I, ‖E n‖ ≤ Real.sqrt 2 * Real.sqrt CNN * R * Real.sqrt ρ := by
    have hsq : Real.sqrt (2 * R * (CNN * R * ρ)) =
        Real.sqrt 2 * Real.sqrt CNN * R * Real.sqrt ρ := by
      rw [show 2 * R * (CNN * R * ρ) = CNN * (2 * (R ^ 2 * ρ)) by ring,
        Real.sqrt_mul' _ (by positivity), Real.sqrt_mul' _ (by positivity),
        Real.sqrt_mul' _ hρ, Real.sqrt_sq (by linarith)]
      ring
    rw [← hsq]
    exact Real.le_sqrt_of_sq_le h3
  calc _ ≤ M₀ * ∑ w ∈ F, ‖E (w / m)‖ := h1
    _ ≤ M₀ * ∑ n ∈ I, ‖E n‖ := mul_le_mul_of_nonneg_left h2 hM₀
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 hM₀

/-- **Steps 2–3 for one modulus.** With the hypotheses of `sum_dvd_eq` and
`norm_sum_mul_sub_model_le`, `m d` coprime to `k` on the support and `G(0) = 0`,
`|P_m - κ_{h,k} S Ā / m| ≤ M₀ √2 √C_N (Y/m) √ρ + (∑_{d ∈ D} |A_d|) k TV(G)`. -/
theorem norm_sum_dvd_sub_le {G H A : ℕ → ℂ} {D : Finset ℕ} (hA : ∀ d, A d ≠ 0 → d ∈ D)
    (hD : ∀ d ∈ D, 0 < d) {M₀ Y CNN ρ : ℝ} (hM₀ : 0 ≤ M₀) (hρ : 0 ≤ ρ) {h : ℤ} {k : ℕ}
    (hk : 0 < k) (hG0 : G 0 = 0) (hΦ : ∀ w, ‖G w * LowFreq.addTwist h k w‖ ≤ M₀)
    (hΦs : ∀ w : ℕ, G w * LowFreq.addTwist h k w ≠ 0 → Y < w) {m : ℕ} (hm : 0 < m)
    (hmY : (m : ℝ) ≤ Y) (hH : ∀ n, H (m * n) = H n)
    (hcop : ∀ d ∈ D, A d ≠ 0 → Nat.Coprime (m * d) k)
    (hE : ∑ n ∈ Ioc ⌊Y / m⌋₊ ⌊2 * (Y / m)⌋₊, ‖H n - ∑ d ∈ n.divisors, A d‖ ^ 2 ≤
      CNN * (Y / m) * ρ) :
    ‖∑ w ∈ (Icc 1 ⌊2 * Y⌋₊).filter (m ∣ ·), G w * LowFreq.addTwist h k w * H w -
        twistMean h k * (∑ w ∈ Icc 1 ⌊2 * Y⌋₊, G w) * (∑ d ∈ D, A d / d) / m‖ ≤
      M₀ * (Real.sqrt 2 * Real.sqrt CNN * (Y / m) * Real.sqrt ρ) +
        (∑ d ∈ D, ‖A d‖) * (k * ∑ w ∈ Icc 1 ⌊2 * Y⌋₊, ‖G w - G (w - 1)‖) := by
  set Nw := ⌊2 * Y⌋₊
  set S := ∑ w ∈ Icc 1 Nw, G w
  set TV := ∑ w ∈ Icc 1 Nw, ‖G w - G (w - 1)‖
  rw [sum_dvd_eq (Φ := fun w => G w * addTwist h k w) hA hm hH Nw]
  have hmain : twistMean h k * S * (∑ d ∈ D, A d / d) / m =
      ∑ d ∈ D, A d * (twistMean h k * S / (m * d : ℕ)) := by
    rw [mul_sum, sum_div]
    refine sum_congr rfl fun d hd => ?_
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (hD d hd).ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
  rw [hmain, add_sub_right_comm, ← sum_sub_distrib]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add ?_ (norm_sum_mul_sub_model_le hM₀ hρ hΦ hΦs hm hmY hE)).trans_eq
    (add_comm _ _)
  · -- the progression errors
    refine (norm_sum_le _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun d hd => ?_
    rw [← mul_sub, norm_mul]
    by_cases hAd : A d = 0
    · rw [hAd, norm_zero, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := norm_sum_dvd_twist_sub_le (Nat.mul_pos hm (hD d hd)) hk (hcop d hd hAd) h Nw
        hG0
      exact this

end Erdos408.TwoSided.LowFreq
