import Erdos408.TwoSided.Endpoint.Low.Model

/-!
# Inputs to the low-frequency bound

The remaining pieces of Lemma E2 (`blueprint/two_sided_correlation.md` §6.2).

* Step 1 (`LowFreq.twistedPoly_eq`): the endpoint polynomial is
  `Y⁻¹ (∑_Q B(init Q) P_{l_Q} - C_B P_1)`, with the progression sums
  `P_m = ∑_{w ≤ 2Y, m ∣ w} ψ₁(w/Y) w^{iτ} e(hw/k) H_m(w)` and `τ = σ + t`.
* Step 5 (`LowFreq.norm_combine_le`): the main terms `Θ/l_Q` cancel against `C_B Θ`, since
  `C_B = ∑_Q B(init Q)/l_Q` over the same tuples.
* `ψ₁(1) = 0` for a continuous piece supported in `[1, 2]`.
* The growth facts of O2: `3L^{0.47} ≤ (c/2) L/T²⁰`, `K L^C e^{2L^{0.47}} ≤ exp((c/2) L/T²⁰)`
  and `L ≤ x^{1 - c/T²⁰}`.
-/

namespace Erdos408.TwoSided.LowFreq

open Filter Finset

/-! ### Step 1: the progression sums -/

/-- The smooth weight `ψ₁(w/Y) w^{iτ}`. -/
noncomputable def lowWeight (ψ₁ : ℝ → ℂ) (Y τ : ℝ) (w : ℕ) : ℂ :=
  ψ₁ (w / Y) * (w : ℂ) ^ ((τ : ℂ) * Complex.I)

/-- The marks `H_m(n) = 𝒲(n) W_S^b(n)` with `S = unsharedSlots C`. -/
noncomputable def marks (x q q₀ : ℝ) {r : ℕ} (a : Fin r → ℝ) {ι : Type} [Fintype ι]
    [DecidableEq ι] (P : ι → Finset ℕ) {J : ℕ} (C : ι → Finset (Fin J))
    (b : (ι → Fin (J + 1) → ℕ) → ℂ) (n : ℕ) : ℂ :=
  (markedWeight Finset.univ q (fun i => band x (a i)) n : ℂ) *
    markedListWeight P q₀ (unsharedSlots C) b n

/-- The progression sum `P_m = ∑_{w ≤ 2Y, m ∣ w} ψ₁(w/Y) w^{iτ} e(hw/k) H(w)`. -/
noncomputable def progSum (ψ₁ : ℝ → ℂ) (Y τ : ℝ) (h : ℤ) (k : ℕ) (H : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ w ∈ (Icc 1 ⌊2 * Y⌋₊).filter (m ∣ ·), lowWeight ψ₁ Y τ w * addTwist h k w * H w

/-- **Step 1.** The endpoint polynomial in terms of the progression sums. -/
theorem twistedPoly_eq (x q q₀ : ℝ) {r d : ℕ} (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ)
    (Bc : (Fin d → ℕ) → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    {J : ℕ} (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ) {ψ₁ : ℝ → ℂ}
    (hψs : ∀ y, ψ₁ y ≠ 0 → 1 ≤ y) {Y : ℝ} (hY : 1 ≤ Y) (σ : ℝ) (h : ℤ) (k : ℕ) (t : ℝ) :
    twistedPoly Y (endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ) h k t =
      (Y : ℂ)⁻¹ * (∑ Q ∈ slotTuples x u v, (Bc (Fin.init Q) : ℂ) *
          progSum ψ₁ Y (σ + t) h k (marks x q q₀ a P C b) (∏ i, Q i) -
        (slotMean x u v Bc : ℂ) * progSum ψ₁ Y (σ + t) h k (marks x q q₀ a P C b) 1) := by
  unfold twistedPoly
  congr 1
  set Nw := ⌊2 * Y⌋₊
  set Φ : ℕ → ℂ := fun w => lowWeight ψ₁ Y (σ + t) w * addTwist h k w * marks x q q₀ a P C b w
  -- extend the sum to `[1, 2Y]`: `ψ₁(w/Y) = 0` for `w < Y`
  have hY0 : 0 < Y := by linarith
  have hext : ∑ w ∈ Icc ⌈Y⌉₊ Nw, endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w *
        Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
        (w : ℂ) ^ ((t : ℂ) * Complex.I) =
      ∑ w ∈ Icc 1 Nw, endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w *
        Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
        (w : ℂ) ^ ((t : ℂ) * Complex.I) := by
    refine sum_subset (Icc_subset_Icc_left (Nat.one_le_iff_ne_zero.2
      (Nat.ceil_pos.2 hY0).ne')) fun w hw hw' => ?_
    have hwY : (w : ℝ) < Y := by
      have : w < ⌈Y⌉₊ := by
        by_contra h'
        exact hw' (mem_Icc.2 ⟨not_lt.1 h', (mem_Icc.1 hw).2⟩)
      exact Nat.lt_ceil.1 this
    have hψ : ψ₁ (w / Y) = 0 := by
      by_contra h'
      have := hψs _ h'
      rw [le_div_iff₀ hY0, one_mul] at this
      linarith
    simp [endpointCoeff, hψ]
  have hterm : ∀ w ∈ Icc 1 Nw, endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w *
        Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
        (w : ℂ) ^ ((t : ℂ) * Complex.I) =
      Φ w * ((slotCount x u v Bc w : ℂ) - (slotMean x u v Bc : ℂ)) := by
    intro w hw
    have hw0 : (w : ℂ) ≠ 0 := by
      have := (mem_Icc.1 hw).1
      exact_mod_cast (show w ≠ 0 by omega)
    simp only [Φ, endpointCoeff, centeredCore, lowWeight, addTwist, marks]
    rw [show (((σ + t : ℝ) : ℂ) * Complex.I) = (σ : ℂ) * Complex.I + (t : ℂ) * Complex.I by
      push_cast; ring, Complex.cpow_add _ _ hw0]
    push_cast
    ring
  rw [hext, sum_congr rfl hterm]
  simp only [mul_sub, sum_sub_distrib]
  congr 1
  · -- the tuple term
    have hf : ∀ w, (slotCount x u v Bc w : ℂ) =
        ∑ Q ∈ slotTuples x u v, if ∏ i, Q i ∣ w then (Bc (Fin.init Q) : ℂ) else 0 := by
      intro w
      rw [slotCount, ← sum_filter]
      push_cast
      rfl
    simp only [hf, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun Q _ => ?_
    rw [progSum, mul_sum, sum_filter]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp [Φ, mul_comm]
  · rw [progSum, filter_true_of_mem fun w _ => one_dvd w, mul_sum]
    exact sum_congr rfl fun w _ => mul_comm _ _

/-! ### Step 5: the cancellation -/

/-- **Step 5.** If `|P_{l_Q} - Θ/l_Q| ≤ αY/l_Q + β` for every slot tuple and
`|P_1 - Θ| ≤ αY + β`, then, since `C_B = ∑_Q B(init Q)/l_Q`,
`|∑_Q B(init Q) P_{l_Q} - C_B P_1| ≤ 2αY ∑_Q 1/l_Q + β (#Q + ∑_Q 1/l_Q)`. -/
theorem norm_combine_le {d : ℕ} {Ts : Finset (Fin (d + 1) → ℕ)} {Bc : (Fin d → ℕ) → ℝ}
    (hBc : ∀ Q, |Bc Q| ≤ 1) (hl : ∀ Q ∈ Ts, 0 < ∏ i, Q i) {Pm : ℕ → ℂ} {Θ : ℂ}
    {α β Y : ℝ}
    (hΔ : ∀ Q ∈ Ts, ‖Pm (∏ i, Q i) - Θ / ((∏ i, Q i : ℕ) : ℂ)‖ ≤
      α * Y / (∏ i, Q i : ℕ) + β)
    (hΔ₁ : ‖Pm 1 - Θ‖ ≤ α * Y + β) :
    ‖∑ Q ∈ Ts, (Bc (Fin.init Q) : ℂ) * Pm (∏ i, Q i) -
        ((∑ Q ∈ Ts, Bc (Fin.init Q) / ∏ i, (Q i : ℝ) : ℝ) : ℂ) * Pm 1‖ ≤
      2 * α * Y * (∑ Q ∈ Ts, 1 / ∏ i, (Q i : ℝ)) +
        β * (#Ts + ∑ Q ∈ Ts, 1 / ∏ i, (Q i : ℝ)) := by
  set Sinv := ∑ Q ∈ Ts, 1 / ∏ i, (Q i : ℝ)
  set CB := ∑ Q ∈ Ts, Bc (Fin.init Q) / ∏ i, (Q i : ℝ)
  have hcast : ∀ Q : Fin (d + 1) → ℕ, ((∏ i, Q i : ℕ) : ℝ) = ∏ i, (Q i : ℝ) := fun Q => by
    push_cast; rfl
  have hCB : |CB| ≤ Sinv := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q hQ => ?_)
    have hpos : (0 : ℝ) < ∏ i, (Q i : ℝ) := by rw [← hcast]; exact_mod_cast hl Q hQ
    rw [abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (hBc _) hpos.le
  -- the main terms cancel
  have hsplit : ∑ Q ∈ Ts, (Bc (Fin.init Q) : ℂ) * Pm (∏ i, Q i) - (CB : ℂ) * Pm 1 =
      ∑ Q ∈ Ts, (Bc (Fin.init Q) : ℂ) * (Pm (∏ i, Q i) - Θ / ((∏ i, Q i : ℕ) : ℂ)) -
        (CB : ℂ) * (Pm 1 - Θ) := by
    have : (CB : ℂ) * Θ = ∑ Q ∈ Ts, (Bc (Fin.init Q) : ℂ) * (Θ / ((∏ i, Q i : ℕ) : ℂ)) := by
      simp only [CB, Complex.ofReal_sum, sum_mul]
      refine sum_congr rfl fun Q _ => ?_
      push_cast
      ring
    simp only [mul_sub, sum_sub_distrib]
    rw [← this]
    ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have h₁ : ‖∑ Q ∈ Ts, (Bc (Fin.init Q) : ℂ) * (Pm (∏ i, Q i) - Θ / ((∏ i, Q i : ℕ) : ℂ))‖ ≤
      α * Y * Sinv + β * #Ts := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ Q ∈ Ts, (α * Y * (1 / ∏ i, (Q i : ℝ)) + β) := by
          refine sum_le_sum fun Q hQ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hb := hΔ Q hQ
          rw [hcast] at hb
          have hpos : (0 : ℝ) < ∏ i, (Q i : ℝ) := by rw [← hcast]; exact_mod_cast hl Q hQ
          calc |Bc (Fin.init Q)| * ‖Pm (∏ i, Q i) - Θ / ((∏ i, Q i : ℕ) : ℂ)‖
              ≤ 1 * (α * Y / ∏ i, (Q i : ℝ) + β) :=
                mul_le_mul (hBc _) hb (norm_nonneg _) zero_le_one
            _ = _ := by ring
      _ = α * Y * Sinv + β * #Ts := by
          rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_comm β]
  have h₂ : ‖(CB : ℂ) * (Pm 1 - Θ)‖ ≤ Sinv * (α * Y + β) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hCB hΔ₁ (norm_nonneg _) ((abs_nonneg _).trans hCB)
  calc _ ≤ α * Y * Sinv + β * #Ts + Sinv * (α * Y + β) := add_le_add h₁ h₂
    _ = _ := by ring

/-! ### The cutoff piece -/

/-- A continuous piece supported in `[1, 2]` vanishes at `1`, so `ψ₁(y) ≠ 0` forces
`y > 1`. -/
theorem one_lt_of_ne_zero {ψ₁ : ℝ → ℂ} (hc : Continuous ψ₁)
    (hs : ∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) {y : ℝ} (hy : ψ₁ y ≠ 0) : 1 < y := by
  have hsub : Set.Iio (1 : ℝ) ⊆ {y | ψ₁ y = 0} := by
    intro z hz
    by_contra h
    exact absurd (hs z h).1 (not_le.2 hz)
  have hcl : closure (Set.Iio (1 : ℝ)) ⊆ {y | ψ₁ y = 0} :=
    (IsClosed.closure_subset_iff (isClosed_eq hc continuous_const)).2 hsub
  rw [closure_Iio] at hcl
  have h1 : ψ₁ 1 = 0 := hcl (Set.mem_Iic.2 le_rfl)
  refine lt_of_le_of_ne (hs y hy).1 fun h => hy ?_
  rw [← h, h1]

/-! ### Growth facts (O2) -/

/-- `K L^a ≤ L^b` eventually, for `a < b`. -/
theorem eventually_mul_log_rpow_le (K : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ^ a ≤ Real.log x ^ b := by
  filter_upwards [((tendsto_rpow_atTop (sub_pos.2 hab)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop K,
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hK hL
  simp only [Function.comp_apply] at hK
  have : Real.log x ^ b = Real.log x ^ (b - a) * Real.log x ^ a := by
    rw [← Real.rpow_add hL]
    ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hL.le a)

/-- `L^A < exp(L^g)` eventually, for `g > 0`. -/
theorem eventually_rpow_lt_exp_rpow (A : ℝ) {g : ℝ} (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ A < Real.exp (Real.log x ^ g) := by
  have hexp := (tendsto_exp_div_rpow_atTop (A / g)).comp
    ((tendsto_rpow_atTop hg).comp Real.tendsto_log_atTop)
  filter_upwards [hexp.eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hL
  have hx' : 1 < Real.exp (Real.log x ^ g) / (Real.log x ^ g) ^ (A / g) := hx
  rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ hg.ne'] at hx'
  rwa [one_lt_div (by positivity)] at hx'

/-- `3 L^{0.47} ≤ (c/2) L / T²⁰` eventually. -/
theorem eventually_three_rpow_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      3 * Real.log x ^ (0.47 : ℝ) ≤ c / 2 * Real.log x / Real.log (Real.log x) ^ 20 := by
  filter_upwards [Sieve.eventually_mul_rpow_le_log_rpow 1 20 (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_mul_log_rpow_le (6 / c) (show (0.47 : ℝ) < 1 / 2 by norm_num),
    Sieve.tendsto_logLog.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hT20 h47 hT1 hL
  simp only [logLog, one_mul] at hT20 hT1
  set L := Real.log x
  set T := Real.log L
  have hT20' : T ^ 20 ≤ L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact_mod_cast hT20
  have hTpos : 0 < T ^ 20 := by positivity
  have hhalf : L / L ^ (1 / 2 : ℝ) = L ^ (1 / 2 : ℝ) := by
    rw [div_eq_iff (by positivity), ← Real.rpow_add hL]
    norm_num
  calc 3 * L ^ (0.47 : ℝ) = c / 2 * (6 / c * L ^ (0.47 : ℝ)) := by field_simp; ring
    _ ≤ c / 2 * L ^ (1 / 2 : ℝ) := by gcongr
    _ = c / 2 * L / L ^ (1 / 2 : ℝ) := by rw [mul_div_assoc, hhalf]
    _ ≤ c / 2 * L / T ^ 20 := div_le_div_of_nonneg_left (by positivity) hTpos hT20'

/-- `K L^C e^{2 L^{0.47}} ≤ exp((c/2) L / T²⁰)` eventually: the slot margin `x^{-ε/2}`
absorbs the model mass, the moduli and the twists. -/
theorem eventually_mul_exp_le {c : ℝ} (hc : 0 < c) (K C : ℝ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ^ C * Real.exp (2 * Real.log x ^ (0.47 : ℝ)) ≤
      Real.exp (c / 2 * Real.log x / Real.log (Real.log x) ^ 20) := by
  filter_upwards [eventually_three_rpow_le hc,
    Sieve.eventually_mul_rpow_le_log_rpow (Real.log (|K| + 1) + |C|) 1
      (show (0 : ℝ) < 0.47 by norm_num),
    Sieve.tendsto_logLog.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x h3 hK hT1 hL
  simp only [logLog, Real.rpow_one] at hK hT1
  set L := Real.log x
  set T := Real.log L
  have hK1 : 0 < |K| + 1 := by positivity
  have hLC : K * L ^ C ≤ Real.exp (L ^ (0.47 : ℝ)) := by
    calc K * L ^ C ≤ (|K| + 1) * L ^ C :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (by positivity)
      _ = Real.exp (Real.log (|K| + 1) + C * T) := by
          rw [Real.exp_add, Real.exp_log hK1, Real.rpow_def_of_pos hL, mul_comm C]
      _ ≤ Real.exp (L ^ (0.47 : ℝ)) := by
          refine Real.exp_le_exp.2 (le_trans ?_ hK)
          have : C * T ≤ |C| * T := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
          have h0 : 0 ≤ Real.log (|K| + 1) := Real.log_nonneg (by linarith [abs_nonneg K])
          nlinarith
  calc K * L ^ C * Real.exp (2 * L ^ (0.47 : ℝ))
      ≤ Real.exp (L ^ (0.47 : ℝ)) * Real.exp (2 * L ^ (0.47 : ℝ)) :=
        mul_le_mul_of_nonneg_right hLC (Real.exp_pos _).le
    _ = Real.exp (3 * L ^ (0.47 : ℝ)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := Real.exp_le_exp.2 h3

/-- `L ≤ x^{1 - c/T²⁰}` eventually. -/
theorem eventually_log_le_rpow (c : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x ≤ x ^ (1 - c / Real.log (Real.log x) ^ 20) := by
  filter_upwards [Sieve.tendsto_logLog.eventually_ge_atTop (max 1 (2 * c)),
    Sieve.eventually_mul_rpow_le_log_rpow 2 1 one_pos,
    Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop 0] with x hT h2 hL hx
  simp only [logLog, Real.rpow_one] at hT h2
  set L := Real.log x
  set T := Real.log L
  have hT1 : 1 ≤ T := le_of_max_le_left hT
  have hT2 : 2 * c ≤ T := le_of_max_le_right hT
  have hT20 : T ≤ T ^ 20 := le_self_pow₀ hT1 (by norm_num)
  have hε : c / T ^ 20 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  rw [Real.rpow_def_of_pos hx]
  calc L = Real.exp T := (Real.exp_log hL).symm
    _ ≤ Real.exp (L * (1 - c / T ^ 20)) := by
        refine Real.exp_le_exp.2 ?_
        nlinarith

end Erdos408.TwoSided.LowFreq
