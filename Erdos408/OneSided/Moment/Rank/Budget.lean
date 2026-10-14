import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The rank budgets

The real inequalities behind the rank cut in M10 (`blueprint/one_sided_type_ii.md` §13,
PD `mem:high-rank` and `mem:low-rank`). Here `L → ∞`, the number of edges is `N ≈ L^{1/2}`,
the number of birth addresses is `Q ≤ L⁴`, and the rank-`r` coefficient mass is `Q^{2r}`.
The cut is `r₀ = ⌈L^{9/20}⌉` instead of PD's `⌈C' N log L / L^{.1}⌉`: it is `o(N / log L)`,
and `r₀ L^{1/10} ≥ L^{11/20}` beats `N log L`.

* `eventually_highRank_sum_le`: the ranks `r ≥ r₀` cost
  `Q^{2r} L^{C₁(N+1)} (C₁ exp(-L^{α₋}))^r`. This is a geometric series of ratio at most
  `exp(-L^{1/10}/2)`, so in total at most `L^{-(E₀ + 2) N}`.
* `eventually_lowRank_sum_le`: the ranks `r < r₀` cost
  `Q^{2r} C₀^{N+1} L^{-GN + 2(C_e + G) r} 2^{KM}`. Since `r₀ = o(N / log L)` and
  `KM = o(N)`, this is at most `L^{-GN + 2N} = L^{-(E₀ + 2) N}` for `G = E₀ + 4`.
* `eventually_addrCount_le`: `Q = KM + NK + (N + 1)B ≤ L⁴` for `B ≤ L² + 1`.
-/

namespace Erdos408.OneSided

open Filter Finset Real

/-! ### Growth facts -/

/-- For `0 ≤ a < b`, eventually `c (L^a + 1) ≤ L^b`. -/
theorem eventually_mul_rpow_add_one_le (c : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, c * (L ^ a + 1) ≤ L ^ b := by
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_rpow_atTop (sub_pos.2 hab)).eventually_ge_atTop (2 * |c|)] with L hL h
  have hLa : 1 ≤ L ^ a := Real.one_le_rpow hL ha
  calc c * (L ^ a + 1) ≤ |c| * (L ^ a + 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (2 * L ^ a) := by gcongr; linarith
    _ = 2 * |c| * L ^ a := by ring
    _ ≤ L ^ (b - a) * L ^ a := by gcongr
    _ = L ^ b := by rw [← Real.rpow_add (by linarith), sub_add_cancel]

/-- For `c, ε > 0`, eventually `log L ≤ c L^ε`. -/
theorem eventually_log_le_const_mul_rpow {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, Real.log L ≤ c * L ^ ε := by
  filter_upwards [(isLittleO_log_rpow_atTop hε).bound hc, eventually_ge_atTop 0] with L h hL
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ L ^ ε)] at h
  exact (le_abs_self _).trans h

/-- For `L ≥ 16`, `4 ≤ L^{1/2}`. -/
theorem four_le_rpow_half {L : ℝ} (hL : 16 ≤ L) : 4 ≤ L ^ (1 / 2 : ℝ) := by
  calc (4 : ℝ) = (16 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
    _ ≤ L ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hL (by norm_num)

/-- The cut `r₀ = ⌈L^{9/20}⌉` is between `L^{9/20}` and `L^{9/20} + 1`. -/
theorem rankCut_bounds {L : ℝ} (hL : 0 ≤ L) :
    L ^ (9 / 20 : ℝ) ≤ ⌈L ^ (9 / 20 : ℝ)⌉₊ ∧ (⌈L ^ (9 / 20 : ℝ)⌉₊ : ℝ) ≤ L ^ (9 / 20 : ℝ) + 1 :=
  ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le⟩

/-! ### The number of addresses -/

/-- `KM + NK + (N + 1)B ≤ L⁴` for `M = J + 1`, `J ≤ L^{1/100}`, `N ≤ L^{1/2} + 2` and
`B ≤ L² + 1`. -/
theorem eventually_addrCount_le (K : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ N J B : ℕ, (N : ℝ) ≤ L ^ (1 / 2 : ℝ) + 2 →
      (J : ℝ) ≤ L ^ (1 / 100 : ℝ) → (B : ℝ) ≤ L ^ 2 + 1 →
      ((K * (J + 1) + (N * K + (N + 1) * B) : ℕ) : ℝ) ≤ L ^ 4 := by
  filter_upwards [eventually_ge_atTop (8 + 5 * (K : ℝ)), eventually_ge_atTop 1]
    with L hLK hL1 N J B hN hJ hB
  have hL0 : 0 ≤ L := by linarith
  -- `L^{1/2}, L^{1/100} ≤ L`
  have hs : L ^ (1 / 2 : ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have ht : L ^ (1 / 100 : ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (1 / 100 : ℝ) ≤ 1 by norm_num)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hN' : (N : ℝ) + 1 ≤ 4 * L := by linarith
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hB' : (B : ℝ) ≤ 2 * L ^ 2 := by linarith
  push_cast
  -- `K M + N K ≤ 5 K L` and `(N + 1) B ≤ 8 L³`
  have h₁ : (K : ℝ) * (J + 1) + N * K ≤ 5 * K * L := by
    have a : (K : ℝ) * (J + 1) ≤ K * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) hK
    have b : (N : ℝ) * K ≤ (L + 2) * K := mul_le_mul_of_nonneg_right (by linarith) hK
    have c : (K : ℝ) * (2 * L + 3) ≤ K * (5 * L) := mul_le_mul_of_nonneg_left (by linarith) hK
    linarith
  have h₂ : ((N : ℝ) + 1) * B ≤ 8 * L ^ 3 :=
    calc ((N : ℝ) + 1) * B ≤ (4 * L) * (2 * L ^ 2) :=
          mul_le_mul hN' hB' (Nat.cast_nonneg _) (by positivity)
      _ = 8 * L ^ 3 := by ring
  have h₃ : 5 * K * L ≤ 5 * K * L ^ 3 := by
    have : L ≤ L ^ 3 :=
      calc L = L * 1 := (mul_one L).symm
        _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left hL2 hL0
        _ = L ^ 3 := by ring
    exact mul_le_mul_of_nonneg_left this (by positivity)
  calc (K : ℝ) * (J + 1) + (N * K + (N + 1) * B) ≤ (8 + 5 * K) * L ^ 3 := by linarith
    _ ≤ L * L ^ 3 := mul_le_mul_of_nonneg_right hLK (by positivity)
    _ = L ^ 4 := by ring

/-! ### High ranks -/

/-- **The high ranks**: for `Q ≤ L⁴` and `N ≤ L^{1/2} + 2`, the ranks `r₀ ≤ r ≤ Q` cost in total
at most `L^{-(E + 2) N}`. -/
theorem eventually_highRank_sum_le {C₁ E alo : ℝ} (hC₁ : 0 ≤ C₁) (hE : 0 ≤ E)
    (halo : 1 / 10 ≤ alo) :
    ∀ᶠ L : ℝ in atTop, ∀ N Q : ℕ, (N : ℝ) ≤ L ^ (1 / 2 : ℝ) + 2 → (Q : ℝ) ≤ L ^ 4 →
      ∑ r ∈ Ico ⌈L ^ (9 / 20 : ℝ)⌉₊ (Q + 1), (Q : ℝ) ^ (2 * r) *
          (L ^ (C₁ * (N + 1)) * (C₁ * Real.exp (-L ^ alo)) ^ r) ≤
        L ^ (-((E + 2) * N)) := by
  set A := 3 * C₁ + 2 * E + 9 with hA
  have hA0 : 0 < A := by positivity
  filter_upwards [eventually_ge_atTop (16 : ℝ),
    eventually_log_le_const_mul_rpow (show (0 : ℝ) < 1 / 32 by norm_num)
      (show (0 : ℝ) < 1 / 10 by norm_num),
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually_ge_atTop
      (4 * Real.log (C₁ + 1)),
    eventually_log_le_const_mul_rpow (inv_pos.2 (mul_pos two_pos hA0))
      (show (0 : ℝ) < 1 / 20 by norm_num)] with L hL16 hlog₁ hC hlog₂ N Q hN hQ
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  set u := L ^ (1 / 10 : ℝ) with hu
  set s := L ^ (1 / 2 : ℝ) with hs
  have hs4 : 4 ≤ s := four_le_rpow_half hL16
  have hu0 : 0 ≤ u := by positivity
  obtain ⟨hr₀, -⟩ := rankCut_bounds hL0.le
  set r₀ := ⌈L ^ (9 / 20 : ℝ)⌉₊
  -- the ratio `ρ = Q² C₁ exp(-L^{α₋})` is at most `exp(-L^{1/10}/2)`
  set ρ := (Q : ℝ) ^ 2 * (C₁ * Real.exp (-L ^ alo)) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ Real.exp (-(u / 2)) := by
    have hexp : Real.exp (-L ^ alo) ≤ Real.exp (-u) :=
      Real.exp_le_exp.2 (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hL1 halo))
    have hQ2 : (Q : ℝ) ^ 2 ≤ L ^ 8 :=
      calc (Q : ℝ) ^ 2 ≤ (L ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 2
        _ = L ^ 8 := by ring
    have hL8 : L ^ 8 = Real.exp (8 * Real.log L) := by
      rw [← Real.log_rpow hL0, Real.exp_log (by positivity)]
      norm_cast
    calc ρ ≤ L ^ 8 * ((C₁ + 1) * Real.exp (-u)) := by
          rw [hρ]
          gcongr
          linarith
      _ = Real.exp (8 * Real.log L + Real.log (C₁ + 1) - u) := by
          rw [hL8, Real.exp_sub, Real.exp_add, Real.exp_log (by linarith), Real.exp_neg]
          ring
      _ ≤ Real.exp (-(u / 2)) := Real.exp_le_exp.2 (by linarith)
  have hρ1' : ρ ≤ 1 := hρ1.trans (by rw [Real.exp_le_one_iff]; linarith)
  -- `ρ^{r₀} ≤ exp(-L^{11/20}/2)`
  have hρr₀ : ρ ^ r₀ ≤ Real.exp (-(L ^ (11 / 20 : ℝ) / 2)) := by
    have h₁ : L ^ (11 / 20 : ℝ) ≤ r₀ * u := by
      calc L ^ (11 / 20 : ℝ) = L ^ (9 / 20 : ℝ) * u := by
            rw [hu, ← Real.rpow_add hL0]
            norm_num
        _ ≤ r₀ * u := mul_le_mul_of_nonneg_right hr₀ hu0
    calc ρ ^ r₀ ≤ Real.exp (-(u / 2)) ^ r₀ := pow_le_pow_left₀ hρ0 hρ1 r₀
      _ = Real.exp (-(r₀ * u / 2)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
      _ ≤ Real.exp (-(L ^ (11 / 20 : ℝ) / 2)) := Real.exp_le_exp.2 (by linarith)
  -- each term is at most `L^{C₁(N+1)} exp(-L^{11/20}/2)`
  have hterm : ∀ r ∈ Ico r₀ (Q + 1), (Q : ℝ) ^ (2 * r) *
      (L ^ (C₁ * (N + 1)) * (C₁ * Real.exp (-L ^ alo)) ^ r) ≤
        L ^ (C₁ * (N + 1)) * Real.exp (-(L ^ (11 / 20 : ℝ) / 2)) := by
    intro r hr
    have hr' : r₀ ≤ r := (mem_Ico.1 hr).1
    calc (Q : ℝ) ^ (2 * r) * (L ^ (C₁ * (N + 1)) * (C₁ * Real.exp (-L ^ alo)) ^ r)
        = L ^ (C₁ * (N + 1)) * ρ ^ r := by rw [hρ, mul_pow, pow_mul]; ring
      _ ≤ L ^ (C₁ * (N + 1)) * ρ ^ r₀ :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1' hr') (by positivity)
      _ ≤ L ^ (C₁ * (N + 1)) * Real.exp (-(L ^ (11 / 20 : ℝ) / 2)) := by gcongr
  -- the final comparison, in logarithms
  have hcard : ((Ico r₀ (Q + 1)).card : ℝ) ≤ L ^ 4 + 1 := by
    rw [Nat.card_Ico]
    calc ((Q + 1 - r₀ : ℕ) : ℝ) ≤ ((Q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ L ^ 4 + 1 := by push_cast; linarith
  have hL5 : L ^ 4 + 1 ≤ Real.exp (5 * Real.log L) := by
    have : L ^ 5 = Real.exp (5 * Real.log L) := by
      rw [← Real.log_rpow hL0, Real.exp_log (by positivity)]
      norm_cast
    have h4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
    calc L ^ 4 + 1 ≤ L ^ 4 + L ^ 4 := by linarith
      _ ≤ L * L ^ 4 := by
          have := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ L by linarith) (by positivity :
            (0 : ℝ) ≤ L ^ 4)
          linarith
      _ = Real.exp (5 * Real.log L) := by rw [← this]; ring
  have hexpo : 5 * Real.log L + Real.log L * (C₁ * (N + 1)) - L ^ (11 / 20 : ℝ) / 2 ≤
      Real.log L * (-((E + 2) * N)) := by
    have hN₂ : (N : ℝ) ≤ 2 * s := by linarith
    have hN₁ : (N : ℝ) + 1 ≤ 3 * s := by linarith
    -- `5 + C₁ (N + 1) + (E + 2) N ≤ A L^{1/2}`
    have hlin : 5 + C₁ * (N + 1) + (E + 2) * N ≤ A * s := by
      have h₁ : C₁ * (N + 1) ≤ C₁ * (3 * s) := mul_le_mul_of_nonneg_left hN₁ hC₁
      have h₂ : (E + 2) * N ≤ (E + 2) * (2 * s) := mul_le_mul_of_nonneg_left hN₂ (by linarith)
      rw [hA]
      linarith
    -- `log L ⋅ A L^{1/2} ≤ L^{1/20} L^{1/2} / 2 = L^{11/20} / 2`
    have hmain : Real.log L * (A * s) ≤ L ^ (11 / 20 : ℝ) / 2 :=
      calc Real.log L * (A * s) ≤ ((2 * A)⁻¹ * L ^ (1 / 20 : ℝ)) * (A * s) :=
            mul_le_mul_of_nonneg_right hlog₂ (by positivity)
        _ = L ^ (1 / 20 : ℝ) * s / 2 := by field_simp
        _ = L ^ (11 / 20 : ℝ) / 2 := by
            rw [hs, ← Real.rpow_add hL0]
            norm_num
    have := mul_le_mul_of_nonneg_left hlin hlogL
    linarith
  calc ∑ r ∈ Ico r₀ (Q + 1), (Q : ℝ) ^ (2 * r) *
        (L ^ (C₁ * (N + 1)) * (C₁ * Real.exp (-L ^ alo)) ^ r)
      ≤ ∑ _r ∈ Ico r₀ (Q + 1), L ^ (C₁ * (N + 1)) * Real.exp (-(L ^ (11 / 20 : ℝ) / 2)) :=
        sum_le_sum hterm
    _ = (Ico r₀ (Q + 1)).card * (L ^ (C₁ * (N + 1)) * Real.exp (-(L ^ (11 / 20 : ℝ) / 2))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (5 * Real.log L) *
          (L ^ (C₁ * (N + 1)) * Real.exp (-(L ^ (11 / 20 : ℝ) / 2))) := by
        gcongr
        exact hcard.trans hL5
    _ = Real.exp (5 * Real.log L + Real.log L * (C₁ * (N + 1)) - L ^ (11 / 20 : ℝ) / 2) := by
        rw [Real.rpow_def_of_pos hL0, Real.exp_sub, Real.exp_add, Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log L * (-((E + 2) * N))) := Real.exp_le_exp.2 hexpo
    _ = L ^ (-((E + 2) * N)) := (Real.rpow_def_of_pos hL0 _).symm

/-! ### Low ranks -/

/-- **The low ranks**: for `N ≥ L^{1/2}`, `J ≤ L^{1/100}` and `Q ≤ L⁴`, the ranks `r < r₀`
cost in total at most `L^{-(E + 2) N}` when `G = E + 4`. -/
theorem eventually_lowRank_sum_le (K : ℕ) {C₀ Ce G E : ℝ} (hC₀ : 1 ≤ C₀) (hCe : 0 ≤ Ce)
    (hG : 0 ≤ G) (hGE : G = E + 4) :
    ∀ᶠ L : ℝ in atTop, ∀ N J Q : ℕ, L ^ (1 / 2 : ℝ) ≤ N → (J : ℝ) ≤ L ^ (1 / 100 : ℝ) →
      (Q : ℝ) ≤ L ^ 4 →
      ∑ r ∈ range ⌈L ^ (9 / 20 : ℝ)⌉₊, (Q : ℝ) ^ (2 * r) *
          (C₀ ^ (N + 1) * L ^ (-G * N + (Ce + G) * ((2 * r : ℕ) : ℝ)) * 2 ^ (K * (J + 1))) ≤
        L ^ (-((E + 2) * N)) := by
  set A := 2 * (Ce + G) + 8 with hA
  have hA0 : 0 ≤ A := by positivity
  filter_upwards [eventually_ge_atTop (16 : ℝ), eventually_ge_atTop (C₀ ^ 4),
    eventually_ge_atTop (Real.exp 1),
    eventually_mul_rpow_add_one_le 2 (show (0 : ℝ) ≤ 9 / 20 by norm_num)
      (show (9 / 20 : ℝ) < 1 / 2 by norm_num),
    eventually_mul_rpow_add_one_le (2 * K) (show (0 : ℝ) ≤ 1 / 100 by norm_num)
      (show (1 / 100 : ℝ) < 1 / 2 by norm_num),
    eventually_mul_rpow_add_one_le (2 * A) (show (0 : ℝ) ≤ 9 / 20 by norm_num)
      (show (9 / 20 : ℝ) < 1 / 2 by norm_num)]
    with L hL16 hLC hLe h₁ h₂ h₃ N J Q hN hJ hQ
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hLe
  have hlog0 : 0 ≤ Real.log L := by linarith
  obtain ⟨hr₀', hr₀⟩ := rankCut_bounds hL0.le
  set r₀ := ⌈L ^ (9 / 20 : ℝ)⌉₊
  have hr₀pos : (0 : ℝ) < r₀ := lt_of_lt_of_le (by positivity) hr₀'
  set s := L ^ (1 / 2 : ℝ) with hs
  have hs4 : 4 ≤ s := four_le_rpow_half hL16
  set n : ℝ := (N : ℝ) with hn
  have hn4 : 4 ≤ n := by linarith
  -- every term is at most `T = C₀^{N+1} 2^{K(J+1)} L^{-G n + A r₀}`
  set T := C₀ ^ (N + 1) * 2 ^ (K * (J + 1)) * L ^ (-G * n + A * r₀) with hT
  have hterm : ∀ r ∈ range r₀, (Q : ℝ) ^ (2 * r) *
      (C₀ ^ (N + 1) * L ^ (-G * n + (Ce + G) * ((2 * r : ℕ) : ℝ)) * 2 ^ (K * (J + 1))) ≤ T := by
    intro r hr
    have hr' : (r : ℝ) ≤ r₀ := by exact_mod_cast (mem_range.1 hr).le
    have hQr : (Q : ℝ) ^ (2 * r) ≤ L ^ ((8 * r : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      calc (Q : ℝ) ^ (2 * r) ≤ (L ^ 4) ^ (2 * r) := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ _
        _ = L ^ (8 * r) := by rw [← pow_mul]; ring_nf
    have hcomb : L ^ ((8 * r : ℕ) : ℝ) * L ^ (-G * n + (Ce + G) * ((2 * r : ℕ) : ℝ)) =
        L ^ (-G * n + A * r) := by
      rw [← Real.rpow_add hL0, hA]
      push_cast
      ring_nf
    have hexp : L ^ (-G * n + A * r) ≤ L ^ (-G * n + A * r₀) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by
        have := mul_le_mul_of_nonneg_left hr' hA0
        linarith)
    calc (Q : ℝ) ^ (2 * r) *
          (C₀ ^ (N + 1) * L ^ (-G * n + (Ce + G) * ((2 * r : ℕ) : ℝ)) * 2 ^ (K * (J + 1)))
        ≤ L ^ ((8 * r : ℕ) : ℝ) *
          (C₀ ^ (N + 1) * L ^ (-G * n + (Ce + G) * ((2 * r : ℕ) : ℝ)) * 2 ^ (K * (J + 1))) := by
          gcongr
      _ = C₀ ^ (N + 1) * 2 ^ (K * (J + 1)) *
          (L ^ ((8 * r : ℕ) : ℝ) * L ^ (-G * n + (Ce + G) * ((2 * r : ℕ) : ℝ))) := by ring
      _ ≤ T := by
          rw [hcomb, hT]
          gcongr
  -- the logarithm of `r₀ C₀^{N+1} 2^{K(J+1)} L^{A r₀}` is at most `2 n log L`
  have hlogC : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have e₁ : Real.log r₀ ≤ n / 2 * Real.log L := by
    have : Real.log r₀ ≤ r₀ := (Real.log_le_sub_one_of_pos hr₀pos).trans (by linarith)
    have : (r₀ : ℝ) ≤ n / 2 := by linarith
    calc Real.log r₀ ≤ n / 2 * 1 := by linarith
      _ ≤ n / 2 * Real.log L := mul_le_mul_of_nonneg_left hlog (by linarith)
  have e₂ : (N + 1 : ℝ) * Real.log C₀ ≤ n / 2 * Real.log L := by
    have h4 : 4 * Real.log C₀ ≤ Real.log L := by
      have : Real.log (C₀ ^ 4) = 4 * Real.log C₀ := by
        rw [Real.log_pow]
        norm_num
      rw [← this]
      exact Real.log_le_log (by positivity) hLC
    have hN1 : (N + 1 : ℝ) ≤ 2 * n := by linarith
    calc (N + 1 : ℝ) * Real.log C₀ ≤ 2 * n * Real.log C₀ :=
          mul_le_mul_of_nonneg_right hN1 hlogC
      _ = n / 2 * (4 * Real.log C₀) := by ring
      _ ≤ n / 2 * Real.log L := mul_le_mul_of_nonneg_left h4 (by linarith)
  have e₃ : ((K * (J + 1) : ℕ) : ℝ) * Real.log 2 ≤ n / 2 * Real.log L := by
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos two_pos]
    have hK : ((K * (J + 1) : ℕ) : ℝ) ≤ n / 2 := by
      push_cast
      have : (K : ℝ) * (J + 1) ≤ K * (L ^ (1 / 100 : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      linarith
    calc ((K * (J + 1) : ℕ) : ℝ) * Real.log 2 ≤ ((K * (J + 1) : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ ≤ n / 2 * 1 := by linarith
      _ ≤ n / 2 * Real.log L := mul_le_mul_of_nonneg_left hlog (by linarith)
  have e₄ : A * r₀ * Real.log L ≤ n / 2 * Real.log L := by
    have : A * r₀ ≤ n / 2 := by
      have : A * r₀ ≤ A * (L ^ (9 / 20 : ℝ) + 1) := mul_le_mul_of_nonneg_left hr₀ hA0
      linarith
    exact mul_le_mul_of_nonneg_right this hlog0
  have hfinal : (r₀ : ℝ) * T ≤ L ^ (-((E + 2) * n)) := by
    have hC₀N : C₀ ^ (N + 1) = Real.exp ((N + 1 : ℝ) * Real.log C₀) := by
      rw [← Real.exp_log (show 0 < C₀ ^ (N + 1) by positivity), Real.log_pow]
      push_cast
      rfl
    have h2 : (2 : ℝ) ^ (K * (J + 1)) = Real.exp (((K * (J + 1) : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    calc (r₀ : ℝ) * T = Real.exp (Real.log r₀ + (N + 1 : ℝ) * Real.log C₀ +
          ((K * (J + 1) : ℕ) : ℝ) * Real.log 2 + Real.log L * (-G * n + A * r₀)) := by
          rw [hT, hC₀N, h2, Real.rpow_def_of_pos hL0, Real.exp_add, Real.exp_add, Real.exp_add,
            Real.exp_log hr₀pos]
          ring
      _ ≤ Real.exp (Real.log L * (-((E + 2) * n))) := by
          refine Real.exp_le_exp.2 ?_
          rw [hGE]
          linarith
      _ = L ^ (-((E + 2) * n)) := (Real.rpow_def_of_pos hL0 _).symm
  calc ∑ r ∈ range r₀, (Q : ℝ) ^ (2 * r) *
        (C₀ ^ (N + 1) * L ^ (-G * n + (Ce + G) * ((2 * r : ℕ) : ℝ)) * 2 ^ (K * (J + 1)))
      ≤ ∑ _r ∈ range r₀, T := sum_le_sum hterm
    _ = r₀ * T := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ L ^ (-((E + 2) * n)) := hfinal

end Erdos408.OneSided
