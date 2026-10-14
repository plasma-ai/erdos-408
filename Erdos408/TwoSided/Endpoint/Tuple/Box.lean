module

public import Erdos408.OneSided.Major.Energy.Mean
public import Erdos408.TwoSided.Endpoint.Tuple.Asymp
public import Erdos408.TwoSided.Endpoint.Tuple.Exceptional
public import Erdos408.TwoSided.Endpoint.Tuple.Gram
public import Erdos408.TwoSided.Endpoint.Tuple.Mark
public import Erdos408.TwoSided.Endpoint.Tuple.Mean
public import Erdos408.TwoSided.Endpoint.Tuple.Twist

/-!
# The mean square of one box (tuple part)

S15–S18 of `blueprint/two_sided_correlation.md` §§6.3–6.6 for one box, one pair of classes
and one character (PD (6.35)–(6.38)). The box polynomial is
`G(τ) = P_s(τ) · (P/Y) P_l(τ) R(τ)` with
`P_s = (PV)⁻¹ ∑_{p_s ∈ (P, 2P]} p_s^{iτ}`, `P_l = ∑_{p_l ∈ (lo, hi]} χ(p_l) p_l^{iτ}` and
`R = ∑_{u ∈ (R, 2R]} c_u u^{iτ}`; the scales satisfy `PNR ≤ 2Y`.

* `boxMeanValue_le`: the mean value of `Q = (P/Y) P_l R`, collapsed at scale `4NR`, over an
  interval of length `≤ 2T₀` is `≤ L^{2C_U + 5}` (the coefficients are `≤ (P/Y) L^{C_U} ω(n)`).
* `integral_boxPoly_le`: the trivial bound `∫ |G|² ≤ (2/v₋)² L^{2C_U + 5}`, since
  `|P_s| ≤ 2/v₋`.

The bound under AP1 and AP2, `eventually_integral_boxPoly_le_of_twist`, is in
`Tuple/Sparse.lean`.
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset MeasureTheory

/-- The polynomial of one box, `G = P_s · (P/Y) P_l R`. -/
noncomputable def boxPoly (Y P V : ℝ) (sP spN uR : Finset ℕ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (c : ℕ → ℂ) (τ : ℝ) : ℂ :=
  (∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((τ : ℂ) * Complex.I)) *
    (((P / Y : ℝ) : ℂ) * ((∑ p ∈ spN, χ p * (p : ℂ) ^ ((τ : ℂ) * Complex.I)) *
      ∑ u ∈ uR, c u * (u : ℂ) ^ ((τ : ℂ) * Complex.I)))

/-- The box polynomial is continuous when its sets avoid `0`. -/
theorem continuous_boxPoly {Y P V : ℝ} {sP spN uR : Finset ℕ} (hsP : ∀ n ∈ sP, 0 < n)
    (hspN : ∀ n ∈ spN, 0 < n) (huR : ∀ n ∈ uR, 0 < n) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (c : ℕ → ℂ) : Continuous (boxPoly Y P V sP spN uR χ c) :=
  (continuous_sum_cpow (fun n hn => (hsP n hn).ne') _).mul (continuous_const.mul
    ((continuous_sum_cpow (fun n hn => (hspN n hn).ne') _).mul
      (continuous_sum_cpow (fun n hn => (huR n hn).ne') _)))

/-- `|c_l| ≤ U V ω(l)` for the coefficient `c_l = ∑_{mn = l} u_m v_n` of a product whose first
factor is supported on primes, `l ≠ 0`: `m` is a prime factor of `l`, and it determines `n`. -/
theorem norm_mulCoeff_le_primeFactors {I₁ I₂ : Finset ℕ} (hI₁ : ∀ m ∈ I₁, m.Prime)
    {u v : ℕ → ℂ} {U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (hu : ∀ m ∈ I₁, ‖u m‖ ≤ U)
    (hv : ∀ n ∈ I₂, ‖v n‖ ≤ V) {l : ℕ} (hl : l ≠ 0) :
    ‖OneSided.mulCoeff I₁ I₂ u v l‖ ≤ U * V * #l.primeFactors := by
  have hcard : #{mn ∈ I₁ ×ˢ I₂ | mn.1 * mn.2 = l} ≤ #l.primeFactors := by
    refine card_le_card_of_injOn Prod.fst (fun mn hmn => ?_) fun mn hmn mn' hmn' h => ?_
    · rw [mem_coe, mem_filter, mem_product] at hmn
      exact Nat.mem_primeFactors.2 ⟨hI₁ _ hmn.1.1, ⟨mn.2, hmn.2.symm⟩, hl⟩
    · rw [mem_coe, mem_filter, mem_product] at hmn hmn'
      have h₁ : 0 < mn.1 := (hI₁ _ hmn.1.1).pos
      have h₂ : mn.1 * mn.2 = mn.1 * mn'.2 := by rw [hmn.2, h, hmn'.2]
      exact Prod.ext h (Nat.eq_of_mul_eq_mul_left h₁ h₂)
  unfold OneSided.mulCoeff
  refine (norm_sum_le _ _).trans ?_
  calc ∑ mn ∈ I₁ ×ˢ I₂ with mn.1 * mn.2 = l, ‖u mn.1 * v mn.2‖
      ≤ ∑ mn ∈ I₁ ×ˢ I₂ with mn.1 * mn.2 = l, U * V := by
        refine sum_le_sum fun mn hmn => ?_
        rw [mem_filter, mem_product] at hmn
        rw [norm_mul]
        exact mul_le_mul (hu _ hmn.1.1) (hv _ hmn.1.2) (norm_nonneg _) hU
    _ = #{mn ∈ I₁ ×ˢ I₂ | mn.1 * mn.2 = l} * (U * V) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ #l.primeFactors * (U * V) := by
        gcongr
    _ = U * V * #l.primeFactors := by ring

/-- `(P/Y) P_l R = Q` is the Dirichlet polynomial of length `N₁ N₂` with coefficients
`mulCoeff`, for `spN ⊆ [1, N₁]` and `uR ⊆ [1, N₂]`. -/
theorem mul_sum_mul_sum_eq {spN uR : Finset ℕ} {N₁ N₂ : ℕ}
    (h₁ : ∀ m ∈ spN, 1 ≤ m ∧ m ≤ N₁) (h₂ : ∀ n ∈ uR, 1 ≤ n ∧ n ≤ N₂) (z : ℂ) {k : ℕ}
    (χ : DirichletCharacter ℂ k) (c : ℕ → ℂ) (τ : ℝ) :
    z * ((∑ p ∈ spN, χ p * (p : ℂ) ^ ((τ : ℂ) * Complex.I)) *
        ∑ u ∈ uR, c u * (u : ℂ) ^ ((τ : ℂ) * Complex.I)) =
      ∑ n ∈ Icc 1 (N₁ * N₂), OneSided.mulCoeff spN uR (fun p => z * χ p) c n *
        (n : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  rw [← OneSided.sum_mul_sum_eq h₁ h₂, ← mul_assoc]
  congr 1
  rw [mul_sum]
  simp_rw [mul_assoc]

/-- **The mean value of one box.** For `Q(τ) = ∑_{n ≤ N_q} q_n n^{iτ}` with
`|q_n| ≤ (P/Y) L^{C_U} · 2 log n`, `N_q ≤ 4NR`, `PNR ≤ 2Y`, `log N_q ≤ 2L` and
`(τ₂ - τ₁) P ≤ Y`: `(τ₂ - τ₁ + 8N_q(1 + log N_q)) ∑ |q_n|² ≤ L^{2C_U + 5}` once `L ≥ 160`. -/
theorem boxMeanValue_le {L Y P N R CU τ₁ τ₂ : ℝ} (hL : 160 ≤ L) (hY : 0 < Y) (hP : 0 < P)
    (hPNR : P * N * R ≤ 2 * Y) {Nq : ℕ} (hNq : (Nq : ℝ) ≤ 4 * N * R)
    (hlog : Real.log Nq ≤ 2 * L) (h₁₂ : τ₁ ≤ τ₂) (hτ : (τ₂ - τ₁) * P ≤ Y) {cq : ℕ → ℂ}
    (hcq : ∀ n ∈ Icc 1 Nq, ‖cq n‖ ≤ P / Y * L ^ CU * (2 * Real.log n)) :
    (τ₂ - τ₁ + 8 * Nq * (1 + Real.log Nq)) * ∑ n ∈ Icc 1 Nq, ‖cq n‖ ^ 2 ≤
      L ^ (2 * CU + 5) := by
  have hL0 : 0 < L := by linarith
  set B := P / Y * L ^ CU * (4 * L) with hB
  have hB0 : 0 ≤ B := by positivity
  -- `∑ |q_n|² ≤ N_q B²`
  have hsum : ∑ n ∈ Icc 1 Nq, ‖cq n‖ ^ 2 ≤ Nq * B ^ 2 := by
    calc ∑ n ∈ Icc 1 Nq, ‖cq n‖ ^ 2 ≤ ∑ _n ∈ Icc 1 Nq, B ^ 2 := by
          refine sum_le_sum fun n hn => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine (hcq n hn).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
          have hn1 : 1 ≤ n := (mem_Icc.1 hn).1
          have : Real.log n ≤ Real.log Nq :=
            Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast (mem_Icc.1 hn).2)
          linarith
      _ = Nq * B ^ 2 := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  -- `N_q (P/Y) ≤ 8` and `N_q (P/Y)² ≤ 8 P/Y`
  have hNqP : (Nq : ℝ) * (P / Y) ≤ 8 := by
    rw [mul_div_assoc', div_le_iff₀ hY]
    nlinarith [Nat.cast_nonneg (α := ℝ) Nq]
  have hlog0 : 0 ≤ Real.log Nq := Real.log_natCast_nonneg Nq
  have hNq0 : (0 : ℝ) ≤ Nq := Nat.cast_nonneg _
  have hPY : 0 ≤ P / Y := by positivity
  set W := L ^ CU * (4 * L) with hW
  have hBW : B = P / Y * W := by rw [hB, hW]; ring
  have hW2 : W ^ 2 = 16 * L ^ (2 * CU + 2) := by
    have e₁ : (L ^ CU) ^ 2 = L ^ (2 * CU) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      ring_nf
    rw [hW, mul_pow, e₁, Real.rpow_add hL0, Real.rpow_two]
    ring
  -- the two terms
  have h₁ : (τ₂ - τ₁) * (Nq * B ^ 2) ≤ 8 * W ^ 2 := by
    rw [hBW]
    have : (τ₂ - τ₁) * (Nq * (P / Y * W) ^ 2) = ((τ₂ - τ₁) * (P / Y)) * (Nq * (P / Y)) * W ^ 2 :=
      by ring
    rw [this]
    have hτ' : (τ₂ - τ₁) * (P / Y) ≤ 1 := by
      rw [mul_div_assoc', div_le_one hY]
      exact hτ
    have : 0 ≤ (τ₂ - τ₁) * (P / Y) := mul_nonneg (by linarith) hPY
    have : (τ₂ - τ₁) * (P / Y) * (Nq * (P / Y)) ≤ 1 * 8 :=
      mul_le_mul hτ' hNqP (by positivity) zero_le_one
    nlinarith [sq_nonneg W]
  have h₂ : 8 * Nq * (1 + Real.log Nq) * (Nq * B ^ 2) ≤ 512 * (1 + 2 * L) * W ^ 2 := by
    rw [hBW]
    have : 8 * Nq * (1 + Real.log Nq) * (Nq * (P / Y * W) ^ 2) =
        8 * (1 + Real.log Nq) * (Nq * (P / Y)) ^ 2 * W ^ 2 := by ring
    rw [this]
    have hsq : (Nq * (P / Y)) ^ 2 ≤ 64 := by
      have : 0 ≤ (Nq : ℝ) * (P / Y) := by positivity
      nlinarith
    have : 8 * (1 + Real.log Nq) * (Nq * (P / Y)) ^ 2 ≤ 8 * (1 + 2 * L) * 64 :=
      mul_le_mul (by linarith) hsq (by positivity) (by positivity)
    nlinarith [sq_nonneg W]
  have hL5 : L ^ (2 * CU + 5) = L ^ (2 * CU + 2) * L ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    norm_num
    ring_nf
  have hL2 : 0 ≤ L ^ (2 * CU + 2) := by positivity
  calc (τ₂ - τ₁ + 8 * Nq * (1 + Real.log Nq)) * ∑ n ∈ Icc 1 Nq, ‖cq n‖ ^ 2
      ≤ (τ₂ - τ₁ + 8 * Nq * (1 + Real.log Nq)) * (Nq * B ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 8 * W ^ 2 + 512 * (1 + 2 * L) * W ^ 2 := by rw [add_mul]; linarith
    _ = (8 + 512 * (1 + 2 * L)) * 16 * L ^ (2 * CU + 2) := by rw [hW2]; ring
    _ ≤ L ^ (2 * CU + 5) := by
        rw [hL5]
        have : (8 + 512 * (1 + 2 * L)) * 16 ≤ L ^ 3 := by
          have : (160 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
          nlinarith
        nlinarith

/-- `|P_s| ≤ 2/v₋` for primes in `(P, 2P]`, `P ≥ 1` and `V ≥ v₋ > 0`. -/
theorem norm_smallPoly_le {P V vlo : ℝ} (hP : 1 ≤ P) (hvlo : 0 < vlo) (hV : vlo ≤ V)
    {sP : Finset ℕ} (hsP : ∀ p ∈ sP, p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) (τ : ℝ) :
    ‖∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤ 2 / vlo := by
  have hP0 : 0 < P := by linarith
  have hV0 : 0 < V := by linarith
  have hsub : sP ⊆ Ioc ⌊P⌋₊ ⌊2 * P⌋₊ := fun p hp => by
    obtain ⟨-, h₁, h₂⟩ := hsP p hp
    rw [mem_Ioc]
    exact ⟨(Nat.floor_lt hP0.le).2 h₁, Nat.le_floor h₂⟩
  have hcard : (#sP : ℝ) ≤ P + 1 :=
    (Nat.cast_le.2 (card_le_card hsub)).trans (card_Ioc_floor_le hP0.le)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p ∈ sP, ‖(((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((τ : ℂ) * Complex.I)‖
      = #sP * (P * V)⁻¹ := by
        rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
        refine sum_congr rfl fun p hp => ?_
        rw [norm_mul, norm_natCast_cpow_ofReal_mul_I (hsP p hp).1.pos, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        simp
    _ ≤ (P + 1) * (P * V)⁻¹ := by gcongr
    _ ≤ 2 / vlo := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hvlo]
        nlinarith

/-- The data of one box, as hypotheses: `P ∈ [e^{L^{0.27}}/2, e^{L^{0.36}}]`,
`N, R ∈ [exp(L/T²²), x]`, `(lo, hi] ⊂ [N, 2N]`, `PNR ≤ 2Y`, `V ≥ v₋`, the small primes in
`(P, 2P]`, `uR ⊂ (⌊R⌋, ⌊2R⌋]` and `|c| ≤ L^{C_U}` on `uR`. -/
structure BoxData (x Cm CU vlo Y P N R V lo hi : ℝ) (sP uR : Finset ℕ) (k : ℕ)
    (c : ℕ → ℂ) : Prop where
  hY₁ : x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y
  hY₂ : Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ))
  hP₁ : Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P
  hP₂ : P ≤ Real.exp (Real.log x ^ (0.36 : ℝ))
  hN₁ : Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤ N
  hN₂ : N ≤ x
  hlo : N ≤ lo
  hhi : hi ≤ 2 * N
  hR₁ : Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤ R
  hR₂ : R ≤ x
  hPNR : P * N * R ≤ 2 * Y
  hV : vlo ≤ V
  hk₁ : 1 ≤ k
  hk₂ : (k : ℝ) ≤ Real.log x ^ Cm
  hsP : ∀ p ∈ sP, p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P
  huR : uR ⊆ Ioc ⌊R⌋₊ ⌊2 * R⌋₊
  hc : ∀ u ∈ uR, ‖c u‖ ≤ Real.log x ^ CU

/-- `⌊a⌋₊ ≤ b` for `a ≤ b` and `b ≥ 0`. -/
theorem natFloor_le_of_le {a b : ℝ} (h : a ≤ b) (hb : 0 ≤ b) : (⌊a⌋₊ : ℝ) ≤ b := by
  rcases le_or_gt 0 a with ha | ha
  · exact (Nat.floor_le ha).trans h
  · rw [Nat.floor_of_nonpos ha.le, Nat.cast_zero]
    exact hb

/-- The growth facts of one box: `L ≥ 160`, `x ≥ 2`, `4 L^{C_m + 2} e^{L^{0.36}} ≤ e^{L^{0.38}}`
(so `4 T₀ P ≤ Y`), `16 e^{L^{0.47}} ≤ x` (so `log(8Y/P) ≤ 2L`) and `L^{C_m + 3} ≤ x`. -/
def BoxScales (Cm x : ℝ) : Prop :=
  160 ≤ Real.log x ∧ 2 ≤ x ∧
    4 * Real.log x ^ (Cm + 2) * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤
      Real.exp (Real.log x ^ (0.38 : ℝ)) ∧
    16 * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ x ∧ Real.log x ^ (Cm + 3) ≤ x

/-- The growth facts of one box hold eventually. -/
theorem eventually_boxScales (Cm : ℝ) : ∀ᶠ x : ℝ in atTop, BoxScales Cm x := by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 160, eventually_ge_atTop 2,
    eventually_mul_rpow_mul_exp_le_exp (by norm_num : (0 : ℝ) ≤ 0.36)
      (by norm_num : (0.36 : ℝ) < 0.38) (Cm + 2) 4,
    eventually_mul_rpow_mul_exp_le_exp (by norm_num : (0 : ℝ) ≤ 0.47)
      (by norm_num : (0.47 : ℝ) < 1) 0 16,
    eventually_log_rpow_le_self (Cm + 3), eventually_gt_atTop 0] with x hL hx h₁ h₂ h₃ hx0
  refine ⟨hL, hx, h₁, ?_, h₃⟩
  rw [Real.rpow_zero, mul_one, Real.rpow_one, Real.exp_log hx0] at h₂
  exact h₂

/-- The scales of one box: `T₀ ≥ 1`, `4 T₀ P ≤ Y`, `2 T₀ ≤ x³`, `Y ≤ x²` and
`log N_q ≤ 2L` for `N_q ≤ 4NR`. -/
theorem boxScales_of {x Cm CU vlo Y P N R V lo hi : ℝ} {sP uR : Finset ℕ} {k : ℕ} {c : ℕ → ℂ}
    (hCm : 0 ≤ Cm) (hd : BoxData x Cm CU vlo Y P N R V lo hi sP uR k c)
    (hs : BoxScales Cm x) :
    1 ≤ x * Real.log x ^ (Cm + 2) ∧ 4 * (x * Real.log x ^ (Cm + 2)) * P ≤ Y ∧
      2 * (x * Real.log x ^ (Cm + 2)) ≤ x ^ 3 ∧ Y ≤ x ^ 2 ∧
      ∀ Nq : ℕ, (Nq : ℝ) ≤ 4 * N * R → Real.log Nq ≤ 2 * Real.log x := by
  obtain ⟨hL, hx, h₁, h₂, h₃⟩ := hs
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hLC : 1 ≤ L ^ (Cm + 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hLC' : L ^ (Cm + 2) ≤ x := by
    refine le_trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) h₃
  have he₁ : 1 ≤ Real.exp (L ^ (0.27 : ℝ)) := Real.one_le_exp (by positivity)
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hd.hP₁
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hd.hY₁
  have hexp : Real.exp (L ^ (0.47 : ℝ)) ≤ x := by
    have := Real.exp_pos (L ^ (0.47 : ℝ))
    linarith
  refine ⟨by nlinarith, ?_, ?_, ?_, ?_⟩
  · calc 4 * (x * L ^ (Cm + 2)) * P ≤ 4 * (x * L ^ (Cm + 2)) * Real.exp (L ^ (0.36 : ℝ)) :=
          mul_le_mul_of_nonneg_left hd.hP₂ (by positivity)
      _ = x * (4 * L ^ (Cm + 2) * Real.exp (L ^ (0.36 : ℝ))) := by ring
      _ ≤ x * Real.exp (L ^ (0.38 : ℝ)) := mul_le_mul_of_nonneg_left h₁ hx0.le
      _ ≤ Y := hd.hY₁
  · have : 2 * (x * L ^ (Cm + 2)) ≤ 2 * (x * x) := by gcongr
    have : 2 * (x * x) ≤ x ^ 3 := by nlinarith
    linarith
  · calc Y ≤ x * Real.exp (L ^ (0.47 : ℝ)) := hd.hY₂
      _ ≤ x * x := mul_le_mul_of_nonneg_left hexp hx0.le
      _ = x ^ 2 := by ring
  · intro Nq hNq
    rcases Nat.eq_zero_or_pos Nq with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      positivity
    have hNR : 4 * N * R ≤ 8 * Y / P := by
      rw [le_div_iff₀ hP0]
      nlinarith [hd.hPNR]
    have hYP : 8 * Y / P ≤ x ^ 2 := by
      rw [div_le_iff₀ hP0]
      have : x * Real.exp (L ^ (0.47 : ℝ)) * 16 ≤ x * x := by nlinarith
      nlinarith [hd.hY₂, hd.hP₁]
    rw [show 2 * L = Real.log (x ^ 2) by rw [Real.log_pow]; push_cast; ring]
    exact Real.log_le_log (by exact_mod_cast hpos) (hNq.trans (hNR.trans hYP))

/-- The collapsed coefficients `q_n` of `Q = (P/Y) P_l R`. -/
noncomputable def boxCoeff (Y P : ℝ) (spN uR : Finset ℕ) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (c : ℕ → ℂ) : ℕ → ℂ :=
  OneSided.mulCoeff spN uR (fun p => ((P / Y : ℝ) : ℂ) * χ p) c

/-- `G = P_s Q` with `Q = ∑_{n ≤ N_q} q_n n^{iτ}`, `N_q = ⌊hi⌋ ⌊2R⌋`. -/
theorem boxPoly_eq {x Cm CU vlo Y P N R V lo hi : ℝ} {sP uR : Finset ℕ} {k : ℕ} {c : ℕ → ℂ}
    (hd : BoxData x Cm CU vlo Y P N R V lo hi sP uR k c) (χ : DirichletCharacter ℂ k) (τ : ℝ) :
    boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c τ =
      (∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((τ : ℂ) * Complex.I)) *
        ∑ n ∈ Icc 1 (⌊hi⌋₊ * ⌊2 * R⌋₊),
          boxCoeff Y P ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c n *
            (n : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  rw [boxPoly, boxCoeff, mul_sum_mul_sum_eq]
  · intro m hm
    rw [mem_filter, mem_Ioc] at hm
    omega
  · intro n hn
    have := hd.huR hn
    rw [mem_Ioc] at this
    omega

/-- The mean value of `Q` over an interval of length `≤ 4T₀` is `≤ L^{2C_U + 5}`. -/
theorem boxMeanValue_le' {x Cm CU vlo Y P N R V lo hi : ℝ} {sP uR : Finset ℕ} {k : ℕ}
    {c : ℕ → ℂ} (hCm : 0 ≤ Cm) (hd : BoxData x Cm CU vlo Y P N R V lo hi sP uR k c)
    (hs : BoxScales Cm x) (χ : DirichletCharacter ℂ k) {τ₁ τ₂ : ℝ} (h₁₂ : τ₁ ≤ τ₂)
    (hlen : τ₂ - τ₁ ≤ 4 * (x * Real.log x ^ (Cm + 2))) :
    (τ₂ - τ₁ + 8 * (⌊hi⌋₊ * ⌊2 * R⌋₊ : ℕ) * (1 + Real.log (⌊hi⌋₊ * ⌊2 * R⌋₊ : ℕ))) *
        ∑ n ∈ Icc 1 (⌊hi⌋₊ * ⌊2 * R⌋₊),
          ‖boxCoeff Y P ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c n‖ ^ 2 ≤
      Real.log x ^ (2 * CU + 5) := by
  obtain ⟨hT₀, hT₀P, -, -, hlog⟩ := boxScales_of hCm hd hs
  have hL := hs.1
  have hx0 : 0 < x := by linarith [hs.2.1]
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hd.hP₁
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hd.hY₁
  have hN0 : 0 < N := lt_of_lt_of_le (Real.exp_pos _) hd.hN₁
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hd.hR₁
  have hNq : ((⌊hi⌋₊ * ⌊2 * R⌋₊ : ℕ) : ℝ) ≤ 4 * N * R := by
    push_cast
    have h₁ : (⌊hi⌋₊ : ℝ) ≤ 2 * N := natFloor_le_of_le hd.hhi (by positivity)
    have h₂ : (⌊2 * R⌋₊ : ℝ) ≤ 2 * R := Nat.floor_le (by positivity)
    calc (⌊hi⌋₊ : ℝ) * ⌊2 * R⌋₊ ≤ 2 * N * (2 * R) :=
          mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (by positivity)
      _ = 4 * N * R := by ring
  refine boxMeanValue_le hL hY0 hP0 hd.hPNR hNq (hlog _ hNq) h₁₂ ?_ ?_
  · nlinarith
  · intro n hn
    have hn0 : n ≠ 0 := by rw [mem_Icc] at hn; omega
    refine (norm_mulCoeff_le_primeFactors (U := P / Y) (V := Real.log x ^ CU)
      (fun m hm => (mem_filter.1 hm).2) (by positivity) (by positivity) (fun m _ => ?_)
      (fun u hu => hd.hc u hu) hn0).trans ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right (by positivity) (DirichletCharacter.norm_le_one χ _)
    · exact mul_le_mul_of_nonneg_left (card_primeFactors_le (Nat.one_le_iff_ne_zero.2 hn0))
        (by positivity : 0 ≤ P / Y * Real.log x ^ CU)

/-- **The trivial bound of one box.** `∫_{τ₁}^{τ₂} |G|² ≤ (2/v₋)² L^{2C_U + 5}` for
`τ₂ - τ₁ ≤ 4T₀`, since `|P_s| ≤ 2/v₋`. -/
theorem integral_boxPoly_le {x Cm CU vlo Y P N R V lo hi : ℝ} {sP uR : Finset ℕ} {k : ℕ}
    {c : ℕ → ℂ} (hvlo : 0 < vlo) (hCm : 0 ≤ Cm)
    (hd : BoxData x Cm CU vlo Y P N R V lo hi sP uR k c) (hs : BoxScales Cm x)
    (χ : DirichletCharacter ℂ k) {τ₁ τ₂ : ℝ} (h₁₂ : τ₁ ≤ τ₂)
    (hlen : τ₂ - τ₁ ≤ 4 * (x * Real.log x ^ (Cm + 2))) :
    ∫ τ in τ₁..τ₂, ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c τ‖ ^ 2 ≤
      (2 / vlo) ^ 2 * Real.log x ^ (2 * CU + 5) := by
  have hx0 : 0 < x := by linarith [hs.2.1]
  have hP1 : 1 ≤ P := le_trans (by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : 2 ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) := by
      have h := Real.add_one_le_exp (Real.log x ^ (0.27 : ℝ))
      have : 1 ≤ Real.log x ^ (0.27 : ℝ) :=
        Real.one_le_rpow (by linarith [hs.1]) (by norm_num)
      linarith
    linarith) hd.hP₁
  set Nq := ⌊hi⌋₊ * ⌊2 * R⌋₊
  set cq := boxCoeff Y P ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c
  have hQ : Continuous fun τ : ℝ =>
      ‖∑ n ∈ Icc 1 Nq, cq n * (n : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 :=
    (continuous_dirichletSum_Icc Nq cq).norm.pow 2
  have hG : Continuous fun τ : ℝ =>
      ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c τ‖ ^ 2 :=
    (continuous_boxPoly (fun p hp => (hd.hsP p hp).1.pos)
      (fun p hp => (mem_filter.1 hp).2.pos)
      (fun u hu => by have := hd.huR hu; rw [mem_Ioc] at this; omega) χ c).norm.pow 2
  calc ∫ τ in τ₁..τ₂, ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c τ‖ ^ 2
      ≤ ∫ τ in τ₁..τ₂, (2 / vlo) ^ 2 *
          ‖∑ n ∈ Icc 1 Nq, cq n * (n : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on h₁₂ (hG.intervalIntegrable _ _)
          ((hQ.const_mul _).intervalIntegrable _ _) fun τ _ => ?_
        rw [boxPoly_eq hd, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
          (norm_smallPoly_le hP1 hvlo hd.hV hd.hsP τ) 2) (by positivity)
    _ = (2 / vlo) ^ 2 * ∫ τ in τ₁..τ₂,
          ‖∑ n ∈ Icc 1 Nq, cq n * (n : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (2 / vlo) ^ 2 * Real.log x ^ (2 * CU + 5) := by
        refine mul_le_mul_of_nonneg_left ((OneSided.integral_norm_dirichlet_sq_le Nq cq τ₁ τ₂).trans
          ?_) (by positivity)
        exact boxMeanValue_le' hCm hd hs χ h₁₂ hlen

end Erdos408.TwoSided.TupleHigh
