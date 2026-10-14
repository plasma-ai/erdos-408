import Erdos408.Extraction.Defs
import Erdos408.Mertens

/-!
# Supporting estimates for the smoothed rectangle statistic

The elementary inputs of steps E0 and E11.

* Asymptotics of `L = log x`, `T = log L` and `s = log T`, and of the presieve
  parameters `h = 2 ⌈C_h s⌉`, `γ = (ε / 4) / (4h + 3)` and `J_c = ⌈C_j s⌉`:
  `γ⁻¹ ≤ T²²`, `z^{4h+2} ≤ x^{ε/4}`, `e^{-h} ≤ T^{-2 C_h}` and
  `2^{-J_c} ≤ T^{-C_j log 2}`.
* E0 size bounds: on `n ≤ x²` the slot count is at most `(2/ε)^{k+1}`, the
  harmonic mass `∑ 1/Q` is at most `(∑_{p ≤ x} 1/p)^{k+1}`, and there are at most
  `x^{∑ v}` slot tuples.
* Mertens: `∑_{p ≤ y} 1 / p ≤ log log y + O(1)`, the product bound
  `∏_{p ≤ y} (1 - 1/p) ≪ 1 / log y`, and the block mass bound
  `∑_{w < p ≤ w²} 1 / p = O(1)` required by `BlockSieve`.
-/

namespace Erdos408

open Filter Real Finset

namespace Sieve

/-! ### Asymptotics of `L`, `T` and `s` -/

/-- `T = log log x` tends to infinity. -/
lemma tendsto_logLog : Tendsto logLog atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_atTop

/-- `s = log log log x` tends to infinity. -/
lemma tendsto_logLogLog : Tendsto logLogLog atTop atTop :=
  tendsto_log_atTop.comp tendsto_logLog

/-- `exp T = L`. -/
lemma exp_logLog {x : ℝ} (hL : 0 < Real.log x) : exp (logLog x) = Real.log x :=
  exp_log hL

/-- `s ≤ T`. -/
lemma logLogLog_le_logLog {x : ℝ} (hT : 0 < logLog x) : logLogLog x ≤ logLog x := by
  have := log_le_sub_one_of_pos hT
  rw [logLogLog]
  linarith

/-- `T^a = exp (a s)`. -/
lemma logLog_rpow_eq {x : ℝ} (hT : 0 < logLog x) (a : ℝ) :
    logLog x ^ a = exp (a * logLogLog x) := by
  rw [rpow_def_of_pos hT, logLogLog, mul_comm]

/-- `L^a = exp (a T)`. -/
lemma log_rpow_eq {x : ℝ} (hL : 0 < Real.log x) (a : ℝ) :
    Real.log x ^ a = exp (a * logLog x) := by
  rw [rpow_def_of_pos hL, logLog, mul_comm]

/-- A fixed multiple of a power of `T` is eventually below any larger power. -/
lemma eventually_mul_rpow_le_rpow (C : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, C * logLog x ^ a ≤ logLog x ^ b := by
  filter_upwards [tendsto_logLog.eventually
      ((tendsto_rpow_atTop (sub_pos.2 hab)).eventually_ge_atTop C),
    tendsto_logLog.eventually_gt_atTop 0] with x hC hT
  have : logLog x ^ b = logLog x ^ (b - a) * logLog x ^ a := by
    rw [← rpow_add hT]
    ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hC (rpow_nonneg hT.le a)

/-- `L^c` eventually dominates any fixed multiple of any power of `T`. -/
lemma eventually_mul_rpow_le_log_rpow (C a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, C * logLog x ^ a ≤ Real.log x ^ c := by
  filter_upwards [tendsto_logLog.eventually
      ((tendsto_exp_mul_div_rpow_atTop a c hc).eventually_ge_atTop C),
    tendsto_logLog.eventually_gt_atTop 0, tendsto_log_atTop.eventually_gt_atTop 0]
    with x hC hT hL
  rw [log_rpow_eq hL]
  rwa [le_div_iff₀ (rpow_pos_of_pos hT a)] at hC

/-- `T` eventually dominates any fixed multiple of `s + 1`. -/
lemma eventually_mul_logLogLog_le (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * (logLogLog x + 1) ≤ logLog x := by
  filter_upwards [eventually_mul_rpow_le_rpow (3 * |C|) (show (1 / 2 : ℝ) < 1 by norm_num),
    tendsto_logLog.eventually_ge_atTop 1] with x hC hT1
  rw [rpow_one] at hC
  have hT0 : 0 < logLog x := by linarith
  have hs : logLogLog x ≤ 2 * logLog x ^ (1 / 2 : ℝ) := by
    have := log_le_rpow_div hT0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [logLogLog]
    linarith
  have hs0 : 0 ≤ logLogLog x := by
    rw [logLogLog]
    exact log_nonneg hT1
  have h1 : 1 ≤ logLog x ^ (1 / 2 : ℝ) := one_le_rpow hT1 (by norm_num)
  have h2 : C * (logLogLog x + 1) ≤ |C| * (logLogLog x + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have h3 : |C| * (logLogLog x + 1) ≤ |C| * (3 * logLog x ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
  linarith

/-! ### The presieve parameters -/

/-- The sieve depth is even. -/
lemma even_sieveDepth (Ch x : ℝ) : Even (sieveDepth Ch x) :=
  even_two_mul _

/-- Eventually the depth `h = 2 ⌈C_h s⌉` exceeds any fixed bound, and
`e^{-h} ≤ T^{-2 C_h}`. -/
lemma eventually_sieveDepth {Ch : ℝ} (hCh : 0 < Ch) (h₀ : ℕ) : ∀ᶠ x : ℝ in atTop,
    h₀ ≤ sieveDepth Ch x ∧ 2 ≤ sieveDepth Ch x ∧
      exp (-(sieveDepth Ch x : ℝ)) ≤ logLog x ^ (-(2 * Ch)) := by
  filter_upwards [tendsto_logLogLog.eventually_ge_atTop ((h₀ + 1) / Ch),
    tendsto_logLog.eventually_gt_atTop 0] with x hs hT
  have hs0 : 0 ≤ logLogLog x := le_trans (by positivity) hs
  have hceil : Ch * logLogLog x ≤ ⌈Ch * logLogLog x⌉₊ := Nat.le_ceil _
  have hh : (2 : ℝ) * (Ch * logLogLog x) ≤ sieveDepth Ch x := by
    rw [sieveDepth]
    push_cast
    linarith
  have hCs : (h₀ : ℝ) + 1 ≤ Ch * logLogLog x := by
    rwa [div_le_iff₀ hCh, mul_comm] at hs
  refine ⟨?_, ?_, ?_⟩
  · have : (h₀ : ℝ) ≤ sieveDepth Ch x := by nlinarith
    exact_mod_cast this
  · have h1 : 1 ≤ ⌈Ch * logLogLog x⌉₊ := by
      rw [Nat.one_le_ceil_iff]
      linarith [(Nat.cast_nonneg h₀ : (0 : ℝ) ≤ h₀)]
    rw [sieveDepth]
    omega
  · rw [logLog_rpow_eq hT]
    exact exp_le_exp.2 (by linarith)

/-- The presieve parameters for large `x`: `0 < γ ≤ 1`, `γ⁻¹ ≤ T²²` and
`γ (4h + 2) ≤ ε / 4`, so that the sieve level `z^{4h+2}` is at most `x^{ε/4}`. -/
lemma eventually_presieveExponent {c Ch : ℝ} (hc : 0 < c) (hCh : 0 < Ch) : ∀ᶠ x : ℝ in atTop,
    0 < presieveExponent c Ch x ∧ presieveExponent c Ch x ≤ 1 ∧
      1 / presieveExponent c Ch x ≤ logLog x ^ 22 ∧
      presieveExponent c Ch x * (4 * sieveDepth Ch x + 2) ≤ c / logLog x ^ 20 / 4 := by
  filter_upwards [tendsto_logLog.eventually_ge_atTop (4 * (8 * Ch + 11) / c + 1),
    tendsto_logLog.eventually_ge_atTop c, tendsto_logLog.eventually_ge_atTop 1]
    with x hT hTc hT1
  have hγ : presieveExponent c Ch x =
      c / (4 * logLog x ^ 20 * (4 * (sieveDepth Ch x : ℝ) + 3)) := by
    rw [presieveExponent, div_div, div_div]
    ring_nf
  rw [hγ]
  set T := logLog x
  set h := sieveDepth Ch x
  have hT0 : 0 < T := by linarith
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  -- `h ≤ 2 C_h s + 2 ≤ 2 C_h T + 2`
  have hh : (h : ℝ) ≤ 2 * Ch * T + 2 := by
    have hs0 : 0 ≤ logLogLog x := by
      rw [logLogLog]
      exact log_nonneg hT1
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ Ch * logLogLog x by positivity)
    have h2 : (h : ℝ) = 2 * ⌈Ch * logLogLog x⌉₊ := by simp [h, sieveDepth]
    have h3 := logLogLog_le_logLog hT0
    nlinarith
  have hT20 : 0 < T ^ 20 := by positivity
  have hTT : T ≤ T ^ 20 := le_self_pow₀ hT1 (by norm_num)
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    nlinarith
  · rw [one_div_div, div_le_iff₀ hc]
    -- `4 (4h + 3) ≤ c T²`
    have hcT : 4 * (4 * (h : ℝ) + 3) ≤ c * T ^ 2 := by
      have h1 : 4 * (8 * Ch + 11) ≤ c * (T - 1) := by
        have := (div_le_iff₀ hc).1 (show 4 * (8 * Ch + 11) / c ≤ T - 1 by linarith)
        linarith
      nlinarith
    calc 4 * T ^ 20 * (4 * h + 3) = T ^ 20 * (4 * (4 * h + 3)) := by ring
      _ ≤ T ^ 20 * (c * T ^ 2) := by gcongr
      _ = T ^ 22 * c := by ring
  · rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hc hT20]

/-- The composite cutoff satisfies `J_c ≥ C_j s` and `2^{-J_c} ≤ T^{-C_j log 2}`. -/
lemma two_pow_neg_compositeCutoff_le {Cj x : ℝ} (hT : 0 < logLog x) :
    ((2 : ℝ) ^ compositeCutoff Cj x)⁻¹ ≤ logLog x ^ (-(Cj * Real.log 2)) := by
  have h2 : (2 : ℝ) ^ compositeCutoff Cj x = exp (compositeCutoff Cj x * Real.log 2) := by
    rw [← rpow_natCast, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  rw [logLog_rpow_eq hT, h2, ← exp_neg]
  apply exp_le_exp.2
  have hJ : Cj * logLogLog x ≤ compositeCutoff Cj x := Nat.le_ceil _
  have hl : 0 < Real.log 2 := log_pos (by norm_num)
  nlinarith

/-! ### Mertens' theorems -/

/-- Sums over `primesIoc 1 y` are sums over the primes of `(0, y]`. -/
lemma sum_primesIoc_one_eq (f : ℕ → ℝ) (y : ℝ) :
    ∑ p ∈ primesIoc 1 y, f p = ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, f p := by
  congr 1
  ext p
  simp only [primesIoc, Nat.floor_one, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨⟨hp.pos, h⟩, hp⟩
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨⟨hp.one_lt, h⟩, hp⟩

/-- Mertens' second theorem with the constant absorbed: for `y ≥ 2`,
`|∑_{p ≤ y} 1 / p - log log y| ≤ E`. -/
lemma abs_sum_inv_primes_sub_le : ∃ E : ℝ, 0 ≤ E ∧ ∀ y : ℝ, 2 ≤ y →
    |∑ p ∈ primesIoc 1 y, (1 : ℝ) / p - Real.log (Real.log y)| ≤ E := by
  obtain ⟨C, hC⟩ := Mertens.sum_prime_div_eq_log_log
  refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
  rw [sum_primesIoc_one_eq]
  exact (hC y hy).trans (le_max_left _ _)

/-- Mertens' product bound: `∏_{p ≤ y} (1 - 1 / p) ≤ C / log y` for `y ≥ 2`. -/
lemma prod_one_sub_inv_primes_le : ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
    ∏ p ∈ primesIoc 1 y, (1 - (1 : ℝ) / p) ≤ C / Real.log y := by
  obtain ⟨E, hE, h⟩ := abs_sum_inv_primes_sub_le
  refine ⟨exp E, exp_pos E, fun y hy => ?_⟩
  have hly : 0 < Real.log y := log_pos (by linarith)
  have hle : ∏ p ∈ primesIoc 1 y, (1 - (1 : ℝ) / p) ≤
      ∏ p ∈ primesIoc 1 y, exp (-((1 : ℝ) / p)) := by
    apply prod_le_prod₀
    · intro p hp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (mem_primesIoc.1 hp).1.one_lt.le
      rw [sub_nonneg, div_le_one (by linarith)]
      exact hp1
    · intro p _
      exact one_sub_le_exp_neg _
  rw [← exp_sum, sum_neg_distrib] at hle
  have := (abs_le.1 (h y hy)).1
  calc _ ≤ exp (-∑ p ∈ primesIoc 1 y, (1 : ℝ) / p) := hle
    _ ≤ exp (E - Real.log (Real.log y)) := exp_le_exp.2 (by linarith)
    _ = exp E / Real.log y := by rw [exp_sub, exp_log hly]

/-- The block mass `∑_{w < p ≤ w²} 1 / p` over all primes is bounded, as
`BlockSieve` requires. -/
lemma sum_inv_primes_block_le : ∃ C₀ : ℝ, ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ w : ℝ,
    1 < w → ∑ p ∈ P.filter (fun p : ℕ => w < p ∧ (p : ℝ) ≤ w ^ 2), (1 : ℝ) / p ≤ C₀ := by
  obtain ⟨E, hE, h⟩ := mertens_second
  refine ⟨Real.log 2 + E / Real.log 2 + 1, fun P hP w hw => ?_⟩
  have hl2 : 0 < Real.log 2 := log_pos (by norm_num)
  -- compare with the sum over `primesIoc w w²`
  have hsub : P.filter (fun p : ℕ => w < p ∧ (p : ℝ) ≤ w ^ 2) ⊆ primesIoc w (w ^ 2) := by
    intro p hp
    obtain ⟨hpP, hlo, hhi⟩ := mem_filter.1 hp
    exact mem_primesIoc.2 ⟨hP p hpP, hlo, hhi⟩
  have hnn : ∀ p ∈ primesIoc w (w ^ 2), 0 ≤ (1 : ℝ) / p := fun p _ => by positivity
  refine (sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp).trans ?_
  rcases lt_or_ge w 2 with hw2 | hw2
  · -- `(w, w²] ⊆ (1, 4]`, which contains only the primes `2` and `3`
    have hsub' : primesIoc w (w ^ 2) ⊆ {2, 3} := by
      intro p hp
      obtain ⟨hp, hlo, hhi⟩ := mem_primesIoc.1 hp
      have h4 : (p : ℝ) < 4 := by nlinarith
      have h4' : p < 4 := by exact_mod_cast h4
      have h2 := hp.two_le
      interval_cases p
      · simp
      · simp
    refine (sum_le_sum_of_subset_of_nonneg hsub' fun p _ _ => by positivity).trans ?_
    rw [sum_pair (by norm_num)]
    have : 0 ≤ E / Real.log 2 := div_nonneg hE hl2.le
    have : (0.6931471803 : ℝ) < Real.log 2 := log_two_gt_d9
    norm_num
    linarith
  · have hw0 : 0 < Real.log w := log_pos hw
    have := h w (w ^ 2) hw2 (by nlinarith)
    rw [Real.log_pow, Nat.cast_ofNat, mul_div_assoc, div_self hw0.ne', mul_one] at this
    have hEw : E / Real.log w ≤ E / Real.log 2 :=
      div_le_div_of_nonneg_left hE hl2 (log_le_log (by norm_num) hw2)
    have := (abs_le.1 this).2
    linarith

/-- `∑_{p ≤ y} 1 / p ≤ T + E` for `2 ≤ y ≤ x`, where `T = log log x`. -/
lemma sum_inv_primes_le_logLog {E : ℝ}
    (hE : ∀ y : ℝ, 2 ≤ y → |∑ p ∈ primesIoc 1 y, (1 : ℝ) / p - Real.log (Real.log y)| ≤ E)
    {x y : ℝ} (hy : 2 ≤ y) (hyx : y ≤ x) :
    ∑ p ∈ primesIoc 1 y, (1 : ℝ) / p ≤ logLog x + E := by
  have h := (abs_le.1 (hE y hy)).2
  have hly : 0 < Real.log y := log_pos (by linarith)
  have : Real.log (Real.log y) ≤ logLog x :=
    log_le_log hly (log_le_log (by linarith) hyx)
  linarith

/-! ### Size bounds for the slot statistic (E0) -/

/-- Membership in `slotTuples`. -/
lemma mem_slotTuples {x : ℝ} {k : ℕ} {u v : Fin k → ℝ} {Q : Fin k → ℕ} :
    Q ∈ slotTuples x u v ↔
      (∀ i, Q i ≤ ⌊x ^ v i⌋₊ ∧ (Q i).Prime ∧ x ^ u i < Q i) ∧ Function.Injective Q := by
  simp [slotTuples]

/-- The slot count and the harmonic mean are linear in the coefficient. -/
lemma slotCount_sub {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) (B B' : (Fin k → ℕ) → ℝ) (n : ℕ) :
    slotCount x u v (fun Q => B Q - B' Q) n = slotCount x u v B n - slotCount x u v B' n := by
  simp only [slotCount, sum_sub_distrib]

/-- The harmonic mean is linear in the coefficient. -/
lemma slotMean_sub {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) (B B' : (Fin k → ℕ) → ℝ) :
    slotMean x u v (fun Q => B Q - B' Q) = slotMean x u v B - slotMean x u v B' := by
  simp only [slotMean, sub_div, sum_sub_distrib]

/-- A nonnegative coefficient has a nonnegative slot count. -/
lemma slotCount_nonneg {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) {B : (Fin k → ℕ) → ℝ}
    (hB : ∀ Q, 0 ≤ B Q) (n : ℕ) : 0 ≤ slotCount x u v B n :=
  sum_nonneg fun _ _ => hB _

/-- A nonnegative coefficient has a nonnegative harmonic mean. -/
lemma slotMean_nonneg {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) {B : (Fin k → ℕ) → ℝ}
    (hB : ∀ Q, 0 ≤ B Q) : 0 ≤ slotMean x u v B :=
  sum_nonneg fun _ _ => div_nonneg (hB _) (prod_nonneg fun _ _ => Nat.cast_nonneg _)

/-- A slot tuple has product at most `x^{∑ v}`. -/
lemma prod_le_of_mem_slotTuples {x : ℝ} (hx : 0 < x) {k : ℕ} {u v : Fin k → ℝ}
    {Q : Fin k → ℕ} (hQ : Q ∈ slotTuples x u v) : ∏ i, (Q i : ℝ) ≤ x ^ ∑ i, v i := by
  rw [rpow_sum_of_pos hx]
  refine prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => ?_
  exact (Nat.cast_le.2 ((mem_slotTuples.1 hQ).1 i).1).trans (Nat.floor_le (by positivity))

/-- There are at most `x^{∑ v}` slot tuples. -/
lemma card_slotTuples_le {x : ℝ} (hx : 0 < x) {k : ℕ} (u v : Fin k → ℝ) :
    (#(slotTuples x u v) : ℝ) ≤ x ^ ∑ i, v i := by
  have h1 : #(slotTuples x u v) ≤ ∏ i, #((Iic ⌊x ^ v i⌋₊).filter
      fun q : ℕ => q.Prime ∧ x ^ u i < q) := by
    rw [← Fintype.card_piFinset]
    exact card_filter_le _ _
  have h2 : ∀ i, (#((Iic ⌊x ^ v i⌋₊).filter fun q : ℕ => q.Prime ∧ x ^ u i < q) : ℝ) ≤
      x ^ v i := by
    intro i
    have hsub : (Iic ⌊x ^ v i⌋₊).filter (fun q : ℕ => q.Prime ∧ x ^ u i < q) ⊆
        Icc 1 ⌊x ^ v i⌋₊ := by
      intro q hq
      simp only [mem_filter, mem_Iic] at hq
      exact mem_Icc.2 ⟨hq.2.1.one_lt.le, hq.1⟩
    have := card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact (Nat.cast_le.2 this).trans (Nat.floor_le (by positivity))
  calc (#(slotTuples x u v) : ℝ) ≤ ∏ i, (#((Iic ⌊x ^ v i⌋₊).filter
        fun q : ℕ => q.Prime ∧ x ^ u i < q) : ℝ) := by exact_mod_cast h1
    _ ≤ ∏ i, x ^ v i := prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => h2 i
    _ = x ^ ∑ i, v i := (rpow_sum_of_pos hx _ _).symm

/-- If `∑ v ≤ 1`, every slot tuple lies in the primes up to `x`. -/
lemma mem_piFinset_of_mem_slotTuples {x : ℝ} (hx : 1 < x) {k : ℕ} {u v : Fin k → ℝ}
    (hv : ∑ i, v i ≤ 1) {Q : Fin k → ℕ} (hQ : Q ∈ slotTuples x u v) :
    Q ∈ Fintype.piFinset fun _ => primesIoc 1 x := by
  rw [Fintype.mem_piFinset]
  intro i
  have hp := ((mem_slotTuples.1 hQ).1 i).2.1
  have hpos : ∀ j, 0 < Q j := fun j => ((mem_slotTuples.1 hQ).1 j).2.1.pos
  have hdvd : Q i ≤ ∏ j, Q j :=
    Nat.le_of_dvd (prod_pos fun j _ => hpos j) (dvd_prod_of_mem _ (mem_univ i))
  have hprod := prod_le_of_mem_slotTuples (by linarith) hQ
  have hle : (Q i : ℝ) ≤ x := by
    calc (Q i : ℝ) ≤ ((∏ j, Q j : ℕ) : ℝ) := by exact_mod_cast hdvd
      _ = ∏ j, (Q j : ℝ) := by push_cast; rfl
      _ ≤ x ^ ∑ j, v j := hprod
      _ ≤ x ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hx.le hv
      _ = x := rpow_one x
  exact mem_primesIoc_one.2 ⟨hp, hle⟩

/-- `∑_Q 1 / Q ≤ (∑_{p ≤ x} 1 / p)^{k}` when `∑ v ≤ 1`. -/
lemma sum_inv_slotTuples_le {x : ℝ} (hx : 1 < x) {k : ℕ} {u v : Fin k → ℝ}
    (hv : ∑ i, v i ≤ 1) :
    ∑ Q ∈ slotTuples x u v, 1 / ∏ i, (Q i : ℝ) ≤ (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ k := by
  have hsub : slotTuples x u v ⊆ Fintype.piFinset fun _ => primesIoc 1 x :=
    fun Q hQ => mem_piFinset_of_mem_slotTuples hx hv hQ
  calc ∑ Q ∈ slotTuples x u v, 1 / ∏ i, (Q i : ℝ)
      ≤ ∑ Q ∈ Fintype.piFinset (fun _ : Fin k => primesIoc 1 x), 1 / ∏ i, (Q i : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∑ Q ∈ Fintype.piFinset (fun _ : Fin k => primesIoc 1 x), ∏ i, (1 : ℝ) / Q i := by
        simp only [one_div, prod_inv_distrib]
    _ = ∏ _i : Fin k, ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p := 
        (prod_univ_sum (fun _ : Fin k => primesIoc 1 x) fun _ (p : ℕ) => (1 : ℝ) / p).symm
    _ = (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ k := by
        rw [prod_const, card_univ, Fintype.card_fin]

/-- The number of prime factors of `n ≤ x²` above `x^ε` is at most `2 / ε`. -/
lemma card_primeFactors_gt_le {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) {n : ℕ} (hn : 0 < n)
    (hnx : (n : ℝ) ≤ x ^ 2) :
    (#(n.primeFactors.filter fun p : ℕ => x ^ ε < (p : ℝ)) : ℝ) ≤ 2 / ε := by
  set P := n.primeFactors.filter fun p : ℕ => x ^ ε < (p : ℝ)
  have hdvd : ∏ p ∈ P, p ∣ n :=
    (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
  have hle : (∏ p ∈ P, (p : ℝ)) ≤ n := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hn hdvd
  have hlo : (x ^ ε) ^ #P ≤ ∏ p ∈ P, (p : ℝ) := by
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => by positivity) fun p hp => (mem_filter.1 hp).2.le
  have h : x ^ (ε * #P) ≤ x ^ (2 : ℝ) := by
    rw [rpow_mul (by linarith), rpow_natCast, rpow_two]
    linarith
  have := (rpow_le_rpow_left_iff hx).1 h
  rw [le_div_iff₀ hε]
  linarith

/-- The slot count at `0 < n ≤ x²` is at most `(2 / ε)^{k+1}` in absolute value, when
the lower slot endpoints exceed `x^ε` and `|𝔟| ≤ 1`. -/
lemma abs_slotCount_le {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) {k : ℕ} {u v : Fin (k + 1) → ℝ}
    (hu : ∀ i, ε ≤ u i) {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, |B Q| ≤ 1) {n : ℕ} (hn : 0 < n)
    (hnx : (n : ℝ) ≤ x ^ 2) : |slotCount x u v B n| ≤ (2 / ε) ^ (k + 1) := by
  set P := n.primeFactors.filter fun p : ℕ => x ^ ε < (p : ℝ)
  have hsub : (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n) ⊆
      Fintype.piFinset fun _ => P := by
    intro Q hQ
    obtain ⟨hQ, hdvd⟩ := mem_filter.1 hQ
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨-, hp, hlt⟩ := (mem_slotTuples.1 hQ).1 i
    refine mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, (dvd_prod_of_mem _ (mem_univ i)).trans hdvd,
      hn.ne'⟩, lt_of_le_of_lt (rpow_le_rpow_of_exponent_le hx.le (hu i)) hlt⟩
  calc |slotCount x u v B n|
      ≤ ∑ Q ∈ (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n), |B (Fin.init Q)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q ∈ (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n), (1 : ℝ) :=
        sum_le_sum fun _ _ => hB _
    _ ≤ #(Fintype.piFinset fun _ : Fin (k + 1) => P) := by
        rw [sum_const, nsmul_one]
        exact_mod_cast card_le_card hsub
    _ = (#P : ℝ) ^ (k + 1) := by rw [Fintype.card_piFinset]; simp
    _ ≤ (2 / ε) ^ (k + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _)
        (card_primeFactors_gt_le hx hε hn hnx) _

end Sieve

end Erdos408
