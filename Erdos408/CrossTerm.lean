module

public import Erdos408.Mertens

/-!
# The harmonic cross term

Summing over the first prime gives the exact identity

  `D(x) = ∑_{q ≤ x} (F q / q) (B(x / q) - [q² ≤ x] F q / q)`.

The diagonal correction lies in `[0, B(x) / log 2]`, since `F q / q ≤ 1 / log 2`,
so it is `O(L)`. Writing `B(t) = α log t + E(t)`, Fubini gives
`∑_{q ≤ x} (F q / q) log(x / q) = ∫_1^x B(t) dt / t = α L² / 2 + O(∫ |E| dt / t)`.
A single bound `|E(t)| ≤ M` on `[1, x]` makes the two `E` contributions `O(M L)`
and `O(M B(x))`. Taking `|E(t)| ≪ 1 + log t ≤ 1 + √L` for `t ≤ exp √L` and
`|E(t)| ≪ log t / (log log t)⁵ ≪ L T⁻⁵` above gives `M = O(L T⁻⁵)`, so
`D(x) = α² L² / 2 + O(L² T⁻⁵)`. This is the explicit-rate form of Erdős,
Granville, Pomerance and Spiro (1990), (2.21)–(2.22), proved in Lemma 5.2 of
*The normal order of the number of iterations of Euler's function* (Plasma AI,
2026), §5.
-/

@[expose] public section

namespace Erdos408

open Filter Real MeasureTheory

/-- `B` is monotone. -/
private lemma harmonicF_monotone : Monotone harmonicF := fun a b hab => by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hab))

/-- `B(x) ≤ (log x + E) / log 2`, from `F q ≤ log q / log 2` and Mertens' first theorem. -/
private lemma exists_harmonicF_le :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x : ℝ, 1 ≤ x → harmonicF x ≤ (log x + E) / log 2 := by
  obtain ⟨E, hE, hM⟩ := mertens_first
  refine ⟨E, hE, fun x hx => ?_⟩
  have h := (abs_le.1 (hM 1 x le_rfl hx)).2
  rw [div_one] at h
  calc harmonicF x ≤ ∑ q ∈ primesIoc 1 x, log q / q / log 2 := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [div_right_comm]
        gcongr
        exact F_le_log_div_log_two (Finset.mem_filter.1 hq).2.ne_zero
    _ = (∑ q ∈ primesIoc 1 x, log q / q) / log 2 := (Finset.sum_div ..).symm
    _ ≤ (log x + E) / log 2 := by gcongr; linarith

/-- First-prime decomposition of `D(x)`, with the diagonal `r = q` removed. -/
private lemma harmonicFPair_eq_sum_harmonicF (x : ℝ) :
    harmonicFPair x = ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * harmonicF (x / q) -
      ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q *
        if q ∈ primesIoc 1 (x / q) then (F q : ℝ) / q else 0 := by
  rw [harmonicFPair, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_sub, Finset.filter_ne', harmonicF]
  simp_rw [mul_div_mul_comm _ _ (q : ℝ), ← Finset.mul_sum]
  congr 1
  split_ifs with h
  · exact Finset.sum_erase_eq_sub h
  · rw [Finset.erase_eq_of_notMem h, sub_zero]

/-- `u(t) / t` is interval integrable on `[a, b] ⊆ (0, ∞)` for monotone `u`. -/
private lemma intervalIntegrable_div_of_monotone {u : ℝ → ℝ} (hu : Monotone u) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable (fun t => u t / t) volume a b := by
  simp_rw [div_eq_mul_inv]
  refine hu.intervalIntegrable.mul_continuousOn (continuousOn_inv₀.mono fun t ht => ?_)
  exact (lt_of_lt_of_le (lt_min ha hb) ht.1).ne'

/-- The step `t ↦ [q ≤ t]` is monotone. -/
private lemma monotone_step (q : ℝ) : Monotone fun t : ℝ => if q ≤ t then (1 : ℝ) else 0 :=
  fun s t hst => by
    dsimp only
    split_ifs with h1 h2 h2 <;> first | exact absurd (h1.trans hst) h2 | norm_num

/-- `∫_1^x [q ≤ t] dt / t = log (x / q)` for `1 ≤ q ≤ x`. -/
private lemma integral_step_div {q x : ℝ} (hq : 1 ≤ q) (hqx : q ≤ x) :
    ∫ t in (1 : ℝ)..x, (if q ≤ t then (1 : ℝ) else 0) / t = log (x / q) := by
  have hq0 : 0 < q := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_div_of_monotone (monotone_step q) one_pos hq0)
    (intervalIntegrable_div_of_monotone (monotone_step q) hq0 (by linarith)),
    ← integral_one_div_of_pos hq0 (by linarith : 0 < x)]
  -- the step vanishes on `(1, q)`
  have h1 : ∫ t in (1 : ℝ)..q, (if q ≤ t then (1 : ℝ) else 0) / t = 0 := by
    rw [← intervalIntegral.integral_zero (a := (1 : ℝ)) (b := q) (μ := volume)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton q)] with t ht ht'
    rw [Set.uIoc_of_le hq] at ht'
    simp [not_le.2 (lt_of_le_of_ne ht'.2 ht)]
  rw [h1, zero_add]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hqx] at ht
  simp [ht.1]

/-- Fubini: `∫_1^x B(t) dt / t = ∑_{q ≤ x} (F q / q) log (x / q)`. -/
private lemma integral_harmonicF_div {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, harmonicF t / t =
      ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * log (x / q) := by
  have hstep : ∀ t ∈ Set.uIcc 1 x, harmonicF t / t = ∑ q ∈ primesIoc 1 x,
      (F q : ℝ) / q * ((if (q : ℝ) ≤ t then (1 : ℝ) else 0) / t) := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have hP : primesIoc 1 t = (primesIoc 1 x).filter fun q : ℕ => (q : ℝ) ≤ t := by
      ext q
      rw [Finset.mem_filter, mem_primesIoc_one, mem_primesIoc_one]
      exact ⟨fun h => ⟨⟨h.1, h.2.trans ht.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [harmonicF, hP, Finset.sum_filter, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> ring
  rw [intervalIntegral.integral_congr hstep, intervalIntegral.integral_finsetSum
    (f := fun q t => (F q : ℝ) / q * ((if (q : ℝ) ≤ t then (1 : ℝ) else 0) / t))
    fun q _ => (intervalIntegrable_div_of_monotone (monotone_step q) one_pos
      (by linarith)).const_mul _]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [mem_primesIoc_one] at hq
  rw [intervalIntegral.integral_const_mul,
    integral_step_div (by exact_mod_cast hq.1.one_lt.le) hq.2]

/-- `log t / t` is interval integrable on `[1, x]`. -/
private lemma intervalIntegrable_log_div {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun t => log t / t) volume 1 x := by
  have hpos : ∀ t ∈ Set.uIcc 1 x, t ≠ 0 := fun t ht => by
    rw [Set.uIcc_of_le hx] at ht
    linarith [ht.1]
  exact ((continuousOn_log.mono hpos).div continuousOn_id hpos).intervalIntegrable

/-- `∫_1^x log t dt / t = (log x)² / 2`. -/
private lemma integral_log_div {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in (1 : ℝ)..x, log t / t = log x ^ 2 / 2 := by
  have hpos : ∀ t ∈ Set.uIcc 1 x, 0 < t := fun t ht => by
    rw [Set.uIcc_of_le hx] at ht
    linarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => log t ^ 2 / 2)]
  · simp
  · intro t ht
    convert ((hasDerivAt_log (hpos t ht).ne').pow 2).div_const 2 using 1
    simp only [Nat.cast_ofNat]
    ring
  · exact intervalIntegrable_log_div hx

/-- Eventually `(log L)⁵ ≤ √L`. -/
private lemma eventually_log_pow_le_sqrt : ∀ᶠ L : ℝ in atTop, log L ^ 5 ≤ √L := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop 5 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    one_pos, eventually_ge_atTop 1] with L hL hL1
  rwa [one_mul, norm_of_nonneg (rpow_nonneg (log_nonneg hL1) _),
    norm_of_nonneg (by positivity), ← sqrt_eq_rpow, rpow_ofNat] at hL

/-- If `|B(t) - α log t| ≤ M` on `[1, x]`, then
`|D(x) - α² L² / 2| ≤ |α| M L + M B(x) + B(x) / log 2`. -/
private lemma abs_harmonicFPair_sub_le {α M x : ℝ} (hx : 1 ≤ x)
    (hErr : ∀ t : ℝ, 1 ≤ t → t ≤ x → |harmonicF t - α * log t| ≤ M) :
    |harmonicFPair x - α ^ 2 / 2 * log x ^ 2| ≤
      |α| * (M * log x) + M * harmonicF x + harmonicF x / log 2 := by
  have hx0 : 0 < x := by linarith
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  -- the main term: `∫_1^x B(t) dt / t = α L² / 2 + O(M L)`
  have hI : |∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * log (x / q) - α * (log x ^ 2 / 2)| ≤
      M * log x := by
    have hMint : ∫ t in (1 : ℝ)..x, M / t = M * log x := by
      simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul,
        integral_inv_of_pos one_pos hx0, inv_one, mul_one]
    rw [← integral_harmonicF_div hx, ← integral_log_div hx,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        (intervalIntegrable_div_of_monotone harmonicF_monotone one_pos hx0)
        ((intervalIntegrable_log_div hx).const_mul α), ← hMint, ← norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hx
      (Eventually.of_forall fun t ht => ?_)
      (intervalIntegrable_div_of_monotone (u := fun _ => M) monotone_const one_pos hx0)
    have ht0 : 0 < t := by linarith [ht.1]
    rw [show harmonicF t / t - α * (log t / t) = (harmonicF t - α * log t) / t by ring,
      norm_div, norm_eq_abs, norm_eq_abs, abs_of_pos ht0]
    exact div_le_div_of_nonneg_right (hErr t ht.1.le ht.2) ht0.le
  -- the error term: `∑ (F q / q) E(x / q) = O(M B(x))`
  have hS : |∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * (harmonicF (x / q) - α * log (x / q))| ≤
      M * harmonicF x := by
    rw [harmonicF, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
    rw [mem_primesIoc_one] at hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.1.one_lt.le
    rw [abs_mul, abs_of_nonneg (by positivity), mul_comm M]
    gcongr
    exact hErr _ ((one_le_div (by linarith)).2 hq.2) (div_le_self hx0.le hq1)
  -- the diagonal: `0 ≤ Δ ≤ B(x) / log 2`, since `F q / q ≤ 1 / log 2`
  have hdiag : ∀ q ∈ primesIoc 1 x,
      0 ≤ (F q : ℝ) / q * (if q ∈ primesIoc 1 (x / q) then (F q : ℝ) / q else 0) ∧
      (F q : ℝ) / q * (if q ∈ primesIoc 1 (x / q) then (F q : ℝ) / q else 0) ≤
        (F q : ℝ) / q / log 2 := by
    intro q hq
    have hqp := (Finset.mem_filter.1 hq).2
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hFq : (F q : ℝ) / q ≤ 1 / log 2 :=
      calc (F q : ℝ) / q ≤ q / log 2 / q := by
            gcongr
            exact (F_le_log_div_log_two hqp.ne_zero).trans
              (by gcongr; exact log_le_self hq0.le)
        _ = 1 / log 2 := by field_simp
    split_ifs
    · exact ⟨by positivity, by rw [div_eq_mul_one_div ((F q : ℝ) / q)]; gcongr⟩
    · simp only [mul_zero, le_refl, true_and]
      positivity
  have hD0 := Finset.sum_nonneg fun q hq => (hdiag q hq).1
  have hD1 : _ ≤ harmonicF x / log 2 :=
    (Finset.sum_le_sum fun q hq => (hdiag q hq).2).trans_eq (Finset.sum_div ..).symm
  have hsplit : ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * harmonicF (x / q) =
      α * ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * log (x / q) +
        ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * (harmonicF (x / q) - α * log (x / q)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [harmonicFPair_eq_sum_harmonicF, hsplit]
  set I := ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * log (x / q)
  set S := ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q * (harmonicF (x / q) - α * log (x / q))
  set Δ := ∑ q ∈ primesIoc 1 x, (F q : ℝ) / q *
    if q ∈ primesIoc 1 (x / q) then (F q : ℝ) / q else 0
  have hαI := (abs_mul α _).trans_le (mul_le_mul_of_nonneg_left hI (abs_nonneg α))
  rw [show α * I + S - Δ - α ^ 2 / 2 * log x ^ 2 =
      α * (I - α * (log x ^ 2 / 2)) + S - Δ by ring, abs_le]
  constructor <;> linarith [abs_le.1 hαI, abs_le.1 hS]

/-- If `B(x) = α log x + O(L T⁻⁵)`, then `D(x) = α² L² / 2 + O(L² T⁻⁵)`. -/
theorem cross_term {α K : ℝ}
    (h : ∀ᶠ x : ℝ in Filter.atTop,
      |harmonicF x - α * Real.log x| ≤ K * Real.log x / Real.log (Real.log x) ^ 5) :
    ∃ K' : ℝ, ∀ᶠ x : ℝ in Filter.atTop,
      |harmonicFPair x - α ^ 2 / 2 * Real.log x ^ 2| ≤
        K' * Real.log x ^ 2 / Real.log (Real.log x) ^ 5 := by
  obtain ⟨E, hE, hB⟩ := exists_harmonicF_le
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 h
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  set c₁ := |α| + 1 / log 2
  set c₂ := E / log 2
  set C := c₁ + c₂ + 32 * |K| with hC
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  -- the error `B(t) - α log t` is `O(log t)` for every `t ≥ 1`
  have hglob : ∀ t : ℝ, 1 ≤ t → |harmonicF t - α * log t| ≤ c₁ * log t + c₂ := by
    intro t ht
    have hBt := hB t ht
    have hB0 : 0 ≤ harmonicF t := Finset.sum_nonneg fun _ _ => by positivity
    have hlt := log_nonneg ht
    calc |harmonicF t - α * log t| ≤ |harmonicF t| + |α * log t| := abs_sub _ _
      _ = harmonicF t + |α| * log t := by rw [abs_of_nonneg hB0, abs_mul, abs_of_nonneg hlt]
      _ ≤ (log t + E) / log 2 + |α| * log t := by linarith
      _ = c₁ * log t + c₂ := by ring
  have hL : ∀ᶠ L : ℝ in atTop, 1 < √L ∧ y₀ ≤ exp √L ∧ log L ^ 5 ≤ √L ∧ E ≤ L := by
    filter_upwards [eventually_gt_atTop 1,
      (tendsto_exp_atTop.comp tendsto_sqrt_atTop).eventually (eventually_ge_atTop y₀),
      eventually_log_pow_le_sqrt, eventually_ge_atTop E] with L h1 hy hT hEL
    exact ⟨(lt_sqrt zero_le_one).2 (by linarith), hy, hT, hEL⟩
  refine ⟨(|α| + 2 / log 2) * C + 2 / log 2 ^ 2, ?_⟩
  filter_upwards [tendsto_log_atTop.eventually hL, eventually_ge_atTop 1]
    with x ⟨hs1, hy, hT, hEL⟩ hx
  set L := log x
  set T := log L
  have hL1 : 1 < L := by simpa using (lt_sqrt zero_le_one).1 hs1
  have hsL : √L * √L = L := mul_self_sqrt (by linarith)
  have hT2 : log √L = T / 2 := log_sqrt (by linarith)
  have hT0 : 0 < T := by linarith [log_pos hs1]
  set M := c₁ * √L + c₂ + 32 * |K| * L / T ^ 5 with hM
  have hM0 : 0 ≤ M := add_nonneg (add_nonneg (mul_nonneg hc₁ (sqrt_nonneg L)) hc₂) (by positivity)
  -- uniform bound `|E| ≤ M` on `[1, x]`, split at `exp √L`
  have hErr : ∀ t : ℝ, 1 ≤ t → t ≤ x → |harmonicF t - α * log t| ≤ M := by
    intro t ht1 htx
    have hlx : log t ≤ L := log_le_log (by linarith) htx
    have hK0 : 0 ≤ 32 * |K| * L / T ^ 5 := by positivity
    rcases le_or_gt t (exp √L) with hte | hte
    · have : log t ≤ √L := by simpa using log_le_log (by linarith) hte
      have := hglob t ht1
      nlinarith
    · have hlt : √L < log t := by simpa using log_lt_log (exp_pos _) hte
      have hTt : T / 2 ≤ log (log t) := hT2 ▸ log_le_log (by linarith) hlt.le
      calc |harmonicF t - α * log t| ≤ K * log t / log (log t) ^ 5 := hy₀ t (hy.trans hte.le)
        _ ≤ |K| * L / (T / 2) ^ 5 := by
          rw [mul_div_assoc, mul_div_assoc]
          refine (mul_le_mul_of_nonneg_right (le_abs_self K)
            (div_nonneg (by linarith) (pow_nonneg (by linarith) 5))).trans ?_
          gcongr
        _ = 32 * |K| * L / T ^ 5 := by ring
        _ ≤ M := by linarith [mul_nonneg hc₁ (sqrt_nonneg L)]
  -- `B(x) ≤ 2 L / log 2`
  have hBx : harmonicF x ≤ 2 / log 2 * L :=
    calc harmonicF x ≤ (L + E) / log 2 := hB x hx
      _ ≤ (L + L) / log 2 := by gcongr
      _ = 2 / log 2 * L := by ring
  -- `L √L ≤ L² / T⁵` and `L ≤ L² / T⁵`, since `T⁵ ≤ √L`
  have hsu : √L ≤ L / T ^ 5 := by
    rw [le_div_iff₀ (by positivity)]
    calc √L * T ^ 5 ≤ √L * √L := mul_le_mul_of_nonneg_left hT (sqrt_nonneg L)
      _ = L := hsL
  have hu : L * √L ≤ L ^ 2 / T ^ 5 := by
    rw [sq, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hsu (by linarith)
  have hLu : L ≤ L ^ 2 / T ^ 5 := (le_mul_of_one_le_right (by linarith) hs1.le).trans hu
  have hML : M * L ≤ C * (L ^ 2 / T ^ 5) :=
    calc M * L = c₁ * (L * √L) + c₂ * L + 32 * |K| * (L ^ 2 / T ^ 5) := by rw [hM]; ring
      _ ≤ c₁ * (L ^ 2 / T ^ 5) + c₂ * (L ^ 2 / T ^ 5) + 32 * |K| * (L ^ 2 / T ^ 5) := by
        gcongr
      _ = C * (L ^ 2 / T ^ 5) := by rw [hC]; ring
  calc |harmonicFPair x - α ^ 2 / 2 * L ^ 2|
      ≤ |α| * (M * L) + M * harmonicF x + harmonicF x / log 2 :=
        abs_harmonicFPair_sub_le hx hErr
    _ ≤ |α| * (M * L) + M * (2 / log 2 * L) + 2 / log 2 * L / log 2 := by gcongr
    _ = (|α| + 2 / log 2) * (M * L) + 2 / log 2 ^ 2 * L := by ring
    _ ≤ (|α| + 2 / log 2) * (C * (L ^ 2 / T ^ 5)) + 2 / log 2 ^ 2 * (L ^ 2 / T ^ 5) := by
      gcongr
    _ = ((|α| + 2 / log 2) * C + 2 / log 2 ^ 2) * L ^ 2 / T ^ 5 := by ring

end Erdos408
