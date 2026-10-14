import Erdos408.OneSided.Bands
import Erdos408.OneSided.Lift
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Good ratios

PD Lemma 3.2 (`blueprint/one_sided_type_ii.md` §5.3): for fixed lists, the ratios
`r ∈ [0, 1]` failing either good-state test have measure at most `exp(-L^{a₋}/4)`, uniformly
in the lists and the varying data.

* For a nonzero integer `N`, the set of `r ∈ [0, 1]` with `‖N r‖ ≤ δ` lies within `δ / |N|`
  of the `2|N| + 1` points `k / N`, so it has measure at most `6δ`.
* Test (i). There are at most `M^K` omission products `D` and at most `Y^{0.2}` integers `l`.
  For the integer `N = l D ≥ 1`, the bad set has measure at most `6 Y^{-0.7}`. The total is
  at most `6 M^K Y^{-0.5}`.
* Test (ii). Fix `I` with `i_* = max I`. For each fresh draw `T`, the ratios at which some
  pair of distinct trial integers `DZ ≠ D'Z'` violates the separation have measure at most
  `#pairs · 600 exp(-L^{a_{i_*}})`. The trial integers number at most
  `M^K exp(2K L^{a_{i_*} - g})`, by the gap (B6). Averaging over `T` (total probability one)
  and applying Markov's inequality at the threshold `exp(-L^{a_{i_*}}/4)` gives
  `600 M^{2K} exp(4K L^{a_{i_*} - g} - (3/4) L^{a_{i_*}})` for each of the `2^K` sets `I`.
* Uniformity. Both totals are at most `exp(-L^{a₋}/4)/2` once `L^g ≥ 32K` and
  `L^{a₋} ≥ 8(K + 2K L^{0.01} + 600)`, using `M ≤ exp(L^{0.01})`.
-/

namespace Erdos408.OneSided

open Filter Finset Real MeasureTheory

variable {K : ℕ}

/-! ### Small circle distances -/

/-- For a nonzero integer `n`, the ratios `r ∈ [0, 1]` with `‖n r‖ ≤ δ` have measure at most
`6δ`: they lie within `δ / |n|` of one of the `2|n| + 1` points `k / n`, `|k| ≤ |n|`. -/
theorem volume_circleDist_intMul_le {n : ℤ} (hn : n ≠ 0) {δ : ℝ} (hδ : 0 ≤ δ) :
    volume {r ∈ Set.Icc (0 : ℝ) 1 | circleDist (n * r) ≤ δ} ≤ ENNReal.ofReal (6 * δ) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn
  have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
  -- each such `r` lies within `δ / |n|` of `k / n` with `k = round (n r)`
  have hsub : {r ∈ Set.Icc (0 : ℝ) 1 | circleDist (n * r) ≤ δ} ⊆
      ⋃ k ∈ Icc (-|n|) |n|, Set.Icc ((k : ℝ) / n - δ / |(n : ℝ)|) (k / n + δ / |(n : ℝ)|) := by
    rintro r ⟨⟨hr0, hr1⟩, hr⟩
    unfold circleDist at hr
    have hk := abs_sub_round ((n : ℝ) * r)
    have hnr : |(n : ℝ) * r| ≤ |(n : ℝ)| := by
      rw [abs_mul, abs_of_nonneg hr0]
      exact mul_le_of_le_one_right (abs_nonneg _) hr1
    -- `|k| ≤ |n r| + 1/2 < |n| + 1`
    have hkn : |round ((n : ℝ) * r)| ≤ |n| := by
      have : ((|round ((n : ℝ) * r)| : ℤ) : ℝ) < |n| + 1 := by
        push_cast
        have := abs_sub_abs_le_abs_sub ((round ((n : ℝ) * r) : ℤ) : ℝ) ((n : ℝ) * r)
        rw [abs_sub_comm ((round ((n : ℝ) * r) : ℤ) : ℝ)] at this
        linarith
      exact Int.lt_add_one_iff.1 (by exact_mod_cast this)
    refine Set.mem_biUnion (x := round ((n : ℝ) * r)) (mem_Icc.2 (abs_le.1 hkn)) ?_
    -- `|r - k/n| = |n r - k| / |n|`
    have hdist : |r - (round ((n : ℝ) * r) : ℝ) / n| ≤ δ / |(n : ℝ)| := by
      rw [show r - (round ((n : ℝ) * r) : ℝ) / n = ((n : ℝ) * r - round ((n : ℝ) * r)) / n by
        field_simp, abs_div]
      exact div_le_div_of_nonneg_right hr (abs_nonneg _)
    rw [abs_le] at hdist
    exact Set.mem_Icc.2 ⟨by linarith, by linarith⟩
  have hcard : ((Icc (-|n|) |n|).card : ℝ) = 2 * |(n : ℝ)| + 1 := by
    have h : ((Icc (-|n|) |n|).card : ℤ) = 2 * |n| + 1 := by
      rw [Int.card_Icc, Int.toNat_of_nonneg (by linarith [abs_nonneg n])]
      ring
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    exact this
  calc volume {r ∈ Set.Icc (0 : ℝ) 1 | circleDist (n * r) ≤ δ}
      ≤ ∑ k ∈ Icc (-|n|) |n|,
          volume (Set.Icc ((k : ℝ) / n - δ / |(n : ℝ)|) (k / n + δ / |(n : ℝ)|)) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ENNReal.ofReal ((Icc (-|n|) |n|).card • (2 * δ / |(n : ℝ)|)) := by
        rw [ENNReal.ofReal_nsmul, ← sum_const]
        refine sum_congr rfl fun k _ => ?_
        rw [Real.volume_Icc]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (6 * δ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [nsmul_eq_mul, hcard, mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

/-! ### Test (i) -/

/-- Test (i) fails on a set of measure at most `6 M^K Y^{-1/2}`: there are at most `M^K`
omission products `D` and `Y^{0.2}` integers `l`, and each pair costs `6 Y^{-0.7}`. -/
theorem volume_not_goodFirst_le {Y : ℝ} (hY : 0 < Y) (d₀ : ℝ) {J : ℕ} {p : Lists K J}
    (hp : ∀ i h, p i h ≠ 0) :
    volume {r ∈ Set.Icc (0 : ℝ) 1 | ¬ GoodFirst Y d₀ r p} ≤
      ENNReal.ofReal (6 * (J + 1) ^ K * Y ^ (-(1 / 2 : ℝ))) := by
  set n := ⌊Y ^ (1 / 5 : ℝ)⌋₊
  set δ := Y ^ (-(7 / 10 : ℝ))
  have hD : ∀ o, omitProd p o ≠ 0 := fun o =>
    prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun h _ => hp i h
  -- a failure is a pair `(D, l)` with `‖l D r‖ ≤ Y^{-0.7}`
  have hsub : {r ∈ Set.Icc (0 : ℝ) 1 | ¬ GoodFirst Y d₀ r p} ⊆
      ⋃ o ∈ (univ : Finset (Fin K → Fin (J + 1))), ⋃ l ∈ Icc 1 n,
        {r ∈ Set.Icc (0 : ℝ) 1 | circleDist (((l * omitProd p o : ℕ) : ℤ) * r) ≤ δ} := by
    rintro r ⟨hr, hbad⟩
    unfold GoodFirst at hbad
    push Not at hbad
    obtain ⟨o, -, -, l, hl1, hlY, hl⟩ := hbad
    refine Set.mem_biUnion (mem_univ o)
      (Set.mem_biUnion (mem_Icc.2 ⟨hl1, Nat.le_floor hlY⟩) ⟨hr, ?_⟩)
    push_cast
    exact hl
  calc volume {r ∈ Set.Icc (0 : ℝ) 1 | ¬ GoodFirst Y d₀ r p}
      ≤ ∑ o ∈ (univ : Finset (Fin K → Fin (J + 1))), ∑ l ∈ Icc 1 n,
          volume {r ∈ Set.Icc (0 : ℝ) 1 |
            circleDist (((l * omitProd p o : ℕ) : ℤ) * r) ≤ δ} :=
        (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
          (sum_le_sum fun o _ => measure_biUnion_finset_le _ _))
    _ ≤ ∑ o ∈ (univ : Finset (Fin K → Fin (J + 1))), ∑ l ∈ Icc 1 n,
          ENNReal.ofReal (6 * δ) := by
        refine sum_le_sum fun o _ => sum_le_sum fun l hl => ?_
        refine volume_circleDist_intMul_le ?_ (by positivity)
        exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by rw [mem_Icc] at hl; omega) (hD o))
    _ = ENNReal.ofReal ((J + 1) ^ K • n • (6 * δ)) := by
        rw [sum_const, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, Nat.card_Icc,
          Nat.add_sub_cancel, ENNReal.ofReal_nsmul, ENNReal.ofReal_nsmul]
    _ ≤ ENNReal.ofReal (6 * (J + 1) ^ K * Y ^ (-(1 / 2 : ℝ))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hn : (n : ℝ) ≤ Y ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
        have hδY : Y ^ (1 / 5 : ℝ) * δ = Y ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hY]
          norm_num
        rw [nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        have hδ : 0 ≤ δ := by positivity
        calc ((J : ℝ) + 1) ^ K * (n * (6 * δ))
            ≤ ((J : ℝ) + 1) ^ K * (Y ^ (1 / 5 : ℝ) * (6 * δ)) := by gcongr
          _ = 6 * ((J : ℝ) + 1) ^ K * Y ^ (-(1 / 2 : ℝ)) := by
              rw [← hδY]
              ring

/-! ### Test (ii) -/

open scoped Classical in
/-- Markov's inequality for a weighted family of sets: if each `E t` has measure at most `ε`
and the weights total at most one, then the `r` whose weight of sets containing it exceeds
`θ` have measure at most `ε / θ`. The sets need not be measurable. -/
private theorem volume_weight_gt_le {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∀ t ∈ s, 0 ≤ w t)
    (hsum : ∑ t ∈ s, w t ≤ 1) (E : ι → Set ℝ) {ε θ : ℝ} (hθ : 0 < θ)
    (hE : ∀ t ∈ s, volume (E t) ≤ ENNReal.ofReal ε) :
    volume {r | θ < ∑ t ∈ s, if r ∈ E t then w t else 0} ≤ ENNReal.ofReal (ε / θ) := by
  -- replace each `E t` by a measurable hull of the same measure
  set G := fun t => toMeasurable volume (E t)
  set f : ℝ → ENNReal := fun r => ∑ t ∈ s, (G t).indicator (fun _ => ENNReal.ofReal (w t)) r
  have hG : ∀ t, Measurable ((G t).indicator fun _ => ENNReal.ofReal (w t)) := fun t =>
    measurable_const.indicator (measurableSet_toMeasurable _ _)
  have hf : Measurable f := Finset.measurable_sum _ fun t _ => hG t
  have hsub : {r | θ < ∑ t ∈ s, if r ∈ E t then w t else 0} ⊆
      {r | ENNReal.ofReal θ ≤ f r} := by
    intro r hr
    simp only [Set.mem_ofPred_eq] at hr ⊢
    calc ENNReal.ofReal θ ≤ ENNReal.ofReal (∑ t ∈ s, if r ∈ E t then w t else 0) :=
          ENNReal.ofReal_le_ofReal hr.le
      _ = ∑ t ∈ s, ENNReal.ofReal (if r ∈ E t then w t else 0) :=
          ENNReal.ofReal_sum_of_nonneg fun t ht => by
            split_ifs
            exacts [hw t ht, le_rfl]
      _ ≤ f r := by
          refine sum_le_sum fun t _ => ?_
          split_ifs with h
          · rw [Set.indicator_of_mem (subset_toMeasurable _ _ h)]
          · simp
  calc volume {r | θ < ∑ t ∈ s, if r ∈ E t then w t else 0}
      ≤ (∫⁻ r, f r) / ENNReal.ofReal θ :=
        (measure_mono hsub).trans (meas_ge_le_lintegral_div hf.aemeasurable
          (ENNReal.ofReal_pos.2 hθ).ne' ENNReal.ofReal_ne_top)
    _ = (∑ t ∈ s, ENNReal.ofReal (w t) * volume (E t)) / ENNReal.ofReal θ := by
        rw [lintegral_finsetSum _ fun t _ => hG t]
        congr 1
        refine sum_congr rfl fun t _ => ?_
        rw [lintegral_indicator_const (measurableSet_toMeasurable _ _), measure_toMeasurable]
    _ ≤ ENNReal.ofReal ε / ENNReal.ofReal θ := by
        refine ENNReal.div_le_div_right ?_ _
        calc ∑ t ∈ s, ENNReal.ofReal (w t) * volume (E t)
            ≤ ∑ t ∈ s, ENNReal.ofReal (w t) * ENNReal.ofReal ε :=
              sum_le_sum fun t ht => by gcongr; exact hE t ht
          _ = ENNReal.ofReal (∑ t ∈ s, w t) * ENNReal.ofReal ε := by
              rw [← sum_mul, ENNReal.ofReal_sum_of_nonneg hw]
          _ ≤ 1 * ENNReal.ofReal ε := by gcongr; exact ENNReal.ofReal_le_one.2 hsum
          _ = ENNReal.ofReal ε := one_mul _
    _ = ENNReal.ofReal (ε / θ) := (ENNReal.ofReal_div_of_pos hθ).symm

/-- The fresh draws have total probability one when every band has positive mass. -/
theorem sum_freshWeight {x : ℝ} {d : Data K} (I : Finset (Fin K))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) :
    ∑ T ∈ freshDraws x d I, freshWeight x d I T = 1 := by
  unfold freshDraws freshWeight
  simp_rw [prod_filter]
  have h := prod_univ_sum (fun i => if i ∈ I then {1} else band x (d.a i))
    fun i (q : ℕ) => if i ∉ I then 1 / ((q : ℝ) * harmonicMass (band x (d.a i))) else 1
  beta_reduce at h
  rw [← h]
  refine prod_eq_one fun i _ => ?_
  by_cases hi : i ∈ I
  · simp [hi]
  · simp only [hi, ite_false, not_false_eq_true, ite_true]
    -- `∑_{q ∈ 𝒫_i} 1 / (q V_i) = V_i / V_i`
    rw [sum_congr rfl fun (q : ℕ) _ => (div_div (1 : ℝ) (q : ℝ) _).symm, ← sum_div]
    exact div_self (hV i).ne'

/-- A fresh draw has nonnegative probability. -/
theorem freshWeight_nonneg {x : ℝ} {d : Data K} (I : Finset (Fin K))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (T : Fin K → ℕ) :
    0 ≤ freshWeight x d I T :=
  prod_nonneg fun i _ => div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (hV i).le)

/-- For one fresh draw `T` with `∏ T ≠ 0`, separation fails on a set of measure at most
`#pairs · 600 e^{-L^{a_i}}`, with at most `M^K |Z|` trial integers `D Z`. -/
theorem volume_not_separated_le {x : ℝ} {d : Data K} (d₀ : ℝ) (I : Finset (Fin K)) (i : Fin K)
    {J : ℕ} (p : Lists K J) {T : Fin K → ℕ} (hT : ∏ j, T j ≠ 0) :
    volume {r ∈ Set.Icc (0 : ℝ) 1 | ¬ Separated x d d₀ I i r p T} ≤
      ENNReal.ofReal (((J + 1) ^ K * (selections x d I i).card) ^ 2 *
        (600 * Real.exp (-Real.log x ^ d.a i))) := by
  set S := selections x d I i
  set δ := 100 * Real.exp (-Real.log x ^ d.a i)
  set N : (Fin K → Fin (J + 1)) × (Fin K → ℕ) → ℕ := fun q => omitProd p q.1 * ∏ j, q.2 j
  set Q := ((univ ×ˢ S) ×ˢ (univ ×ˢ S)).filter fun q => N q.1 ≠ N q.2
  -- a failure is a pair of distinct trial integers `D Z ≠ D' Z'` at distance `< δ`
  have hsub : {r ∈ Set.Icc (0 : ℝ) 1 | ¬ Separated x d d₀ I i r p T} ⊆
      ⋃ q ∈ Q, {r ∈ Set.Icc (0 : ℝ) 1 |
        circleDist (((((N q.1 : ℤ) - N q.2) * ∏ j, (T j : ℤ) : ℤ) : ℝ) * r) ≤ δ} := by
    rintro r ⟨hr, hbad⟩
    unfold Separated at hbad
    push Not at hbad
    obtain ⟨o, o', Z, hZ, Z', hZ', -, -, -, -, hne, hlt⟩ := hbad
    refine Set.mem_biUnion (x := ((o, Z), (o', Z')))
      (mem_filter.2 ⟨mem_product.2 ⟨mem_product.2 ⟨mem_univ _, hZ⟩,
        mem_product.2 ⟨mem_univ _, hZ'⟩⟩, hne⟩) ⟨hr, ?_⟩
    simp only [N]
    push_cast at hlt ⊢
    exact hlt.le
  calc volume {r ∈ Set.Icc (0 : ℝ) 1 | ¬ Separated x d d₀ I i r p T}
      ≤ ∑ q ∈ Q, volume {r ∈ Set.Icc (0 : ℝ) 1 |
          circleDist (((((N q.1 : ℤ) - N q.2) * ∏ j, (T j : ℤ) : ℤ) : ℝ) * r) ≤ δ} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ q ∈ Q, ENNReal.ofReal (6 * δ) := by
        refine sum_le_sum fun q hq => volume_circleDist_intMul_le ?_ (by positivity)
        refine mul_ne_zero (sub_ne_zero.2 ?_) (by exact_mod_cast hT)
        exact_mod_cast (mem_filter.1 hq).2
    _ = ENNReal.ofReal (Q.card • (6 * δ)) := by rw [sum_const, ENNReal.ofReal_nsmul]
    _ ≤ ENNReal.ofReal (((J + 1) ^ K * S.card) ^ 2 * (600 * Real.exp (-Real.log x ^ d.a i))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hQ : (Q.card : ℝ) ≤ ((J + 1) ^ K * S.card) ^ 2 := by
          have := card_filter_le ((univ ×ˢ S) ×ˢ (univ ×ˢ S)) fun q => N q.1 ≠ N q.2
          rw [card_product, card_product, card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin] at this
          calc (Q.card : ℝ) ≤ (((J + 1) ^ K * S.card * ((J + 1) ^ K * S.card) : ℕ) : ℝ) := by
                exact_mod_cast this
            _ = ((J + 1) ^ K * S.card) ^ 2 := by push_cast; ring
        rw [nsmul_eq_mul]
        calc (Q.card : ℝ) * (6 * δ) ≤ ((J + 1) ^ K * S.card) ^ 2 * (6 * δ) := by
              gcongr
          _ = ((J + 1) ^ K * S.card) ^ 2 * (600 * Real.exp (-Real.log x ^ d.a i)) := by
              ring

/-- With `i_* = max I`, the selections number at most `exp(2 L^{a_{i_*} - g})^K`: every
selected group lies at least `g` below `i_*`, by the gap (B6). -/
theorem card_selections_le {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hL : 1 ≤ Real.log x) {I : Finset (Fin K)}
    (hI : I.Nonempty) :
    ((selections x d I (I.max' hI)).card : ℝ) ≤
      Real.exp (2 * Real.log x ^ (d.a (I.max' hI) - g)) ^ K := by
  unfold selections
  rw [Fintype.card_piFinset, Nat.cast_prod]
  calc ∏ j, ((if j ∈ I.erase (I.max' hI) then band x (d.a j) else {1}).card : ℝ)
      ≤ ∏ _j : Fin K, Real.exp (2 * Real.log x ^ (d.a (I.max' hI) - g)) := by
        refine prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) fun j _ => ?_
        split_ifs with hj
        · -- `j < i_*`, so `a_j ≤ a_{i_*} - g`
          have hlt : j < I.max' hI :=
            lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase hj)) (ne_of_mem_erase hj)
          have hgap := hd.gap _ _ hlt
          exact (card_band_le _ _).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) zero_le_two))
        · rw [card_singleton, Nat.cast_one]
          exact Real.one_le_exp (by positivity)
    _ = Real.exp (2 * Real.log x ^ (d.a (I.max' hI) - g)) ^ K := by
        rw [prod_const, card_univ, Fintype.card_fin]

open scoped Classical in
/-- Test (ii) at one nonempty `I`, with `i_* = max I`: Markov's inequality over the fresh
draws at the threshold `θ = exp(-L^{a_{i_*}}/4)` bounds the failing ratios by
`M^{2K} |Z|² 600 e^{-L^{a_{i_*}}} / θ`. -/
theorem volume_not_goodSecond_at_le {x : ℝ} {d : Data K}
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (d₀ : ℝ) {J : ℕ} (p : Lists K J)
    {I : Finset (Fin K)} (hI : I.Nonempty) :
    volume {r ∈ Set.Icc (0 : ℝ) 1 |
        ¬ ∑ T ∈ (freshDraws x d I).filter
            (fun T => ¬ Separated x d d₀ I (I.max' hI) r p T), freshWeight x d I T ≤
          Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} ≤
      ENNReal.ofReal (((J + 1) ^ K * (selections x d I (I.max' hI)).card) ^ 2 *
          (600 * Real.exp (-Real.log x ^ d.a (I.max' hI))) /
        Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)) := by
  set E := fun T => {r ∈ Set.Icc (0 : ℝ) 1 | ¬ Separated x d d₀ I (I.max' hI) r p T}
  -- fresh draws consist of `1`s and band primes
  have hT : ∀ T ∈ freshDraws x d I, ∏ j, T j ≠ 0 := by
    intro T hT
    refine prod_ne_zero_iff.2 fun j _ => ?_
    have hTj := Fintype.mem_piFinset.1 hT j
    split_ifs at hTj
    · rw [mem_singleton.1 hTj]
      exact one_ne_zero
    · exact (TypeII.band_prime hTj).ne_zero
  refine (measure_mono ?_).trans (volume_weight_gt_le (freshDraws x d I)
    (fun T _ => freshWeight_nonneg I hV T) (sum_freshWeight I hV).le E (Real.exp_pos _)
    fun T hT' => volume_not_separated_le d₀ I (I.max' hI) p (hT T hT'))
  rintro r ⟨⟨hr0, hr1⟩, hbad⟩
  rw [sum_filter, not_le] at hbad
  refine lt_of_lt_of_eq hbad (sum_congr rfl fun T _ => ?_)
  by_cases h : Separated x d d₀ I (I.max' hI) r p T <;> simp [E, h, hr0, hr1]

/-- `L^{a₋} ≥ 8 (K + 2K L^{0.01} + 600)` eventually, since `a₋ > 0.01`. -/
private theorem eventually_rpow_ge_affine {alo : ℝ} (halo : 1 / 10 < alo) (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, 8 * (K + 2 * K * Real.log x ^ (1 / 100 : ℝ) + 600) ≤
      Real.log x ^ alo := by
  have hu := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
    Real.tendsto_log_atTop
  filter_upwards [hu.eventually_ge_atTop (8 * (3 * K + 600) + 1),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hL
  set u := Real.log x ^ (1 / 100 : ℝ) with hu_def
  have hx' : 8 * (3 * K + 600) + 1 ≤ u := hx
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  -- `L^{a₋} ≥ L^{0.1} = u^{10} ≥ u^2`
  have h10 : u ^ (10 : ℕ) ≤ Real.log x ^ alo := by
    rw [hu_def, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith)
  have h2 : u ^ 2 ≤ u ^ (10 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
  nlinarith

/-! ### Both tests -/

open scoped Classical in
/-- PD Lemma 3.2: the ratios failing goodness have measure at most `exp(-L^{a₋}/4)`, for
label dyads `Y ≥ exp(L^{a₋})/4`. -/
theorem eventually_volume_not_good {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ Y d₀ : ℝ, Real.exp (Real.log x ^ alo) ≤ 4 * Y →
      ∀ p ∈ lists x d (padCount x),
        volume {r ∈ Set.Icc (0 : ℝ) 1 | ¬ (GoodFirst Y d₀ r p ∧ GoodSecond x d d₀ r p)} ≤
          ENNReal.ofReal (Real.exp (-Real.log x ^ alo / 4)) := by
  have hLg := (tendsto_rpow_atTop hg).comp Real.tendsto_log_atTop
  filter_upwards [eventually_harmonicMass_band halo.le, eventually_rpow_ge_affine halo K,
    hLg.eventually_ge_atTop (32 * K), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hVx hlo hgK hL d hd Y d₀ hY4 p hp
  set u := Real.log x ^ (1 / 100 : ℝ)
  set ε := Real.exp (-Real.log x ^ alo / 4)
  have hgK' : 32 * (K : ℝ) ≤ Real.log x ^ g := hgK
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hu : 0 ≤ u := by positivity
  have hY : 0 < Y := by linarith [Real.exp_pos (Real.log x ^ alo)]
  have hV : ∀ i, 0 < harmonicMass (band x (d.a i)) := fun i =>
    lt_of_lt_of_le (by norm_num) (hVx _ (hd.window i).1).1
  have hp' : ∀ i h, p i h ≠ 0 := fun i h =>
    (TypeII.band_prime (Fintype.mem_piFinset.1
      (Fintype.mem_piFinset.1 (mem_filter.1 hp).1 i) h)).ne_zero
  -- `M = J + 1 ≤ exp(L^{0.01})`
  have hM : ((padCount x : ℝ) + 1) ^ K ≤ Real.exp (K * u) := by
    rw [Real.exp_nat_mul]
    gcongr
    exact (Real.add_one_le_exp _).trans (Real.exp_le_exp.2 (Nat.floor_le (by positivity)))
  -- split the failures into the two tests, and test (ii) by the set `I`
  have hsub : {r ∈ Set.Icc (0 : ℝ) 1 | ¬ (GoodFirst Y d₀ r p ∧ GoodSecond x d d₀ r p)} ⊆
      {r ∈ Set.Icc (0 : ℝ) 1 | ¬ GoodFirst Y d₀ r p} ∪
        ⋃ I : Finset (Fin K), {r ∈ Set.Icc (0 : ℝ) 1 | ∃ hI : I.Nonempty,
          ¬ ∑ T ∈ (freshDraws x d I).filter
              (fun T => ¬ Separated x d d₀ I (I.max' hI) r p T), freshWeight x d I T ≤
            Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} := by
    rintro r ⟨hr, hbad⟩
    by_cases h1 : GoodFirst Y d₀ r p
    · have h2 : ¬ GoodSecond x d d₀ r p := fun h2 => hbad ⟨h1, h2⟩
      unfold GoodSecond at h2
      push Not at h2
      obtain ⟨I, hI, h⟩ := h2
      exact Or.inr (Set.mem_iUnion.2 ⟨I, hr, hI, not_le.2 h⟩)
    · exact Or.inl ⟨hr, h1⟩
  -- test (i): `6 M^K Y^{-1/2} ≤ ε / 2`
  have hfirst : volume {r ∈ Set.Icc (0 : ℝ) 1 | ¬ GoodFirst Y d₀ r p} ≤
      ENNReal.ofReal (ε / 2) := by
    refine (volume_not_goodFirst_le hY d₀ hp').trans (ENNReal.ofReal_le_ofReal ?_)
    -- `log Y ≥ L^{a₋} - log 4 ≥ L^{a₋} - 3`
    have hlogY : Real.log x ^ alo ≤ 3 + Real.log Y := by
      have h := Real.log_le_log (Real.exp_pos _) hY4
      rw [Real.log_exp, Real.log_mul (by norm_num) hY.ne'] at h
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hYr : Y ^ (-(1 / 2 : ℝ)) ≤ Real.exp ((3 - Real.log x ^ alo) / 2) := by
      rw [Real.rpow_def_of_pos hY]
      exact Real.exp_le_exp.2 (by linarith)
    have h12 : (12 : ℝ) ≤ Real.exp 11 := by linarith [Real.add_one_le_exp (11 : ℝ)]
    calc 6 * ((padCount x : ℝ) + 1) ^ K * Y ^ (-(1 / 2 : ℝ))
        ≤ 6 * Real.exp (K * u) * Real.exp ((3 - Real.log x ^ alo) / 2) := by gcongr
      _ ≤ Real.exp 11 * Real.exp (K * u) * Real.exp ((3 - Real.log x ^ alo) / 2) / 2 := by
          rw [le_div_iff₀ two_pos]
          nlinarith [mul_pos (Real.exp_pos (K * u)) (Real.exp_pos ((3 - Real.log x ^ alo) / 2))]
      _ = Real.exp (11 + K * u + (3 - Real.log x ^ alo) / 2) / 2 := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ ε / 2 :=
          div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by linarith [mul_nonneg hK hu]))
            zero_le_two
  -- test (ii): each nonempty `I` costs at most `ε / 2^{K+1}`
  have hsecond : ∀ I : Finset (Fin K), volume {r ∈ Set.Icc (0 : ℝ) 1 | ∃ hI : I.Nonempty,
      ¬ ∑ T ∈ (freshDraws x d I).filter
          (fun T => ¬ Separated x d d₀ I (I.max' hI) r p T), freshWeight x d I T ≤
        Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)} ≤ ENNReal.ofReal (ε / 2 / 2 ^ K) := by
    intro I
    by_cases hI : I.Nonempty
    swap
    · rw [measure_mono_null (fun r hr => absurd hr.2.1 hI) measure_empty]
      positivity
    refine (measure_mono ?_).trans
      ((volume_not_goodSecond_at_le hV d₀ p hI).trans (ENNReal.ofReal_le_ofReal ?_))
    · rintro r ⟨hr, _, h⟩
      exact ⟨hr, h⟩
    set a := d.a (I.max' hI)
    set S := ((selections x d I (I.max' hI)).card : ℝ)
    have ha : alo ≤ a := (hd.window _).1
    have hLa : Real.log x ^ alo ≤ Real.log x ^ a := Real.rpow_le_rpow_of_exponent_le hL ha
    have hS := card_selections_le hd hL hI
    -- `4K L^{a - g} ≤ L^a / 8`, since `L^g ≥ 32K`
    have hgap : 4 * K * Real.log x ^ (a - g) ≤ Real.log x ^ a / 8 := by
      have h := Real.rpow_add (by linarith : (0 : ℝ) < Real.log x) (a - g) g
      rw [sub_add_cancel] at h
      have : 0 ≤ Real.log x ^ (a - g) := by positivity
      nlinarith
    have hMS : ((padCount x : ℝ) + 1) ^ K * S ≤
        Real.exp (K * u + 2 * K * Real.log x ^ (a - g)) := by
      calc ((padCount x : ℝ) + 1) ^ K * S
          ≤ Real.exp (K * u) * Real.exp (2 * Real.log x ^ (a - g)) ^ K :=
            mul_le_mul hM hS (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (K * u + 2 * K * Real.log x ^ (a - g)) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            ring_nf
    have h600 : (600 : ℝ) ≤ Real.exp 599 := by linarith [Real.add_one_le_exp (599 : ℝ)]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (((padCount x : ℝ) + 1) ^ K * S) ^ 2 * (600 * Real.exp (-Real.log x ^ a)) /
          Real.exp (-Real.log x ^ a / 4)
        = (((padCount x : ℝ) + 1) ^ K * S) ^ 2 * 600 *
            Real.exp (-Real.log x ^ a - -Real.log x ^ a / 4) := by
          rw [Real.exp_sub]
          ring
      _ ≤ Real.exp (K * u + 2 * K * Real.log x ^ (a - g)) ^ 2 * Real.exp 599 *
            Real.exp (-Real.log x ^ a - -Real.log x ^ a / 4) := by
          gcongr
      _ = Real.exp (2 * (K * u + 2 * K * Real.log x ^ (a - g)) + 599 +
            (-Real.log x ^ a - -Real.log x ^ a / 4)) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-Real.log x ^ alo / 4 - (K + 1)) := by
          refine Real.exp_le_exp.2 ?_
          nlinarith
      _ ≤ ε / 2 / 2 ^ K := by
          rw [le_div_iff₀ (by positivity), le_div_iff₀ two_pos, Real.exp_sub]
          calc Real.exp (-Real.log x ^ alo / 4) / Real.exp (K + 1) * 2 ^ K * 2
              ≤ Real.exp (-Real.log x ^ alo / 4) / Real.exp (K + 1) * Real.exp 1 ^ K *
                  Real.exp 1 := by gcongr
            _ = ε := by
                rw [← Real.exp_nat_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add,
                  ← Real.exp_add, ← Real.exp_sub,
                  show ε = Real.exp (-Real.log x ^ alo / 4) from rfl]
                congr 1
                ring
  -- sum the two tests and the `2^K` sets `I`
  calc volume {r ∈ Set.Icc (0 : ℝ) 1 | ¬ (GoodFirst Y d₀ r p ∧ GoodSecond x d d₀ r p)}
      ≤ ENNReal.ofReal (ε / 2) + ∑ _I : Finset (Fin K), ENNReal.ofReal (ε / 2 / 2 ^ K) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add hfirst ((measure_iUnion_fintype_le _ _).trans
            (sum_le_sum fun I _ => hsecond I))))
    _ = ENNReal.ofReal ε := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, ← ENNReal.ofReal_nsmul,
          ← ENNReal.ofReal_add (by positivity) (by positivity), nsmul_eq_mul]
        congr 1
        push_cast
        field_simp
        ring

end Erdos408.OneSided
