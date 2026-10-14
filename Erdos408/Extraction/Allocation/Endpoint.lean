module

public import Erdos408.Extraction.Allocation.Expansion
public import Erdos408.Extraction.Allocation.Groups

/-!
# Pointwise bounds for the weights and the endpoint

* The single-group weights: `n q^{n-1} ≤ 1/(1 - q)`, and `n 2^{1-n} ≤ 1`. So
  with reciprocal masses at least `1/2`, the success coins lie in
  `[0, 4 c₁]`, and `c_w` times a band weight lies in `[0, 1]`
  (as `c_w ≤ (1 - q)²/3`). Hence `0 ≤ P ≤ 1`.
* The slot statistic: on `n ≤ κ x`, a tuple dividing `n` uses primes of
  `n` above `x^ε`, of which there are at most `2/ε`; and
  `C_𝔟 ≤ (∑_{x^ε < p ≤ x} 1/p)^{d+1} ≤ (T + 1)^3` by Mertens. So
  `|f_𝔟 - C_𝔟| ≤ (2 T^{20}/c + 1)^3 + (T + 1)^3` with `ε = c T^{-20}`.
-/

@[expose] public section

namespace Erdos408

open Finset Filter Real

noncomputable section

/-! ### Single-group weights -/

/-- `n q^{n - 1} ≤ 1/(1 - q)` for `0 < q < 1`. -/
lemma natCast_mul_zpow_le {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (n : ℕ) :
    (n : ℝ) * q ^ ((n : ℤ) - 1) ≤ 1 / (1 - q) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul]
    exact (one_div_pos.2 (by linarith)).le
  have he : q ^ ((n : ℤ) - 1) = q ^ (n - 1) := by
    rw [show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [he]
  calc (n : ℝ) * q ^ (n - 1) = ∑ _k ∈ range n, q ^ (n - 1) := by simp
    _ ≤ ∑ k ∈ range n, q ^ k := sum_le_sum fun k hk =>
        pow_le_pow_of_le_one hq.le hq₁.le (by have := mem_range.1 hk; omega)
    _ = (1 - q ^ n) / (1 - q) := by
        rw [geom_sum_eq hq₁.ne, ← neg_div_neg_eq]
        ring_nf
    _ ≤ 1 / (1 - q) :=
        div_le_div_of_nonneg_right (by linarith [pow_pos hq n]) (by linarith)

/-- `n 2^{1 - n} ≤ 1`. -/
lemma natCast_mul_half_zpow_le (n : ℕ) : (n : ℝ) * (1 / 2 : ℝ) ^ ((n : ℤ) - 1) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have he : (1 / 2 : ℝ) ^ ((n : ℤ) - 1) = 1 / 2 ^ (n - 1) := by
    rw [show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) by omega, zpow_natCast, one_div_pow]
  rw [he, mul_one_div, div_le_one (by positivity)]
  have : n ≤ 2 ^ (n - 1) := by
    have := Nat.lt_two_pow_self (n := n - 1)
    omega
  exact_mod_cast this

/-- The weight of one group is `q^{ω - 1} ω / V`. -/
lemma markedWeight_singleton {ι : Type*} (i : ι) (q : ℝ) (G : ι → Finset ℕ) (n : ℕ) :
    markedWeight {i} q G n =
      (primeCount (G i) n : ℝ) * q ^ ((primeCount (G i) n : ℤ) - 1) / harmonicMass (G i) := by
  simp only [markedWeight, sum_singleton, card_singleton, prod_singleton, Nat.cast_one]
  ring

/-- With reciprocal mass at least `1/2`, the weight of one group with `q₀ = 1/2`
lies in `[0, 2]`. -/
lemma markedWeight_half_mem {g : Finset ℕ} (hg : 1 / 2 ≤ harmonicMass g) (n : ℕ) :
    0 ≤ markedWeight {g} (1 / 2) id n ∧ markedWeight {g} (1 / 2) id n ≤ 2 := by
  rw [markedWeight_singleton]
  simp only [id]
  have hV : 0 < harmonicMass g := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hV]
  have := natCast_mul_half_zpow_le (primeCount g n)
  linarith

/-- With masses at least `1/2` and `c₁ ≤ 1/4`, the coins lie in `[0, 1]`. -/
lemma successCoin_mem {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) {g : Finset ℕ}
    (hg : 1 / 2 ≤ harmonicMass g) (w : ℕ) :
    0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1 := by
  obtain ⟨h₁, h₂⟩ := markedWeight_half_mem hg w
  obtain ⟨h₃, h₄⟩ := markedWeight_half_mem hg (w + 1)
  refine ⟨by unfold successCoin; positivity, ?_⟩
  unfold successCoin
  calc c₁ * markedWeight {g} (1 / 2) id w * markedWeight {g} (1 / 2) id (w + 1)
      ≤ (1 / 4) * 2 * 2 := by gcongr
    _ = 1 := by norm_num

/-- With band masses at least `1/2`, the inert polynomial lies in `[0, 1]`. -/
lemma inertPoly_mem {q cw : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hcw : 0 ≤ cw)
    (hcw₁ : cw ≤ (1 - q) ^ 2 / 3) {K : ℕ} {CN x : ℝ}
    (hband : ∀ c ∈ range K, ∀ i ∈ range (inertPerCluster K CN x),
      1 / 2 ≤ harmonicMass (band x (inertExponent K x c i))) (n : ℕ) :
    0 ≤ inertPoly q cw K CN x n ∧ inertPoly q cw K CN x n ≤ 1 := by
  -- each factor `1 - c_w w_{c,i}` lies in `[0, 1]`
  have hf : ∀ c ∈ range K, ∀ i ∈ range (inertPerCluster K CN x),
      0 ≤ 1 - cw * bandWeight q x (inertExponent K x c i) n ∧
        1 - cw * bandWeight q x (inertExponent K x c i) n ≤ 1 := by
    intro c hc i hi
    have hV := hband c hc i hi
    rw [bandWeight, Finset.univ_unique, markedWeight_singleton]
    set V := harmonicMass (band x (inertExponent K x c i))
    set ω := primeCount (band x (inertExponent K x c i)) n
    have hV0 : 0 < V := by linarith
    have hw0 : 0 ≤ (ω : ℝ) * q ^ ((ω : ℤ) - 1) / V := by positivity
    have hw : (ω : ℝ) * q ^ ((ω : ℤ) - 1) / V ≤ 2 / (1 - q) := by
      rw [div_le_iff₀ hV0]
      have := natCast_mul_zpow_le hq hq₁ ω
      have h1 : 1 / (1 - q) ≤ 2 / (1 - q) * V := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith), one_div_mul_cancel (by linarith)]
        linarith
      linarith
    have h1q : 0 < 1 - q := by linarith
    have : cw * (2 / (1 - q)) ≤ 1 := by
      rw [mul_div_assoc', div_le_one h1q]
      nlinarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hw hcw]
    · nlinarith [mul_nonneg hcw hw0]
  have hc : ∀ c ∈ range K,
      0 ≤ 1 - ∏ i ∈ range (inertPerCluster K CN x),
        (1 - cw * bandWeight q x (inertExponent K x c i) n) ∧
      1 - ∏ i ∈ range (inertPerCluster K CN x),
        (1 - cw * bandWeight q x (inertExponent K x c i) n) ≤ 1 := by
    intro c hc
    have h0 := prod_nonneg fun i hi => (hf c hc i hi).1
    have h1 := prod_le_one₀ (fun i hi => (hf c hc i hi).1) fun i hi => (hf c hc i hi).2
    constructor <;> linarith
  exact ⟨prod_nonneg fun c hc' => (hc c hc').1,
    prod_le_one₀ (fun c hc' => (hc c hc').1) fun c hc' => (hc c hc').2⟩

/-! ### The slot statistic -/

/-- Membership in the slot tuples. -/
lemma mem_slotTuples {x : ℝ} (hx : 1 ≤ x) {k : ℕ} {u v : Fin k → ℝ} {Q : Fin k → ℕ}
    (hQ : Q ∈ slotTuples x u v) : ∀ i, (Q i).Prime ∧ x ^ u i < Q i ∧ (Q i : ℝ) ≤ x ^ v i := by
  intro i
  have h := (Fintype.mem_piFinset.1 (mem_filter.1 hQ).1) i
  simp only [mem_filter, mem_Iic] at h
  exact ⟨h.2.1, h.2.2, (Nat.le_floor_iff (rpow_nonneg (by linarith) _)).1 h.1⟩

/-- On `1 ≤ n ≤ κ x` with `L ≥ log κ`, the slot statistic and its mean are
at most `(2/ε + 1)^3` and `H^3` in absolute value, where `H ≥ 1` bounds the
reciprocal sum of the primes in `(x^ε, x]`. -/
lemma abs_slotCount_sub_slotMean_le {x κ ε H : ℝ} (hx : 1 < x) (hκ : Real.log κ ≤ Real.log x)
    (hκ0 : 0 < κ) (hε : 0 < ε) (hH : ∑ p ∈ primesIoc (x ^ ε) x, (1 : ℝ) / p ≤ H) (hH1 : 1 ≤ H)
    {k : ℕ} (hk : k ≤ 2) {u v : Fin (k + 1) → ℝ} (hu : ∀ i, ε ≤ u i) (hv : ∑ i, v i ≤ 1)
    {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hnx : (n : ℝ) ≤ κ * x) :
    |slotCount x u v B n - slotMean x u v B| ≤ (2 / ε + 1) ^ 3 + H ^ 3 := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  have hn0 : n ≠ 0 := by omega
  -- the primes of `n` above `x^ε`
  set D := n.primeFactors.filter fun p : ℕ => x ^ ε < (p : ℝ)
  have hD : (D.card : ℝ) ≤ 2 / ε := by
    have hprod : ∏ p ∈ D, p ∣ n :=
      (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
    have hle : ((x ^ ε) ^ D.card : ℝ) ≤ n := by
      calc ((x ^ ε) ^ D.card : ℝ) = ∏ _p ∈ D, x ^ ε := by rw [prod_const]
        _ ≤ ∏ p ∈ D, (p : ℝ) :=
            prod_le_prod₀ (fun _ _ => by positivity) fun p hp => (mem_filter.1 hp).2.le
        _ = ((∏ p ∈ D, p : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ n := by exact_mod_cast Nat.le_of_dvd (by omega) hprod
    have hlog := Real.log_le_log (by positivity) (hle.trans hnx)
    rw [Real.log_pow, Real.log_rpow hx0, Real.log_mul hκ0.ne' hx0.ne'] at hlog
    rw [le_div_iff₀ hε]
    nlinarith
  -- the slot statistic
  have hf0 : 0 ≤ slotCount x u v B n := sum_nonneg fun Q _ => (hB _).1
  have hf : slotCount x u v B n ≤ (2 / ε + 1) ^ 3 := by
    calc slotCount x u v B n
        ≤ ((slotTuples x u v).filter fun Q => ∏ i, Q i ∣ n).card := by
          rw [slotCount, card_eq_sum_ones, Nat.cast_sum]
          exact sum_le_sum fun Q _ => by simpa using (hB _).2
      _ ≤ ((Fintype.piFinset fun _ : Fin (k + 1) => D).card : ℝ) := by
          refine Nat.cast_le.2 (card_le_card fun Q hQ => ?_)
          obtain ⟨hQ, hdvd⟩ := mem_filter.1 hQ
          refine Fintype.mem_piFinset.2 fun i => mem_filter.2 ⟨?_, ?_⟩
          · exact Nat.mem_primeFactors.2 ⟨(mem_slotTuples hx.le hQ i).1,
              (dvd_prod_of_mem _ (mem_univ i)).trans hdvd, hn0⟩
          · exact lt_of_le_of_lt (rpow_le_rpow_of_exponent_le hx.le (hu i))
              (mem_slotTuples hx.le hQ i).2.1
      _ = (D.card : ℝ) ^ (k + 1) := by simp
      _ ≤ (2 / ε + 1) ^ (k + 1) := by gcongr; linarith
      _ ≤ (2 / ε + 1) ^ 3 := pow_le_pow_right₀ (by linarith [div_pos two_pos hε])
          (by omega)
  -- the harmonic mean
  have hC0 : 0 ≤ slotMean x u v B :=
    sum_nonneg fun Q hQ => div_nonneg (hB _).1 (prod_nonneg fun i _ => Nat.cast_nonneg _)
  have hC : slotMean x u v B ≤ H ^ 3 := by
    calc slotMean x u v B
        ≤ ∑ Q ∈ slotTuples x u v, ∏ i, (1 : ℝ) / Q i := by
          refine sum_le_sum fun Q hQ => ?_
          rw [prod_div_distrib, prod_const_one]
          have : 0 < ∏ i, (Q i : ℝ) :=
            prod_pos fun i _ => by exact_mod_cast (mem_slotTuples hx.le hQ i).1.pos
          exact div_le_div_of_nonneg_right (hB _).2 this.le
      _ ≤ ∑ Q ∈ Fintype.piFinset fun _ : Fin (k + 1) => primesIoc (x ^ ε) x,
            ∏ i, (1 : ℝ) / Q i := by
          refine sum_le_sum_of_subset_of_nonneg (fun Q hQ => Fintype.mem_piFinset.2 fun i => ?_)
            fun Q _ _ => prod_nonneg fun i _ => by positivity
          obtain ⟨hp, hlo, hhi⟩ := mem_slotTuples hx.le hQ i
          -- every upper slot coordinate is at most `1`
          have hvl : ∀ l, 0 ≤ v l := by
            intro l
            obtain ⟨-, hlo', hhi'⟩ := mem_slotTuples hx.le hQ l
            have := hlo'.trans_le hhi'
            have := (rpow_lt_rpow_left_iff hx).1 this
            linarith [hu l]
          have hvi : v i ≤ 1 := (single_le_sum (fun l _ => hvl l) (mem_univ i)).trans hv
          refine mem_primesIoc.2 ⟨hp, ?_, hhi.trans ?_⟩
          · exact lt_of_le_of_lt (rpow_le_rpow_of_exponent_le hx.le (hu i)) hlo
          · simpa using rpow_le_rpow_of_exponent_le hx.le hvi
      _ = (∑ p ∈ primesIoc (x ^ ε) x, (1 : ℝ) / p) ^ (k + 1) := by
          rw [← prod_univ_sum (t := fun _ => primesIoc (x ^ ε) x) (f := fun _ p => (1 : ℝ) / p),
            prod_const, card_univ, Fintype.card_fin]
      _ ≤ H ^ (k + 1) := by gcongr
      _ ≤ H ^ 3 := pow_le_pow_right₀ hH1 (by omega)
  rw [abs_le]
  constructor <;> nlinarith

end

/-- For large `x`, the primes in `(x^ε, x]` with `ε = c T^{-20}` have
reciprocal sum at most `T`. -/
lemma eventually_sum_primesIoc_le {c : ℝ} (hc : 0 < c) : ∀ᶠ x : ℝ in atTop,
    ∑ p ∈ primesIoc (x ^ (c / logLog x ^ 20)) x, (1 : ℝ) / p ≤ logLog x := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  filter_upwards [eventually_logLog_rpow_le 22 one_pos, eventually_le_logLog (max (1 / c) 1),
    eventually_le_logLog (4 * |Real.log c| + 4 * (E + 1) + c + 1),
    eventually_mul_logLogLog_le 20 (show (0 : ℝ) < 1 / 2 by norm_num), eventually_gt_atTop 1]
    with x hL hT hT' hs hx
  have hT1 : 1 ≤ logLog x := (le_max_right _ _).trans hT
  have hT0 : 0 < logLog x := by linarith
  have hx0 : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx
  rw [rpow_one, show (22 : ℝ) = ((22 : ℕ) : ℝ) by norm_num, rpow_natCast] at hL
  set T := logLog x
  set ε := c / T ^ 20
  have hT20 : 0 < T ^ 20 := by positivity
  have hε : 0 < ε := div_pos hc hT20
  -- `ε L ≥ T ≥ 1`
  have hεL : T ≤ ε * Real.log x := by
    have hcT : 1 / c ≤ T := (le_max_left _ _).trans hT
    rw [div_le_iff₀ hc] at hcT
    rw [show ε * Real.log x = c * Real.log x / T ^ 20 by ring, le_div_iff₀ hT20]
    calc T * T ^ 20 = T ^ 20 * T * 1 := by ring
      _ ≤ T ^ 20 * T * (T * c) := by gcongr
      _ = c * T ^ 22 := by ring
      _ ≤ c * Real.log x := by gcongr
  have hεx : Real.log (x ^ ε) = ε * Real.log x := Real.log_rpow hx0 ε
  have h2 : 2 ≤ x ^ ε := by
    rw [← exp_log (rpow_pos_of_pos hx0 ε), hεx]
    have := add_one_le_exp (ε * Real.log x)
    linarith
  have hε1 : ε ≤ 1 := by
    rw [div_le_one hT20]
    have := le_self_pow₀ hT1 (show (20 : ℕ) ≠ 0 by norm_num)
    have := abs_nonneg (Real.log c)
    linarith
  have hxε : x ^ ε ≤ x := by
    simpa using rpow_le_rpow_of_exponent_le hx.le hε1
  have hm := (abs_le.1 (hM _ _ h2 hxε)).2
  rw [hεx, show Real.log x / (ε * Real.log x) = 1 / ε by field_simp] at hm
  -- `log (1/ε) = 20 s - log c` and `E / (ε L) ≤ E / T`
  have hlog : Real.log (1 / ε) = 20 * logLogLog x - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_div hc.ne' hT20.ne', Real.log_pow, logLogLog]
    push_cast
    ring
  have hEL : E / (ε * Real.log x) ≤ (E + 1) / T :=
    div_le_div₀ (by linarith) (by linarith) hT0 hεL
  have hET : (E + 1) / T ≤ T / 4 := by
    rw [div_le_iff₀ hT0]
    have := abs_nonneg (Real.log c)
    nlinarith
  have hlc : -Real.log c ≤ T / 4 := by
    have h1 := neg_abs_le (Real.log c)
    have h2 : 0 ≤ E := hE
    linarith
  rw [hlog] at hm
  linarith

end Erdos408
