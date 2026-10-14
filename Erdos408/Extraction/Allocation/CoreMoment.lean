module

public import Erdos408.Extraction.Allocation.Euler
public import Erdos408.Extraction.Allocation.Decomposition

/-!
# The mean square of the core

E8, the case `r = 2` of the core moment bound of *The normal order of the
number of iterations of Euler's function* (Plasma AI, 2026), §6.3, with a fixed
but unoptimized log power: for large `x` and `2 ≤ j ≤ J_c`,
`∑_{w ≤ κ x} G_j(w + 1)² ≤ x L^{14}`.

* Each core factor is at most `1`: `D_j ≥ ∏_{p ≤ Y} (1 - 1/p) ≥ C₁ / log Y`
  and `log e > γ L`, so `D_j log e ≥ C₁ γ T^{25} ≥ 1`, as `γ T^{25} ≍ T^5 / s`.
* Hence `G_j(v) ≤ d_j(v̄)` if `v̄` is `Y`-rough, and `G_j(v) = 0` otherwise.
* On squarefree `v̄`, `d_j(v̄)² = d_{j²}(v̄)`. Counting `(v, f)` with
  `f₁ ⋯ f_{j²} = v̄` by `(v_P, f)` gives
  `∑_{v ≤ Z} d_{j²}(v̄) ≤ Z ∑_{c P-factored} c⁻¹ (∑_{n Y-rough} n⁻¹)^{j²}`,
  and the Euler products are `≤ L^{12}` and `≤ (2e T^{25})²`, so the last
  factor is `exp(O(s³)) ≤ L`.
* A `Y`-rough `v̄ ≤ Z` has `Ω(v̄) ≤ log Z / log Y ≤ 2 T^{25}`, so on the
  multiples of `p²`, `p > Y`, `d_j(v̄)² ≤ T^{4 T^{25}}`; there are at most
  `x (25 s + 2) / Y` of them, and `Y = exp(L / T^{25})` beats the count.
-/

@[expose] public section

namespace Erdos408

open Finset Filter Real

noncomputable section

/-- `Y`-roughness of `n`: every prime factor exceeds `Y`. -/
def IsYRough (Y : ℝ) (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, Y < p

/-- Roughness is decided classically. -/
instance (Y : ℝ) : DecidablePred (IsYRough Y) := fun _ => Classical.dec _

/-- Divisors of rough numbers are rough. -/
lemma IsYRough.of_dvd {Y : ℝ} {a b : ℕ} (hb : IsYRough Y b) (hb0 : b ≠ 0) (hab : a ∣ b) :
    IsYRough Y a := fun p hp => hb p (Nat.primeFactors_mono hab hb0 hp)

/-- A rough number `n ≠ 0` with `Y ≥ 1` has `Y^{Ω(n)} ≤ n`. -/
lemma rpow_cardFactors_le {Y : ℝ} (hY : 1 ≤ Y) {n : ℕ} (hn : n ≠ 0) (hr : IsYRough Y n) :
    Y ^ ArithmeticFunction.cardFactors n ≤ n := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum, ← prod_pow_eq_pow_sum]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.cast_prod]
  refine prod_le_prod₀ (fun p _ => by positivity) fun p hp => ?_
  rw [Nat.support_factorization] at hp
  push_cast
  exact pow_le_pow_left₀ (by linarith) (hr p hp).le _

/-! ### The core factors are at most one -/

/-- The candidate factor of `D_j` is at least `1`. -/
lemma one_le_prod_candidate (x : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    1 ≤ ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
  have hj1 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hj)
  refine one_le_prod₀ fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).two_le
  have h0 : 0 ≤ (j : ℝ)⁻¹ / p := by positivity
  have h1 : (j : ℝ)⁻¹ / p < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  exact one_le_inv₀ (by linarith) |>.2 (by linarith)

/-- For large `x`, every core factor is at most `1`, uniformly in `j ≥ 1`. -/
lemma eventually_coreFactor_le_one {c : ℝ} (hc : 0 < c) (Ch : ℝ) : ∀ᶠ x : ℝ in atTop,
    ∀ j : ℕ, 1 ≤ j → ∀ e : ℕ, coreFactor x (presieveExponent c Ch x) j e ≤ 1 := by
  obtain ⟨C₁, hC₁, hprod⟩ := exists_prod_one_sub_ge
  set M := max Ch 0
  have hM : 0 ≤ M := le_max_right _ _
  set K₀ := 4 * (8 * M + 11) / (C₁ * c)
  have hK₀ : 0 ≤ K₀ := by positivity
  filter_upwards [eventually_gt_atTop 1, eventually_le_logLog (K₀ + 1),
    eventually_logLog_rpow_le 25 one_pos] with x hx hT hL25 j hj e
  set T := logLog x
  set L := Real.log x
  set γ := presieveExponent c Ch x
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 0 < L := Real.log_pos hx
  rw [rpow_one, show (25 : ℝ) = ((25 : ℕ) : ℝ) by norm_num, rpow_natCast] at hL25
  have hT25 : 0 < T ^ 25 := by positivity
  -- `log Y = L / T^{25} ≥ 1`, so `Y ≥ 2`
  have hlogY : Real.log (proxyCutoff x) = L / T ^ 25 := by
    rw [proxyCutoff, log_exp]
  have hlogY1 : 1 ≤ L / T ^ 25 := by rw [le_div_iff₀ hT25]; linarith
  have hY2 : 2 ≤ proxyCutoff x := by
    rw [proxyCutoff]
    have := add_one_le_exp (L / T ^ 25)
    simp only [L, T, logLog] at this hlogY1 ⊢
    linarith
  -- `γ T^{25} ≥ 1 / C₁`
  have hs : logLogLog x ≤ T := by
    have := Real.log_le_sub_one_of_pos hT0
    rw [logLogLog]
    linarith
  have hs0 : 0 ≤ logLogLog x := by rw [logLogLog]; exact Real.log_nonneg hT1
  have hh : (sieveDepth Ch x : ℝ) ≤ 2 * (M * T + 1) := by
    rw [sieveDepth]
    push_cast
    have h1 : (⌈Ch * logLogLog x⌉₊ : ℝ) ≤ M * logLogLog x + 1 := by
      refine (Nat.cast_le.2 (Nat.ceil_mono (show Ch * logLogLog x ≤ M * logLogLog x from
        mul_le_mul_of_nonneg_right (le_max_left _ _) hs0))).trans ?_
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : M * logLogLog x ≤ M * T := mul_le_mul_of_nonneg_left hs hM
    linarith
  have hden : 4 * (sieveDepth Ch x : ℝ) + 3 ≤ (8 * M + 11) * T := by nlinarith
  have hden0 : 0 < 4 * (sieveDepth Ch x : ℝ) + 3 := by positivity
  have hγT : 1 ≤ C₁ * (γ * T ^ 25) := by
    have hγ : γ * T ^ 25 = c * T ^ 5 / (4 * (4 * (sieveDepth Ch x : ℝ) + 3)) := by
      simp only [γ, presieveExponent, T]
      field_simp
    rw [hγ, mul_div_assoc', le_div_iff₀ (by positivity)]
    have hT4 : T ≤ T ^ 4 := le_self_pow₀ hT1 (by norm_num)
    have hK : K₀ * (C₁ * c) = 4 * (8 * M + 11) := by
      simp only [K₀]
      field_simp
    have h1 : 4 * (8 * M + 11) ≤ C₁ * c * T := by nlinarith
    calc 1 * (4 * (4 * (sieveDepth Ch x : ℝ) + 3)) ≤ 4 * ((8 * M + 11) * T) := by linarith
      _ ≤ C₁ * c * T * T := by nlinarith
      _ ≤ C₁ * c * T ^ 4 * T := by gcongr
      _ = C₁ * (c * T ^ 5) := by ring
  unfold coreFactor
  split_ifs with h
  · obtain ⟨he, -⟩ := h
    have hx0 : 0 < x := by linarith
    have hxγ : 0 < x ^ γ := rpow_pos_of_pos hx0 γ
    have hloge : γ * L < Real.log e := by
      rw [← Real.log_rpow hx0]
      exact Real.log_lt_log hxγ he
    have hγ0 : 0 ≤ γ := by
      simp only [γ, presieveExponent]
      positivity
    have hD : C₁ / (L / T ^ 25) ≤ dampedDensity x j := by
      rw [dampedDensity, ← hlogY]
      calc C₁ / Real.log (proxyCutoff x) ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) :=
            hprod _ hY2
        _ ≤ _ := le_mul_of_one_le_right (le_trans (div_nonneg hC₁.le (by
              rw [hlogY]
              positivity)) (hprod _ hY2)) (one_le_prod_candidate x hj)
    have hD0 : 0 < C₁ / (L / T ^ 25) := by positivity
    rw [div_le_one (mul_pos (hD0.trans_le hD) (by nlinarith [mul_nonneg hγ0 hL.le]))]
    calc (1 : ℝ) ≤ C₁ * (γ * T ^ 25) := hγT
      _ = C₁ / (L / T ^ 25) * (γ * L) := by field_simp
      _ ≤ dampedDensity x j * Real.log e := by
          gcongr
          · nlinarith [mul_nonneg hγ0 hL.le]
  · exact zero_le_one

/-! ### The core and the divisor function -/

/-- With core factors at most `1`, `G_j(v) ≤ d_j(v̄)` when `v̄` is `Y`-rough,
and `G_j(v) = 0` otherwise. -/
lemma proxyCore_le_card {x γ : ℝ} {j : ℕ} (hj : 1 ≤ j) (hγ : 1 ≤ x ^ γ)
    (hb : ∀ e, coreFactor x γ j e ≤ 1) (v : ℕ) :
    proxyCore x γ j v ≤ if IsYRough (proxyCutoff x) (candidateStrip x v) then
      ((Nat.finMulAntidiag j (candidateStrip x v)).card : ℝ) else 0 := by
  unfold proxyCore
  split_ifs with hr
  · calc ∑ e ∈ Nat.finMulAntidiag j (candidateStrip x v), ∏ i, coreFactor x γ j (e i)
        ≤ ∑ _e ∈ Nat.finMulAntidiag j (candidateStrip x v), (1 : ℝ) :=
          sum_le_sum fun e _ =>
            prod_le_one₀ (fun i _ => coreFactor_nonneg hj hγ _) fun i _ => hb _
      _ = _ := by rw [sum_const, nsmul_eq_mul, mul_one]
  · refine le_of_eq (sum_eq_zero fun e he => ?_)
    -- a prime `p ≤ Y` of `v̄` divides some factor `e_i`
    simp only [IsYRough, not_forall, not_lt] at hr
    obtain ⟨p, hp, hpY⟩ := hr
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ ∏ i, e i := by
      rw [Nat.prod_eq_of_mem_finMulAntidiag he]
      exact Nat.dvd_of_mem_primeFactors hp
    obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpr.prime _).1 hdvd
    refine prod_eq_zero (mem_univ i) ?_
    unfold coreFactor
    split_ifs with hc
    · have := hc.2 p (Nat.mem_primeFactors.2 ⟨hpr, hi, Nat.ne_zero_of_mem_finMulAntidiag he i⟩)
      linarith
    · rfl

/-- Counting the factorizations of the stripped parts:
`∑_{v ≤ Z, v̄ rough} d_m(v̄) ≤ Z ∑_{c ≤ Z, P-factored} c⁻¹ (∑_{n ≤ Z rough} n⁻¹)^m`. -/
theorem sum_card_finMulAntidiag_le (P : Finset ℕ) (Y : ℝ) (m Z : ℕ) :
    ∑ v ∈ Icc 1 Z, (if IsYRough Y (stripPrimes P v) then
        ((Nat.finMulAntidiag m (stripPrimes P v)).card : ℝ) else 0) ≤
      Z * (∑ c ∈ (Icc 1 Z).filter (· ∈ Nat.factoredNumbers P), (1 : ℝ) / c) *
        (∑ n ∈ (Icc 1 Z).filter (IsYRough Y), (1 : ℝ) / n) ^ m := by
  set C := (Icc 1 Z).filter (· ∈ Nat.factoredNumbers P)
  set A := (Icc 1 Z).filter (IsYRough Y)
  set V := (Icc 1 Z).filter fun v => IsYRough Y (stripPrimes P v)
  set W := (C ×ˢ Fintype.piFinset fun _ : Fin m => A).filter fun t => t.1 * ∏ i, t.2 i ≤ Z
  -- the left side counts the pairs `(v, f)` with `f₁ ⋯ f_m = v̄`
  have h1 : ∑ v ∈ Icc 1 Z, (if IsYRough Y (stripPrimes P v) then
      ((Nat.finMulAntidiag m (stripPrimes P v)).card : ℝ) else 0) =
      ((V.sigma fun v => Nat.finMulAntidiag m (stripPrimes P v)).card : ℝ) := by
    rw [card_sigma, ← sum_filter]
    push_cast
    rfl
  -- they inject into `W` by `(v, f) ↦ (v_P, f)`
  have h2 : (V.sigma fun v => Nat.finMulAntidiag m (stripPrimes P v)).card ≤ W.card := by
    refine card_le_card_of_injOn (fun vf => (keepPrimes P vf.1, vf.2)) (fun vf hvf => ?_) ?_
    · obtain ⟨hv, hf⟩ := mem_sigma.1 (mem_coe.1 hvf)
      obtain ⟨hv, hr⟩ := mem_filter.1 hv
      obtain ⟨hv1, hvZ⟩ := mem_Icc.1 hv
      have hv0 : vf.1 ≠ 0 := by omega
      have hs0 := stripPrimes_ne_zero P vf.1
      have hkv : keepPrimes P vf.1 ∣ vf.1 := ⟨stripPrimes P vf.1, by
        rw [mul_comm, stripPrimes_mul_keepPrimes P hv0]⟩
      have hsv : stripPrimes P vf.1 ∣ vf.1 := ⟨keepPrimes P vf.1, by
        rw [stripPrimes_mul_keepPrimes P hv0]⟩
      refine mem_coe.2 (mem_filter.2 ⟨mem_product.2 ⟨mem_filter.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, ?_⟩,
        Fintype.mem_piFinset.2 fun i => mem_filter.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, ?_⟩⟩, ?_⟩)
      · exact Nat.pos_of_ne_zero (keepPrimes_ne_zero P _)
      · exact (Nat.le_of_dvd (by omega) hkv).trans hvZ
      · exact Nat.mem_factoredNumbers_of_primeFactors_subset (keepPrimes_ne_zero P _)
          fun p hp => mem_of_mem_primeFactors_keepPrimes hp
      · exact Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_finMulAntidiag hf i)
      · exact (Nat.le_of_dvd (by omega) ((Nat.dvd_of_mem_finMulAntidiag hf i).trans hsv)).trans
          hvZ
      · exact hr.of_dvd hs0 (Nat.dvd_of_mem_finMulAntidiag hf i)
      · simp only
        rw [Nat.prod_eq_of_mem_finMulAntidiag hf, mul_comm, stripPrimes_mul_keepPrimes P hv0]
        exact hvZ
    · intro a ha b hb hab
      simp only [Prod.mk.injEq] at hab
      obtain ⟨ha1, haf⟩ := mem_sigma.1 (mem_coe.1 ha)
      obtain ⟨hb1, hbf⟩ := mem_sigma.1 (mem_coe.1 hb)
      have ha0 : a.1 ≠ 0 := by have := (mem_Icc.1 (mem_filter.1 ha1).1).1; omega
      have hb0 : b.1 ≠ 0 := by have := (mem_Icc.1 (mem_filter.1 hb1).1).1; omega
      have hs : stripPrimes P a.1 = stripPrimes P b.1 := by
        rw [← Nat.prod_eq_of_mem_finMulAntidiag haf, ← Nat.prod_eq_of_mem_finMulAntidiag hbf,
          hab.2]
      have h1 : a.1 = b.1 := by
        rw [← stripPrimes_mul_keepPrimes P ha0, ← stripPrimes_mul_keepPrimes P hb0, hs, hab.1]
      exact Sigma.ext h1 (heq_of_eq hab.2)
  -- each element of `W` has weight `Z / (c ∏ f) ≥ 1`
  have h3 : (W.card : ℝ) ≤ ∑ t ∈ W, (Z : ℝ) / (t.1 * ∏ i, (t.2 i : ℝ)) := by
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_le_sum fun t ht => ?_
    obtain ⟨ht, hle⟩ := mem_filter.1 ht
    obtain ⟨hc, hf⟩ := mem_product.1 ht
    have hc1 : (1 : ℝ) ≤ t.1 := by exact_mod_cast (mem_Icc.1 (mem_filter.1 hc).1).1
    have hf1 : ∀ i, (1 : ℝ) ≤ t.2 i := fun i => by
      exact_mod_cast (mem_Icc.1 (mem_filter.1 (Fintype.mem_piFinset.1 hf i)).1).1
    have hpos : 0 < (t.1 : ℝ) * ∏ i, (t.2 i : ℝ) :=
      mul_pos (by linarith) (prod_pos fun i _ => by linarith [hf1 i])
    rw [Nat.cast_one, le_div_iff₀ hpos, one_mul]
    exact_mod_cast hle
  have h4 : ∑ t ∈ W, (Z : ℝ) / (t.1 * ∏ i, (t.2 i : ℝ)) ≤
      ∑ t ∈ C ×ˢ Fintype.piFinset (fun _ : Fin m => A), (Z : ℝ) / (t.1 * ∏ i, (t.2 i : ℝ)) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ => by positivity
  have h5 : ∑ t ∈ C ×ˢ Fintype.piFinset (fun _ : Fin m => A), (Z : ℝ) / (t.1 * ∏ i, (t.2 i : ℝ)) =
      Z * (∑ c ∈ C, (1 : ℝ) / c) * (∑ n ∈ A, (1 : ℝ) / n) ^ m := by
    have hpow : (∑ n ∈ A, (1 : ℝ) / n) ^ m =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin m => A), ∏ i, (1 : ℝ) / (f i) := by
      rw [← prod_univ_sum (t := fun _ => A) (f := fun _ n => (1 : ℝ) / n), prod_const, card_univ,
        Fintype.card_fin]
    rw [hpow, sum_product, mul_assoc, sum_mul, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun f _ => ?_
    rw [prod_div_distrib, prod_const_one]
    field_simp
  rw [h1]
  calc ((V.sigma fun v => Nat.finMulAntidiag m (stripPrimes P v)).card : ℝ) ≤ W.card := by
        exact_mod_cast h2
    _ ≤ _ := h3.trans (h4.trans h5.le)

/-! ### The pointwise split -/

/-- Pointwise, `G_j(v)² ≤ [v̄ rough] d_{j²}(v̄) + [v̄ rough, not squarefree] j^{2 Ω(v̄)}`. -/
lemma proxyCore_sq_le {x γ : ℝ} {j : ℕ} (hj : 1 ≤ j) (hγ : 1 ≤ x ^ γ)
    (hb : ∀ e, coreFactor x γ j e ≤ 1) (v : ℕ) :
    proxyCore x γ j v ^ 2 ≤
      (if IsYRough (proxyCutoff x) (candidateStrip x v) then
        ((Nat.finMulAntidiag (j ^ 2) (candidateStrip x v)).card : ℝ) else 0) +
      (if IsYRough (proxyCutoff x) (candidateStrip x v) ∧ ¬ Squarefree (candidateStrip x v) then
        (j : ℝ) ^ (2 * ArithmeticFunction.cardFactors (candidateStrip x v)) else 0) := by
  have h0 := proxyCore_nonneg hj hγ v
  have hle := proxyCore_le_card hj hγ hb v
  set n := candidateStrip x v
  by_cases hr : IsYRough (proxyCutoff x) n
  · simp only [hr, ↓reduceIte] at hle
    have hsq : proxyCore x γ j v ^ 2 ≤ ((Nat.finMulAntidiag j n).card : ℝ) ^ 2 :=
      pow_le_pow_left₀ h0 hle 2
    by_cases hs : Squarefree n
    · simp only [hr, hs, not_true_eq_false, and_false, ↓reduceIte, add_zero]
      rw [Nat.card_finMulAntidiag_of_squarefree hs] at hsq
      rw [Nat.card_finMulAntidiag_of_squarefree hs]
      push_cast at hsq ⊢
      rw [← pow_mul, mul_comm, pow_mul] at hsq
      exact hsq
    · simp only [hr, hs, not_false_eq_true, and_self, ↓reduceIte]
      have hd : ((Nat.finMulAntidiag j n).card : ℝ) ≤
          (j : ℝ) ^ ArithmeticFunction.cardFactors n := by
        exact_mod_cast card_finMulAntidiag_le j n
      have : ((Nat.finMulAntidiag j n).card : ℝ) ^ 2 ≤
          (j : ℝ) ^ (2 * ArithmeticFunction.cardFactors n) := by
        rw [mul_comm, pow_mul]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      have h1 : (0 : ℝ) ≤ ((Nat.finMulAntidiag (j ^ 2) n).card : ℝ) := Nat.cast_nonneg _
      linarith
  · simp only [hr, ↓reduceIte] at hle
    have : proxyCore x γ j v = 0 := le_antisymm hle h0
    rw [this]
    simp only [hr, false_and, ↓reduceIte, add_zero]
    norm_num

/-- Shifting `w ↦ w + 1` into `[1, M + 1]`. -/
lemma sum_Icc_succ_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (M : ℕ) :
    ∑ w ∈ Icc 1 M, f (w + 1) ≤ ∑ v ∈ Icc 1 (M + 1), f v := by
  rw [← sum_image (g := (· + 1)) (fun a _ b _ h => by simpa using h)]
  refine sum_le_sum_of_subset_of_nonneg (fun v hv => ?_) fun v _ _ => hf v
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hv
  rw [mem_Icc] at hw ⊢
  omega

/-- A rough `n ≤ Z` has `j^{2 Ω(n)} ≤ exp(2 log j · log Z / log Y)`. -/
lemma pow_two_mul_cardFactors_le {Y : ℝ} (hY : 1 < Y) {j n Z : ℕ} (hj : 1 ≤ j) (hn : n ≠ 0)
    (hnZ : n ≤ Z) (hr : IsYRough Y n) :
    (j : ℝ) ^ (2 * ArithmeticFunction.cardFactors n) ≤
      Real.exp (2 * Real.log j * (Real.log Z / Real.log Y)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hlY : 0 < Real.log Y := Real.log_pos hY
  have hΩ : (ArithmeticFunction.cardFactors n : ℝ) ≤ Real.log Z / Real.log Y := by
    rw [le_div_iff₀ hlY]
    have h1 := rpow_cardFactors_le hY.le hn hr
    have h2 : (Y : ℝ) ^ ArithmeticFunction.cardFactors n ≤ Z :=
      h1.trans (by exact_mod_cast hnZ)
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    exact h3
  rw [← exp_log (pow_pos hj0 _), Real.log_pow]
  refine exp_le_exp.2 ?_
  push_cast
  have hlj : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj)
  nlinarith

/-! ### The Euler products -/

/-- The reciprocals of the candidate-factored numbers sum to at most `exp(12 T)`. -/
lemma sum_inv_candidateFactored_le {x : ℝ} (hx : 1 ≤ Real.log x) (hg : GroupFacts x) (Z : ℕ) :
    ∑ c ∈ (Icc 1 Z).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)), (1 : ℝ) / c ≤
      Real.exp (12 * logLog x) := by
  have hfp : (candidatePrimes x).filter Nat.Prime = candidatePrimes x :=
    filter_true_of_mem fun p hp => prime_of_mem_candidatePrimes hp
  refine (sum_inv_le_prod_of_factored _ _ fun n hn => (mem_filter.1 hn).2).trans
    ((prod_inv_one_sub_le_exp _).trans (exp_le_exp.2 ?_))
  rw [hfp]
  linarith [sum_one_div_candidatePrimes_le hx hg]

/-- The reciprocals of the `Y`-rough numbers up to `Z` sum to at most
`exp(2 (log (log Z / log Y) + E / log Y))`, given Mertens' second theorem with
constant `E`. -/
lemma sum_inv_rough_le {E : ℝ}
    (hM : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ E / Real.log y)
    {Y : ℝ} {Z : ℕ} (hY : 2 ≤ Y) (hYZ : Y ≤ Z) :
    ∑ n ∈ (Icc 1 Z).filter (IsYRough Y), (1 : ℝ) / n ≤
      Real.exp (2 * (Real.log (Real.log Z / Real.log Y) + E / Real.log Y)) := by
  have hfp : (primesIoc Y Z).filter Nat.Prime = primesIoc Y Z :=
    filter_true_of_mem fun p hp => (mem_primesIoc.1 hp).1
  refine (sum_inv_le_prod_of_factored (primesIoc Y Z) _ fun n hn => ?_).trans
    ((prod_inv_one_sub_le_exp _).trans (exp_le_exp.2 ?_))
  · obtain ⟨hn, hr⟩ := mem_filter.1 hn
    obtain ⟨hn1, hnZ⟩ := mem_Icc.1 hn
    refine Nat.mem_factoredNumbers_of_primeFactors_subset (by omega) fun p hp => ?_
    exact mem_primesIoc.2 ⟨Nat.prime_of_mem_primeFactors hp, hr p hp,
      by exact_mod_cast (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hnZ⟩
  · rw [hfp]
    have := (abs_le.1 (hM Y Z hY hYZ)).2
    linarith

/-- The `w ≤ M` with `w + 1` rough and not squarefree in its stripped part are
multiples of `p²` for primes `Y < p ≤ M + 1`. -/
lemma card_filter_not_squarefree_le (x : ℝ) (M : ℕ) :
    (((Icc 1 M).filter fun w => IsYRough (proxyCutoff x) (candidateStrip x (w + 1)) ∧
        ¬ Squarefree (candidateStrip x (w + 1))).card : ℝ) ≤
      ∑ p ∈ primesIoc (proxyCutoff x) (M + 1), ((M : ℝ) + 1) / (p * p) := by
  refine le_trans ?_ (card_filter_sq_dvd_le _ M)
  refine Nat.cast_le.2 (card_le_card fun w hw => ?_)
  obtain ⟨hw, hr, hs⟩ := mem_filter.1 hw
  refine mem_filter.2 ⟨hw, ?_⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hs
  push Not at hs
  obtain ⟨p, hp, hpp⟩ := hs
  have hs0 := stripPrimes_ne_zero (candidatePrimes x) (w + 1)
  have hsv : candidateStrip x (w + 1) ∣ w + 1 := ⟨keepPrimes (candidatePrimes x) (w + 1), by
    rw [candidateStrip, stripPrimes_mul_keepPrimes _ (by omega)]⟩
  have hpf : p ∈ (candidateStrip x (w + 1)).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, (dvd_mul_right p p).trans hpp, hs0⟩
  refine ⟨p, mem_primesIoc.2 ⟨hp, hr p hpf, ?_⟩, hpp.trans hsv⟩
  have := Nat.le_of_dvd (by omega) ((Nat.dvd_of_mem_primeFactors hpf).trans hsv)
  have hwM := (mem_Icc.1 hw).2
  exact_mod_cast (show p ≤ M + 1 by omega)

/-! ### Assembly -/

/-- The scale facts used for the mean square: `Y ≥ 2`, `Y ≤ Z ≤ x L`, and
`log Z / log Y ≤ 2 T^{25}`, with `Z = ⌊κ x⌋ + 1`. -/
lemma core_scale_facts {x κ : ℝ} (hx : 1 < x) (hκ : 1 < κ) (hκL : κ + 1 ≤ Real.log x)
    (hT : 1 ≤ logLog x) (hL25 : logLog x ^ 25 ≤ Real.log x) :
    2 ≤ proxyCutoff x ∧ proxyCutoff x ≤ ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ∧
      ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ≤ x * Real.log x ∧
      Real.log (proxyCutoff x) = Real.log x / logLog x ^ 25 ∧
      0 < Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) / Real.log (proxyCutoff x) ∧
      Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) / Real.log (proxyCutoff x) ≤ 2 * logLog x ^ 25 := by
  set L := Real.log x
  set T := logLog x
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := Real.log_pos hx
  have hT25 : 0 < T ^ 25 := by positivity
  have hlogY : Real.log (proxyCutoff x) = L / T ^ 25 := by rw [proxyCutoff, log_exp]
  have hlogY1 : 1 ≤ L / T ^ 25 := by rw [le_div_iff₀ hT25]; linarith
  have hY2 : 2 ≤ proxyCutoff x := by
    rw [proxyCutoff]
    have := add_one_le_exp (L / T ^ 25)
    simp only [L, T, logLog] at this hlogY1 ⊢
    linarith
  have hκx : 0 ≤ κ * x := by positivity
  have hZ1 : κ * x ≤ ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.lt_floor_add_one (κ * x)]
  have hZ2 : ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ≤ x * L := by
    push_cast
    have := Nat.floor_le hκx
    nlinarith
  have hYx : proxyCutoff x ≤ x := by
    have h : L / T ^ 25 ≤ L := div_le_self hL.le (one_le_pow₀ hT)
    calc proxyCutoff x = Real.exp (L / T ^ 25) := rfl
      _ ≤ Real.exp L := exp_le_exp.2 h
      _ = x := exp_log hx0
  have hYZ : proxyCutoff x ≤ ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) := hYx.trans (by nlinarith)
  have hZpos : (1 : ℝ) < ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) := by linarith
  have hlogZ : Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * L := by
    calc Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (x * L) :=
          Real.log_le_log (by linarith) hZ2
      _ = L + Real.log L := Real.log_mul hx0.ne' hL.ne'
      _ ≤ 2 * L := by linarith [Real.log_le_sub_one_of_pos hL]
  refine ⟨hY2, hYZ, hZ2, hlogY, div_pos (Real.log_pos hZpos) (by rw [hlogY]; positivity), ?_⟩
  rw [hlogY, div_div_eq_mul_div, div_le_iff₀ hL]
  nlinarith

/-- The squarefree part of the mean square: at most `x L^{14}`. -/
lemma sum_first_le_at {x κ E : ℝ} {j : ℕ}
    (hM : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ E / Real.log y)
    (hx : 1 < x) (hκ : 1 < κ) (hκL : κ + 1 ≤ Real.log x) (hT : 1 ≤ logLog x)
    (hL25 : logLog x ^ 25 ≤ Real.log x) (hEL : E ≤ Real.log x / logLog x ^ 25)
    (hgroups : GroupFacts x) (hj : 52 * (j : ℝ) ^ 2 * (logLogLog x + 1) ≤ logLog x) :
    ∑ w ∈ Icc 1 ⌊κ * x⌋₊, (if IsYRough (proxyCutoff x) (candidateStrip x (w + 1)) then
        ((Nat.finMulAntidiag (j ^ 2) (candidateStrip x (w + 1))).card : ℝ) else 0) ≤
      x * Real.log x ^ (14 : ℝ) := by
  obtain ⟨hY2, hYZ, hZ, hlogY, hrpos, hratio⟩ := core_scale_facts hx hκ hκL hT hL25
  set L := Real.log x
  set T := logLog x
  set s := logLogLog x
  set Y := proxyCutoff x
  set Z := ⌊κ * x⌋₊ + 1
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := Real.log_pos hx
  have hs0 : 0 ≤ s := Real.log_nonneg hT
  have hlY : 0 < Real.log Y := by rw [hlogY]; positivity
  -- the rough reciprocal sum is at most `exp(52 (s + 1))`
  have hSA : ∑ n ∈ (Icc 1 Z).filter (IsYRough Y), (1 : ℝ) / n ≤ Real.exp (52 * (s + 1)) := by
    refine (sum_inv_rough_le hM hY2 hYZ).trans (exp_le_exp.2 ?_)
    have h1 : Real.log (Real.log Z / Real.log Y) ≤ Real.log 2 + 25 * s := by
      calc Real.log (Real.log Z / Real.log Y) ≤ Real.log (2 * T ^ 25) :=
            Real.log_le_log hrpos hratio
        _ = Real.log 2 + 25 * s := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            push_cast
            rfl
    have h2 : E / Real.log Y ≤ 1 := by
      rw [div_le_one hlY, hlogY]
      exact hEL
    have := Real.log_two_lt_d9
    nlinarith
  have hSA0 : 0 ≤ ∑ n ∈ (Icc 1 Z).filter (IsYRough Y), (1 : ℝ) / n :=
    sum_nonneg fun _ _ => by positivity
  have hSC := sum_inv_candidateFactored_le (by
    have := Real.log_le_sub_one_of_pos hL
    simp only [T, logLog] at hT
    linarith) hgroups Z
  have hSC0 : 0 ≤ ∑ c ∈ (Icc 1 Z).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
      (1 : ℝ) / c := sum_nonneg fun _ _ => by positivity
  have hpow : (∑ n ∈ (Icc 1 Z).filter (IsYRough Y), (1 : ℝ) / n) ^ (j ^ 2) ≤ Real.exp T := by
    calc (∑ n ∈ (Icc 1 Z).filter (IsYRough Y), (1 : ℝ) / n) ^ (j ^ 2)
        ≤ Real.exp (52 * (s + 1)) ^ (j ^ 2) := pow_le_pow_left₀ hSA0 hSA _
      _ = Real.exp (52 * (j : ℝ) ^ 2 * (s + 1)) := by
          rw [← exp_nat_mul]
          push_cast
          ring_nf
      _ ≤ Real.exp T := exp_le_exp.2 hj
  have hLT : Real.exp T = L := exp_log hL
  have hlogL : Real.log L = T := rfl
  have hL14 : L ^ (14 : ℝ) = L * Real.exp (12 * T) * Real.exp T := by
    rw [rpow_def_of_pos hL, hlogL, mul_assoc, ← exp_add]
    conv_rhs => rw [← hLT]
    rw [← exp_add]
    ring_nf
  calc ∑ w ∈ Icc 1 ⌊κ * x⌋₊, (if IsYRough Y (candidateStrip x (w + 1)) then
        ((Nat.finMulAntidiag (j ^ 2) (candidateStrip x (w + 1))).card : ℝ) else 0)
      ≤ ∑ v ∈ Icc 1 Z, (if IsYRough Y (candidateStrip x v) then
        ((Nat.finMulAntidiag (j ^ 2) (candidateStrip x v)).card : ℝ) else 0) :=
        sum_Icc_succ_le (f := fun v => if IsYRough Y (candidateStrip x v) then
          ((Nat.finMulAntidiag (j ^ 2) (candidateStrip x v)).card : ℝ) else 0)
          (fun n => by split_ifs <;> positivity) _
    _ ≤ Z * (∑ c ∈ (Icc 1 Z).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
          (1 : ℝ) / c) * (∑ n ∈ (Icc 1 Z).filter (IsYRough Y), (1 : ℝ) / n) ^ (j ^ 2) :=
        sum_card_finMulAntidiag_le (candidatePrimes x) Y (j ^ 2) Z
    _ ≤ (x * L) * Real.exp (12 * T) * Real.exp T := by
        gcongr
    _ = x * L ^ (14 : ℝ) := by rw [hL14]; ring

/-- The non-squarefree part of the mean square: at most `x`. -/
lemma sum_second_le_at {x κ E : ℝ} {j : ℕ}
    (hM : ∀ y z : ℝ, 2 ≤ y → y ≤ z →
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤ E / Real.log y)
    (hx : 1 < x) (hκ : 1 < κ) (hκL : κ + 1 ≤ Real.log x) (hT : 64 ≤ logLog x)
    (hL52 : logLog x ^ 52 ≤ Real.log x) (hEL : E ≤ Real.log x / logLog x ^ 25)
    (hj1 : 1 ≤ j) (hjT : (j : ℝ) ≤ logLog x) :
    ∑ w ∈ Icc 1 ⌊κ * x⌋₊,
      (if IsYRough (proxyCutoff x) (candidateStrip x (w + 1)) ∧
          ¬ Squarefree (candidateStrip x (w + 1)) then
        (j : ℝ) ^ (2 * ArithmeticFunction.cardFactors (candidateStrip x (w + 1))) else 0) ≤ x := by
  have hT1 : 1 ≤ logLog x := by linarith
  have hL25 : logLog x ^ 25 ≤ Real.log x :=
    (pow_le_pow_right₀ hT1 (by norm_num)).trans hL52
  obtain ⟨hY2, hYZ, hZ, hlogY, hrpos, hratio⟩ := core_scale_facts hx hκ hκL hT1 hL25
  set L := Real.log x
  set T := logLog x
  set s := logLogLog x
  set Y := proxyCutoff x
  set M := ⌊κ * x⌋₊
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := Real.log_pos hx
  have hs0 : 0 ≤ s := Real.log_nonneg hT1
  have hsT : s ≤ T := by
    have := Real.log_le_sub_one_of_pos (show 0 < T by linarith)
    simp only [s, logLogLog]
    linarith
  have hlY : 0 < Real.log Y := by rw [hlogY]; positivity
  have hY0 : 0 < Y := by linarith
  -- each nonzero term is at most `exp(4 T^{26})`
  set B := Real.exp (4 * T ^ 26)
  have hterm : ∀ w ∈ Icc 1 M,
      (if IsYRough Y (candidateStrip x (w + 1)) ∧ ¬ Squarefree (candidateStrip x (w + 1)) then
        (j : ℝ) ^ (2 * ArithmeticFunction.cardFactors (candidateStrip x (w + 1))) else 0) ≤
      if IsYRough Y (candidateStrip x (w + 1)) ∧ ¬ Squarefree (candidateStrip x (w + 1)) then
        B else 0 := by
    intro w hw
    split_ifs with h
    · have hn0 := stripPrimes_ne_zero (candidatePrimes x) (w + 1)
      have hsv : candidateStrip x (w + 1) ∣ w + 1 :=
        ⟨keepPrimes (candidatePrimes x) (w + 1),
          (stripPrimes_mul_keepPrimes _ (Nat.succ_ne_zero w)).symm⟩
      have hwM := (mem_Icc.1 hw).2
      have hnZ : candidateStrip x (w + 1) ≤ M + 1 :=
        (Nat.le_of_dvd (Nat.succ_pos w) hsv).trans (by omega)
      refine (pow_two_mul_cardFactors_le (by linarith) hj1 hn0 hnZ h.1).trans (exp_le_exp.2 ?_)
      have hlj : Real.log j ≤ T :=
        (Real.log_le_sub_one_of_pos (by exact_mod_cast hj1)).trans (by linarith)
      have hlj0 : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast hj1)
      calc 2 * Real.log j * (Real.log ((M + 1 : ℕ) : ℝ) / Real.log Y)
          ≤ 2 * T * (2 * T ^ 25) := by gcongr
        _ = 4 * T ^ 26 := by ring
    · exact le_rfl
  -- the number of nonzero terms
  have hcount := card_filter_not_squarefree_le x M
  push_cast at hYZ hrpos hratio
  have hsum : ∑ p ∈ primesIoc Y ((M : ℝ) + 1), ((M : ℝ) + 1) / (p * p) ≤
      ((M : ℝ) + 1) / Y * (26 * (s + 1)) := by
    have hm := (abs_le.1 (hM Y _ hY2 hYZ)).2
    have h1 : Real.log (Real.log ((M : ℝ) + 1) / Real.log Y) ≤ Real.log 2 + 25 * s := by
      calc Real.log (Real.log ((M : ℝ) + 1) / Real.log Y) ≤ Real.log (2 * T ^ 25) :=
            Real.log_le_log hrpos hratio
        _ = Real.log 2 + 25 * s := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            push_cast
            rfl
    have h2 : E / Real.log Y ≤ 1 := by
      rw [div_le_one hlY, hlogY]
      exact hEL
    have hp : ∀ p ∈ primesIoc Y ((M : ℝ) + 1),
        ((M : ℝ) + 1) / (p * p) ≤ ((M : ℝ) + 1) / Y * (1 / p) := by
      intro p hp
      obtain ⟨-, hYp, -⟩ := mem_primesIoc.1 hp
      have hp0 : (0 : ℝ) < p := hY0.trans hYp
      rw [div_mul_div_comm, mul_one]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right hYp.le hp0.le)
    calc ∑ p ∈ primesIoc Y ((M : ℝ) + 1), ((M : ℝ) + 1) / (p * p)
        ≤ ∑ p ∈ primesIoc Y ((M : ℝ) + 1), ((M : ℝ) + 1) / Y * (1 / p) := sum_le_sum hp
      _ = ((M : ℝ) + 1) / Y * ∑ p ∈ primesIoc Y ((M : ℝ) + 1), (1 : ℝ) / p := by rw [mul_sum]
      _ ≤ ((M : ℝ) + 1) / Y * (26 * (s + 1)) := by
          gcongr
          have := Real.log_two_lt_d9
          linarith
  -- `L · 26 (s + 1) · exp(4 T^{26}) ≤ Y`
  have hgrow : L * (26 * (s + 1)) * B ≤ Y := by
    have hLT : Real.exp T = L := exp_log hL
    have h26 : 26 * (s + 1) ≤ Real.exp (52 * T) := by
      have := add_one_le_exp (52 * T)
      linarith
    have hT27 : T ^ 27 ≤ L / T ^ 25 := by
      rw [le_div_iff₀ (by positivity)]
      calc T ^ 27 * T ^ 25 = T ^ 52 := by ring
        _ ≤ L := hL52
    have hexp : T + 52 * T + 4 * T ^ 26 ≤ T ^ 27 := by
      have h1 : 64 * T ^ 26 ≤ T * T ^ 26 := by gcongr
      have h2 : T ≤ T ^ 26 := le_self_pow₀ hT1 (by norm_num)
      have h3 : T ^ 27 = T * T ^ 26 := by ring
      linarith
    calc L * (26 * (s + 1)) * B ≤ Real.exp T * Real.exp (52 * T) * B := by
          rw [hLT]
          gcongr
      _ = Real.exp (T + 52 * T + 4 * T ^ 26) := by rw [← exp_add, ← exp_add]
      _ ≤ Real.exp (L / T ^ 25) := exp_le_exp.2 (hexp.trans hT27)
      _ = Y := rfl
  have hB0 : 0 ≤ B := (exp_pos _).le
  calc _ ≤ ∑ w ∈ Icc 1 M,
        (if IsYRough Y (candidateStrip x (w + 1)) ∧ ¬ Squarefree (candidateStrip x (w + 1)) then
          B else 0) := sum_le_sum hterm
    _ = (((Icc 1 M).filter fun w => IsYRough Y (candidateStrip x (w + 1)) ∧
          ¬ Squarefree (candidateStrip x (w + 1))).card : ℝ) * B := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ((M : ℝ) + 1) / Y * (26 * (s + 1)) * B := by
        gcongr
        exact hcount.trans hsum
    _ ≤ x * L / Y * (26 * (s + 1)) * B := by
        gcongr
        push_cast at hZ
        linarith
    _ = x * (L * (26 * (s + 1)) * B) / Y := by ring
    _ ≤ x * Y / Y := by gcongr
    _ = x := by field_simp

/-- E8 (the core moment bound at `r = 2`): for large `x` and `2 ≤ j ≤ J_c`,
`∑_{w ≤ κ x} G_j(w + 1)² ≤ x L^{15}`. -/
theorem eventually_sum_proxyCore_sq_le {c : ℝ} (hc : 0 < c) (Ch Cj κ : ℝ) (hκ : 1 < κ) :
    ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 2 ≤ j → j ≤ compositeCutoff Cj x →
      ∑ w ∈ Icc 1 ⌊κ * x⌋₊, proxyCore x (presieveExponent c Ch x) j (w + 1) ^ 2 ≤
        x * Real.log x ^ (15 : ℝ) := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  filter_upwards [eventually_coreFactor_le_one hc Ch, eventually_candidateGroups,
    eventually_gt_atTop 1, eventually_le_log (κ + 1), eventually_le_logLog (64 + E),
    eventually_logLog_rpow_le 52 one_pos,
    eventually_mul_logLogLog_cube_le (52 * (|Cj| + 1) ^ 2)]
    with x hb hgroups hx hκL hT hL52 hcube j hj2 hjJ
  set L := Real.log x
  set T := logLog x
  set s := logLogLog x
  set γ := presieveExponent c Ch x
  have hT64 : 64 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hL : 0 < L := Real.log_pos hx
  rw [rpow_one, show (52 : ℝ) = ((52 : ℕ) : ℝ) by norm_num, rpow_natCast] at hL52
  have hL25 : T ^ 25 ≤ L := (pow_le_pow_right₀ hT1 (by norm_num)).trans hL52
  have hEL : E ≤ L / T ^ 25 := by
    rw [le_div_iff₀ (by positivity)]
    calc E * T ^ 25 ≤ T * T ^ 25 := by gcongr; linarith
      _ = T ^ 26 := by ring
      _ ≤ T ^ 52 := pow_le_pow_right₀ hT1 (by norm_num)
      _ ≤ L := hL52
  have hγ0 : 0 ≤ γ := by
    simp only [γ, presieveExponent]
    positivity
  have hγ : 1 ≤ x ^ γ := one_le_rpow hx.le hγ0
  have hj1 : 1 ≤ j := by omega
  have hs0 : 0 ≤ s := Real.log_nonneg hT1
  -- `j ≤ (|C_j| + 1)(s + 1)`, so `52 j² (s + 1) ≤ T` and `j ≤ T`
  have hjs : (j : ℝ) ≤ (|Cj| + 1) * (s + 1) := by
    have h1 : (j : ℝ) ≤ ⌈Cj * s⌉₊ := by exact_mod_cast hjJ
    have h2 : (⌈Cj * s⌉₊ : ℝ) ≤ max (Cj * s) 0 + 1 :=
      (Nat.cast_le.2 (Nat.ceil_mono (le_max_left _ 0))).trans
        (Nat.ceil_lt_add_one (le_max_right _ _)).le
    have h3 : max (Cj * s) 0 ≤ |Cj| * s :=
      max_le ((le_abs_self (Cj * s)).trans (by rw [abs_mul, abs_of_nonneg hs0]))
        (by positivity)
    nlinarith [abs_nonneg Cj]
  have hj52 : 52 * (j : ℝ) ^ 2 * (s + 1) ≤ T := by
    refine le_trans ?_ hcube
    have h1 : (j : ℝ) ^ 2 ≤ ((|Cj| + 1) * (s + 1)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hjs 2
    nlinarith
  have hjT : (j : ℝ) ≤ T := by
    have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    nlinarith
  have hpt : ∀ w ∈ Icc 1 ⌊κ * x⌋₊, proxyCore x γ j (w + 1) ^ 2 ≤
      (if IsYRough (proxyCutoff x) (candidateStrip x (w + 1)) then
        ((Nat.finMulAntidiag (j ^ 2) (candidateStrip x (w + 1))).card : ℝ) else 0) +
      (if IsYRough (proxyCutoff x) (candidateStrip x (w + 1)) ∧
          ¬ Squarefree (candidateStrip x (w + 1)) then
        (j : ℝ) ^ (2 * ArithmeticFunction.cardFactors (candidateStrip x (w + 1))) else 0) :=
    fun w _ => proxyCore_sq_le hj1 hγ (hb j hj1) (w + 1)
  have h1 := sum_first_le_at (j := j) hM hx hκ hκL hT1 hL25 hEL hgroups hj52
  have h2 := sum_second_le_at (j := j) hM hx hκ hκL hT64 hL52 hEL hj1 hjT
  have hL15 : L ^ (14 : ℝ) + 1 ≤ L ^ (15 : ℝ) := by
    have hL2 : 2 ≤ L := by
      have := Real.log_le_sub_one_of_pos hL
      simp only [T, logLog] at hT
      linarith
    have h14 : 1 ≤ L ^ (14 : ℝ) := one_le_rpow (by linarith) (by norm_num)
    rw [show (15 : ℝ) = 14 + 1 by norm_num, rpow_add hL, rpow_one]
    nlinarith
  calc ∑ w ∈ Icc 1 ⌊κ * x⌋₊, proxyCore x γ j (w + 1) ^ 2
      ≤ ∑ w ∈ Icc 1 ⌊κ * x⌋₊, ((if IsYRough (proxyCutoff x) (candidateStrip x (w + 1)) then
          ((Nat.finMulAntidiag (j ^ 2) (candidateStrip x (w + 1))).card : ℝ) else 0) +
        (if IsYRough (proxyCutoff x) (candidateStrip x (w + 1)) ∧
            ¬ Squarefree (candidateStrip x (w + 1)) then
          (j : ℝ) ^ (2 * ArithmeticFunction.cardFactors (candidateStrip x (w + 1))) else 0)) :=
        sum_le_sum hpt
    _ ≤ x * L ^ (14 : ℝ) + x := by
        rw [sum_add_distrib]
        exact add_le_add h1 h2
    _ ≤ x * L ^ (15 : ℝ) := by nlinarith

end

end Erdos408
