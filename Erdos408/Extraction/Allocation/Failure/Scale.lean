module

public import Erdos408.Extraction.Allocation.Failure.GroupBounds
public import Erdos408.Extraction.Allocation.Failure.Inner
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Summing the free-factor bound

The free-factor bound summed over the candidate parts `d` and the factors
`e₂, …, e_j`:

* the `v`-side: `∑_d (Φ_F(d) + δ) / d ≤ ∏_{p ∈ P} (1 - 1/p)⁻¹ ((1 - θ c₁/75)^{|F|} + δ)`,
  by factoring over the groups and the local loss `V_g ≥ ∏_{p ∈ g} (1 - 1/p)⁻¹ / 15`;
* `∑_e ∏ b(e_i) / ∏ e_i = (∑_a b(a) / a)^{j - 1}`;
* the tuples with `(A + 1) d ∏ e ≤ X` number at most `X/(A + 1) (1 + log X)^j`.
-/

@[expose] public section

namespace Erdos408

open Finset Real

noncomputable section

/-! ### The `v`-side sum -/

/-- The local loss of a group: `∑_{m g-factored} [ω_g(m) ≠ 1] / m ≤ (1 - β/15) ∏_{p ∈ g}
(1 - 1/p)⁻¹`. -/
lemma sum_local_le {g : Finset ℕ} (hg : SideGroup g) {X : ℕ} (hgX : ∀ p ∈ g, p ≤ X) {β : ℝ}
    (hβ : 0 ≤ β) :
    ∑ m ∈ (Icc 1 X).filter (· ∈ Nat.factoredNumbers g),
        (1 - β * (if primeCount g m = 1 then 1 else 0)) * (1 / (m : ℝ)) ≤
      (1 - β / 15) * ∏ p ∈ g, (1 - (1 : ℝ) / p)⁻¹ := by
  set Dg := (Icc 1 X).filter (· ∈ Nat.factoredNumbers g)
  have hgf : g.filter Nat.Prime = g := filter_true_of_mem hg.prime
  set Eg := ∏ p ∈ g, (1 - (1 : ℝ) / p)⁻¹
  have hsum : ∑ m ∈ Dg, (1 : ℝ) / m ≤ Eg := by
    have := sum_inv_le_prod_of_factored g Dg fun n hn => (mem_filter.1 hn).2
    rwa [hgf] at this
  have hgD : g ⊆ Dg.filter (fun m => primeCount g m = 1) := by
    intro p hp
    have hpr := hg.prime p hp
    refine mem_filter.2 ⟨mem_filter.2 ⟨mem_Icc.2 ⟨hpr.one_lt.le, hgX p hp⟩,
      Nat.mem_factoredNumbers_of_primeFactors_subset hpr.ne_zero (by
        rw [hpr.primeFactors]; exact singleton_subset_iff.2 hp)⟩, ?_⟩
    unfold primeCount
    rw [card_eq_one]
    refine ⟨p, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨hp, dvd_rfl⟩, fun q hq => ?_⟩⟩
    obtain ⟨hq, hqp⟩ := mem_filter.1 hq
    exact (Nat.prime_dvd_prime_iff_eq (hg.prime q hq) hpr).1 hqp
  have hlone : harmonicMass g ≤
      ∑ m ∈ Dg, (if primeCount g m = 1 then 1 else 0) * (1 / (m : ℝ)) := by
    have : ∑ m ∈ Dg, (if primeCount g m = 1 then 1 else 0) * (1 / (m : ℝ)) =
        ∑ m ∈ Dg.filter (fun m => primeCount g m = 1), (1 : ℝ) / m := by
      rw [Finset.sum_filter (fun m => primeCount g m = 1) (fun m => (1 : ℝ) / m)]
      exact sum_congr rfl fun m _ => by split_ifs <;> simp
    rw [this]
    exact sum_le_sum_of_subset_of_nonneg hgD fun m _ _ => by positivity
  -- `V_g ≥ E_g / 15`
  have hE : Eg ≤ 15 / 2 := by
    have h1 := prod_inv_one_sub_le_exp g
    rw [hgf] at h1
    have h2 : Real.exp (2 * ∑ p ∈ g, (1 : ℝ) / p) ≤ Real.exp 2 := by
      refine exp_le_exp.2 ?_
      have := hg.mass_le
      unfold harmonicMass at this
      linarith
    have h3 : Real.exp 2 < 15 / 2 := by
      have := Real.exp_one_lt_d9
      rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
      nlinarith [exp_pos 1]
    linarith
  have hV := hg.mass_ge
  calc ∑ m ∈ Dg, (1 - β * (if primeCount g m = 1 then 1 else 0)) * (1 / (m : ℝ))
      = ∑ m ∈ Dg, (1 : ℝ) / m -
          β * ∑ m ∈ Dg, (if primeCount g m = 1 then 1 else 0) * (1 / (m : ℝ)) := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun m _ => by ring
    _ ≤ Eg - β * harmonicMass g := by
        have := mul_le_mul_of_nonneg_left hlone hβ
        linarith
    _ ≤ (1 - β / 15) * Eg := by nlinarith

/-- The `v`-side sum: `∑_d (Φ_F(d) + δ)/d ≤ ∏_P (1 - 1/p)⁻¹ ((1 - θ c₁ / 75)^{|F|} + δ)`. -/
theorem sum_loneFactor_div_le {x : ℝ} (hx : 1 ≤ Real.log x)
    (hg : ∀ g ∈ candidateGroups x, SideGroup g) {F : Finset (Finset ℕ)}
    (hF : F ⊆ candidateGroups x) {X : ℕ} (hX : ∀ p ∈ candidatePrimes x, p ≤ X) {c₁ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ d ∈ (Icc 1 X).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
        (loneFactor c₁ F d + δ) / d ≤
      (∏ p ∈ candidatePrimes x, (1 - (1 : ℝ) / p)⁻¹) *
        ((1 - chernoffTheta * c₁ / 75) ^ F.card + δ) := by
  classical
  set P := candidatePrimes x
  set 𝒞 := candidateGroups x
  set D := (Icc 1 X).filter (· ∈ Nat.factoredNumbers P)
  set β := chernoffTheta * c₁ / 5
  have hβ : 0 ≤ β := by have := chernoffTheta_pos; positivity
  have hβ1 : β ≤ 1 := by
    have := chernoffTheta_le_one
    simp only [β]
    nlinarith
  have hdisj := pairwiseDisjoint_candidateGroups hx
  have hPf : P.filter Nat.Prime = P :=
    filter_true_of_mem fun p hp => prime_of_mem_candidatePrimes hp
  have hPP : ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ = ∏ g ∈ 𝒞, ∏ p ∈ g, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_biUnion hdisj
  have hEP0 : 0 ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).two_le
    have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    exact inv_nonneg.2 (by linarith)
  have hD : ∀ d ∈ D, d ≠ 0 ∧ ∀ p ∈ d.primeFactors, p ∈ 𝒞.biUnion id := by
    intro d hd
    obtain ⟨hd, hdP⟩ := mem_filter.1 hd
    exact ⟨Nat.ne_zero_of_mem_factoredNumbers hdP, fun p hp =>
      Nat.primeFactors_subset_of_mem_factoredNumbers hdP hp⟩
  -- `Φ(d)/d` factors over the groups
  set h : Finset ℕ → ℕ → ℝ := fun g m =>
    (if g ∈ F then 1 - β * (if primeCount g m = 1 then 1 else 0) else 1) * (1 / (m : ℝ))
  have hfac : ∀ d ∈ D, loneFactor c₁ F d / d = ∏ g ∈ 𝒞, h g (keepPrimes g d) := by
    intro d hd
    obtain ⟨hd0, hdP⟩ := hD d hd
    simp only [h]
    rw [prod_mul_distrib, prod_ite_mem, inter_eq_right.2 hF]
    have hprod : ∏ g ∈ 𝒞, (1 / (keepPrimes g d : ℝ)) = 1 / d := by
      rw [prod_div_distrib, prod_const_one, ← Nat.cast_prod, prod_keepPrimes_eq hdisj hd0 hdP]
    rw [hprod, loneFactor, div_eq_mul_one_div]
    congr 1
    refine prod_congr rfl fun g hgF => ?_
    have hgpr : ∀ p ∈ g, p.Prime := (hg g (hF hgF)).prime
    rw [primeCount_keepPrimes hgpr hd0]
  set Dg : Finset ℕ → Finset ℕ := fun g => (Icc 1 X).filter (· ∈ Nat.factoredNumbers g)
  have hDg : ∀ d ∈ D, ∀ g ∈ 𝒞, keepPrimes g d ∈ Dg g := by
    intro d hd g _
    obtain ⟨hd0, -⟩ := hD d hd
    have hkd : keepPrimes g d ∣ d := ⟨stripPrimes g d, by
      rw [mul_comm, stripPrimes_mul_keepPrimes g hd0]⟩
    refine mem_filter.2 ⟨mem_Icc.2 ⟨Nat.pos_of_ne_zero (keepPrimes_ne_zero g d),
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hkd).trans (mem_Icc.1 (mem_filter.1 hd).1).2⟩,
      Nat.mem_factoredNumbers_of_primeFactors_subset (keepPrimes_ne_zero g d)
        fun p hp => mem_of_mem_primeFactors_keepPrimes hp⟩
  have hh0 : ∀ g ∈ 𝒞, ∀ m ∈ Dg g, 0 ≤ h g m := by
    intro g _ m _
    simp only [h]
    refine mul_nonneg ?_ (by positivity)
    split_ifs <;> linarith
  have hloc : ∀ g ∈ 𝒞, ∑ m ∈ Dg g, h g m ≤
      (if g ∈ F then 1 - β / 15 else 1) * ∏ p ∈ g, (1 - (1 : ℝ) / p)⁻¹ := by
    intro g hg𝒞
    have hgX : ∀ p ∈ g, p ≤ X := fun p hp => hX p (mem_biUnion.2 ⟨g, hg𝒞, hp⟩)
    by_cases hgF : g ∈ F
    · simp only [h, hgF, ↓reduceIte]
      exact sum_local_le (hg g hg𝒞) hgX hβ
    · simp only [h, hgF, ↓reduceIte, one_mul]
      have := sum_inv_le_prod_of_factored g (Dg g) fun n hn => (mem_filter.1 hn).2
      rwa [filter_true_of_mem (hg g hg𝒞).prime] at this
  have hΦ : ∑ d ∈ D, loneFactor c₁ F d / d ≤
      (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) * (1 - β / 15) ^ F.card := by
    rw [sum_congr rfl hfac]
    refine (sum_prod_keepPrimes_le hdisj hD Dg hDg h hh0).trans ?_
    refine (prod_le_prod₀ (fun g hg𝒞 => sum_nonneg (hh0 g hg𝒞)) hloc).trans (le_of_eq ?_)
    rw [prod_mul_distrib, prod_ite_mem, inter_eq_right.2 hF, prod_const, hPP]
    ring
  have h1 : ∑ d ∈ D, (1 : ℝ) / d ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := by
    have := sum_inv_le_prod_of_factored P D fun n hn => (mem_filter.1 hn).2
    rwa [hPf] at this
  have hβ15 : β / 15 = chernoffTheta * c₁ / 75 := by simp only [β]; ring
  calc ∑ d ∈ D, (loneFactor c₁ F d + δ) / d
      = ∑ d ∈ D, loneFactor c₁ F d / d + δ * ∑ d ∈ D, (1 : ℝ) / d := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun d _ => by ring
    _ ≤ (∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹) * (1 - β / 15) ^ F.card +
          δ * ∏ p ∈ P, (1 - (1 : ℝ) / p)⁻¹ := add_le_add hΦ (mul_le_mul_of_nonneg_left h1 hδ)
    _ = _ := by rw [hβ15]; ring

/-! ### Counting tuples -/

/-- The `(d, e)` with `(A + 1) d ∏ e ≤ X` number at most `X/(A + 1) (1 + log X)^{m + 1}`. -/
lemma card_tuples_le (X A m : ℕ) :
    (((Icc 1 X ×ˢ Fintype.piFinset (fun _ : Fin m => Icc 1 X)).filter
        fun t => (A + 1) * ((∏ i, t.2 i) * t.1) ≤ X).card : ℝ) ≤
      (X : ℝ) / (A + 1) * (1 + Real.log X) ^ (m + 1) := by
  set T := Icc 1 X ×ˢ Fintype.piFinset (fun _ : Fin m => Icc 1 X)
  have hH : ∑ n ∈ Icc 1 X, (1 : ℝ) / n ≤ 1 + Real.log X := by
    have := harmonic_le_one_add_log X
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [one_div] using this
  have hpos : ∀ t ∈ T, (0 : ℝ) < t.1 * ∏ i, (t.2 i : ℝ) := by
    intro t ht
    obtain ⟨h1, h2⟩ := mem_product.1 ht
    have : (1 : ℝ) ≤ t.1 := by exact_mod_cast (mem_Icc.1 h1).1
    exact mul_pos (by linarith) (prod_pos fun i _ => by
      have : (1 : ℝ) ≤ t.2 i := by exact_mod_cast (mem_Icc.1 (Fintype.mem_piFinset.1 h2 i)).1
      linarith)
  calc (((T.filter fun t => (A + 1) * ((∏ i, t.2 i) * t.1) ≤ X).card : ℝ))
      ≤ ∑ t ∈ T.filter (fun t => (A + 1) * ((∏ i, t.2 i) * t.1) ≤ X),
          (X : ℝ) / (A + 1) / (t.1 * ∏ i, (t.2 i : ℝ)) := by
        rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
        refine sum_le_sum fun t ht => ?_
        obtain ⟨ht, hle⟩ := mem_filter.1 ht
        have hp := hpos t ht
        rw [le_div_iff₀ hp, one_mul, le_div_iff₀ (by positivity)]
        have : (((A + 1) * ((∏ i, t.2 i) * t.1) : ℕ) : ℝ) ≤ X := by exact_mod_cast hle
        push_cast at this
        linarith
    _ ≤ ∑ t ∈ T, (X : ℝ) / (A + 1) / (t.1 * ∏ i, (t.2 i : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t ht _ =>
          div_nonneg (by positivity) (hpos t ht).le
    _ = (X : ℝ) / (A + 1) * ((∑ n ∈ Icc 1 X, (1 : ℝ) / n) *
          (∑ n ∈ Icc 1 X, (1 : ℝ) / n) ^ m) := by
        have hpow : (∑ n ∈ Icc 1 X, (1 : ℝ) / n) ^ m =
            ∑ f ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 X), ∏ i, (1 : ℝ) / (f i) := by
          rw [← prod_univ_sum (t := fun _ => Icc 1 X) (f := fun _ n => (1 : ℝ) / n), prod_const,
            card_univ, Fintype.card_fin]
        rw [hpow, sum_mul_sum, mul_sum, sum_product]
        refine sum_congr rfl fun d _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun f _ => ?_
        rw [prod_div_distrib, prod_const_one]
        field_simp
    _ ≤ (X : ℝ) / (A + 1) * (1 + Real.log X) ^ (m + 1) := by
        have h0 : 0 ≤ ∑ n ∈ Icc 1 X, (1 : ℝ) / n := sum_nonneg fun n _ => by positivity
        rw [pow_succ']
        gcongr

/-! ### The free-factor sum -/

/-- `0 ≤ Φ_F(d) ≤ 1`. -/
lemma loneFactor_mem {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) (F : Finset (Finset ℕ))
    (d : ℕ) : 0 ≤ loneFactor c₁ F d ∧ loneFactor c₁ F d ≤ 1 := by
  have h0 : 0 ≤ chernoffTheta * c₁ / 5 := by have := chernoffTheta_pos; positivity
  have h1 : chernoffTheta * c₁ / 5 ≤ 1 := by
    have := chernoffTheta_le_one
    nlinarith [chernoffTheta_pos]
  refine ⟨prod_nonneg fun g _ => ?_, prod_le_one₀ (fun g _ => ?_) fun g _ => ?_⟩ <;>
    split_ifs <;> linarith

/-- A product of rough factors is free of the primes up to `Y`. -/
lemma not_dvd_prod_of_coreFactor_ne_zero {x γ : ℝ} {j m : ℕ} {e : Fin m → ℕ}
    (he : ∏ i, coreFactor x γ j (e i) ≠ 0) :
    ∀ p ∈ primesIcc 2 (proxyCutoff x), ¬ p ∣ ∏ i, e i := by
  intro p hp hpd
  obtain ⟨hpr, -, hpY⟩ := mem_primesIcc.1 hp
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpr.prime _).1 hpd
  have hne := prod_ne_zero_iff.1 he i (mem_univ i)
  unfold coreFactor at hne
  split_ifs at hne with h
  · have hei : e i ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, Real.log_zero, mul_zero, div_zero] at hne
      exact hne rfl
    have := h.2 p (Nat.mem_primeFactors.2 ⟨hpr, hi, hei⟩)
    linarith
  · exact hne rfl

/-- The bound for one `(d, e)`, as real arithmetic. -/
lemma term_le_of {Bc inner S0 W N Cnt Pi ε Φ δ wA Xr Bn : ℝ} (hBc0 : 0 ≤ Bc) (hBc1 : Bc ≤ 1)
    (hinner : inner ≤ S0 * (Φ + δ) + 4 * N * wA * Cnt) (hS0 : S0 ≤ W * (Bn * (Pi + 2 * ε) + N))
    (hBn : Bn ≤ Xr) (hwA : wA ≤ W) (hΦ0 : 0 ≤ Φ) (hΦ1 : Φ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hW : 0 ≤ W) (hN : 0 ≤ N) (hCnt : 0 ≤ Cnt) (hPi : 0 ≤ Pi) (hε : 0 ≤ ε) :
    Bc * inner ≤ Bc * (W * Xr * (Pi + 2 * ε) * (Φ + δ)) + W * N * (2 + 4 * Cnt) := by
  have hΦδ : 0 ≤ Φ + δ := by linarith
  have h1 : S0 * (Φ + δ) ≤ W * (Bn * (Pi + 2 * ε) + N) * (Φ + δ) :=
    mul_le_mul_of_nonneg_right hS0 hΦδ
  have h2 : W * (Bn * (Pi + 2 * ε)) ≤ W * (Xr * (Pi + 2 * ε)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBn (by linarith)) hW
  have h3 : W * (Bn * (Pi + 2 * ε)) * (Φ + δ) ≤ W * (Xr * (Pi + 2 * ε)) * (Φ + δ) :=
    mul_le_mul_of_nonneg_right h2 hΦδ
  have h4 : W * N * (Φ + δ) ≤ W * N * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hW hN)
  have h5 : 4 * N * wA * Cnt ≤ 4 * N * W * Cnt :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwA (by linarith)) hCnt
  have hin : inner ≤ W * Xr * (Pi + 2 * ε) * (Φ + δ) + W * N * (2 + 4 * Cnt) := by
    have : W * (Bn * (Pi + 2 * ε) + N) * (Φ + δ) =
        W * (Bn * (Pi + 2 * ε)) * (Φ + δ) + W * N * (Φ + δ) := by ring
    have : W * (Xr * (Pi + 2 * ε)) * (Φ + δ) = W * Xr * (Pi + 2 * ε) * (Φ + δ) := by ring
    linarith
  have hE0 : 0 ≤ W * N * (2 + 4 * Cnt) := by positivity
  calc Bc * inner ≤ Bc * (W * Xr * (Pi + 2 * ε) * (Φ + δ) + W * N * (2 + 4 * Cnt)) :=
        mul_le_mul_of_nonneg_left hin hBc0
    _ = Bc * (W * Xr * (Pi + 2 * ε) * (Φ + δ)) + Bc * (W * N * (2 + 4 * Cnt)) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left hE0 hBc1)

/-- Summing the main terms: `∑_d ∑_e ∏ b(e_i) / (∏ e_i d) c f(d) = c ∑_d f(d)/d (∑_a b(a)/a)^m`. -/
lemma sum_sum_prod_div_mul (D I : Finset ℕ) (m : ℕ) (b : ℕ → ℝ) (c : ℝ) (f : ℕ → ℝ) :
    ∑ d ∈ D, ∑ e ∈ Fintype.piFinset (fun _ : Fin m => I),
        (∏ i, b (e i)) / ((∏ i, (e i : ℝ)) * d) * (c * f d) =
      c * (∑ d ∈ D, f d / d) * (∑ a ∈ I, b a / a) ^ m := by
  have hpow : (∑ a ∈ I, b a / a) ^ m =
      ∑ e ∈ Fintype.piFinset (fun _ : Fin m => I), ∏ i, b (e i) / (e i) := by
    rw [← prod_univ_sum (t := fun _ => I) (f := fun _ a => b a / a), prod_const, card_univ,
      Fintype.card_fin]
  rw [hpow, mul_assoc, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun d _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [prod_div_distrib]
  by_cases hd : (d : ℝ) = 0
  · simp [hd]
  by_cases he : ∏ i, (e i : ℝ) = 0
  · simp [he]
  field_simp

/-- Summing the rounding terms over the tuples with `(A + 1) ∏ e d ≤ X`. -/
lemma sum_sum_ite_le (X A m : ℕ) {D : Finset ℕ} (hD : D ⊆ Icc 1 X) {c : ℝ} (hc : 0 ≤ c) :
    ∑ d ∈ D, ∑ e ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 X),
        (if (A + 1) * ((∏ i, e i) * d) ≤ X then c else 0) ≤
      c * ((X : ℝ) / (A + 1) * (1 + Real.log X) ^ (m + 1)) := by
  have hcount := card_tuples_le X A m
  have h1 : ∑ d ∈ D, ∑ e ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 X),
      (if (A + 1) * ((∏ i, e i) * d) ≤ X then c else 0) ≤
      c * (((Icc 1 X ×ˢ Fintype.piFinset (fun _ : Fin m => Icc 1 X)).filter
        fun t => (A + 1) * ((∏ i, t.2 i) * t.1) ≤ X).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter, sum_product]
    refine (sum_le_sum_of_subset_of_nonneg hD fun d _ _ =>
      sum_nonneg fun e _ => by split_ifs <;> linarith).trans (le_of_eq ?_)
    refine sum_congr rfl fun d _ => sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  exact h1.trans (mul_le_mul_of_nonneg_left hcount hc)

/-- The hypotheses on the weight `w = 1/(D_j log e)` above `A = ⌊x^γ⌋`. -/
structure WeightFacts (x γ : ℝ) (j X : ℕ) (W K : ℝ) : Prop where
  nonneg : ∀ e, 0 ≤ roughWeight x j e
  anti : ∀ e, ⌊x ^ γ⌋₊ < e → roughWeight x j (e + 1) ≤ roughWeight x j e
  le : ∀ e, ⌊x ^ γ⌋₊ < e → roughWeight x j e ≤ W
  ratio : ∀ e, ⌊x ^ γ⌋₊ < e → e ≤ X → roughWeight x j (⌊x ^ γ⌋₊ + 1) ≤ K * roughWeight x j e

/-- The bound for one `(d, e)`. -/
lemma free_term_le {x γ c₁ : ℝ} {j' X : ℕ} (R : ℕ) {F : Finset (Finset ℕ)}
    (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) (hF : ∀ g ∈ F, SideGroup g)
    (hFS : ∀ g ∈ F, g ⊆ primesIcc 2 (proxyCutoff x))
    (hdisj : (F : Set (Finset ℕ)).PairwiseDisjoint id) (hγ : 1 ≤ x ^ γ)
    (hb1 : ∀ e, coreFactor x γ (j' + 1) e ≤ 1) {W K : ℝ} (hW : 0 ≤ W) (hK0 : 0 ≤ K)
    (hwf : WeightFacts x γ (j' + 1) X W K)
    (hδ : 2 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
      K / ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) ≤ 1 / 2)
    (hδ' : 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
      ∏ p ∈ u, (1 : ℝ) / p) * K / (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
        (5 / 2) ^ F.card ≤ 1)
    {d : ℕ} (hd : 1 ≤ d) {e : Fin j' → ℕ} (he : ∀ i, 1 ≤ e i) :
    (∏ i, coreFactor x γ (j' + 1) (e i)) * ∑ a ∈ Ioc ⌊x ^ γ⌋₊ (X / ((∏ i, e i) * d)),
        (if ∀ p ∈ primesIcc 2 (proxyCutoff x), ¬ p ∣ a then roughWeight x (j' + 1) a else 0) *
          sideProd c₁ F d (a * ((∏ i, e i) * d) - 1) ≤
      (∏ i, coreFactor x γ (j' + 1) (e i)) / ((∏ i, (e i : ℝ)) * d) *
          (X * W * (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) +
            2 * ∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
          (loneFactor c₁ F d + 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
            ∏ p ∈ u, (1 : ℝ) / p) * K / (∏ p ∈ primesIcc 2 (proxyCutoff x),
              (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card)) +
        (if (⌊x ^ γ⌋₊ + 1) * ((∏ i, e i) * d) ≤ X then
          W * (((primesIcc 2 (proxyCutoff x)).powerset.filter (·.card ≤ R + 1)).card : ℝ) *
            (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) else 0) := by
  set S := primesIcc 2 (proxyCutoff x)
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (mem_primesIcc.1 hp).1
  have hA : 1 ≤ ⌊x ^ γ⌋₊ := Nat.le_floor (by simpa using hγ)
  have hj : 1 ≤ j' + 1 := by omega
  have hB0 : 0 ≤ ∏ i, coreFactor x γ (j' + 1) (e i) :=
    prod_nonneg fun i _ => coreFactor_nonneg hj hγ _
  have hB1 : ∏ i, coreFactor x γ (j' + 1) (e i) ≤ 1 :=
    prod_le_one₀ (fun i _ => coreFactor_nonneg hj hγ _) fun i _ => hb1 _
  have hr1 : 1 ≤ ∏ i, e i := by
    rw [Nat.one_le_iff_ne_zero, prod_ne_zero_iff]
    exact fun i _ => by have := he i; omega
  have hPi0 : 0 ≤ ∏ p ∈ S, (1 - (1 : ℝ) / p) := prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hε0 : 0 ≤ ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p :=
    sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  have hδ0 : 0 ≤ 8 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) * K /
      (∏ p ∈ S, (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card := by positivity
  have hCnt0 : 0 ≤ ∏ g ∈ F, ((lowSubsets g).card : ℝ) := prod_nonneg fun _ _ => by positivity
  have hite0 : 0 ≤ (if (⌊x ^ γ⌋₊ + 1) * ((∏ i, e i) * d) ≤ X then
      W * ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ) *
        (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) else 0) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg hW (Nat.cast_nonneg _)) (by linarith)
    · exact le_rfl
  have hlone := loneFactor_mem hc₁ hc₁' F d
  have hrd0 : (0 : ℝ) < (∏ i, (e i : ℝ)) * d := by
    have : (1 : ℝ) ≤ ∏ i, (e i : ℝ) := by exact_mod_cast hr1
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hmain0 : 0 ≤ (∏ i, coreFactor x γ (j' + 1) (e i)) / ((∏ i, (e i : ℝ)) * d) *
      (X * W * (∏ p ∈ S, (1 - (1 : ℝ) / p) +
        2 * ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
      (loneFactor c₁ F d + 8 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) * K /
        (∏ p ∈ S, (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card)) := by
    have := hlone.1
    positivity
  by_cases hB : ∏ i, coreFactor x γ (j' + 1) (e i) = 0
  · rw [hB, zero_mul, zero_div, zero_mul, zero_add]
    exact hite0
  have hrS := not_dvd_prod_of_coreFactor_ne_zero hB
  by_cases hAB : ⌊x ^ γ⌋₊ < X / ((∏ i, e i) * d)
  swap
  · rw [Ioc_eq_empty (by omega), sum_empty, mul_zero]
    linarith
  have hrdpos : 0 < (∏ i, e i) * d := Nat.mul_pos (by omega) (by omega)
  have hAX : (⌊x ^ γ⌋₊ + 1) * ((∏ i, e i) * d) ≤ X :=
    (Nat.le_div_iff_mul_le hrdpos).1 (show ⌊x ^ γ⌋₊ + 1 ≤ X / ((∏ i, e i) * d) by omega)
  rw [ite_eq_left hAX]
  have hBX : X / ((∏ i, e i) * d) ≤ X := Nat.div_le_self _ _
  have hinner := sum_free_le S hS hF hFS hdisj hc₁ hc₁' hd hr1 hrS R hA hwf.nonneg hwf.anti hK0
    (fun a ha => hwf.ratio a (mem_Ioc.1 ha).1 ((mem_Ioc.1 ha).2.trans hBX)) hδ
  have hS0 := sum_rough_weight_le S hS R (A := ⌊x ^ γ⌋₊) (B := X / ((∏ i, e i) * d))
    (w := roughWeight x (j' + 1)) (fun a ha => hwf.le a (mem_Ioc.1 ha).1) hW
  have hBn : ((X / ((∏ i, e i) * d) : ℕ) : ℝ) ≤ (X : ℝ) / ((∏ i, (e i : ℝ)) * d) := by
    have := Nat.cast_div_le (m := X) (n := (∏ i, e i) * d) (α := ℝ)
    push_cast at this
    exact this
  have h := term_le_of hB0 hB1 hinner hS0 hBn (hwf.le _ (by omega)) hlone.1 hlone.2 hδ0 hδ' hW
    (Nat.cast_nonneg _) hCnt0 hPi0 hε0
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp

/-- The free-factor sum: a main term `X W (Π + 2ε) ∑_d (Φ_F(d) + δ)/d (∑_a b(a)/a)^{j-1}` and a
rounding term `W N (2 + 4 ∏_g #K_g) X/(A + 1) (1 + log X)^j`. -/
theorem freeFactorSum_le {x γ c₁ : ℝ} {j' X : ℕ} (R : ℕ) {F : Finset (Finset ℕ)}
    (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) (hF : ∀ g ∈ F, SideGroup g)
    (hFS : ∀ g ∈ F, g ⊆ primesIcc 2 (proxyCutoff x))
    (hdisj : (F : Set (Finset ℕ)).PairwiseDisjoint id) (hγ : 1 ≤ x ^ γ)
    (hb1 : ∀ e, coreFactor x γ (j' + 1) e ≤ 1) {W K : ℝ} (hW : 0 ≤ W) (hK0 : 0 ≤ K)
    (hwf : WeightFacts x γ (j' + 1) X W K)
    (hδ : 2 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
      K / ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) ≤ 1 / 2)
    (hδ' : 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
      ∏ p ∈ u, (1 : ℝ) / p) * K / (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
        (5 / 2) ^ F.card ≤ 1) :
    freeFactorSum x γ c₁ j' X F ≤
      X * W * (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) +
          2 * ∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
        (∑ d ∈ (Icc 1 X).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
          (loneFactor c₁ F d + 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
            ∏ p ∈ u, (1 : ℝ) / p) * K / (∏ p ∈ primesIcc 2 (proxyCutoff x),
              (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card) / d) *
        (∑ a ∈ Icc 1 X, coreFactor x γ (j' + 1) a / a) ^ j' +
      W * (((primesIcc 2 (proxyCutoff x)).powerset.filter (·.card ≤ R + 1)).card : ℝ) *
        (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) *
        ((X : ℝ) / (⌊x ^ γ⌋₊ + 1) * (1 + Real.log X) ^ (j' + 1)) := by
  unfold freeFactorSum
  refine (sum_le_sum fun d hd => sum_le_sum fun e he => free_term_le R hc₁ hc₁' hF hFS hdisj hγ
    hb1 hW hK0 hwf hδ hδ' (mem_Icc.1 (mem_filter.1 hd).1).1
    fun i => (mem_Icc.1 (Fintype.mem_piFinset.1 he i)).1).trans ?_
  simp only [sum_add_distrib]
  refine add_le_add (le_of_eq ?_) ?_
  · exact sum_sum_prod_div_mul _ _ _ _ _ _
  · have hc : 0 ≤ W * (((primesIcc 2 (proxyCutoff x)).powerset.filter (·.card ≤ R + 1)).card : ℝ) *
        (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) := by
      have : 0 ≤ ∏ g ∈ F, ((lowSubsets g).card : ℝ) := prod_nonneg fun _ _ => by positivity
      exact mul_nonneg (mul_nonneg hW (Nat.cast_nonneg _)) (by linarith)
    exact sum_sum_ite_le X _ j' (filter_subset _ _) hc

end

end Erdos408
