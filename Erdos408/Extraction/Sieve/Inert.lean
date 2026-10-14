module

public import Erdos408.Extraction.Sieve.Basic
public import Erdos408.Extraction.Sieve.Model

/-!
# The clustered inert polynomial

Facts about `P = ∏_{c < K} (1 - ∏_i (1 - c_w w_{c,i}))` at the damping
`q = 1/2` and the constant `c_w = (1 - q)² / 3 = 1/12`.

* For large `x` every band exponent lies in `[0.11, 0.2]`, every band has
  reciprocal mass in `[1/2, 1]`, and the bands of one cluster are disjoint.
* `0 ≤ c_w w ≤ 1`, hence `0 ≤ P ≤ 1`.
* `P(n)` depends only on the band primes dividing `n`.
* The divisor-model failure `M(1 - P) ≤ K exp(-N / (12 e))` (E10), where `N`
  is the number of bands per cluster: within a cluster the band weights are
  independent in the model, each with mean at least `e⁻¹`.
-/

@[expose] public section

namespace Erdos408

open Filter Real Finset

namespace Sieve

noncomputable section

/-- All band primes of the inert polynomial. -/
def inertBands (K : ℕ) (CN x : ℝ) : Finset ℕ :=
  (range K ×ˢ range (inertPerCluster K CN x)).biUnion fun ci =>
    band x (inertExponent K x ci.1 ci.2)

/-- The band part `∏_{p ∈ 𝔅, p ∣ n} p` of `n`. -/
def bandPart (𝔅 : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ 𝔅.filter (· ∣ n), p

/-! ### Bands -/

/-- Membership in a band. -/
lemma mem_band {x a : ℝ} {p : ℕ} :
    p ∈ band x a ↔ p.Prime ∧ ⌈exp (Real.log x ^ a)⌉₊ ≤ p ∧ p ≤ ⌊exp (2 * Real.log x ^ a)⌋₊ := by
  simp only [band, mem_filter, mem_Icc]
  tauto

/-- Band primes lie in `[exp(L^a), exp(2 L^a)]`. -/
lemma le_of_mem_band {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) :
    exp (Real.log x ^ a) ≤ p ∧ (p : ℝ) ≤ exp (2 * Real.log x ^ a) := by
  obtain ⟨-, h1, h2⟩ := mem_band.1 hp
  exact ⟨Nat.ceil_le.1 h1, (Nat.le_floor_iff (exp_pos _).le).1 h2⟩

/-- Band primes are prime. -/
lemma prime_of_mem_band {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) : p.Prime :=
  (mem_band.1 hp).1

/-- The inert band primes are prime. -/
lemma prime_of_mem_inertBands {K : ℕ} {CN x : ℝ} {p : ℕ} (hp : p ∈ inertBands K CN x) :
    p.Prime := by
  obtain ⟨_, _, hp⟩ := mem_biUnion.1 hp
  exact prime_of_mem_band hp

/-- Each band lies in the inert band primes. -/
lemma band_subset_inertBands {K : ℕ} {CN x : ℝ} {c i : ℕ} (hc : c < K)
    (hi : i < inertPerCluster K CN x) : band x (inertExponent K x c i) ⊆ inertBands K CN x := by
  intro p hp
  unfold inertBands
  exact mem_biUnion.2 ⟨(c, i), mem_product.2 ⟨mem_range.2 hc, mem_range.2 hi⟩, hp⟩

/-- The band reciprocal mass is in `[1/2, 1]` once `L^a` is large. -/
lemma harmonicMass_band_mem : ∃ t₀ : ℝ, ∀ x a : ℝ, t₀ ≤ Real.log x ^ a →
    1 / 2 ≤ harmonicMass (band x a) ∧ harmonicMass (band x a) ≤ 1 := by
  obtain ⟨E, hE, h⟩ := mertens_second
  have hl2 : 0 < Real.log 2 := log_pos (by norm_num)
  have hl2' : Real.log 2 < 0.6931471808 := log_two_lt_d9
  have hl2'' : 0.6931471803 < Real.log 2 := log_two_gt_d9
  refine ⟨6 * E + 10 * (1 + E) + 4, fun x a ht => ?_⟩
  set t := Real.log x ^ a
  have ht0 : 0 < t := by linarith
  set y := exp t
  have hy : Real.log y = t := log_exp t
  have hz : Real.log (exp (2 * t)) = 2 * t := log_exp _
  have hy2 : 2 ≤ y := by
    have := add_one_le_exp t
    linarith
  have hnn : ∀ s : Finset ℕ, ∀ p ∈ s, 0 ≤ (1 : ℝ) / p := fun _ _ _ => by positivity
  constructor
  · -- `band ⊇ primesIoc y z`
    have hsub : primesIoc y (exp (2 * t)) ⊆ band x a := by
      intro p hp
      obtain ⟨hp, hlo, hhi⟩ := mem_primesIoc.1 hp
      exact mem_band.2 ⟨hp, Nat.ceil_le.2 hlo.le, Nat.le_floor hhi⟩
    have h1 := h y (exp (2 * t)) hy2 (exp_le_exp.2 (by linarith))
    rw [hy, hz, mul_div_assoc, div_self ht0.ne', mul_one] at h1
    have h2 := (abs_le.1 h1).1
    have h3 : E / t ≤ 1 / 6 := by
      rw [div_le_iff₀ ht0]
      linarith
    have := sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn _ p hp
    rw [harmonicMass]
    linarith
  · -- `band ⊆ primesIoc (y / 2) z`
    have hsub : band x a ⊆ primesIoc (y / 2) (exp (2 * t)) := by
      intro p hp
      obtain ⟨hlo, hhi⟩ := le_of_mem_band hp
      exact mem_primesIoc.2 ⟨prime_of_mem_band hp, by linarith [exp_pos t], hhi⟩
    have hy' : Real.log (y / 2) = t - Real.log 2 := by
      rw [log_div (exp_pos t).ne' (by norm_num), hy]
    have hd : 0 < t - Real.log 2 := by linarith
    have h1 := h (y / 2) (exp (2 * t)) (by
      have := add_one_le_exp t
      linarith) (by linarith [exp_le_exp.2 (show t ≤ 2 * t by linarith)])
    rw [hy', hz] at h1
    have h2 := (abs_le.1 h1).2
    -- `log (2t / (t - log 2)) ≤ log 2 + log 2 / (t - log 2)`
    have h3 : Real.log (2 * t / (t - Real.log 2)) ≤ Real.log 2 + Real.log 2 / (t - Real.log 2) := by
      rw [mul_div_assoc, log_mul (by norm_num) (by positivity)]
      have := log_le_sub_one_of_pos (show 0 < t / (t - Real.log 2) by positivity)
      have h4 : t / (t - Real.log 2) - 1 = Real.log 2 / (t - Real.log 2) := by
        field_simp
        ring
      linarith
    have h4 : (Real.log 2 + E) / (t - Real.log 2) ≤ 3 / 10 := by
      rw [div_le_iff₀ hd]
      linarith
    have h5 : Real.log 2 / (t - Real.log 2) + E / (t - Real.log 2) ≤ 3 / 10 := by
      rw [← add_div]
      exact h4
    have := sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn _ p hp
    rw [harmonicMass]
    linarith

/-- For large `x`, every band exponent of the inert polynomial lies in `[0.11, 0.2]`. -/
lemma eventually_inertExponent_mem {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) : ∀ᶠ x : ℝ in atTop,
    ∀ c < K, ∀ i < inertPerCluster K CN x,
      11 / 100 ≤ inertExponent K x c i ∧ inertExponent K x c i ≤ 1 / 5 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  filter_upwards [eventually_mul_logLogLog_le (200 * (|CN| / K + 1)),
    tendsto_logLog.eventually_ge_atTop 1] with x hT hT1
  intro c hc i hi
  set T := logLog x
  have hT0 : 0 < T := by linarith
  have hs0 : 0 ≤ logLogLog x := by
    rw [logLogLog]
    exact log_nonneg hT1
  have hc' : (c : ℝ) + 1 ≤ K := by exact_mod_cast hc
  have hi' : (i : ℝ) + 1 ≤ inertPerCluster K CN x := by exact_mod_cast hi
  have hN : (inertPerCluster K CN x : ℝ) ≤ |CN| / K * logLogLog x + 1 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ |CN| * logLogLog x / K by positivity)
    have h1 : (inertPerCluster K CN x : ℝ) ≤ ⌈|CN| * logLogLog x / K⌉₊ := by
      exact_mod_cast Nat.ceil_mono (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self CN) hs0) hK0.le)
    have h2 : |CN| * logLogLog x / K = |CN| / K * logLogLog x := by ring
    linarith
  rw [inertExponent]
  have hci : (c : ℝ) * (8 / 100 / K) ≤ 8 / 100 - 8 / 100 / K := by
    rw [show (8 : ℝ) / 100 - 8 / 100 / K = (K - 1) * (8 / 100 / K) by field_simp]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hii : (i : ℝ) * (2 / T) ≤ 1 / 100 := by
    rw [mul_div_assoc', div_le_iff₀ hT0]
    have : (i : ℝ) ≤ |CN| / K * logLogLog x := by linarith
    have : 0 ≤ |CN| / K := by positivity
    nlinarith
  constructor
  · have : 0 ≤ (c : ℝ) * (8 / 100 / K) := by positivity
    have : 0 ≤ (i : ℝ) * (2 / T) := by positivity
    linarith
  · have : 0 ≤ 8 / 100 / (K : ℝ) := by positivity
    linarith

/-- Bands whose exponents differ by at least `2 / T` are disjoint. -/
lemma disjoint_band {x a b : ℝ} (hL : 1 < Real.log x)
    (hab : a + 2 / logLog x ≤ b) : Disjoint (band x a) (band x b) := by
  rw [disjoint_left]
  intro p hpa hpb
  have hL0 : 0 < Real.log x := by linarith
  have hT : 0 < logLog x := log_pos hL
  obtain ⟨-, hpa⟩ := le_of_mem_band hpa
  obtain ⟨hpb, -⟩ := le_of_mem_band hpb
  -- `L^b ≥ L^a L^{2/T} = e² L^a > 2 L^a`
  have h1 : Real.log x ^ b ≥ Real.log x ^ a * exp 2 := by
    calc Real.log x ^ b ≥ Real.log x ^ (a + 2 / logLog x) :=
          rpow_le_rpow_of_exponent_le hL.le hab
      _ = Real.log x ^ a * exp 2 := by
          rw [rpow_add hL0, log_rpow_eq hL0 (2 / logLog x), div_mul_cancel₀ _ hT.ne']
  have h2 : (2 : ℝ) < exp 2 := by
    have := add_one_le_exp (2 : ℝ)
    linarith
  have h3 : 0 < Real.log x ^ a := rpow_pos_of_pos hL0 a
  have : 2 * Real.log x ^ a < Real.log x ^ b := by nlinarith
  have := exp_lt_exp.2 this
  linarith

/-- The bands of one cluster are pairwise disjoint. -/
lemma pairwiseDisjoint_cluster {K : ℕ} {CN x : ℝ} (hL : 1 < Real.log x) (c : ℕ) :
    ((range (inertPerCluster K CN x) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun i => band x (inertExponent K x c i) := by
  have hT : 0 < logLog x := log_pos hL
  have key : ∀ i j : ℕ, i < j →
      Disjoint (band x (inertExponent K x c i)) (band x (inertExponent K x c j)) := by
    intro i j hij
    refine disjoint_band hL ?_
    rw [inertExponent, inertExponent]
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have : 0 ≤ 2 / logLog x := by positivity
    nlinarith
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-! ### The band part -/

/-- For a set `𝔅` of primes and `p ∈ 𝔅`, `p ∣ bandPart 𝔅 n ↔ p ∣ n`. -/
lemma dvd_bandPart_iff {𝔅 : Finset ℕ} (h𝔅 : ∀ p ∈ 𝔅, p.Prime) {p : ℕ} (hp : p ∈ 𝔅) (n : ℕ) :
    p ∣ bandPart 𝔅 n ↔ p ∣ n := by
  rw [bandPart, (h𝔅 p hp).prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨hq𝔅, hqn⟩ := mem_filter.1 hq
    rwa [(Nat.prime_dvd_prime_iff_eq (h𝔅 p hp) (h𝔅 q hq𝔅)).1 hpq]
  · exact fun h => ⟨p, mem_filter.2 ⟨hp, h⟩, dvd_rfl⟩

/-- For a set `S` of primes, a prime `p` divides `∏ S` iff `p ∈ S`. -/
lemma dvd_prod_primes_iff {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ S, q ↔ p ∈ S := by
  rw [hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hpq⟩
    rwa [(Nat.prime_dvd_prime_iff_eq hp (hS q hq)).1 hpq]
  · exact fun h => ⟨p, h, dvd_rfl⟩

/-- The prime count of a band only sees the primes of the band dividing `n`. -/
lemma primeCount_congr {G : Finset ℕ} {n m : ℕ} (h : ∀ p ∈ G, p ∣ n ↔ p ∣ m) :
    primeCount G n = primeCount G m := by
  rw [primeCount, primeCount, filter_congr h]

/-- The prime count of a band of primes at a product of primes. -/
lemma primeCount_prod {G S : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) (hS : ∀ p ∈ S, p.Prime) :
    primeCount G (∏ p ∈ S, p) = #(S ∩ G) := by
  rw [primeCount, filter_congr fun p hp => dvd_prod_primes_iff hS (hG p hp), filter_mem_eq_inter,
    inter_comm]

/-! ### Bounds on the inert polynomial -/

/-- `m (1/2)^{m - 1} ≤ 1`. -/
lemma half_zpow_mul_le_one (m : ℕ) : (1 / 2 : ℝ) ^ ((m : ℤ) - 1) * m ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · have hz : (1 / 2 : ℝ) ^ ((m : ℤ) - 1) = ((2 : ℝ) ^ (m - 1))⁻¹ := by
      rw [show (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) by omega, zpow_natCast, one_div, inv_pow]
    rw [hz, inv_mul_le_iff₀ (by positivity), mul_one]
    have : m - 1 < 2 ^ (m - 1) := Nat.lt_two_pow_self
    have : m ≤ 2 ^ (m - 1) := by omega
    exact_mod_cast this

/-- The single-band weight `q^{ω - 1} ω / V`. -/
lemma bandWeight_eq (q x a : ℝ) (n : ℕ) : bandWeight q x a n =
    q ^ ((primeCount (band x a) n : ℤ) - 1) * primeCount (band x a) n /
      harmonicMass (band x a) := by
  simp [bandWeight, markedWeight, mul_div_assoc]

/-- If the band mass is at least `1/2`, then `0 ≤ c_w w ≤ 1` with `c_w = 1/12`. -/
lemma bandWeight_mem {x a : ℝ} (hV : 1 / 2 ≤ harmonicMass (band x a)) (n : ℕ) :
    0 ≤ 1 / 12 * bandWeight (1 / 2) x a n ∧ 1 / 12 * bandWeight (1 / 2) x a n ≤ 1 := by
  have hV0 : 0 < harmonicMass (band x a) := by linarith
  rw [bandWeight_eq]
  have h1 := half_zpow_mul_le_one (primeCount (band x a) n)
  have h0 : 0 ≤ (1 / 2 : ℝ) ^ ((primeCount (band x a) n : ℤ) - 1) * primeCount (band x a) n :=
    by positivity
  constructor
  · positivity
  · rw [mul_div_assoc', div_le_one hV0]
    nlinarith

/-- `1 - ∏ (1 - a_c) ≤ ∑ a_c` for `a_c ∈ [0, 1]`. -/
lemma one_sub_prod_one_sub_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) : 1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj]
    have ih := ih fun i hi => ha i (mem_insert_of_mem hi)
    have hp0 : 0 ≤ ∏ i ∈ s, (1 - a i) := prod_nonneg fun i hi => by
      linarith [(ha i (mem_insert_of_mem hi)).2]
    have hp1 : ∏ i ∈ s, (1 - a i) ≤ 1 := prod_le_one₀ (fun i hi => by
      linarith [(ha i (mem_insert_of_mem hi)).2]) fun i hi => by
      linarith [(ha i (mem_insert_of_mem hi)).1]
    have := ha j (mem_insert_self j s)
    nlinarith

/-- A product of numbers in `[0, 1]` is in `[0, 1]`. -/
lemma prod_mem_unit {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) :
    0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ 1 :=
  ⟨prod_nonneg fun i hi => (hf i hi).1, prod_le_one₀ (fun i hi => (hf i hi).1)
    fun i hi => (hf i hi).2⟩

/-- For large `x`, every band of the inert polynomial has mass in `[1/2, 1]`. -/
lemma eventually_harmonicMass_inert {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) : ∀ᶠ x : ℝ in atTop,
    ∀ c < K, ∀ i < inertPerCluster K CN x,
      1 / 2 ≤ harmonicMass (band x (inertExponent K x c i)) ∧
        harmonicMass (band x (inertExponent K x c i)) ≤ 1 := by
  obtain ⟨t₀, ht₀⟩ := harmonicMass_band_mem
  filter_upwards [eventually_inertExponent_mem hK CN,
    (tendsto_rpow_atTop (show (0 : ℝ) < 11 / 100 by norm_num)).comp tendsto_log_atTop
      |>.eventually_ge_atTop t₀, tendsto_log_atTop.eventually_ge_atTop 1] with x ha ht hL c hc i hi
  refine ht₀ x _ (le_trans ht ?_)
  exact rpow_le_rpow_of_exponent_le hL (ha c hc i hi).1

/-- For large `x`, `0 ≤ P ≤ 1`. -/
lemma eventually_inertPoly_mem {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) : ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
    0 ≤ inertPoly (1 / 2) (1 / 12) K CN x n ∧ inertPoly (1 / 2) (1 / 12) K CN x n ≤ 1 := by
  filter_upwards [eventually_harmonicMass_inert hK CN] with x hV n
  refine prod_mem_unit _ _ fun c hc => ?_
  have h := prod_mem_unit (range (inertPerCluster K CN x))
    (fun i => 1 - 1 / 12 * bandWeight (1 / 2) x (inertExponent K x c i) n) fun i hi => by
    have := bandWeight_mem (hV c (mem_range.1 hc) i (mem_range.1 hi)).1 n
    constructor <;> linarith
  constructor <;> linarith [h.1, h.2]

/-- `P(n)` only depends on the band primes dividing `n`. -/
lemma inertPoly_congr {q cw : ℝ} {K : ℕ} {CN x : ℝ} {n m : ℕ}
    (h : ∀ p ∈ inertBands K CN x, p ∣ n ↔ p ∣ m) :
    inertPoly q cw K CN x n = inertPoly q cw K CN x m := by
  unfold inertPoly
  refine prod_congr rfl fun c hc => congrArg (1 - ·) (prod_congr rfl fun i hi => ?_)
  have hsub := band_subset_inertBands (CN := CN) (mem_range.1 hc) (mem_range.1 hi)
  have hc' : primeCount (band x (inertExponent K x c i)) n =
      primeCount (band x (inertExponent K x c i)) m :=
    primeCount_congr fun p hp => h p (hsub hp)
  rw [bandWeight_eq, bandWeight_eq, hc']

/-- `P(n) = P(bandPart n)`. -/
lemma inertPoly_bandPart (q cw : ℝ) (K : ℕ) (CN x : ℝ) (n : ℕ) :
    inertPoly q cw K CN x n = inertPoly q cw K CN x (bandPart (inertBands K CN x) n) :=
  inertPoly_congr fun _ hp =>
    (dvd_bandPart_iff (fun _ h => prime_of_mem_inertBands h) hp n).symm

/-! ### The divisor-model failure of the inert polynomial (E10) -/

/-- `e^{-2t} ≤ 1 - t` for `0 ≤ t ≤ 1/2`. -/
lemma exp_neg_two_mul_le {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1 / 2) : exp (-(2 * t)) ≤ 1 - t := by
  have h1 := add_one_le_exp (2 * t)
  have h2 : 1 / (2 * t + 1) ≤ 1 - t := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : exp (-(2 * t)) ≤ 1 / (2 * t + 1) := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) h1
  linarith

/-- In the model, the damped band weight of a band `G` with mass `V ∈ [1/2, 1]` has
`E[1 - c_w w] ≤ exp(-1 / (12 e))`. -/
lemma modelMean_one_sub_bandWeight_le {G : Finset ℕ} (hG : ∀ p ∈ G, p.Prime)
    (hV : 1 / 2 ≤ harmonicMass G) (hV₁ : harmonicMass G ≤ 1) :
    modelMean G (fun T => 1 - 1 / 12 * ((1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T / harmonicMass G)) ≤
      exp (-(1 / (12 * exp 1))) := by
  have hG0 : ∀ p ∈ G, 0 < p := fun p hp => (hG p hp).pos
  have hV0 : 0 < harmonicMass G := by linarith
  have hlow := le_modelMean_card_mul_zpow hG0 (t := 1 / 2) (by norm_num) (by norm_num)
  -- `∏ (1 - (1/2)/p) ≥ exp(-V) ≥ e⁻¹`
  have hprod : exp (-1) ≤ ∏ p ∈ G, (1 - (1 - 1 / 2 : ℝ) / p) := by
    have h1 : ∏ p ∈ G, exp (-(2 * ((1 - 1 / 2 : ℝ) / p))) ≤ ∏ p ∈ G, (1 - (1 - 1 / 2 : ℝ) / p) := by
      refine prod_le_prod₀ (fun _ _ => (exp_pos _).le) fun p hp => exp_neg_two_mul_le
        (by have := hG0 p hp; positivity) ?_
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hG0 p hp
      rw [div_le_iff₀ (by linarith)]
      linarith
    rw [← exp_sum] at h1
    refine le_trans (exp_le_exp.2 ?_) h1
    rw [sum_neg_distrib, neg_le_neg_iff]
    have : ∑ p ∈ G, 2 * ((1 - 1 / 2 : ℝ) / p) = harmonicMass G := by
      rw [harmonicMass]
      exact sum_congr rfl fun p _ => by ring
    linarith
  have hmean : exp (-1) ≤ modelMean G (fun T => (1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T) /
      harmonicMass G := by
    rw [le_div_iff₀ hV0]
    have : harmonicMass G * exp (-1) ≤
        (∑ p ∈ G, (1 : ℝ) / p) * ∏ p ∈ G, (1 - (1 - 1 / 2 : ℝ) / p) :=
      mul_le_mul_of_nonneg_left hprod hV0.le
    rw [harmonicMass] at this ⊢
    linarith
  have hfun : (fun T : Finset ℕ =>
      1 - 1 / 12 * ((1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T / harmonicMass G)) =
      fun T => 1 - 1 / 12 * (harmonicMass G)⁻¹ * ((1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T) := by
    funext T
    rw [div_eq_mul_inv]
    ring
  rw [hfun, modelMean_sub, modelMean_const, modelMean_mul_left]
  have he : (exp 1)⁻¹ ≤ (harmonicMass G)⁻¹ *
      modelMean G (fun T => (1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T) := by
    rw [← exp_neg, mul_comm, ← div_eq_mul_inv]
    exact hmean
  calc 1 - 1 / 12 * (harmonicMass G)⁻¹ *
        modelMean G (fun T => (1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T)
      = 1 - 1 / 12 * ((harmonicMass G)⁻¹ *
        modelMean G (fun T => (1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T)) := by ring
    _ ≤ 1 - 1 / 12 * (exp 1)⁻¹ := by linarith
    _ = 1 - 1 / (12 * exp 1) := by ring
    _ ≤ exp (-(1 / (12 * exp 1))) := one_sub_le_exp_neg _

/-- E10: for large `x`, the divisor-model failure of the inert polynomial is
`M(1 - P) ≤ K exp(-N / (12 e))`, where `N = ⌈C_N s / K⌉` is the number of bands
per cluster. -/
lemma eventually_divisorModel_one_sub_inertPoly_le {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      divisorModel (inertBands K CN x) (fun n => 1 - inertPoly (1 / 2) (1 / 12) K CN x n) ≤
        K * exp (-(inertPerCluster K CN x / (12 * exp 1))) := by
  filter_upwards [eventually_harmonicMass_inert hK CN, eventually_gt_atTop (exp 1)]
    with x hV hx
  have hL : 1 < Real.log x := by
    rw [lt_log_iff_exp_lt (by linarith [exp_pos 1])]
    exact hx
  set 𝔅 := inertBands K CN x
  set N := inertPerCluster K CN x
  have h𝔅 : ∀ p ∈ 𝔅, p.Prime := fun p hp => prime_of_mem_inertBands hp
  have h𝔅0 : ∀ p ∈ 𝔅, 0 < p := fun p hp => (h𝔅 p hp).pos
  set G : ℕ → ℕ → Finset ℕ := fun c i => band x (inertExponent K x c i)
  have hG𝔅 : ∀ c ∈ range K, ∀ i ∈ range N, G c i ⊆ 𝔅 := fun c hc i hi =>
    band_subset_inertBands (mem_range.1 hc) (mem_range.1 hi)
  -- the cluster failure functions on subsets of `𝔅`
  set f : ℕ → ℕ → Finset ℕ → ℝ := fun c i T =>
    1 - 1 / 12 * ((1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T / harmonicMass (G c i))
  have hf : ∀ c ∈ range K, ∀ i ∈ range N, ∀ T, 0 ≤ f c i T ∧ f c i T ≤ 1 := by
    intro c hc i hi T
    have hV' := (hV c (mem_range.1 hc) i (mem_range.1 hi)).1
    have hV0 : 0 < harmonicMass (G c i) := by linarith
    have h1 := half_zpow_mul_le_one #T
    have h0 : 0 ≤ (1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T := by positivity
    have h2 : (1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T / harmonicMass (G c i) ≤ 2 := by
      rw [div_le_iff₀ hV0]
      nlinarith
    have h3 : 0 ≤ (1 / 2 : ℝ) ^ ((#T : ℤ) - 1) * #T / harmonicMass (G c i) := by positivity
    simp only [f]
    constructor <;> linarith
  -- `P(∏ S) = ∏_c (1 - ∏_i f_{c,i}(S ∩ G_{c,i}))` for `S ⊆ 𝔅`
  have hP : ∀ S ⊆ 𝔅, inertPoly (1 / 2) (1 / 12) K CN x (∏ p ∈ S, p) =
      ∏ c ∈ range K, (1 - ∏ i ∈ range N, f c i (S ∩ G c i)) := by
    intro S hS
    unfold inertPoly
    refine prod_congr rfl fun c hc => congrArg (1 - ·) (prod_congr rfl fun i hi => ?_)
    have hpc := primeCount_prod (G := G c i) (S := S) (fun p hp => prime_of_mem_band hp)
      fun p hp => h𝔅 p (hS hp)
    simp only [f, G]
    rw [bandWeight_eq, hpc]
  -- `1 - P ≤ ∑_c ∏_i f_{c,i}`
  have hle : ∀ S ⊆ 𝔅, 1 - inertPoly (1 / 2) (1 / 12) K CN x (∏ p ∈ S, p) ≤
      ∑ c ∈ range K, ∏ i ∈ range N, f c i (S ∩ G c i) := by
    intro S hS
    rw [hP S hS]
    exact one_sub_prod_one_sub_le _ _ fun c hc =>
      prod_mem_unit _ _ fun i hi => hf c hc i hi _
  calc divisorModel 𝔅 (fun n => 1 - inertPoly (1 / 2) (1 / 12) K CN x n)
      ≤ modelMean 𝔅 (fun S => ∑ c ∈ range K, ∏ i ∈ range N, f c i (S ∩ G c i)) :=
        modelMean_mono h𝔅0 hle
    _ = ∑ c ∈ range K, ∏ i ∈ range N, modelMean (G c i) (f c i) := by
        rw [modelMean_sum]
        refine sum_congr rfl fun c hc => ?_
        exact modelMean_prod (range N) (G c) (pairwiseDisjoint_cluster hL c)
          (biUnion_subset.2 fun i hi => hG𝔅 c hc i hi) (f c)
    _ ≤ ∑ _c ∈ range K, ∏ _i ∈ range N, exp (-(1 / (12 * exp 1))) := by
        refine sum_le_sum fun c hc => prod_le_prod₀ (fun i hi => ?_) fun i hi => ?_
        · exact modelMean_nonneg (fun p hp => (prime_of_mem_band hp).pos)
            fun T _ => (hf c hc i hi T).1
        · have hVci := hV c (mem_range.1 hc) i (mem_range.1 hi)
          exact modelMean_one_sub_bandWeight_le (fun p hp => prime_of_mem_band hp) hVci.1 hVci.2
    _ = K * exp (-(N / (12 * exp 1))) := by
        rw [prod_const, card_range, ← exp_nat_mul, sum_const, card_range, nsmul_eq_mul]
        congr 2
        ring

end

end Sieve

end Erdos408
