module

public import Erdos408.Extraction.TypeII.Bands
public import Erdos408.OneSided.Setup

/-!
# Uniform band facts

The facts B1–B5 of `blueprint/one_sided_type_ii.md` §2, uniform over band exponents in a
fixed window. A band is `band x a = {p prime : exp(L^a) ≤ p ≤ exp(2 L^a)}` with `L = log x`.

* B1. Bands whose exponents differ by a fixed gap are eventually disjoint and ordered.
* B2. Band primes lie in `[exp(L^a), exp(2 L^a)]`. For exponents below `0.2` they are below
  the roughness level `W = exp(L^{0.24})`, so they divide no rough integer. For exponents
  above a fixed positive bound they exceed every fixed power of `L`.
* B3. The harmonic mass of a band is eventually in `[1/2, 1]` (Mertens).
* B4. `∑_{p ∈ band} 1/p² ≤ 2 exp(-L^a)` and `|band| ≤ exp(2 L^a)`.
* B5. A product of one prime from each band lies in
  `[exp(∑ L^{a_i}), exp(2 ∑ L^{a_i})]`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset

/-! ### Band membership and growth -/

/-- A band prime lies in `[exp(L^a), exp(2 L^a)]`. -/
theorem mem_band_bounds {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) :
    Real.exp (Real.log x ^ a) ≤ p ∧ (p : ℝ) ≤ Real.exp (2 * Real.log x ^ a) := by
  unfold band at hp
  rw [mem_filter, mem_Icc] at hp
  exact ⟨Nat.ceil_le.1 hp.1.1, (Nat.le_floor_iff (by positivity)).1 hp.1.2⟩

/-- Exponents at least `g` apart give `2 L^a < L^{a'}`, eventually. -/
theorem eventually_two_mul_rpow_lt {g : ℝ} (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ a a' : ℝ, a + g ≤ a' → 2 * Real.log x ^ a < Real.log x ^ a' := by
  have hLg := (tendsto_rpow_atTop hg).comp Real.tendsto_log_atTop
  filter_upwards [hLg.eventually_gt_atTop 2, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hL a a' h
  have hx' : 2 < Real.log x ^ g := hx
  have hLa : 0 < Real.log x ^ a := by positivity
  -- `L^{a'} ≥ L^a L^g > 2 L^a`
  calc 2 * Real.log x ^ a < Real.log x ^ a * Real.log x ^ g := by nlinarith
    _ = Real.log x ^ (a + g) := (Real.rpow_add (by linarith) a g).symm
    _ ≤ Real.log x ^ a' := Real.rpow_le_rpow_of_exponent_le hL h

/-! ### B1: disjoint and ordered -/

/-- Bands at least `g` apart are eventually disjoint. -/
theorem eventually_band_disjoint {g : ℝ} (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ a a' : ℝ, a + g ≤ a' → Disjoint (band x a) (band x a') := by
  filter_upwards [eventually_two_mul_rpow_lt hg] with x hx a a' h
  refine disjoint_left.2 fun p hp hp' => ?_
  have := Real.exp_lt_exp.2 (hx a a' h)
  linarith [(mem_band_bounds hp).2, (mem_band_bounds hp').1]

/-- Every prime of a band lies below every prime of a band at least `g` higher, eventually. -/
theorem eventually_band_lt {g : ℝ} (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ a a' : ℝ, a + g ≤ a' →
      ∀ p ∈ band x a, ∀ p' ∈ band x a', p < p' := by
  filter_upwards [eventually_two_mul_rpow_lt hg] with x hx a a' h p hp p' hp'
  have := Real.exp_lt_exp.2 (hx a a' h)
  exact_mod_cast (show (p : ℝ) < p' by
    linarith [(mem_band_bounds hp).2, (mem_band_bounds hp').1])

/-! ### B2: size of band primes -/

/-- A band prime is at least `exp(L^a)`. -/
theorem exp_le_of_mem_band {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) :
    Real.exp (Real.log x ^ a) ≤ p :=
  (mem_band_bounds hp).1

/-- A band prime is at most `exp(2 L^a)`. -/
theorem le_exp_of_mem_band {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) :
    (p : ℝ) ≤ Real.exp (2 * Real.log x ^ a) :=
  (mem_band_bounds hp).2

/-- For exponents at most `ahi < 0.2`, band primes are eventually below `W = exp(L^{0.24})`. -/
theorem eventually_lt_roughLevel {ahi : ℝ} (hahi : ahi < 1 / 5) :
    ∀ᶠ x : ℝ in atTop, ∀ a ≤ ahi, ∀ p ∈ band x a, (p : ℝ) < roughLevel x := by
  filter_upwards [eventually_two_mul_rpow_lt (show 0 < 0.24 - ahi by linarith)]
    with x hx a ha p hp
  have := Real.exp_lt_exp.2 (hx a 0.24 (by linarith))
  unfold roughLevel
  linarith [le_exp_of_mem_band hp]

/-- For exponents at most `ahi < 0.2`, band primes eventually divide no nonzero rough
integer. -/
theorem eventually_not_dvd_of_isRough {ahi : ℝ} (hahi : ahi < 1 / 5) :
    ∀ᶠ x : ℝ in atTop, ∀ a ≤ ahi, ∀ p ∈ band x a, ∀ m : ℕ, m ≠ 0 → IsRough x m → ¬ p ∣ m := by
  filter_upwards [eventually_lt_roughLevel hahi] with x hx a ha p hp m hm hrough hdvd
  have hpm : p ∈ m.primeFactors :=
    Nat.mem_primeFactors.2 ⟨TypeII.band_prime hp, hdvd, hm⟩
  linarith [hx a ha p hp, hrough p hpm]

/-- For exponents at least `alo > 0`, band primes eventually exceed `L^A` for any fixed
`A`. -/
theorem eventually_rpow_lt_of_mem_band {alo : ℝ} (halo : 0 < alo) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ a, alo ≤ a → ∀ p ∈ band x a, Real.log x ^ A < p := by
  have hexp := (tendsto_exp_div_rpow_atTop (A / alo)).comp
    ((tendsto_rpow_atTop halo).comp Real.tendsto_log_atTop)
  filter_upwards [hexp.eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hL a ha p hp
  have hx' : 1 < Real.exp (Real.log x ^ alo) / (Real.log x ^ alo) ^ (A / alo) := hx
  -- `(L^{alo})^{A/alo} = L^A`
  rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ halo.ne'] at hx'
  rw [one_lt_div (by positivity)] at hx'
  have hle : Real.exp (Real.log x ^ alo) ≤ Real.exp (Real.log x ^ a) :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL ha)
  linarith [exp_le_of_mem_band hp]

/-! ### B3: harmonic mass -/

/-- For exponents at least `alo ≥ 1/10`, the harmonic mass of a band is eventually in
`[1/2, 1]`. -/
theorem eventually_harmonicMass_band {alo : ℝ} (halo : 1 / 10 ≤ alo) :
    ∀ᶠ x : ℝ in atTop, ∀ a, alo ≤ a →
      1 / 2 ≤ harmonicMass (band x a) ∧ harmonicMass (band x a) ≤ 1 := by
  obtain ⟨L₀, hL₀⟩ := TypeII.harmonicMass_band_ge
  obtain ⟨E, hE0, hE⟩ := mertens_second
  have hL10 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop
  filter_upwards [hL10.eventually_ge_atTop (5 + 4 * E),
    Real.tendsto_log_atTop.eventually_ge_atTop (max L₀ 1)] with x hx hL a ha
  have hL1 : 1 ≤ Real.log x := le_of_max_le_right hL
  refine ⟨hL₀ x a (le_of_max_le_left hL) (halo.trans ha), ?_⟩
  set u := Real.log x ^ a with hu
  have hu5 : 5 + 4 * E ≤ u :=
    (show 5 + 4 * E ≤ Real.log x ^ (1 / 10 : ℝ) from hx).trans
      (Real.rpow_le_rpow_of_exponent_le hL1 (halo.trans ha))
  -- the band lies in `(exp(u - 1), exp(2u)]`
  have hsub : band x a ⊆ primesIoc (Real.exp (u - 1)) (Real.exp (2 * u)) := by
    intro p hp
    have := Real.exp_lt_exp.2 (show u - 1 < u by linarith)
    exact mem_primesIoc.2 ⟨TypeII.band_prime hp, by linarith [exp_le_of_mem_band hp],
      le_exp_of_mem_band hp⟩
  have hy2 : 2 ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have hm := hE (Real.exp (u - 1)) (Real.exp (2 * u)) hy2 (Real.exp_le_exp.2 (by linarith))
  rw [Real.log_exp, Real.log_exp, abs_le] at hm
  -- Mertens: `log (2u / (u - 1)) ≤ log 2 + 1 / (u - 1)`
  have hu1 : 0 < u - 1 := by linarith
  have hlog : Real.log (2 * u / (u - 1)) ≤ Real.log 2 + 1 / (u - 1) := by
    have hq : 0 < u / (u - 1) := div_pos (by linarith) hu1
    rw [mul_div_assoc, Real.log_mul two_ne_zero hq.ne']
    have h1 := Real.log_le_sub_one_of_pos hq
    have h2 : u / (u - 1) - 1 = 1 / (u - 1) := by field_simp; ring
    linarith
  have hEdiv : 1 / (u - 1) + E / (u - 1) ≤ 1 / 4 := by
    rw [← add_div, div_le_iff₀ hu1]
    linarith
  have hsum : harmonicMass (band x a) ≤
      ∑ p ∈ primesIoc (Real.exp (u - 1)) (Real.exp (2 * u)), (1 : ℝ) / p :=
    sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  linarith [hm.2, Real.log_two_lt_d9]

/-! ### B4: squares and cardinality -/

/-- `∑_{p ∈ band} 1/p² ≤ 2 exp(-L^a)`, for every `x` and `a`. -/
theorem sum_band_inv_sq_le (x a : ℝ) :
    ∑ p ∈ band x a, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 * Real.exp (-Real.log x ^ a) := by
  set N := ⌈Real.exp (Real.log x ^ a)⌉₊ with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.exp_pos _)).ne'
  -- the band lies in `(N - 1, M + 1)`
  have hsub : band x a ⊆ Ioo (N - 1) (⌊Real.exp (2 * Real.log x ^ a)⌋₊ + 1) := by
    intro p hp
    unfold band at hp
    rw [mem_filter, mem_Icc] at hp
    rw [mem_Ioo]
    omega
  have hcast : (((N - 1 : ℕ) : ℝ) + 1) = N := by
    rw [Nat.cast_sub hN1, Nat.cast_one, sub_add_cancel]
  calc ∑ p ∈ band x a, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Ioo (N - 1) (⌊Real.exp (2 * Real.log x ^ a)⌋₊ + 1), ((p : ℝ) ^ 2)⁻¹ := by
        simp_rw [one_div]
        exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ 2 / (((N - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ ≤ 2 / Real.exp (Real.log x ^ a) := by
        rw [hcast]
        exact div_le_div_of_nonneg_left zero_le_two (Real.exp_pos _) (Nat.le_ceil _)
    _ = 2 * Real.exp (-Real.log x ^ a) := by rw [Real.exp_neg, div_eq_mul_inv]

/-- A band has at most `exp(2 L^a)` primes. -/
theorem card_band_le (x a : ℝ) : ((band x a).card : ℝ) ≤ Real.exp (2 * Real.log x ^ a) := by
  have hN1 : 1 ≤ ⌈Real.exp (Real.log x ^ a)⌉₊ :=
    Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.exp_pos _)).ne'
  -- `|band| ≤ M + 1 - N ≤ M`
  have hcard : (band x a).card ≤ ⌊Real.exp (2 * Real.log x ^ a)⌋₊ := by
    unfold band
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    omega
  calc ((band x a).card : ℝ) ≤ ⌊Real.exp (2 * Real.log x ^ a)⌋₊ := by exact_mod_cast hcard
    _ ≤ Real.exp (2 * Real.log x ^ a) := Nat.floor_le (Real.exp_pos _).le

/-! ### B5: label products -/

/-- A product of one prime from each band lies in `[exp(∑ L^{a_i}), exp(2 ∑ L^{a_i})]`. -/
theorem labelProduct_bounds {K : ℕ} {x : ℝ} {a : Fin K → ℝ} {p : Fin K → ℕ}
    (hp : ∀ i, p i ∈ band x (a i)) :
    Real.exp (∑ i, Real.log x ^ a i) ≤ ∏ i, (p i : ℝ) ∧
      ∏ i, (p i : ℝ) ≤ Real.exp (2 * ∑ i, Real.log x ^ a i) := by
  constructor
  · rw [Real.exp_sum]
    exact prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ => exp_le_of_mem_band (hp i)
  · rw [mul_sum, Real.exp_sum]
    exact prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => le_exp_of_mem_band (hp i)

end Erdos408.OneSided
