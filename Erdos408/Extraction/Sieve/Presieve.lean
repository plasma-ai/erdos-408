module

public import Erdos408.Extraction.Sieve.Progression

/-!
# The presieve and mark removal (E0, E2, E10)

Put `z = x^γ` with `γ = (ε / 4) / (4h + 3)`. The presieved sum of a weight
`w` is `∑_{u ≤ κ x, P⁻(u + 1) > z} w(u)`.

* E0 (`eventually_slot_size`): `|f_𝔟(n)| ≤ T⁶¹` for `n ≤ x²` and `|C_𝔟| ≤ T⁴`.
* E10 (`eventually_mark_removal`): the upper block sieve at `h = 2` on
  `Φ (1 - P)` with the remainders of E1 gives
  `∑_p Φ((p-1)/x) (1 - P(p-1)) ≪ (x / L) (T²² M_x(1 - P) + 1/L)`.
* E2 (`eventually_presieve`): the block sieve at depth `h` on the
  nonnegative weights `Φ f_𝔟 P` and `Φ P` separately; the main terms cancel
  and `|∑_{P⁻(u+1) > z} Φ P (f_𝔟 - C_𝔟)| ≪ (x / L) (T²⁶ e^{-h} + T⁴ / L)`.
-/

@[expose] public section

namespace Erdos408

open Filter Real Finset

namespace Sieve

noncomputable section

/-- The presieved sum `∑_{1 ≤ u ≤ κ x, P⁻(u + 1) > z} w(u)`. -/
def presieved (κ x z : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ primesIcc 2 z, ¬ p ∣ u + 1), w u

/-! ### Size bounds (E0) -/

/-- E0: for large `x`, on admissible slots with `|𝔟| ≤ 1`, the slot count is at
most `T⁶¹` on `0 < n ≤ x²` and the harmonic mean is at most `T⁴`. -/
lemma eventually_slot_size {c : ℝ} (hc : 0 < c) : ∀ᶠ x : ℝ in atTop, ∀ k ≤ 2,
    ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ), AdmissibleSlots c x u v →
      (∀ Q, |B Q| ≤ 1) →
      (∀ n : ℕ, 0 < n → (n : ℝ) ≤ x ^ 2 → |slotCount x u v B n| ≤ logLog x ^ 61) ∧
        |slotMean x u v B| ≤ logLog x ^ 4 := by
  obtain ⟨E, hE, hmert⟩ := abs_sum_inv_primes_sub_le
  filter_upwards [eventually_ge_atTop 2,
    tendsto_logLog.eventually_ge_atTop (max (max c 1) (max E (8 / c ^ 3 + 8)))]
    with x hx2 hT k hk u v B hslot hB
  have hT1 : 1 ≤ logLog x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTc : c ≤ logLog x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTE : E ≤ logLog x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT8 : 8 / c ^ 3 + 8 ≤ logLog x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  set T := logLog x
  have hT0 : 0 < T := by linarith
  obtain ⟨hu, hv⟩ := hslot
  have hε : 0 < c / T ^ 20 := by positivity
  constructor
  · intro n hn hnx
    have h := abs_slotCount_le (v := v) (by linarith) hε hu hB hn hnx
    have h2 : 2 / (c / T ^ 20) = 2 * T ^ 20 / c := by field_simp
    rw [h2] at h
    have h1 : 1 ≤ 2 * T ^ 20 / c := by
      rw [le_div_iff₀ hc]
      have : T ≤ T ^ 20 := le_self_pow₀ hT1 (by norm_num)
      linarith
    calc |slotCount x u v B n| ≤ (2 * T ^ 20 / c) ^ (k + 1) := h
      _ ≤ (2 * T ^ 20 / c) ^ 3 := pow_le_pow_right₀ h1 (by omega)
      _ = 8 / c ^ 3 * T ^ 60 := by field_simp; ring
      _ ≤ T * T ^ 60 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith
      _ = T ^ 61 := by ring
  · have hv1 : ∑ i, v i ≤ 1 := by linarith
    have h1 := sum_inv_slotTuples_le (x := x) (by linarith) hv1 (u := u)
    have h2 := sum_inv_primes_le_logLog hmert hx2 le_rfl
    have h0 : 0 ≤ ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
    have h3 : |slotMean x u v B| ≤ ∑ Q ∈ slotTuples x u v, 1 / ∏ i, (Q i : ℝ) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q _ => ?_)
      have h0 : (0 : ℝ) ≤ ∏ i, (Q i : ℝ) := prod_nonneg fun i _ => Nat.cast_nonneg _
      rw [abs_div, abs_of_nonneg h0]
      exact div_le_div_of_nonneg_right (hB _) h0
    calc |slotMean x u v B| ≤ (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) := h3.trans h1
      _ ≤ (2 * T) ^ (k + 1) := pow_le_pow_left₀ h0 (by linarith) _
      _ ≤ (2 * T) ^ 3 := pow_le_pow_right₀ (by linarith) (by omega)
      _ = 8 * T ^ 3 := by ring
      _ ≤ T * T ^ 3 := by
          have h8 : 8 ≤ T := by
            have : 0 ≤ 8 / c ^ 3 := by positivity
            linarith
          exact mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = T ^ 4 := by ring

/-! ### Primes inject into the presieved integers -/

/-- `⌊κ x + 1⌋ = ⌊κ x⌋ + 1`. -/
lemma floor_add_one_eq {κ x : ℝ} (h : 0 ≤ κ * x) : ⌊κ * x + 1⌋₊ = ⌊κ * x⌋₊ + 1 :=
  Nat.floor_add_one h

/-- A nonnegative weight vanishing at `u ≤ z` has its prime sum at most its
presieved sum. -/
lemma sum_primes_le_presieved {κ x z : ℝ} (hκx : 0 ≤ κ * x) (f : ℕ → ℝ) (hf : ∀ u, 0 ≤ f u)
    (hfz : ∀ u : ℕ, f u ≠ 0 → z < u) :
    ∑ p ∈ primesIcc 2 (κ * x + 1), f (p - 1) ≤ presieved κ x z f := by
  set A := (primesIcc 2 (κ * x + 1)).filter fun p => f (p - 1) ≠ 0
  have hA : ∑ p ∈ primesIcc 2 (κ * x + 1), f (p - 1) = ∑ p ∈ A, f (p - 1) :=
    (sum_filter_ne_zero _).symm
  have hinj : Set.InjOn (fun p : ℕ => p - 1) A := by
    intro p hp q hq h
    have hp2 := (mem_primesIcc_two.1 (mem_filter.1 hp).1).1.two_le
    have hq2 := (mem_primesIcc_two.1 (mem_filter.1 hq).1).1.two_le
    simp only at h
    omega
  rw [hA, ← sum_image hinj]
  refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun u _ _ => hf u
  obtain ⟨p, hpA, rfl⟩ := mem_image.1 hu
  obtain ⟨hpP, hfp⟩ := mem_filter.1 hpA
  obtain ⟨hp, hpκ⟩ := mem_primesIcc_two.1 hpP
  have hp2 := hp.two_le
  have hzp : z < ((p - 1 : ℕ) : ℝ) := hfz _ hfp
  refine mem_filter.2 ⟨mem_Icc.2 ⟨by omega, ?_⟩, fun q hq hqd => ?_⟩
  · have : p ≤ ⌊κ * x + 1⌋₊ := Nat.le_floor hpκ
    rw [floor_add_one_eq hκx] at this
    omega
  · obtain ⟨hqp, hqz⟩ := mem_primesIcc_two.1 hq
    rw [Nat.sub_add_cancel (by omega)] at hqd
    have := (Nat.prime_dvd_prime_iff_eq hqp hp).1 hqd
    subst this
    have : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
    linarith

/-! ### The level `z = x^γ` -/

/-- For large `x`, `γ ≤ 1/40` and `κ z < x`, and `z^{4h+2} ≤ x^{ε/4}` with `z = x^γ`. -/
lemma eventually_level {c Ch κ : ℝ} (hc : 0 < c) (hCh : 0 < Ch) (hκ : 1 < κ) :
    ∀ᶠ x : ℝ in atTop,
    presieveExponent c Ch x ≤ 1 / 40 ∧ κ * x ^ presieveExponent c Ch x < x ∧
      (x ^ presieveExponent c Ch x) ^ (4 * sieveDepth Ch x + 2) ≤
        x ^ (c / logLog x ^ 20 / 4) := by
  filter_upwards [eventually_presieveExponent hc hCh, eventually_sieveDepth hCh 0,
    tendsto_logLog.eventually_ge_atTop (max c 1), eventually_ge_atTop 1,
    (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_gt_atTop κ]
    with x ⟨hγ0, _, _, hγlev⟩ ⟨_, hh2, _⟩ hT hx1 hxκ
  have hT1 : 1 ≤ logLog x := le_trans (le_max_right _ _) hT
  have hε : c / logLog x ^ 20 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact (le_max_left _ _).trans (hT.trans (le_self_pow₀ hT1 (by norm_num)))
  have hh : (2 : ℝ) ≤ sieveDepth Ch x := by exact_mod_cast hh2
  have hγ : presieveExponent c Ch x ≤ 1 / 40 := by nlinarith
  have hx0 : 0 < x := by linarith
  refine ⟨hγ, ?_, ?_⟩
  · have h1 : x ^ presieveExponent c Ch x ≤ x ^ (1 / 2 : ℝ) :=
      rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
      rw [← rpow_add hx0]
      norm_num
    have h3 : 0 < x ^ (1 / 2 : ℝ) := by positivity
    have h4 : κ * x ^ presieveExponent c Ch x ≤ κ * x ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  · rw [← rpow_natCast, ← rpow_mul hx0.le]
    refine rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    linarith

/-- Combining the upper sieve with bounds on its main term and remainders. -/
lemma combine_bound {sift main rem KB A B₁ B₂ : ℝ} (hup : sift ≤ KB * main + KB * rem)
    (hmain0 : 0 ≤ main) (hrem0 : 0 ≤ rem) (hmain : main ≤ A * B₁) (hrem : rem ≤ A * B₂) :
    sift ≤ |KB| * (A * (B₁ + B₂)) := by
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self KB) hmain0
  have h2 := mul_le_mul_of_nonneg_right (le_abs_self KB) hrem0
  have h3 := mul_le_mul_of_nonneg_left hmain (abs_nonneg KB)
  have h4 := mul_le_mul_of_nonneg_left hrem (abs_nonneg KB)
  nlinarith

/-- `a u + b w ≤ (a + b)(u + w)` for nonnegative numbers. -/
lemma add_mul_le_add_mul_add {a b u w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    a * u + b * w ≤ (a + b) * (u + w) := by
  nlinarith [mul_nonneg ha hw, mul_nonneg hb hu]

/-! ### Mark removal (E10) -/

/-- E10: the upper block sieve on `Φ(u/x)(1 - P(u))`. For large `x`,
`∑_p Φ((p-1)/x) (1 - P(p-1)) ≤ C (x / L) (T²² M_x(1 - P) + 1/L)`, and
`M_x(1 - P) ≤ K exp(-N / (12 e))`. -/
theorem eventually_mark_removal (h₃ : BlockSieve) {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) {c Ch κ CΦ : ℝ}
    (M : ℕ → ℝ) (hc : 0 < c) (hCh : 0 < Ch) (hκ : 1 < κ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ Φ : ℝ → ℝ, IsCutoff κ CΦ M x Φ →
      ∑ p ∈ primesIcc 2 (κ * x + 1),
          Φ (((p : ℝ) - 1) / x) * (1 - inertPoly (1 / 2) (1 / 12) K CN x (p - 1)) ≤
        C * (x / Real.log x) * (logLog x ^ 22 * exp (-(inertPerCluster K CN x / (12 * exp 1))) +
          1 / Real.log x) := by
  obtain ⟨C₀, hC₀⟩ := sum_inv_primes_block_le
  obtain ⟨h₀, KB, hBS⟩ := h₃ (1 / 2) C₀ (by norm_num)
  obtain ⟨CM, hCM, hprod⟩ := prod_one_sub_inv_primes_le
  obtain ⟨CE, hE1⟩ := eventually_progression_one h₃ hK CN c κ CΦ M hc hκ
  refine ⟨|KB| * (κ * |M 0| * CM * K + |CE|), ?_⟩
  filter_upwards [hE1, eventually_presieveExponent hc hCh, eventually_sieveDepth hCh h₀,
    eventually_inertPoly_mem hK CN, eventually_divisorModel_one_sub_inertPoly_le hK CN,
    eventually_level hc hCh hκ, eventually_ge_atTop 1,
    tendsto_log_atTop.eventually_gt_atTop 0, tendsto_logLog.eventually_gt_atTop 0,
    eventually_mul_rpow_le_log_rpow 1 22 one_pos]
    with x hE1x ⟨hγ0, _, hγinv, _⟩ ⟨_, hh2, _⟩ hP hM1P ⟨_, hκz, hlev⟩ hx1 hL hT hT22 Φ hΦ
  have hx0 : 0 < x := by linarith
  rw [one_mul, rpow_one, show (22 : ℝ) = ((22 : ℕ) : ℝ) by norm_num, rpow_natCast] at hT22
  set γ := presieveExponent c Ch x
  set z := x ^ γ
  set h := sieveDepth Ch x
  set 𝔅 := inertBands K CN x
  set P := primesIcc 2 z
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_primesIcc_two.1 hp).1
  set f : ℕ → ℝ := fun u => Φ (u / x) * (1 - inertPoly (1 / 2) (1 / 12) K CN x u)
  have hf0 : ∀ u, 0 ≤ f u := fun u => mul_nonneg (hΦ.2.1 _) (by linarith [(hP u).2])
  have hκx : 0 ≤ κ * x := by positivity
  -- the prime sum is at most the presieved sum
  have hfz : ∀ u : ℕ, f u ≠ 0 → z < u := by
    intro u hu
    have hΦu : Φ (u / x) ≠ 0 := fun h0 => hu (by simp only [f, h0, zero_mul])
    have h1 := (hΦ.2.2.1 _ hΦu).1
    rw [inv_le_iff_one_le_mul₀ (by linarith)] at h1
    have h2 : x ≤ u * κ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hx0, one_mul] at h1
      exact h1
    nlinarith
  have hstep1 : ∑ p ∈ primesIcc 2 (κ * x + 1),
      Φ (((p : ℝ) - 1) / x) * (1 - inertPoly (1 / 2) (1 / 12) K CN x (p - 1)) =
      ∑ p ∈ primesIcc 2 (κ * x + 1), f (p - 1) := by
    refine sum_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (mem_primesIcc_two.1 hp).1.one_lt.le
    simp only [f, Nat.cast_sub hp1, Nat.cast_one]
  rw [hstep1]
  refine (sum_primes_le_presieved hκx f hf0 hfz).trans ?_
  -- the upper block sieve
  set I := cutoffMass κ x Φ
  set m := divisorModel 𝔅 fun n => 1 - inertPoly (1 / 2) (1 / 12) K CN x n
  have hI0 : 0 ≤ I := cutoffMass_nonneg hx0 hΦ
  have hI : I ≤ κ * M 0 := cutoffMass_le hκ hx0 hΦ
  have hm0 : 0 ≤ m := modelMean_nonneg (fun p hp => (prime_of_mem_inertBands hp).pos)
    fun S _ => by linarith [(hP (∏ p ∈ S, p)).2]
  have hBS' := hBS (Icc 1 ⌊κ * x⌋₊) f P z (x * I * m) (fun p u => p ∣ u + 1)
    (fun p => 1 / (p : ℝ)) (fun u _ => hf0 u) (one_le_rpow hx1 hγ0.le)
    (fun p hp => mem_primesIcc_two.1 hp)
    (by positivity) (fun p hp => by
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
      constructor
      · positivity
      · rw [div_le_iff₀ (by linarith)]
        linarith)
    (hC₀ P hPp)
  simp only at hBS'
  have hup := hBS'.2
  -- the main term
  have hγL : logLog x ^ 22 / Real.log x * (γ * Real.log x) ≥ 1 := by
    rw [one_div, inv_le_iff_one_le_mul₀ hγ0] at hγinv
    rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hL, one_mul]
    nlinarith
  have hγL1 : 1 ≤ γ * Real.log x := by
    have h1 : logLog x ^ 22 / Real.log x ≤ 1 := by rw [div_le_one hL]; exact hT22
    have h2 : 0 ≤ γ * Real.log x := by positivity
    nlinarith
  have hlz : Real.log z = γ * Real.log x := Real.log_rpow hx0 γ
  have hz2 : 2 ≤ z := by
    have h1 : z = exp (γ * Real.log x) := by rw [← hlz, exp_log (by positivity)]
    rw [h1]
    linarith [add_one_le_exp (γ * Real.log x)]
  have hprodP : ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ CM * logLog x ^ 22 / Real.log x := by
    rw [show P = primesIoc 1 z from primesIcc_two_eq z]
    refine (hprod z hz2).trans ?_
    have hTγ : 1 ≤ logLog x ^ 22 * γ := by
      rw [one_div, inv_le_iff_one_le_mul₀ hγ0] at hγinv
      linarith
    rw [hlz, div_le_div_iff₀ (by positivity) hL]
    have := mul_le_mul_of_nonneg_left hTγ (mul_nonneg hCM.le hL.le)
    nlinarith
  have hP0 : 0 ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) := prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hmain : x * I * m * ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤
      x / Real.log x * (κ * |M 0| * CM * K * (logLog x ^ 22 *
        exp (-(inertPerCluster K CN x / (12 * exp 1))))) := by
    have hI' : I ≤ κ * |M 0| := hI.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith))
    calc x * I * m * ∏ p ∈ P, (1 - 1 / (p : ℝ))
        ≤ x * (κ * |M 0|) * (K * exp (-(inertPerCluster K CN x / (12 * exp 1)))) *
            (CM * logLog x ^ 22 / Real.log x) := by
          have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
          have hM0 : 0 ≤ κ * |M 0| := mul_nonneg (by linarith) (abs_nonneg _)
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hI' hx0.le) (hM1P.trans
            (le_refl _)) hm0 (mul_nonneg hx0.le hM0)) hprodP hP0
            (mul_nonneg (mul_nonneg hx0.le hM0) (mul_nonneg hK0 (exp_pos _).le))
      _ = _ := by ring
  have hmain0 : 0 ≤ x * I * m * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    refine mul_nonneg (by positivity) (prod_nonneg fun p hp => ?_)
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  -- the remainders
  have hrem := sum_powerset_rem_le hPp (Icc 1 ⌊κ * x⌋₊) f (x * I * m)
    ((pow_le_pow_right₀ (one_le_rpow hx1 hγ0.le) (by omega : 10 ≤ 4 * h + 2)).trans hlev)
  have hE := hE1x Φ (fun n => 1 - inertPoly (1 / 2) (1 / 12) K CN x n) hΦ
    (fun n => by rw [abs_le]; constructor <;> linarith [hP n]) (fun n => by
      rw [← inertPoly_bandPart])
  have hrem' : ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
      |∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ D, p ∣ u + 1), f u -
        x * I * m * ∏ p ∈ D, 1 / (p : ℝ)| ≤ |CE| * x / Real.log x ^ 2 := by
    refine hrem.trans (le_trans (le_of_eq (sum_congr rfl fun r _ => ?_)) (hE.trans ?_))
    · congr 1
      congr 1
      ring
    · gcongr
      exact le_abs_self _
  have hrem0 : 0 ≤ ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10),
      |∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ D, p ∣ u + 1), f u -
        x * I * m * ∏ p ∈ D, 1 / (p : ℝ)| := sum_nonneg fun _ _ => abs_nonneg _
  have hx2 : |CE| * x / Real.log x ^ 2 = x / Real.log x * (|CE| * (1 / Real.log x)) := by
    field_simp
  rw [hx2] at hrem'
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hM0 : 0 ≤ κ * |M 0| * CM * K := by
    have : 0 ≤ κ := by linarith
    positivity
  have hTe : 0 ≤ logLog x ^ 22 * exp (-(inertPerCluster K CN x / (12 * exp 1))) :=
    mul_nonneg (by positivity) (exp_pos _).le
  have hiL : 0 ≤ 1 / Real.log x := by positivity
  calc _ ≤ _ := combine_bound hup hmain0 hrem0 hmain hrem'
    _ ≤ |KB| * (x / Real.log x * ((κ * |M 0| * CM * K + |CE|) *
        (logLog x ^ 22 * exp (-(inertPerCluster K CN x / (12 * exp 1))) + 1 / Real.log x))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_mul_le_add_mul_add hM0 (abs_nonneg _) hTe hiL) (by positivity)) (abs_nonneg _)
    _ = _ := by ring

/-! ### The presieve (E2) -/

/-- The cancellation of the two main terms in E2. -/
lemma presieve_cancel {D₁ D₂ C main₂ e R₁ R₂ KB : ℝ}
    (h1 : |D₁| ≤ KB * e * (C * main₂) + KB * R₁) (h2 : |D₂| ≤ KB * e * main₂ + KB * R₂)
    (hC : 0 ≤ C) (hm : 0 ≤ main₂) (he : 0 ≤ e) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    |D₁ - C * D₂| ≤ |KB| * (2 * (C * (e * main₂)) + R₁ + C * R₂) := by
  have hK1 : KB * e * (C * main₂) ≤ |KB| * e * (C * main₂) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) he) (by positivity)
  have hK2 : KB * R₁ ≤ |KB| * R₁ := mul_le_mul_of_nonneg_right (le_abs_self _) hR₁
  have hK3 : KB * e * main₂ ≤ |KB| * e * main₂ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) he) hm
  have hK4 : KB * R₂ ≤ |KB| * R₂ := mul_le_mul_of_nonneg_right (le_abs_self _) hR₂
  have h3 : |C * D₂| ≤ C * (|KB| * e * main₂ + |KB| * R₂) := by
    rw [abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (by linarith) hC
  calc |D₁ - C * D₂| ≤ |D₁| + |C * D₂| := abs_sub _ _
    _ ≤ _ := by nlinarith

/-- The bookkeeping of E2. -/
lemma presieve_budget {KB C e m R₁ R₂ A T₄ T₂₂ B E₁ E₂ iL : ℝ} (hA : 0 ≤ A)
    (hCT : C ≤ T₄) (hT₄ : 1 ≤ T₄) (he : 0 ≤ e) (hm : 0 ≤ m) (hB : 0 ≤ B) (hT₂₂ : 0 ≤ T₂₂)
    (hiL : 0 ≤ iL) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂) (hR₂0 : 0 ≤ R₂)
    (hmain : m ≤ A * (B * T₂₂)) (hR₁ : R₁ ≤ A * (E₁ * iL)) (hR₂ : R₂ ≤ A * (E₂ * iL)) :
    |KB| * (2 * (C * (e * m)) + R₁ + C * R₂) ≤
      |KB| * (2 * B + E₁ + E₂) * A * (T₄ * T₂₂ * e + T₄ * iL) := by
  have h1 : C * (e * m) ≤ T₄ * (e * (A * (B * T₂₂))) :=
    mul_le_mul hCT (mul_le_mul_of_nonneg_left hmain he) (by positivity) (by linarith)
  have hAE₁ : 0 ≤ A * (E₁ * iL) := by positivity
  have h2 : R₁ ≤ T₄ * (A * (E₁ * iL)) := by nlinarith
  have h3 : C * R₂ ≤ T₄ * (A * (E₂ * iL)) := mul_le_mul hCT hR₂ hR₂0 (by linarith)
  have h4 : 2 * (C * (e * m)) + R₁ + C * R₂ ≤ A * ((2 * B) * (T₄ * T₂₂ * e) +
      (E₁ + E₂) * (T₄ * iL)) := by nlinarith
  have h5 : (2 * B) * (T₄ * T₂₂ * e) + (E₁ + E₂) * (T₄ * iL) ≤
      (2 * B + (E₁ + E₂)) * (T₄ * T₂₂ * e + T₄ * iL) :=
    add_mul_le_add_mul_add (by positivity) (by positivity) (by positivity) (by positivity)
  calc |KB| * (2 * (C * (e * m)) + R₁ + C * R₂)
      ≤ |KB| * (A * ((2 * B + (E₁ + E₂)) * (T₄ * T₂₂ * e + T₄ * iL))) :=
        mul_le_mul_of_nonneg_left (h4.trans (mul_le_mul_of_nonneg_left h5 hA)) (abs_nonneg _)
    _ = _ := by ring

/-- E2: the presieve at depth `h` on the weights `Φ f_𝔟 P` and `Φ P`, applied
separately. For large `x` and `0 ≤ 𝔟 ≤ 1`,
`|∑_{P⁻(u+1) > z} Φ(u/x) P(u) (f_𝔟(u) - C_𝔟)| ≤ C (x / L) (T²⁶ e^{-h} + T⁴ / L)`. -/
theorem eventually_presieve (h₃ : BlockSieve) {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) {c Ch κ CΦ : ℝ}
    (M : ℕ → ℝ) (hc : 0 < c) (hCh : 0 < Ch) (hκ : 1 < κ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ)
      (Φ : ℝ → ℝ), AdmissibleSlots c x u v → (∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) →
      IsCutoff κ CΦ M x Φ →
      |presieved κ x (x ^ presieveExponent c Ch x)
          (fun m => Φ (m / x) * endpoint (1 / 2) (1 / 12) K CN x u v B m)| ≤
        C * (x / Real.log x) * (logLog x ^ 4 * logLog x ^ 22 * exp (-(sieveDepth Ch x : ℝ)) +
          logLog x ^ 4 * (1 / Real.log x)) := by
  obtain ⟨C₀, hC₀⟩ := sum_inv_primes_block_le
  obtain ⟨h₀, KB, hBS⟩ := h₃ (1 / 2) C₀ (by norm_num)
  obtain ⟨CM, hCM, hprod⟩ := prod_one_sub_inv_primes_le
  obtain ⟨CE₁, hE1s⟩ := eventually_progression_slot h₃ hK CN c κ CΦ M hc hκ
  obtain ⟨CE₂, hE1o⟩ := eventually_progression_one h₃ hK CN c κ CΦ M hc hκ
  refine ⟨|KB| * (2 * (κ * |M 0| * CM) + |CE₁| + |CE₂|), ?_⟩
  filter_upwards [hE1s, hE1o, eventually_presieveExponent hc hCh, eventually_sieveDepth hCh h₀,
    eventually_inertPoly_mem hK CN, eventually_level hc hCh hκ, eventually_slot_size hc,
    eventually_ge_atTop 1, tendsto_log_atTop.eventually_gt_atTop 0,
    tendsto_logLog.eventually_ge_atTop 1, eventually_mul_rpow_le_log_rpow 1 22 one_pos]
    with x hE1sx hE1ox ⟨hγ0, _, hγinv, _⟩ ⟨hh₀, _, _⟩ hP ⟨_, hκz, hlev⟩ hsize hx1 hL hT1 hT22
    k hk u v B Φ hslot hB hΦ
  have hx0 : 0 < x := by linarith
  rw [one_mul, rpow_one, show (22 : ℝ) = ((22 : ℕ) : ℝ) by norm_num, rpow_natCast] at hT22
  have hB' : ∀ Q, |B Q| ≤ 1 := fun Q => by rw [abs_le]; constructor <;> linarith [hB Q]
  set γ := presieveExponent c Ch x
  set z := x ^ γ
  set h := sieveDepth Ch x
  set 𝔅 := inertBands K CN x
  set P := primesIcc 2 z
  set Pw := inertPoly (1 / 2) (1 / 12) K CN x
  set Cb := slotMean x u v B
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (mem_primesIcc_two.1 hp).1
  set f₁ : ℕ → ℝ := fun m => Φ (m / x) * slotCount x u v B m * Pw m
  set f₂ : ℕ → ℝ := fun m => Φ (m / x) * Pw m
  have hf₁ : ∀ m, 0 ≤ f₁ m := fun m =>
    mul_nonneg (mul_nonneg (hΦ.2.1 _) (slotCount_nonneg u v (fun Q => (hB Q).1) m)) (hP m).1
  have hf₂ : ∀ m, 0 ≤ f₂ m := fun m => mul_nonneg (hΦ.2.1 _) (hP m).1
  set I := cutoffMass κ x Φ
  set mP := divisorModel 𝔅 Pw
  have hI0 : 0 ≤ I := cutoffMass_nonneg hx0 hΦ
  have hI : I ≤ κ * M 0 := cutoffMass_le hκ hx0 hΦ
  have hm0 : 0 ≤ mP := modelMean_nonneg (fun p hp => (prime_of_mem_inertBands hp).pos)
    fun S _ => (hP (∏ p ∈ S, p)).1
  have hm1 : mP ≤ 1 := modelMean_le_one (fun p hp => (prime_of_mem_inertBands hp).pos)
    fun S _ => (hP (∏ p ∈ S, p)).2
  have hCb0 : 0 ≤ Cb := slotMean_nonneg u v fun Q => (hB Q).1
  have hCbT : Cb ≤ logLog x ^ 4 := (le_abs_self _).trans ((hsize k hk u v B hslot hB').2)
  have hg : ∀ p ∈ P, 0 ≤ 1 / (p : ℝ) ∧ 1 / (p : ℝ) ≤ 1 - 1 / 2 := fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
    constructor
    · positivity
    · rw [div_le_iff₀ (by linarith)]
      linarith
  have hz1 : 1 ≤ z := one_le_rpow hx1 hγ0.le
  have hBS₁ := hBS (Icc 1 ⌊κ * x⌋₊) f₁ P z (x * I * Cb * mP) (fun p u => p ∣ u + 1)
    (fun p => 1 / (p : ℝ)) (fun u _ => hf₁ u) hz1 (fun p hp => mem_primesIcc_two.1 hp)
    (by positivity) hg (hC₀ P hPp)
  have hBS₂ := hBS (Icc 1 ⌊κ * x⌋₊) f₂ P z (x * I * mP) (fun p u => p ∣ u + 1)
    (fun p => 1 / (p : ℝ)) (fun u _ => hf₂ u) hz1 (fun p hp => mem_primesIcc_two.1 hp)
    (by positivity) hg (hC₀ P hPp)
  simp only at hBS₁ hBS₂
  have hs₁ := hBS₁.1 h (even_sieveDepth Ch x) hh₀
  have hs₂ := hBS₂.1 h (even_sieveDepth Ch x) hh₀
  -- the main terms
  have hγL1 : 1 ≤ logLog x ^ 22 * γ := by
    rw [one_div, inv_le_iff_one_le_mul₀ hγ0] at hγinv
    linarith
  have hlz : Real.log z = γ * Real.log x := Real.log_rpow hx0 γ
  have hz2 : 2 ≤ z := by
    have h1 : 1 ≤ γ * Real.log x := by
      have : logLog x ^ 22 * γ * Real.log x ≤ Real.log x * (γ * Real.log x) := by
        have := mul_le_mul_of_nonneg_right hT22 (show 0 ≤ γ * Real.log x by positivity)
        nlinarith
      nlinarith
    have h2 : z = exp (γ * Real.log x) := by rw [← hlz, exp_log (by positivity)]
    rw [h2]
    linarith [add_one_le_exp (γ * Real.log x)]
  have hprodP : ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ CM * logLog x ^ 22 / Real.log x := by
    rw [show P = primesIoc 1 z from primesIcc_two_eq z]
    refine (hprod z hz2).trans ?_
    rw [hlz, div_le_div_iff₀ (by positivity) hL]
    have := mul_le_mul_of_nonneg_left hγL1 (mul_nonneg hCM.le hL.le)
    nlinarith
  have hP0 : 0 ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ)) := prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hPp p hp).two_le
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hmain : x * I * mP * ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤
      x / Real.log x * (κ * |M 0| * CM * logLog x ^ 22) := by
    have hI' : I ≤ κ * |M 0| := hI.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith))
    have hM0 : 0 ≤ κ * |M 0| := mul_nonneg (by linarith) (abs_nonneg _)
    calc x * I * mP * ∏ p ∈ P, (1 - 1 / (p : ℝ))
        ≤ x * (κ * |M 0|) * 1 * (CM * logLog x ^ 22 / Real.log x) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hI' hx0.le) hm1 hm0
            (mul_nonneg hx0.le hM0)) hprodP hP0 (by positivity)
      _ = _ := by ring
  have hmain0 : 0 ≤ x * I * mP * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by positivity
  -- the remainders
  have hYY : z ^ (4 * h + 2) ≤ x ^ (c / logLog x ^ 20 / 4) := hlev
  have hrem₁ := sum_powerset_rem_le hPp (Icc 1 ⌊κ * x⌋₊) f₁ (x * I * Cb * mP) hYY
  have hrem₂ := sum_powerset_rem_le hPp (Icc 1 ⌊κ * x⌋₊) f₂ (x * I * mP) hYY
  have hPb : ∀ n, |Pw n| ≤ 1 := fun n => by rw [abs_le]; constructor <;> linarith [hP n]
  have hPband : ∀ n, Pw n = Pw (bandPart 𝔅 n) := fun n => inertPoly_bandPart _ _ _ _ _ n
  have hE₁ := hE1sx k hk u v B Φ Pw hslot hB' hΦ hPb hPband
  have hE₂ := hE1ox Φ Pw hΦ hPb hPband
  have hx2 : ∀ E : ℝ, E * x / Real.log x ^ 2 = x / Real.log x * (E * (1 / Real.log x)) :=
    fun E => by field_simp
  have hR₁ : ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2)),
      |∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ D, p ∣ u + 1), f₁ u -
        x * I * Cb * mP * ∏ p ∈ D, 1 / (p : ℝ)| ≤
      x / Real.log x * (|CE₁| * (1 / Real.log x)) := by
    rw [← hx2]
    refine hrem₁.trans (le_trans (le_of_eq (sum_congr rfl fun r _ => ?_)) (hE₁.trans ?_))
    · congr 2
      ring
    · gcongr
      exact le_abs_self _
  have hR₂ : ∑ D ∈ P.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2)),
      |∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ D, p ∣ u + 1), f₂ u -
        x * I * mP * ∏ p ∈ D, 1 / (p : ℝ)| ≤
      x / Real.log x * (|CE₂| * (1 / Real.log x)) := by
    rw [← hx2]
    refine hrem₂.trans (le_trans (le_of_eq (sum_congr rfl fun r _ => ?_)) (hE₂.trans ?_))
    · congr 2
      ring
    · gcongr
      exact le_abs_self _
  -- the cancellation
  have hsplit : presieved κ x z (fun m => Φ (m / x) * endpoint (1 / 2) (1 / 12) K CN x u v B m) =
      ∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ P, ¬ p ∣ u + 1), f₁ u -
        Cb * ∑ u ∈ (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ P, ¬ p ∣ u + 1), f₂ u := by
    rw [presieved, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun m _ => ?_
    simp only [endpoint, f₁, f₂, Pw, Cb]
    ring
  have hmain₁ : x * I * Cb * mP * ∏ p ∈ P, (1 - 1 / (p : ℝ)) =
      Cb * (x * I * mP * ∏ p ∈ P, (1 - 1 / (p : ℝ))) := by ring
  rw [hmain₁] at hs₁
  rw [hsplit]
  refine le_trans (le_of_eq (congrArg abs (by ring))) ((presieve_cancel hs₁ hs₂ hCb0 hmain0
    (exp_pos _).le (sum_nonneg fun _ _ => abs_nonneg _)
    (sum_nonneg fun _ _ => abs_nonneg _)).trans ?_)
  exact presieve_budget (by positivity) hCbT (one_le_pow₀ hT1) (exp_pos _).le hmain0
    (mul_nonneg (mul_nonneg (by linarith) (abs_nonneg _)) hCM.le) (by positivity)
    (by positivity) (abs_nonneg _) (abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
    (by simpa [mul_assoc] using hmain) hR₁ hR₂

end

end Sieve

end Erdos408
