import Erdos408.Extraction.Sieve.Presieve

/-!
# The composite tail of the presieved sum (E3)

In the presieved sum, write `n = u + 1`. The primes give the prime
statistic, the squarefree composites with `ω(n) ≤ J` give
`∑_{2 ≤ j ≤ J} Comp_j / j!` exactly (`abs_sum_rough_sub_le`), and the rest are
nonsquarefree (`O(x / z)`) or have `ω(n) > J` (Rankin, `O(x γ⁻² L⁻¹ 2^{-J})`).
With `|Φ P (f_𝔟 - C_𝔟)| ≤ M₀ T⁶²`, the error is
`≪ (x / L) (T⁶² L / z + T¹⁰⁶ 2^{-J})`.
-/

namespace Erdos408

open Filter Real Finset

namespace Sieve

noncomputable section

/-- The presieved sum, reindexed by `n = u + 1`. -/
lemma presieved_eq_sum_rough {κ x z : ℝ} (hκx : 0 ≤ κ * x) (g : ℕ → ℝ) (hg0 : g 0 = 0) :
    presieved κ x z g = ∑ n ∈ (Icc 1 ⌊κ * x + 1⌋₊).filter (Rough z), g (n - 1) := by
  set A := (Icc 1 ⌊κ * x⌋₊).filter (fun u => ∀ p ∈ primesIcc 2 z, ¬ p ∣ u + 1)
  have hinj : Set.InjOn (fun u : ℕ => u + 1) A := fun a _ b _ h => by simpa using h
  have h1 : presieved κ x z g = ∑ n ∈ A.image (· + 1), g (n - 1) := by
    rw [sum_image hinj]
    rfl
  rw [h1, floor_add_one_eq hκx]
  refine sum_subset (fun n hn => ?_) fun n hn hnA => ?_
  · obtain ⟨u, hu, rfl⟩ := mem_image.1 hn
    obtain ⟨hu1, hur⟩ := mem_filter.1 hu
    have := mem_Icc.1 hu1
    exact mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, hur⟩
  · obtain ⟨hn1, hnr⟩ := mem_filter.1 hn
    have hn1' := mem_Icc.1 hn1
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      rw [this, Nat.sub_self, hg0]
    · exfalso
      refine hnA (mem_image.2 ⟨n - 1, mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩, by omega⟩)
      rw [Nat.sub_add_cancel (by omega)]
      exact hnr

/-- The rough primes are the primes, when `G` vanishes at primes `p ≤ z`. -/
lemma sum_rough_prime_eq {z Y : ℝ} (G : ℕ → ℝ) (hG : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → G p = 0) :
    ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (fun n => Rough z n ∧ n.Prime), G n =
      ∑ p ∈ primesIcc 2 Y, G p := by
  have hP : primesIcc 2 Y = (Icc 1 ⌊Y⌋₊).filter Nat.Prime := by
    ext p
    simp only [primesIcc, mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨-, h⟩, hp⟩
      exact ⟨⟨hp.one_lt.le, h⟩, hp⟩
    · rintro ⟨⟨-, h⟩, hp⟩
      refine ⟨⟨?_, h⟩, hp⟩
      rw [Nat.ceil_le]
      exact_mod_cast hp.two_le
  rw [hP]
  refine sum_subset (fun n hn => ?_) fun p hp hpr => ?_
  · obtain ⟨h1, -, h2⟩ := mem_filter.1 hn
    exact mem_filter.2 ⟨h1, h2⟩
  · obtain ⟨h1, hpp⟩ := mem_filter.1 hp
    refine hG p hpp ?_
    by_contra hlt
    refine hpr (mem_filter.2 ⟨h1, ?_, hpp⟩)
    rw [rough_iff]
    intro q hq hqp
    rw [(Nat.prime_dvd_prime_iff_eq hq hpp).1 hqp]
    exact lt_of_not_ge hlt

/-- The error sum of E3: a uniform bound `G₀` on `|G|` times the number of rough
`n ≤ Y` that are not squarefree or have `ω(n) > J`. -/
lemma sum_bad_le {z Y G₀ : ℝ} (hz : 1 ≤ z) (J : ℕ) (G : ℕ → ℝ) (hG₀ : 0 ≤ G₀)
    (hG : ∀ n ∈ Icc 1 ⌊Y⌋₊, |G n| ≤ G₀) :
    ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (fun n => Rough z n ∧ ¬ (Squarefree n ∧ #n.primeFactors ≤ J)),
        |G n| ≤
      G₀ * (⌊Y⌋₊ / ⌊z⌋₊ + ((2 : ℝ) ^ J)⁻¹ *
        ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (Rough z), (2 : ℝ) ^ #n.primeFactors) := by
  set R := (Icc 1 ⌊Y⌋₊).filter (fun n => Rough z n ∧ ¬ (Squarefree n ∧ #n.primeFactors ≤ J))
  set R₁ := (Icc 1 ⌊Y⌋₊).filter (fun n => Rough z n ∧ ¬ Squarefree n)
  set R₂ := (Icc 1 ⌊Y⌋₊).filter (fun n => Rough z n ∧ J < #n.primeFactors)
  have hsub : R ⊆ R₁ ∪ R₂ := by
    intro n hn
    obtain ⟨h1, hr, hbad⟩ := mem_filter.1 hn
    by_cases hsq : Squarefree n
    · exact mem_union_right _ (mem_filter.2 ⟨h1, hr, by
        by_contra h
        exact hbad ⟨hsq, not_lt.1 h⟩⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨h1, hr, hsq⟩)
  have hcard : (#R : ℝ) ≤ #R₁ + #R₂ := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have h₁ := card_rough_not_squarefree_le hz ⌊Y⌋₊
  have h₂ : (#R₂ : ℝ) ≤ ((2 : ℝ) ^ J)⁻¹ *
      ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (Rough z), (2 : ℝ) ^ #n.primeFactors := by
    rw [le_inv_mul_iff₀ (by positivity)]
    calc (2 : ℝ) ^ J * #R₂ = ∑ _n ∈ R₂, (2 : ℝ) ^ J := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ R₂, (2 : ℝ) ^ #n.primeFactors := sum_le_sum fun n hn =>
          pow_le_pow_right₀ (by norm_num) (mem_filter.1 hn).2.2.le
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun n hn => by
          obtain ⟨h1, hr, -⟩ := mem_filter.1 hn
          exact mem_filter.2 ⟨h1, hr⟩) fun _ _ _ => by positivity
  calc ∑ n ∈ R, |G n| ≤ ∑ _n ∈ R, G₀ := sum_le_sum fun n hn => hG n (mem_filter.1 hn).1
    _ = G₀ * #R := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hG₀

/-- The bookkeeping of E3. -/
lemma tail_budget {x L T z Y γ D₀ E κ m N Z S Pr J : ℝ} (hx0 : 0 < x) (hL : 0 < L)
    (hκ : 0 < κ) (hD₀ : 0 ≤ D₀) (hE : 0 ≤ E) (hz : 1 ≤ z) (hT : 1 ≤ T) (hγ : 0 < γ)
    (hγT : 1 ≤ T ^ 22 * γ) (hY : 0 < Y) (hY2 : Y ≤ 2 * κ * x) (hN : N ≤ Y) (hZ : z / 2 ≤ Z)
    (hPr0 : 0 ≤ Pr) (hPr : Pr ≤ 2 * exp E * T ^ 22) (hS : S ≤ D₀ / (γ * L) * Y * (1 + Pr))
    (hJ : 0 ≤ J) :
    |m| * T ^ 62 * (N / Z + J * S) ≤
      |m| * (4 * κ + 6 * κ * D₀ * exp E) * (x / L) * (T ^ 62 * (L / z) + T ^ 62 * T ^ 44 * J) := by
  have hz0 : 0 < z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hT22 : 1 ≤ T ^ 22 := one_le_pow₀ hT
  have h1 : N / Z ≤ x / L * (4 * κ * (L / z)) := by
    rw [div_le_iff₀ hZ0]
    have : x / L * (4 * κ * (L / z)) * (z / 2) = 2 * κ * x := by
      field_simp
      ring
    calc N ≤ 2 * κ * x := hN.trans hY2
      _ = x / L * (4 * κ * (L / z)) * (z / 2) := this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hZ (by positivity)
  have hD : D₀ / (γ * L) ≤ D₀ * T ^ 22 / L := by
    rw [div_le_div_iff₀ (by positivity) hL]
    calc D₀ * L = D₀ * L * 1 := by ring
      _ ≤ D₀ * L * (T ^ 22 * γ) := mul_le_mul_of_nonneg_left hγT (mul_nonneg hD₀ hL.le)
      _ = D₀ * T ^ 22 * (γ * L) := by ring
  have hTE : 1 ≤ exp E * T ^ 22 := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ exp E * T ^ 22 := mul_le_mul (one_le_exp hE) hT22 zero_le_one (exp_pos E).le
  have hPr1 : 0 ≤ 1 + Pr := by linarith
  have h2 : S ≤ x / L * (6 * κ * D₀ * exp E * T ^ 44) := by
    refine hS.trans ?_
    calc D₀ / (γ * L) * Y * (1 + Pr)
        ≤ D₀ * T ^ 22 / L * (2 * κ * x) * (3 * exp E * T ^ 22) :=
          mul_le_mul (mul_le_mul hD hY2 hY.le (by positivity)) (by linarith) hPr1
            (by positivity)
      _ = x / L * (6 * κ * D₀ * exp E * T ^ 44) := by
          field_simp
          ring
  have ha : 0 ≤ |m| * (4 * κ) := by positivity
  have hb : 0 ≤ |m| * (6 * κ * D₀ * exp E) := by
    have := exp_pos E
    positivity
  calc |m| * T ^ 62 * (N / Z + J * S)
      ≤ |m| * T ^ 62 * (x / L * (4 * κ * (L / z)) + J * (x / L * (6 * κ * D₀ * exp E * T ^ 44))) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 (mul_le_mul_of_nonneg_left h2 hJ))
          (by positivity)
    _ = x / L * ((|m| * (4 * κ)) * (T ^ 62 * (L / z)) +
        (|m| * (6 * κ * D₀ * exp E)) * (T ^ 62 * T ^ 44 * J)) := by ring
    _ ≤ x / L * ((|m| * (4 * κ) + |m| * (6 * κ * D₀ * exp E)) *
        (T ^ 62 * (L / z) + T ^ 62 * T ^ 44 * J)) :=
        mul_le_mul_of_nonneg_left (add_mul_le_add_mul_add ha hb (by positivity)
          (by positivity)) (by positivity)
    _ = _ := by ring

/-- E3: for large `x`, the presieved sum of `Φ P (f_𝔟 - C_𝔟)` is the prime sum plus
`∑_{2 ≤ j ≤ J} Comp_j / j!` up to `C (x / L) (T⁶² L / z + T¹⁰⁶ 2^{-J})`. -/
theorem eventually_composite (h₃ : BlockSieve) {K : ℕ} (hK : 1 ≤ K) (CN : ℝ) {c Ch κ CΦ : ℝ}
    (M : ℕ → ℝ) (Cj : ℝ) (hc : 0 < c) (hCh : 0 < Ch) (hκ : 1 < κ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop, ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ)
      (Φ : ℝ → ℝ), AdmissibleSlots c x u v → (∀ Q, |B Q| ≤ 1) → IsCutoff κ CΦ M x Φ →
      |presieved κ x (x ^ presieveExponent c Ch x)
          (fun m => Φ (m / x) * endpoint (1 / 2) (1 / 12) K CN x u v B m) -
        ∑ p ∈ primesIcc 2 (κ * x + 1),
          Φ (((p : ℝ) - 1) / x) * endpoint (1 / 2) (1 / 12) K CN x u v B (p - 1) -
        ∑ j ∈ Icc 2 (compositeCutoff Cj x), ((j.factorial : ℝ))⁻¹ *
          compositeSum (1 / 2) (1 / 12) K CN x (presieveExponent c Ch x) κ j Φ u v B| ≤
        C * (x / Real.log x) * (logLog x ^ 62 * (Real.log x / x ^ presieveExponent c Ch x) +
          logLog x ^ 62 * logLog x ^ 44 * ((2 : ℝ) ^ compositeCutoff Cj x)⁻¹) := by
  obtain ⟨D₀, hD₀, hrough⟩ := card_rough_le h₃
  obtain ⟨E, hE, hmert⟩ := mertens_second
  refine ⟨|M 0| * (4 * κ + 6 * κ * D₀ * exp E), ?_⟩
  filter_upwards [eventually_presieveExponent hc hCh, eventually_inertPoly_mem hK CN,
    eventually_level hc hCh hκ, eventually_slot_size hc, eventually_ge_atTop 1,
    tendsto_log_atTop.eventually_gt_atTop 0, tendsto_logLog.eventually_ge_atTop 2,
    eventually_mul_rpow_le_log_rpow 20 22 one_pos, eventually_ge_atTop (κ + 1)]
    with x ⟨hγ0, _, hγinv, _⟩ hP ⟨_, hκz, _⟩ hsize hx1 hL hT2 hT22 hxκ k hk u v B Φ hslot hB hΦ
  rw [rpow_one, show (22 : ℝ) = ((22 : ℕ) : ℝ) by norm_num, rpow_natCast] at hT22
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκx : 0 ≤ κ * x := by positivity
  set T := logLog x
  set γ := presieveExponent c Ch x
  set z := x ^ γ
  set Y := κ * x + 1
  set J := compositeCutoff Cj x
  set G : ℕ → ℝ := fun n => Φ (((n : ℝ) - 1) / x) * endpoint (1 / 2) (1 / 12) K CN x u v B (n - 1)
  -- the parameters
  have hlz : Real.log z = γ * Real.log x := Real.log_rpow hx0 γ
  have hγL : 20 ≤ γ * Real.log x := by
    rw [one_div, inv_le_iff_one_le_mul₀ hγ0] at hγinv
    have h1 : 20 * T ^ 22 * γ ≤ Real.log x * γ := mul_le_mul_of_nonneg_right hT22 hγ0.le
    nlinarith
  have hz0 : 0 < z := by positivity
  have hzexp : z = exp (γ * Real.log x) := by rw [← hlz, exp_log hz0]
  have hz20 : 2 ^ 20 ≤ z := by
    rw [hzexp]
    calc (2 : ℝ) ^ 20 ≤ exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num)
          (by linarith [add_one_le_exp (1 : ℝ)]) 20
      _ = exp 20 := by rw [← exp_nat_mul]; norm_num
      _ ≤ exp (γ * Real.log x) := exp_le_exp.2 hγL
  have hz1 : 1 ≤ z := le_trans (by norm_num) hz20
  have hzx : z < x := by nlinarith
  have hzY : z ≤ Y := by nlinarith
  have hYx : Y ≤ x ^ 2 := by nlinarith
  have hY2 : Y ≤ 2 * κ * x := by nlinarith
  -- vanishing of `Φ` outside `[κ⁻¹, κ]`
  have hΦ0 : ∀ t : ℝ, (t < κ⁻¹ ∨ κ < t) → Φ t = 0 := fun t ht => by
    by_contra h
    obtain ⟨h1, h2⟩ := hΦ.2.2.1 t h
    rcases ht with ht | ht <;> linarith
  have hG1 : G 1 = 0 := by
    simp only [G, Nat.cast_one, sub_self, zero_div]
    rw [hΦ0 0 (Or.inl (inv_pos.2 hκ0)), zero_mul]
  have hGY : ∀ n, ⌊Y⌋₊ < n → G n = 0 := by
    intro n hn
    have h1 : Y < n := (Nat.floor_lt (by positivity)).1 hn
    simp only [G]
    rw [hΦ0 _ (Or.inr (by rw [lt_div_iff₀ hx0]; linarith)), zero_mul]
  have hGz : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → G p = 0 := by
    intro p _ hpz
    have h : ((p : ℝ) - 1) / x < κ⁻¹ := by
      rw [div_lt_iff₀ hx0, show κ⁻¹ * x = x / κ by ring, lt_div_iff₀ hκ0]
      nlinarith
    simp only [G]
    rw [hΦ0 _ (Or.inl h), zero_mul]
  -- the uniform bound `|G| ≤ M₀ T⁶²`
  have hG₀ : ∀ n ∈ Icc 1 ⌊Y⌋₊, |G n| ≤ |M 0| * T ^ 62 := by
    intro n hn
    obtain ⟨hn1, hnY⟩ := mem_Icc.1 hn
    rcases Nat.lt_or_ge n 2 with h | h
    · rw [show n = 1 by omega, hG1, abs_zero]
      positivity
    have hm : 0 < n - 1 := by omega
    have hmx : ((n - 1 : ℕ) : ℝ) ≤ x ^ 2 := by
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      have : (n : ℝ) ≤ Y := (Nat.le_floor_iff (by positivity)).1 hnY
      linarith
    have hB' := hsize k hk u v B hslot hB
    have hf := hB'.1 (n - 1) hm hmx
    have hC := hB'.2
    have hP1 : |inertPoly (1 / 2) (1 / 12) K CN x (n - 1)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hP (n - 1)]
    have hfC : |slotCount x u v B (n - 1) - slotMean x u v B| ≤ T ^ 62 := by
      have h61 : T ^ 4 ≤ T ^ 61 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h62 : 2 * T ^ 61 ≤ T ^ 62 := by
        have h0 : 0 ≤ T ^ 61 := by positivity
        have : T ^ 62 = T ^ 61 * T := pow_succ T 61
        nlinarith
      calc _ ≤ |slotCount x u v B (n - 1)| + |slotMean x u v B| := abs_sub _ _
        _ ≤ T ^ 62 := by linarith
    simp only [G, endpoint, abs_mul]
    calc |Φ (((n : ℝ) - 1) / x)| * (|inertPoly (1 / 2) (1 / 12) K CN x (n - 1)| *
          |slotCount x u v B (n - 1) - slotMean x u v B|) ≤ |M 0| * (1 * T ^ 62) :=
          mul_le_mul ((abs_le_of_isCutoff hΦ _).trans (le_abs_self _))
            (mul_le_mul hP1 hfC (abs_nonneg _) zero_le_one) (by positivity) (abs_nonneg _)
      _ = |M 0| * T ^ 62 := by ring
  -- the decomposition
  have hrough_eq : presieved κ x z
      (fun m => Φ (m / x) * endpoint (1 / 2) (1 / 12) K CN x u v B m) =
      ∑ n ∈ (Icc 1 ⌊Y⌋₊).filter (Rough z), G n := by
    rw [presieved_eq_sum_rough hκx _ (by
      simp only [Nat.cast_zero, zero_div]
      rw [hΦ0 0 (Or.inl (inv_pos.2 hκ0)), zero_mul])]
    refine sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (mem_Icc.1 (mem_filter.1 hn).1).1
    simp only [G, Nat.cast_sub hn1, Nat.cast_one]
  have hprime_eq := sum_rough_prime_eq (Y := Y) G hGz
  have hcomp_eq : ∀ j, compositeSum (1 / 2) (1 / 12) K CN x γ κ j Φ u v B =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin j => primesIcc z Y),
        (if ∀ i, z < (p i : ℝ) then G (∏ i, p i) else 0) := fun j => rfl
  have hdec := abs_sum_rough_sub_le (z := z) (Y := Y) J G hG1 hGY
  rw [hprime_eq] at hdec
  simp only [← hcomp_eq] at hdec
  rw [hrough_eq]
  refine hdec.trans ((sum_bad_le hz1 J G (by positivity) hG₀).trans ?_)
  have hY0 : 0 < Y := hz0.trans_le hzY
  clear_value G J Y z γ T
  have hγT : 1 ≤ T ^ 22 * γ := by
    rw [one_div, inv_le_iff_one_le_mul₀ hγ0] at hγinv
    linarith
  -- Mertens for `∏_{z < p ≤ Y} (1 + 1/p)`
  have hEz : E / Real.log z ≤ E := div_le_self hE (by rw [hlz]; linarith)
  have hlY : Real.log Y ≤ 2 * Real.log x := by
    have := Real.log_le_log hY0 hYx
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hratio : Real.log Y / Real.log z ≤ 2 * T ^ 22 := by
    rw [hlz, div_le_iff₀ (by positivity)]
    calc Real.log Y ≤ 2 * Real.log x * 1 := by rw [mul_one]; exact hlY
      _ ≤ 2 * Real.log x * (T ^ 22 * γ) := mul_le_mul_of_nonneg_left hγT (by positivity)
      _ = 2 * T ^ 22 * (γ * Real.log x) := by ring
  have hratio0 : 0 < Real.log Y / Real.log z := by
    have : 0 < Real.log Y := Real.log_pos (by linarith)
    rw [hlz]
    positivity
  have hprod : ∏ p ∈ primesIoc z Y, (1 + 1 / (p : ℝ)) ≤ 2 * exp E * T ^ 22 := by
    have h1 : ∏ p ∈ primesIoc z Y, (1 + 1 / (p : ℝ)) ≤
        exp (∑ p ∈ primesIoc z Y, (1 : ℝ) / p) := by
      rw [exp_sum]
      exact prod_le_prod₀ (fun p _ => by positivity) fun p _ => by
        linarith [add_one_le_exp (1 / (p : ℝ))]
    have h2 := (abs_le.1 (hmert z Y (by linarith) hzY)).2
    refine h1.trans ((exp_le_exp.2 (show _ ≤ Real.log (Real.log Y / Real.log z) + E by
      linarith)).trans ?_)
    rw [exp_add, exp_log hratio0]
    calc Real.log Y / Real.log z * exp E ≤ 2 * T ^ 22 * exp E :=
          mul_le_mul_of_nonneg_right hratio (exp_pos E).le
      _ = 2 * exp E * T ^ 22 := by ring
  have hS := sum_two_pow_card_primeFactors_le (D := D₀ / Real.log z) hz0.le hzY
    fun Y' h1 h2 => by
      rw [div_mul_eq_mul_div]
      exact hrough z Y' hz20 h1
  rw [hlz] at hS
  exact tail_budget hx0 hL hκ0 hD₀ hE hz1 (by linarith) hγ0 hγT hY0 hY2
    (Nat.floor_le hY0.le) (by have := Nat.lt_floor_add_one z; linarith)
    (prod_nonneg fun p _ => by positivity) hprod hS (by positivity)

end

end Sieve

end Erdos408
