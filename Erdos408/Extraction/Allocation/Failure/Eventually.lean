import Erdos408.Extraction.Allocation.Failure.Final
import Erdos408.Extraction.Allocation.Failure.GroupBounds

/-!
# The numerical facts of E6 for large `x`

Each fact needed by `freeFactorSum_le_of_facts` holds for large `x`, uniformly
in `2 ≤ j ≤ J_c` and the two families. The savings come from the scale
separations `L / T^{25} = log Y`, `γ L ≥ L / (C_γ T^{21})`, and the candidate
primes `≤ exp(L^{0.46})`; the losses are powers of `T`, or `exp(O(s²))` from the
`j - 1` free core factors.
-/

namespace Erdos408

open Finset Filter Real

noncomputable section

/-- For large `x`, every candidate group satisfies `SideGroup`. -/
lemma eventually_sideGroup : ∀ᶠ x : ℝ in atTop, ∀ g ∈ candidateGroups x, SideGroup g := by
  have hL : Tendsto (fun x : ℝ => Real.log x ^ (28 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [eventually_candidateGroups, eventually_harmonicMass_le,
    hL.eventually_ge_atTop 99] with x hgroups hmass hL99 g hg
  refine ⟨(hgroups.1 g hg).1, hmass g hg, fun p hp => prime_of_mem_candidatePrimes
    (mem_biUnion.2 ⟨g, hg, hp⟩), fun p hp => ?_⟩
  have h1 := hgroups.2.2.2.2.2.2 p (mem_biUnion.2 ⟨g, hg, hp⟩)
  have h2 := add_one_le_exp (Real.log x ^ (28 / 100 : ℝ))
  have : (100 : ℝ) ≤ p := by linarith
  exact_mod_cast this

/-- At most `b` primes in `[a, b]` for `a ≥ 1`. -/
lemma card_primesIcc_le' {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) : ((primesIcc a b).card : ℝ) ≤ b := by
  have h1 : (primesIcc a b).card ≤ ⌊b⌋₊ := by
    refine (card_filter_le _ _).trans ?_
    rw [Nat.card_Icc]
    have : 1 ≤ ⌈a⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
    omega
  exact (Nat.cast_le.2 h1).trans (Nat.floor_le hb)

/-- For large `x`, the candidate primes lie below `Y` and `X = ⌊κ x⌋ + 1`, and each group has at
most `exp(L^{0.46})` primes. -/
lemma eventually_groups_small (κ : ℝ) (hκ : 1 < κ) : ∀ᶠ x : ℝ in atTop,
    (∀ g ∈ candidateGroups x, g ⊆ primesIcc 2 (proxyCutoff x) ∧
      (g.card : ℝ) ≤ Real.exp (Real.log x ^ (46 / 100 : ℝ))) ∧
    (∀ p ∈ candidatePrimes x, p ≤ ⌊κ * x⌋₊ + 1) ∧ x ≤ ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ∧
    proxyCutoff x ≤ x ∧ 2 ≤ proxyCutoff x := by
  filter_upwards [eventually_candidateGroups, eventually_le_log 1, eventually_le_logLog 1,
    eventually_logLog_rpow_le 25 (show (0 : ℝ) < 54 / 100 by norm_num), eventually_gt_atTop 1]
    with x hgroups hlog hT hT25 hx
  have hL0 : 0 < Real.log x := by linarith
  have hx0 : 0 < x := by linarith
  set L := Real.log x
  set T := logLog x
  have hT25' : T ^ (25 : ℕ) ≤ L ^ (54 / 100 : ℝ) := by
    rw [← rpow_natCast]; exact_mod_cast hT25
  -- `exp(L^{0.46}) ≤ Y ≤ x`
  have hY : Real.exp (L ^ (46 / 100 : ℝ)) ≤ proxyCutoff x := by
    refine exp_le_exp.2 ?_
    rw [le_div_iff₀ (by positivity)]
    calc L ^ (46 / 100 : ℝ) * T ^ 25 ≤ L ^ (46 / 100 : ℝ) * L ^ (54 / 100 : ℝ) := by gcongr
      _ = L := by rw [← rpow_add hL0]; norm_num
  have hYx : proxyCutoff x ≤ x := by
    calc proxyCutoff x = Real.exp (L / T ^ 25) := rfl
      _ ≤ Real.exp L := exp_le_exp.2 (div_le_self hL0.le (one_le_pow₀ hT))
      _ = x := exp_log hx0
  have hY2 : 2 ≤ proxyCutoff x := by
    refine le_trans ?_ hY
    have := add_one_le_exp (L ^ (46 / 100 : ℝ))
    have : 1 ≤ L ^ (46 / 100 : ℝ) := one_le_rpow hlog (by norm_num)
    linarith
  have hxX : x ≤ ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    have := Nat.lt_floor_add_one (κ * x)
    nlinarith
  have hsub : ∀ g ∈ candidateGroups x, g ⊆ primesIcc (Real.exp (L ^ (27 / 100 : ℝ)))
      (Real.exp (L ^ (46 / 100 : ℝ))) := by
    intro g hg p hp
    have e27 : (0.27 : ℝ) = 27 / 100 := by norm_num
    have e46 : (0.46 : ℝ) = 46 / 100 := by norm_num
    rcases mem_union.1 hg with hg' | hg'
    · obtain ⟨hpr, h1, h2⟩ := mem_primesIcc.1 (hgroups.2.2.1 g hg' hp)
      rw [e27] at h1
      refine mem_primesIcc.2 ⟨hpr, h1, h2.trans (exp_le_exp.2 ?_)⟩
      exact rpow_le_rpow_of_exponent_le hlog (by norm_num)
    · obtain ⟨hpr, h1, h2⟩ := mem_primesIcc.1 (hgroups.2.2.2.1 g hg' hp)
      rw [e46] at h2
      refine mem_primesIcc.2 ⟨hpr, le_trans (exp_le_exp.2 ?_) h1, h2⟩
      exact rpow_le_rpow_of_exponent_le hlog (by norm_num)
  refine ⟨fun g hg => ⟨fun p hp => ?_, ?_⟩, fun p hp => ?_, hxX, hYx, hY2⟩
  · obtain ⟨hpr, -, h2⟩ := mem_primesIcc.1 (hsub g hg hp)
    exact mem_primesIcc.2 ⟨hpr, by exact_mod_cast hpr.two_le, h2.trans hY⟩
  · exact (Nat.cast_le.2 (card_le_card (hsub g hg))).trans
      (card_primesIcc_le' (one_le_exp (by positivity)) (exp_pos _).le)
  · obtain ⟨g, hg, hpg⟩ := mem_biUnion.1 hp
    obtain ⟨-, -, h2⟩ := mem_primesIcc.1 (hsub g hg hpg)
    have : (p : ℝ) ≤ ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) := h2.trans (hY.trans (hYx.trans hxX))
    exact_mod_cast this

/-- For large `x`, `0 < γ ≤ 1` and `1/γ ≤ C_γ T^{21}`. -/
lemma eventually_presieveExponent {c : ℝ} (hc : 0 < c) (Ch : ℝ) : ∀ᶠ x : ℝ in atTop,
    0 < presieveExponent c Ch x ∧ presieveExponent c Ch x ≤ 1 ∧
      1 / presieveExponent c Ch x ≤ 4 * (8 * |Ch| + 11) / c * logLog x ^ 21 := by
  filter_upwards [eventually_le_logLog (c + 1)] with x hT
  have hT1 : 1 ≤ logLog x := by linarith
  obtain ⟨h0, h1⟩ := presieveExponent_facts (Ch := Ch) hc hT1
  refine ⟨h0, ?_, h1⟩
  have hden : 1 ≤ 4 * (sieveDepth Ch x : ℝ) + 3 := by
    have : (0 : ℝ) ≤ sieveDepth Ch x := Nat.cast_nonneg _
    linarith
  have hT20 : c ≤ logLog x ^ 20 := by
    have : logLog x ≤ logLog x ^ 20 := le_self_pow₀ hT1 (by norm_num)
    linarith
  rw [presieveExponent, div_div, div_div, div_le_one (by positivity)]
  nlinarith

/-- For large `x`, `D_j γ L ≥ 1` for every `j ≥ 1`. -/
lemma eventually_one_le_dampedDensity_mul {c : ℝ} (hc : 0 < c) (Ch : ℝ) : ∀ᶠ x : ℝ in atTop,
    ∀ j : ℕ, 1 ≤ j → 1 ≤ dampedDensity x j * (presieveExponent c Ch x * Real.log x) := by
  obtain ⟨C₁, hC₁, hprod⟩ := exists_prod_one_sub_ge
  set Cγ := 4 * (8 * |Ch| + 11) / c
  have hCγ : 0 < Cγ := by positivity
  filter_upwards [eventually_presieveExponent hc Ch, eventually_groups_small 2 (by norm_num),
    eventually_le_logLog (Cγ / C₁ + 1), eventually_le_log 1]
    with x hγ hsmall hT hlog j hj
  obtain ⟨hγ0, -, hγC⟩ := hγ
  have hY2 := hsmall.2.2.2.2
  set L := Real.log x
  set T := logLog x
  set γ := presieveExponent c Ch x
  have hT1 : 1 ≤ T := by linarith [div_pos hCγ hC₁]
  have hL0 : 0 < L := by linarith
  have hlogY : Real.log (proxyCutoff x) = L / T ^ 25 := by rw [proxyCutoff, log_exp]
  have hPi : C₁ / (L / T ^ 25) ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) := by
    rw [← hlogY]; exact hprod _ hY2
  have hD : C₁ / (L / T ^ 25) ≤ dampedDensity x j := by
    refine hPi.trans ?_
    rw [dampedDensity]
    refine le_mul_of_one_le_right (le_trans (by positivity) hPi) (one_le_prod_candidate x hj)
  -- `D γ L ≥ C₁ T^{25} γ ≥ C₁ T^4 / C_γ ≥ 1`
  have hγ' : 1 / (Cγ * T ^ 21) ≤ γ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hγ0] at hγC
    linarith
  calc (1 : ℝ) ≤ C₁ * T ^ 4 / Cγ := by
        rw [le_div_iff₀ hCγ, one_mul]
        have h4 : T ≤ T ^ 4 := le_self_pow₀ hT1 (by norm_num)
        have : Cγ ≤ C₁ * T := by
          have := (div_le_iff₀ hC₁).1 (show Cγ / C₁ ≤ T by linarith)
          linarith
        nlinarith
    _ = C₁ / (L / T ^ 25) * (1 / (Cγ * T ^ 21) * L) := by field_simp
    _ ≤ dampedDensity x j * (γ * L) := by
        gcongr
        exact (dampedDensity_pos x hj).le

/-- For large `x`, `κ_j^j ∏_{p ∈ P} (1 - 1/p)⁻¹ ≤ 2` for every `j ≥ 1`. -/
lemma eventually_candKappa_pow_mul_le : ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, 1 ≤ j →
    candKappa x j ^ j * ∏ p ∈ candidatePrimes x, (1 - (1 : ℝ) / p)⁻¹ ≤ 2 := by
  filter_upwards [eventually_candidateGroups, eventually_le_log 20,
    eventually_exp_neg_rpow_le (show (0 : ℝ) < 28 / 100 by norm_num) 2] with x hgroups hL hexp j hj
  refine (candKappa_pow_mul_le x hj).trans ?_
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have h6 := sum_one_div_candidatePrimes_le (by linarith) hgroups
  have hT : logLog x ≤ L := by
    have := Real.log_le_sub_one_of_pos hL0
    simp only [logLog]
    linarith
  -- `∑ 1/p² ≤ e^{-L^{0.28}} ∑ 1/p ≤ L^{-2} 6 L`
  have hsq : ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ^ 2 ≤
      Real.exp (-(L ^ (28 / 100 : ℝ))) * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    have h1 := hgroups.2.2.2.2.2.2 p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).pos
    have h2 : (1 : ℝ) / p ≤ Real.exp (-(L ^ (28 / 100 : ℝ))) := by
      rw [exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (exp_pos _) h1
    calc (1 : ℝ) / p ^ 2 = 1 / p * (1 / p) := by ring
      _ ≤ Real.exp (-(L ^ (28 / 100 : ℝ))) * (1 / p) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  have hL2 : L ^ (-(2 : ℝ)) = 1 / L ^ 2 := by
    rw [rpow_neg hL0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast, one_div]
  rw [hL2] at hexp
  have hfin : 2 * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ^ 2 ≤ Real.log 2 := by
    have h1 : ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ^ 2 ≤ 1 / L ^ 2 * (6 * L) := by
      refine hsq.trans ?_
      have h0 : 0 ≤ ∑ p ∈ candidatePrimes x, (1 : ℝ) / p := sum_nonneg fun p _ => by positivity
      calc Real.exp (-(L ^ (28 / 100 : ℝ))) * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p
          ≤ 1 / L ^ 2 * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p :=
            mul_le_mul_of_nonneg_right hexp h0
        _ ≤ 1 / L ^ 2 * (6 * L) := by gcongr; linarith
    have h2 : 1 / L ^ 2 * (6 * L) = 6 / L := by field_simp
    have h3 : 6 / L ≤ 3 / 10 := by rw [div_le_iff₀ hL0]; linarith
    have := Real.log_two_gt_d9
    linarith
  calc Real.exp (2 * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ^ 2) ≤ Real.exp (Real.log 2) :=
        exp_le_exp.2 hfin
    _ = 2 := exp_log (by norm_num)

/-- `L = e^T`. -/
lemma exp_logLog {x : ℝ} (hx : 0 < Real.log x) : Real.exp (logLog x) = Real.log x := by
  rw [logLog, exp_log hx]

/-- `log X ≤ 2 L` for `X = ⌊κ x⌋ + 1` and large `x`. -/
lemma eventually_log_le_two_mul (κ : ℝ) (hκ : 1 < κ) : ∀ᶠ x : ℝ in atTop,
    Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * Real.log x := by
  filter_upwards [eventually_ge_atTop (κ + 1)] with x hx
  have hx0 : 0 < x := by linarith
  have hX : ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) ≤ x ^ 2 := by
    push_cast
    have := Nat.floor_le (show 0 ≤ κ * x by positivity)
    nlinarith
  have hX0 : (0 : ℝ) < ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) := by positivity
  calc Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) ≤ Real.log (x ^ 2) := Real.log_le_log hX0 hX
    _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num

/-- For large `x`, the relative error `δ = 8 ε K / Π (5/2)^n` at depth `R = ⌈6 T⌉` is at most
`e^{-T}` for every `n ≤ T`. -/
lemma eventually_delta_le {c : ℝ} (hc : 0 < c) (Ch κ : ℝ) (hκ : 1 < κ) : ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ, (n : ℝ) ≤ logLog x →
      8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (⌈6 * logLog x⌉₊ + 1),
          ∏ p ∈ u, (1 : ℝ) / p) *
        (Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) / (presieveExponent c Ch x * Real.log x)) /
          (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (5 / 2) ^ n ≤
        Real.exp (-logLog x) := by
  obtain ⟨C₁, hC₁, hprod⟩ := exists_prod_one_sub_ge
  obtain ⟨CS, hCS⟩ := exists_sum_one_div_primesIcc_le
  set Cγ := 4 * (8 * |Ch| + 11) / c
  have hCγ : 0 < Cγ := by positivity
  set K₀ := 16 * Cγ * Real.exp (8 * |CS|) / C₁
  have hK₀ : 0 < K₀ := by positivity
  filter_upwards [eventually_presieveExponent hc Ch, eventually_groups_small κ hκ,
    eventually_log_le_two_mul κ hκ, eventually_le_logLog 1, eventually_le_log (K₀ ^ 2),
    eventually_le_log 1, eventually_logLog_rpow_le 21 (show (0 : ℝ) < 1 / 2 by norm_num)]
    with x hγ hsmall hlogX hT hLK hL1 hT21 n hn
  obtain ⟨hγ0, -, hγC⟩ := hγ
  have hY2 := hsmall.2.2.2.2
  set L := Real.log x
  set T := logLog x
  set γ := presieveExponent c Ch x
  set S := primesIcc 2 (proxyCutoff x)
  set R := ⌈6 * T⌉₊
  have hL0 : 0 < L := by linarith
  have hLT : Real.exp T = L := exp_logLog hL0
  have hT0 : 0 < T := by linarith
  have hlogY : Real.log (proxyCutoff x) = L / T ^ 25 := by rw [proxyCutoff, log_exp]
  -- `ε ≤ e^{8 (T + |C_S|)} / e^{12 T}`
  have hSsum : ∑ p ∈ S, (1 : ℝ) / p ≤ T + |CS| := by
    refine (hCS _ hY2).trans ?_
    have : Real.log (Real.log (proxyCutoff x)) ≤ T := by
      rw [hlogY]
      exact Real.log_le_log (by positivity) (div_le_self hL0.le (one_le_pow₀ hT))
    linarith [le_abs_self CS]
  have h8 : Real.exp (12 * T) ≤ (8 : ℝ) ^ (R + 1) := by
    have hR : 6 * T ≤ ((R + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (6 * T)]
    have hlog8 : 2 ≤ Real.log 8 := by
      rw [le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
      nlinarith [exp_pos 1]
    calc Real.exp (12 * T) ≤ Real.exp (((R + 1 : ℕ) : ℝ) * Real.log 8) :=
          exp_le_exp.2 (by nlinarith)
      _ = (8 : ℝ) ^ (R + 1) := by rw [Real.exp_nat_mul, exp_log (by norm_num)]
  have hε : ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p ≤
      Real.exp (8 * (T + |CS|)) / Real.exp (12 * T) :=
    (sum_powersetCard_le_exp S R).trans (div_le_div₀ (exp_pos _).le
      (exp_le_exp.2 (by linarith)) (exp_pos _) h8)
  have hε0 : 0 ≤ ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p :=
    sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  -- `K ≤ 2 C_γ T^{21}`
  have hγC' : 1 / γ ≤ Cγ * T ^ 21 := hγC
  have hK : Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) / (γ * L) ≤ 2 * Cγ * T ^ 21 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ Cγ * T ^ 21 * γ := by
      rw [div_le_iff₀ hγ0] at hγC'
      linarith
    have h2 : 2 * L * 1 ≤ 2 * L * (Cγ * T ^ 21 * γ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have hK0 : 0 ≤ Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) / (γ * L) :=
    div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  -- `1/Π ≤ L / C₁`
  have hPi : C₁ / (L / T ^ 25) ≤ ∏ p ∈ S, (1 - (1 : ℝ) / p) := by
    rw [← hlogY]; exact hprod _ hY2
  have hPi0 : 0 < ∏ p ∈ S, (1 - (1 : ℝ) / p) := lt_of_lt_of_le (by positivity) hPi
  have hPi' : 1 / ∏ p ∈ S, (1 - (1 : ℝ) / p) ≤ L / C₁ := by
    rw [div_le_div_iff₀ hPi0 hC₁, one_mul]
    have h25 : L / T ^ 25 ≤ L := div_le_self hL0.le (one_le_pow₀ hT)
    have h1 : C₁ ≤ (∏ p ∈ S, (1 - (1 : ℝ) / p)) * (L / T ^ 25) := by
      rw [div_le_iff₀ (by positivity)] at hPi
      linarith
    have h2 : (∏ p ∈ S, (1 - (1 : ℝ) / p)) * (L / T ^ 25) ≤ (∏ p ∈ S, (1 - (1 : ℝ) / p)) * L :=
      mul_le_mul_of_nonneg_left h25 hPi0.le
    linarith
  -- `(5/2)^n ≤ e^T`
  have h52 : (5 / 2 : ℝ) ^ n ≤ Real.exp T := by
    calc (5 / 2 : ℝ) ^ n ≤ Real.exp 1 ^ n := by
          gcongr
          have := Real.exp_one_gt_d9
          linarith
      _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ Real.exp T := exp_le_exp.2 hn
  -- `K₀ T^{21} ≤ L`
  have hT21' : T ^ 21 ≤ L ^ (1 / 2 : ℝ) := by
    have := hT21
    rwa [show (21 : ℝ) = ((21 : ℕ) : ℝ) by norm_num, rpow_natCast] at this
  have hKL : K₀ ≤ L ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt hK₀.le hL0.le]
    exact hLK
  have hfin : K₀ * T ^ 21 ≤ L := by
    have := mul_le_mul hKL hT21' (by positivity) (by positivity)
    rwa [← rpow_add hL0, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, rpow_one] at this
  calc 8 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
        (Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) / (γ * L)) / (∏ p ∈ S, (1 - (1 : ℝ) / p)) *
          (5 / 2) ^ n
      = 8 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
        (Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) / (γ * L)) * (1 / ∏ p ∈ S, (1 - (1 : ℝ) / p)) *
          (5 / 2) ^ n := by ring
    _ ≤ 8 * (Real.exp (8 * (T + |CS|)) / Real.exp (12 * T)) * (2 * Cγ * T ^ 21) * (L / C₁) *
          Real.exp T := by
        gcongr
    _ = K₀ * T ^ 21 * (L * Real.exp (8 * T) * Real.exp T / Real.exp (12 * T)) := by
        simp only [K₀]
        rw [mul_add, exp_add]
        field_simp
        norm_num
    _ = K₀ * T ^ 21 * Real.exp (-(2 * T)) := by
        congr 1
        rw [← hLT, ← exp_add, ← exp_add, ← exp_sub]
        ring_nf
    _ ≤ L * Real.exp (-(2 * T)) := by gcongr
    _ = Real.exp (-T) := by
        rw [← hLT, ← exp_add]
        ring_nf

/-- `j ≤ J_c` gives `j ≤ (|C_j| + 1)(s + 1)`. -/
lemma natCast_le_of_le_compositeCutoff {Cj x : ℝ} (hs : 0 ≤ logLogLog x) {j : ℕ}
    (hj : j ≤ compositeCutoff Cj x) : (j : ℝ) ≤ (|Cj| + 1) * (logLogLog x + 1) := by
  have h1 : (j : ℝ) ≤ ⌈Cj * logLogLog x⌉₊ := by exact_mod_cast hj
  have h2 : (⌈Cj * logLogLog x⌉₊ : ℝ) ≤ max (Cj * logLogLog x) 0 + 1 :=
    (Nat.cast_le.2 (Nat.ceil_mono (le_max_left _ 0))).trans
      (Nat.ceil_lt_add_one (le_max_right _ _)).le
  have h3 : max (Cj * logLogLog x) 0 ≤ |Cj| * logLogLog x :=
    max_le ((le_abs_self (Cj * logLogLog x)).trans (by rw [abs_mul, abs_of_nonneg hs]))
      (by positivity)
  nlinarith [abs_nonneg Cj]

/-- The power bound: `(B₀ T^{46})^j ≤ e^{a T/4}` when `j ≤ (|C_j| + 1)(s + 1)` and
`D (s + 1)³ ≤ T`. -/
lemma pow_le_exp_of_cube {B₀ T a Cj : ℝ} (hB₀ : 1 ≤ B₀) (hT : 1 ≤ T) (ha : 0 < a) {j : ℕ}
    (hj : (j : ℝ) ≤ (|Cj| + 1) * (Real.log T + 1))
    (hcube : 4 * (|Cj| + 1) * (Real.log B₀ + 46) / a * (Real.log T + 1) ^ 3 ≤ T) :
    (B₀ * T ^ 46) ^ j ≤ Real.exp (a * T / 4) := by
  set s := Real.log T
  have hs0 : 0 ≤ s := Real.log_nonneg hT
  have hlB : 0 ≤ Real.log B₀ := Real.log_nonneg hB₀
  have hT0 : 0 < T := by linarith
  have hBT : Real.log (B₀ * T ^ 46) ≤ (Real.log B₀ + 46) * (s + 1) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    nlinarith
  have hl0 : 0 ≤ Real.log (B₀ * T ^ 46) := Real.log_nonneg (by
    have : 1 ≤ T ^ 46 := one_le_pow₀ hT
    nlinarith)
  rw [← exp_log (show 0 < (B₀ * T ^ 46) ^ j by positivity), Real.log_pow]
  refine exp_le_exp.2 ?_
  have h1 : (j : ℝ) * Real.log (B₀ * T ^ 46) ≤
      (|Cj| + 1) * (s + 1) * ((Real.log B₀ + 46) * (s + 1)) :=
    mul_le_mul hj hBT hl0 (by positivity)
  have h3 : (s + 1) ^ 2 ≤ (s + 1) ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h4 : (|Cj| + 1) * (s + 1) * ((Real.log B₀ + 46) * (s + 1)) =
      a / 4 * (4 * (|Cj| + 1) * (Real.log B₀ + 46) / a * (s + 1) ^ 2) := by
    field_simp
  have hD : 0 ≤ 4 * (|Cj| + 1) * (Real.log B₀ + 46) / a := by positivity
  have h5 : a / 4 * (4 * (|Cj| + 1) * (Real.log B₀ + 46) / a * (s + 1) ^ 2) ≤
      a / 4 * (4 * (|Cj| + 1) * (Real.log B₀ + 46) / a * (s + 1) ^ 3) := by
    gcongr
  have h6 : a / 4 * (4 * (|Cj| + 1) * (Real.log B₀ + 46) / a * (s + 1) ^ 3) ≤ a / 4 * T :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  linarith

/-- `2/(γ L) ≤ B₀ T^{46} / L` when `1/γ ≤ C_γ T^{21}` and `2 C_γ ≤ B₀`. -/
lemma two_div_le_of {γ L T Cγ B₀ : ℝ} (hγ0 : 0 < γ) (hL0 : 0 < L) (hT : 1 ≤ T)
    (hγC : 1 / γ ≤ Cγ * T ^ 21) (hB : 2 * Cγ ≤ B₀) : 2 / (γ * L) ≤ B₀ * T ^ 46 / L := by
  have h1 : 2 / (γ * L) = 2 * (1 / γ) / L := by field_simp
  rw [h1]
  refine div_le_div_of_nonneg_right ?_ hL0.le
  have hCγ : 0 ≤ Cγ := by
    have : 0 < 1 / γ := by positivity
    have : 0 < Cγ * T ^ 21 := by linarith
    by_contra h
    push Not at h
    nlinarith [pow_pos (show 0 < T by linarith) 21]
  calc 2 * (1 / γ) ≤ 2 * (Cγ * T ^ 21) := by gcongr
    _ = 2 * Cγ * T ^ 21 := by ring
    _ ≤ B₀ * T ^ 21 := by gcongr
    _ ≤ B₀ * T ^ 46 := by
        have : T ^ 21 ≤ T ^ 46 := pow_le_pow_right₀ hT (by norm_num)
        have : 0 ≤ B₀ := by linarith
        gcongr

/-- The bound `H ≤ B₀ T^{46}` for one free factor, as real arithmetic. -/
lemma free_factor_le_of {Pi Sr lX lY γ L T C₁ Cγ B₀ : ℝ} (hC₁ : 0 < C₁) (hγ0 : 0 < γ)
    (hL0 : 0 < L) (hT : 1 ≤ T) (hlY : lY = L / T ^ 25) (hPi : C₁ / lY ≤ Pi)
    (hSr : Sr ≤ (lX / lY) ^ 2 * Real.exp 1) (hSr0 : 0 ≤ Sr) (hlX0 : 0 ≤ lX) (hlX : lX ≤ 2 * L)
    (hγC : 1 / γ ≤ Cγ * T ^ 21) (hB : 4 * Real.exp 1 * Cγ / C₁ ≤ B₀) :
    1 / (Pi * (γ * L)) * Sr ≤ B₀ * T ^ 46 := by
  have hlY0 : 0 < lY := by rw [hlY]; positivity
  have hPi0 : 0 < Pi := lt_of_lt_of_le (by positivity) hPi
  have hCγ : 0 ≤ Cγ := by
    have : 0 < 1 / γ := by positivity
    by_contra h
    push Not at h
    nlinarith [pow_pos (show 0 < T by linarith) 21]
  have h1 : 1 / (Pi * (γ * L)) ≤ lY / (C₁ * (γ * L)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    rw [div_le_iff₀ hlY0] at hPi
    nlinarith [mul_pos hγ0 hL0]
  calc 1 / (Pi * (γ * L)) * Sr ≤ lY / (C₁ * (γ * L)) * ((lX / lY) ^ 2 * Real.exp 1) :=
        mul_le_mul h1 hSr hSr0 (by positivity)
    _ = Real.exp 1 * lX ^ 2 * T ^ 25 / (C₁ * L ^ 2) * (1 / γ) := by
        rw [hlY]
        field_simp
    _ ≤ Real.exp 1 * (2 * L) ^ 2 * T ^ 25 / (C₁ * L ^ 2) * (Cγ * T ^ 21) := by
        gcongr
    _ = 4 * Real.exp 1 * Cγ / C₁ * T ^ 46 := by
        field_simp
        ring
    _ ≤ B₀ * T ^ 46 := by gcongr

/-- For large `x`, the free core factors cost at most `e^{a T / 4}`:
`(2/(γ L)) H^{j-1} ≤ e^{a T/4} / L` for `j ≤ J_c`. -/
lemma eventually_free_factors_le {c : ℝ} (hc : 0 < c) (Ch Cj κ : ℝ) (hκ : 1 < κ) {a : ℝ}
    (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, ∀ j' : ℕ, j' + 1 ≤ compositeCutoff Cj x →
      2 / (presieveExponent c Ch x * Real.log x) *
        (1 / ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
          (presieveExponent c Ch x * Real.log x)) *
          ∑ a ∈ (Icc 1 (⌊κ * x⌋₊ + 1)).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a) ^ j' ≤
        Real.exp (a * logLog x / 4) / Real.log x := by
  obtain ⟨C₁, hC₁, hprod⟩ := exists_prod_one_sub_ge
  obtain ⟨E, hE, hM⟩ := mertens_second
  obtain ⟨B₀, hB1, hB2, hB₀⟩ : ∃ B₀ : ℝ, 2 * (4 * (8 * |Ch| + 11) / c) ≤ B₀ ∧
      4 * Real.exp 1 * (4 * (8 * |Ch| + 11) / c) / C₁ ≤ B₀ ∧ 1 ≤ B₀ :=
    ⟨max (max _ _) 1, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _⟩
  filter_upwards [eventually_presieveExponent hc Ch, eventually_groups_small κ hκ,
    eventually_log_le_two_mul κ hκ, eventually_le_logLog 1, eventually_le_log 1,
    eventually_logLog_rpow_le 26 one_pos, eventually_le_logLog (2 * E + 1),
    eventually_mul_logLogLog_cube_le (4 * (|Cj| + 1) * (Real.log B₀ + 46) / a)]
    with x hγ hsmall hlogX hT hL1 hT26 hTE hcube j' hj'
  obtain ⟨hγ0, -, hγC⟩ := hγ
  obtain ⟨-, -, hxX, hYx, hY2⟩ := hsmall
  have hL0 : 0 < Real.log x := by linarith
  have hlogY : Real.log (proxyCutoff x) = Real.log x / logLog x ^ 25 := by
    rw [proxyCutoff, log_exp]
  have hlogY0 : 0 < Real.log (proxyCutoff x) := by rw [hlogY]; positivity
  have hYX : proxyCutoff x ≤ ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) := hYx.trans hxX
  have hT26' : logLog x ^ 26 ≤ Real.log x := by
    have := hT26
    rwa [show (26 : ℝ) = ((26 : ℕ) : ℝ) by norm_num, rpow_natCast, rpow_one] at this
  -- the rough reciprocal sum is at most `(log X / log Y)² e`
  have hrough := sum_inv_rough_le hM (Z := ⌊κ * x⌋₊ + 1) hY2 hYX
  have hEY : 2 * E / Real.log (proxyCutoff x) ≤ 1 := by
    rw [div_le_one hlogY0, hlogY, le_div_iff₀ (by positivity)]
    have h1 : 2 * E * logLog x ^ 25 ≤ logLog x * logLog x ^ 25 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : logLog x * logLog x ^ 25 = logLog x ^ 26 := by ring
    exact h1.trans (le_of_eq_of_le h2 hT26')
  have hSr : ∑ a ∈ (Icc 1 (⌊κ * x⌋₊ + 1)).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a ≤
      (Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) / Real.log (proxyCutoff x)) ^ 2 * Real.exp 1 := by
    have heq : Real.exp (2 * (Real.log (Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) /
        Real.log (proxyCutoff x)) + E / Real.log (proxyCutoff x))) =
        (Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) / Real.log (proxyCutoff x)) ^ 2 *
          Real.exp (2 * E / Real.log (proxyCutoff x)) := by
      rw [mul_add, exp_add, show 2 * Real.log (Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) /
        Real.log (proxyCutoff x)) = ((2 : ℕ) : ℝ) * Real.log (Real.log ((⌊κ * x⌋₊ + 1 : ℕ) : ℝ) /
          Real.log (proxyCutoff x)) by norm_num, Real.exp_nat_mul,
        exp_log (div_pos (by linarith [Real.log_le_log (by linarith) hYX]) hlogY0)]
      ring_nf
    refine hrough.trans (heq.le.trans ?_)
    gcongr
  have hH := free_factor_le_of hC₁ hγ0 hL0 hT hlogY (hprod _ hY2) hSr
    (sum_nonneg fun _ _ => by positivity) (Real.log_natCast_nonneg _) hlogX hγC
    hB2
  have hpre := two_div_le_of hγ0 hL0 hT hγC hB1
  have hpow := pow_le_exp_of_cube hB₀ hT ha (j := j' + 1)
    (natCast_le_of_le_compositeCutoff (Real.log_nonneg hT) hj') hcube
  have hH0 : 0 ≤ 1 / ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
      (presieveExponent c Ch x * Real.log x)) *
      ∑ a ∈ (Icc 1 (⌊κ * x⌋₊ + 1)).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a := by
    have hPi0 : 0 ≤ ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) :=
      le_trans (by positivity) (hprod _ hY2)
    have : 0 ≤ ∑ a ∈ (Icc 1 (⌊κ * x⌋₊ + 1)).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a :=
      sum_nonneg fun _ _ => by positivity
    positivity
  calc _ ≤ B₀ * logLog x ^ 46 / Real.log x * (B₀ * logLog x ^ 46) ^ j' := by
        gcongr
    _ = (B₀ * logLog x ^ 46) ^ (j' + 1) / Real.log x := by ring
    _ ≤ _ := by gcongr

/-- The rounding bound as real arithmetic: with `M = L^{0.46}`, the rounding term is at most
`X e^{-T} / L` once `16 C_γ ≤ T³`, `T + 16 ≤ M` and `6 C_γ T^{22} M ≤ L`. -/
lemma err_le_of {N Cnt Xr A1 lX L T lY M γ Cγ R1 : ℝ} {k : ℕ} (hXr : 0 ≤ Xr) (hT : 1 ≤ T)
    (hLT : Real.exp T = L) (hN : N ≤ Real.exp (R1 * (lY + 1)))
    (hCnt0 : 0 ≤ Cnt) (hCnt : Cnt ≤ Real.exp (2 * T * (M + 1))) (hA1 : 0 < A1)
    (hA : Real.exp (γ * L) ≤ A1) (hlX : 0 ≤ lX) (hlog : (1 + lX) ^ k ≤ Real.exp (T * (T + 2)))
    (hlY : lY = L / T ^ 25) (hR1 : R1 ≤ 8 * T) (hCγ : 0 < Cγ)
    (hγ : L / (Cγ * T ^ 21) ≤ γ * L) (h1 : 16 * Cγ ≤ T ^ 3) (h2 : T + 16 ≤ M)
    (h3 : 6 * Cγ * T ^ 22 * M ≤ L) :
    N * (2 + 4 * Cnt) * (Xr / A1 * (1 + lX) ^ k) ≤ Xr * Real.exp (-T) / L := by
  have hL0 : 0 < L := by rw [← hLT]; exact exp_pos T
  have hT0 : 0 < T := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hlY0 : 0 ≤ lY := by rw [hlY]; positivity
  -- `2 + 4 Cnt ≤ 6 e^{2T(M+1)}`
  have hC6 : 2 + 4 * Cnt ≤ 6 * Real.exp (2 * T * (M + 1)) := by
    have : 1 ≤ Real.exp (2 * T * (M + 1)) := one_le_exp (by positivity)
    linarith
  have hXA : Xr / A1 ≤ Xr * Real.exp (-(γ * L)) := by
    rw [exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hXr (exp_pos _) hA
  have hprod : N * (2 + 4 * Cnt) * (Xr / A1 * (1 + lX) ^ k) ≤
      Real.exp (R1 * (lY + 1)) * (6 * Real.exp (2 * T * (M + 1))) *
        (Xr * Real.exp (-(γ * L)) * Real.exp (T * (T + 2))) := by
    have hpow0 : 0 ≤ (1 + lX) ^ k := pow_nonneg (by linarith) k
    have hA0 : 0 ≤ Xr / A1 := div_nonneg hXr hA1.le
    gcongr
  refine hprod.trans ?_
  -- the exponent
  have hexp : R1 * (lY + 1) + 2 * T * (M + 1) + T * (T + 2) - γ * L + 2 + 2 * T ≤ 0 := by
    have e1 : R1 * (lY + 1) ≤ 8 * L / T ^ 24 + 8 * T := by
      rw [hlY]
      have : R1 * (L / T ^ 25) ≤ 8 * T * (L / T ^ 25) :=
        mul_le_mul_of_nonneg_right hR1 (by positivity)
      have h8 : 8 * T * (L / T ^ 25) = 8 * L / T ^ 24 := by field_simp
      nlinarith
    have e2 : T * (T + 2) + 2 * T + 2 + 2 * T + 8 * T ≤ T * M := by nlinarith
    have e3 : 8 * L / T ^ 24 ≤ L / (2 * (Cγ * T ^ 21)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 16 * Cγ * T ^ 21 ≤ T ^ 24 := by
        have := mul_le_mul_of_nonneg_right h1 (show 0 ≤ T ^ 21 by positivity)
        calc 16 * Cγ * T ^ 21 ≤ T ^ 3 * T ^ 21 := this
          _ = T ^ 24 := by ring
      nlinarith
    have e4 : 3 * T * M ≤ L / (2 * (Cγ * T ^ 21)) := by
      rw [le_div_iff₀ (by positivity)]
      have : 6 * Cγ * T ^ 22 * M = 3 * T * M * (2 * (Cγ * T ^ 21)) := by ring
      linarith
    have e5 : L / (2 * (Cγ * T ^ 21)) + L / (2 * (Cγ * T ^ 21)) = L / (Cγ * T ^ 21) := by
      field_simp
      ring
    nlinarith
  have hfin : Real.exp (R1 * (lY + 1)) * (6 * Real.exp (2 * T * (M + 1))) *
      (Xr * Real.exp (-(γ * L)) * Real.exp (T * (T + 2))) =
      Xr * (6 * Real.exp (R1 * (lY + 1) + 2 * T * (M + 1) + T * (T + 2) - γ * L)) := by
    rw [sub_eq_add_neg, exp_add, exp_add, exp_add]
    ring
  rw [hfin]
  have h6 : 6 * Real.exp (R1 * (lY + 1) + 2 * T * (M + 1) + T * (T + 2) - γ * L) ≤
      Real.exp (-T) / L := by
    have hEL : Real.exp (-T) / L = Real.exp (-T - T) := by
      conv_lhs => rw [← hLT]
      rw [← exp_sub]
    rw [hEL]
    have : (6 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 2
      have h2' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← exp_add]; norm_num
      have := Real.exp_one_gt_d9
      nlinarith
    calc 6 * Real.exp (R1 * (lY + 1) + 2 * T * (M + 1) + T * (T + 2) - γ * L)
        ≤ Real.exp 2 * Real.exp (R1 * (lY + 1) + 2 * T * (M + 1) + T * (T + 2) - γ * L) := by
          gcongr
      _ = Real.exp (R1 * (lY + 1) + 2 * T * (M + 1) + T * (T + 2) - γ * L + 2) := by
          rw [← exp_add]; ring_nf
      _ ≤ Real.exp (-T - T) := exp_le_exp.2 (by linarith)
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h6 hXr

/-- For large `x`, the rounding term of a family with at most `T` groups of at most
`exp(L^{0.46})` primes each is at most `X e^{-T} / L`, for `j ≤ J_c`. -/
lemma eventually_err_le {c : ℝ} (hc : 0 < c) (Ch Cj κ : ℝ) (hκ : 1 < κ) : ∀ᶠ x : ℝ in atTop,
    ∀ j' : ℕ, j' + 1 ≤ compositeCutoff Cj x → ∀ F : Finset (Finset ℕ),
      (F.card : ℝ) ≤ logLog x → (∀ g ∈ F, (g.card : ℝ) ≤ Real.exp (Real.log x ^ (46 / 100 : ℝ))) →
      (((primesIcc 2 (proxyCutoff x)).powerset.filter (·.card ≤ ⌈6 * logLog x⌉₊ + 1)).card : ℝ) *
          (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) *
          ((((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) / (⌊x ^ presieveExponent c Ch x⌋₊ + 1) *
            (1 + Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ))) ^ (j' + 1)) ≤
        (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) * Real.exp (-logLog x) / Real.log x := by
  obtain ⟨Cγ, hCγdef⟩ : ∃ Cγ : ℝ, Cγ = 4 * (8 * |Ch| + 11) / c := ⟨_, rfl⟩
  have hCγ : 0 < Cγ := by rw [hCγdef]; positivity
  filter_upwards [eventually_presieveExponent hc Ch, eventually_groups_small κ hκ,
    eventually_log_le_two_mul κ hκ, eventually_le_logLog (16 * Cγ + 18), eventually_le_log 1,
    eventually_logLog_rpow_le 2 (show (0 : ℝ) < 46 / 100 by norm_num),
    eventually_logLog_rpow_le 23 (show (0 : ℝ) < 54 / 100 by norm_num),
    eventually_mul_logLogLog_cube_le (|Cj| + 1), eventually_gt_atTop 1]
    with x hγ hsmall hlogX hT hL1 hT2 hT23 hcube hx j' hj' F hF hFg
  obtain ⟨hγ0, -, hγC⟩ := hγ
  rw [← hCγdef] at hγC
  obtain ⟨-, -, hxX, hYx, hY2⟩ := hsmall
  have hL0 : 0 < Real.log x := by linarith
  have hT1 : 1 ≤ logLog x := by linarith
  have hT0 : 0 < logLog x := by linarith
  have hLT : Real.exp (logLog x) = Real.log x := exp_logLog hL0
  have hs0 : 0 ≤ logLogLog x := Real.log_nonneg hT1
  have hlogY : Real.log (proxyCutoff x) = Real.log x / logLog x ^ 25 := by
    rw [proxyCutoff, log_exp]
  have hM0 : 0 ≤ Real.log x ^ (46 / 100 : ℝ) := by positivity
  -- `k = j' + 1 ≤ T`
  have hk : ((j' + 1 : ℕ) : ℝ) ≤ logLog x := by
    have h1 := natCast_le_of_le_compositeCutoff hs0 hj'
    have h2 : (logLogLog x + 1) ≤ (logLogLog x + 1) ^ 3 :=
      le_self_pow₀ (by linarith) (by norm_num)
    have : 0 ≤ |Cj| + 1 := by positivity
    nlinarith
  -- the roundings
  have hN : (((primesIcc 2 (proxyCutoff x)).powerset.filter
      (·.card ≤ ⌈6 * logLog x⌉₊ + 1)).card : ℝ) ≤
      Real.exp (((⌈6 * logLog x⌉₊ + 1 : ℕ) : ℝ) * (Real.log (proxyCutoff x) + 1)) := by
    refine (card_filter_powerset_primesIcc_le (by linarith) _).trans ?_
    rw [Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by linarith) ?_ _
    rw [exp_add, exp_log (by linarith)]
    have := Real.exp_one_gt_d9
    nlinarith
  have hCnt : ∏ g ∈ F, ((lowSubsets g).card : ℝ) ≤
      Real.exp (2 * logLog x * (Real.log x ^ (46 / 100 : ℝ) + 1)) := by
    have hg : ∀ g ∈ F, ((lowSubsets g).card : ℝ) ≤
        Real.exp (2 * (Real.log x ^ (46 / 100 : ℝ) + 1)) := by
      intro g hg
      refine (card_lowSubsets_le g).trans ?_
      have h1 : (g.card : ℝ) + 1 ≤ Real.exp (Real.log x ^ (46 / 100 : ℝ) + 1) := by
        rw [exp_add]
        have := hFg g hg
        have := one_le_exp hM0
        have := Real.exp_one_gt_d9
        nlinarith
      calc ((g.card : ℝ) + 1) ^ 2 ≤ Real.exp (Real.log x ^ (46 / 100 : ℝ) + 1) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
        _ = Real.exp (2 * (Real.log x ^ (46 / 100 : ℝ) + 1)) := by
            rw [← Real.exp_nat_mul]; norm_num
    calc ∏ g ∈ F, ((lowSubsets g).card : ℝ)
        ≤ ∏ _g ∈ F, Real.exp (2 * (Real.log x ^ (46 / 100 : ℝ) + 1)) :=
          prod_le_prod₀ (fun _ _ => by positivity) hg
      _ = Real.exp ((F.card : ℝ) * (2 * (Real.log x ^ (46 / 100 : ℝ) + 1))) := by
          rw [prod_const, Real.exp_nat_mul]
      _ ≤ _ := by
          refine exp_le_exp.2 ?_
          have := mul_le_mul_of_nonneg_right hF
            (show 0 ≤ 2 * (Real.log x ^ (46 / 100 : ℝ) + 1) by positivity)
          linarith
  have hA : Real.exp (presieveExponent c Ch x * Real.log x) ≤
      (⌊x ^ presieveExponent c Ch x⌋₊ : ℝ) + 1 := by
    have hx0 : 0 < x := by linarith
    rw [mul_comm, ← rpow_def_of_pos hx0]
    exact (Nat.lt_floor_add_one _).le
  have hlog : (1 + Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ))) ^ (j' + 1) ≤
      Real.exp (logLog x * (logLog x + 2)) := by
    have h1 : 1 + Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ)) ≤ Real.exp (logLog x + 2) := by
      rw [exp_add, hLT]
      have : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp 2
        linarith
      nlinarith
    calc (1 + Real.log (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ))) ^ (j' + 1)
        ≤ Real.exp (logLog x + 2) ^ (j' + 1) :=
          pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg (⌊κ * x⌋₊ + 1)]) h1 _
      _ = Real.exp (((j' + 1 : ℕ) : ℝ) * (logLog x + 2)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := exp_le_exp.2 (by nlinarith)
  have hR1 : (((⌈6 * logLog x⌉₊ + 1 : ℕ) : ℝ)) ≤ 8 * logLog x := by
    push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ 6 * logLog x by positivity)
    linarith
  have hγ' : Real.log x / (Cγ * logLog x ^ 21) ≤ presieveExponent c Ch x * Real.log x := by
    rw [div_le_iff₀ (by positivity)]
    have h : 1 ≤ Cγ * logLog x ^ 21 * presieveExponent c Ch x := by
      rw [div_le_iff₀ hγ0] at hγC
      linarith
    calc Real.log x = Real.log x * 1 := by ring
      _ ≤ Real.log x * (Cγ * logLog x ^ 21 * presieveExponent c Ch x) :=
          mul_le_mul_of_nonneg_left h hL0.le
      _ = presieveExponent c Ch x * Real.log x * (Cγ * logLog x ^ 21) := by ring
  have h1 : 16 * Cγ ≤ logLog x ^ 3 := by
    have : logLog x ≤ logLog x ^ 3 := le_self_pow₀ hT1 (by norm_num)
    linarith
  have hT2' : logLog x ^ 2 ≤ Real.log x ^ (46 / 100 : ℝ) := by
    have := hT2
    rwa [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast] at this
  have hT23' : logLog x ^ 23 ≤ Real.log x ^ (54 / 100 : ℝ) := by
    have := hT23
    rwa [show (23 : ℝ) = ((23 : ℕ) : ℝ) by norm_num, rpow_natCast] at this
  have h2 : logLog x + 16 ≤ Real.log x ^ (46 / 100 : ℝ) := by
    have hT18 : 18 ≤ logLog x := by linarith only [hT, hCγ]
    have : logLog x + 16 ≤ logLog x ^ 2 := by nlinarith only [hT18]
    linarith only [this, hT2']
  have h3 : 6 * Cγ * logLog x ^ 22 * Real.log x ^ (46 / 100 : ℝ) ≤ Real.log x := by
    have h4 : 6 * Cγ * logLog x ^ 22 ≤ logLog x ^ 23 := by
      have : 6 * Cγ ≤ logLog x := by linarith
      calc 6 * Cγ * logLog x ^ 22 ≤ logLog x * logLog x ^ 22 := by gcongr
        _ = logLog x ^ 23 := by ring
    calc 6 * Cγ * logLog x ^ 22 * Real.log x ^ (46 / 100 : ℝ)
        ≤ Real.log x ^ (54 / 100 : ℝ) * Real.log x ^ (46 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_right (h4.trans hT23') hM0
      _ = Real.log x := by rw [← rpow_add hL0]; norm_num
  have hA1 : (0 : ℝ) < (⌊x ^ presieveExponent c Ch x⌋₊ : ℝ) + 1 := by positivity
  have hCnt0 : 0 ≤ ∏ g ∈ F, ((lowSubsets g).card : ℝ) := prod_nonneg fun _ _ => by positivity
  have key := err_le_of (Xr := (((⌊κ * x⌋₊ + 1 : ℕ) : ℝ))) (k := j' + 1) (Nat.cast_nonneg _) hT1
    hLT hN hCnt0 hCnt hA1 hA (Real.log_natCast_nonneg _) hlog hlogY hR1 hCγ hγ' h1 h2 h3
  exact key

end

end Erdos408
