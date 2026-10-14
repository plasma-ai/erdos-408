module

public import Erdos408.TwoSided.Endpoint.Factor
public import Erdos408.TwoSided.Endpoint.Tuple.General

/-!
# The tuple part at high times

S18 of `blueprint/two_sided_correlation.md` §6.6 (PD §6.6; X1, X3), with the factorization,
character and separation steps E6 (PD (6.32); WD §§5.4–5.5). The only use of the premise
`PrimeTwistBound` (AP1).

* `exists_integral_tuple_high_le`: the part of the mean square (6.24) of `𝒰_tup` over
  `L^{B'} ≤ |t| ≤ T₀` is `O(L^{-A₀})`, for `A'` independent of `E` and `B' ≥ E + B_min`.

The proof for a general coefficient is in `Tuple/`: the boxes, classes and characters
(`Split`, `Assembly`), the Mellin separation (`Energy`), one box (`Box`, `Sparse`), the growth
facts (`Asymp`) and the assembly (`General`), with E7 (`Mean`), S16 (`Exceptional`), E8 (`Gram`)
and E9 (`Twist`). The coefficient bounds are in `Tuple/Mark.lean` and `Setup.lean`.
-/

@[expose] public section

namespace Erdos408.TwoSided

open Filter

/-- **The tuple part at high times (S13–S18).** There are `A'` and `B_min` such that for every
`E, κ'` and `B' ≥ max(B_min, E + B_min)` there is `C_T` with: eventually, under AP1 and AP2,
for all data as in package E and a small group `g_s`, the mean square of `𝒰_tup` over
`L^{B'} ≤ t ≤ T₀` and over `-T₀ ≤ t ≤ -L^{B'}` is at most `C_T L^{-A₀}`. The coefficient
`c = 𝒲 𝒜_B W_{S'}^b` is `≤ L^{C_U}` on `[1, x²]`, `C_U = C_W + d + 2` (U7, U9 and
`|𝒜_B| ≤ ω^d`); an empty weighted slot makes `𝒜_B = 0`, and otherwise `v_d ≤ 1 - ε`. Fix
classes `p_s ≡ α`, `u ≡ β` mod `k`, expand `e(hαβ p_l/k)` over the characters of `p_l` and
split into dyadic boxes below `⌈3L⌉`: at most `64 L^{3C_m + 3}` terms, by Cauchy–Schwarz at a
cost of their number squared. Separate `ψ₁(p_s p_l u/Y)` by its Mellin density
(`∫ |a| ≤ L^{K₁}`, frequency `L^{C_sep}`): `t' = t + σ + 2πξ` has `L^E ≤ |t'| ≤ 2T₀ - 2` for
`B_min = max(C_m, C_sep) + 2`. On the ordinary times E7 gives `L^{-2A_s} L^{2C_U + 5}`; on the
exceptional set (S16) `|P_s| ≤ 2/v₋`, `|P_l| ≤ 4κ' N_l L^{-A'}` (E9, `N_l ∈ [x^ε/2, x]`) and
`∑_{j ∈ 𝒥} sup |R|² ≤ 9(1 + |κ'|) L^{2C_U + 4}` (E8, `R ∈ [exp(L/T²²), x]` by (6.34)); the
tail of the density meets the trivial bound `(2/v₋)² L^{2C_U + 5}`. With
`D = 6C_m + 2K₁ + 2C_U + 11`, `A' = (A₀ + D - 1)/2` does not depend on `E` (blueprint §1.3).
This is `TupleHigh.exists_integral_tupleSum_high_le` for the tuple coefficient. -/
theorem exists_integral_tuple_high_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ)
    (d : ℕ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo)
    (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c) (m₀ : ℕ)
    (Cm A₀ : ℝ) (M₁ : ℕ → ℝ) :
    ∃ A' Bmin : ℝ, ∀ E κ' B' : ℝ, Bmin ≤ B' → E + Bmin ≤ B' → ∃ CT : ℝ,
      ∀ᶠ x : ℝ in atTop,
        PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
        ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
          GroupAdmissible c₀ C₀ vlo vhi x P big → ∀ gs ∉ big,
          ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
            InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
            (∀ Q, |Bc Q| ≤ 1) →
          ∀ (J : ℕ) (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ),
            (∀ g, (C g).card ≤ m₀) → (∀ g ∉ big, C g = ∅) → (∀ p, ‖b p‖ ≤ 1) →
            (∀ p p', (∀ g ∈ big, p g = p' g) → b p = b p') →
          ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
            (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) →
            (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
          ∀ (Y σ : ℝ) (k : ℕ) (h : ℤ),
            x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y →
            Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
            |σ| ≤ Real.log x ^ Cm → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
            (∫ t in (Real.log x ^ B')..(x * Real.log x ^ (Cm + 2)),
                ‖twistedPoly Y (tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t‖ ^ 2 ≤
              CT * Real.log x ^ (-A₀)) ∧
            ∫ t in -(x * Real.log x ^ (Cm + 2))..-(Real.log x ^ B'),
                ‖twistedPoly Y (tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t‖ ^ 2 ≤
              CT * Real.log x ^ (-A₀) := by
  obtain ⟨CW, hCW⟩ := exists_norm_markedListWeight_le_rpow q₀ c₀ C₀ vlo vhi hq₀ hq₀₁ hvlo m₀
  obtain ⟨A', Bmin, hgen⟩ := TupleHigh.exists_integral_tupleSum_high_le vlo c Cm
    (1 + ((d : ℝ) + 1) + CW) A₀ hvlo hc M₁
  refine ⟨A', Bmin, fun E κ' B' hB₁ hB₂ => ?_⟩
  obtain ⟨CT, hCT0, hx⟩ := hgen E κ' B' hB₁ hB₂
  refine ⟨CT, ?_⟩
  filter_upwards [hx, hCW, eventually_markedWeight_band_le q alo ahi K₀ CN hq hq₁ halo,
    Real.tendsto_log_atTop.eventually_ge_atTop (4 ^ d + 1), eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
    with x hx hCW h𝒲 hL hx1 hT
  intro hAP1 hAP2 ι _ _ P big hadm gs hgs r a u v Bc hin hsl hBc J C b hC hCb hb hbb ψ₁ hψ
    hψs hψd Y σ k h hY₁ hY₂ hσ hk₁ hk₂
  simp only [Function.comp_apply] at hT
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := le_trans (by linarith [pow_pos (by norm_num : (0 : ℝ) < 4) d]) hL
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  have hT₀0 : 0 ≤ x * L ^ (Cm + 2) := by positivity
  -- the tuple coefficient `c(u) = 𝒲(u) 𝒜_B(u) W_{S'}^b(u)`
  set cf : ℕ → ℂ := fun n => ((markedWeight Finset.univ q (fun i => band x (a i)) n *
      weightedSlotCount x u v Bc n : ℝ) : ℂ) *
    markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b n with hcf
  have htup : tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ = fun w : ℕ => ψ₁ (w / Y) *
      (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (((harmonicMass (P gs))⁻¹ : ℝ) : ℂ) *
      ∑ ps ∈ (P gs).filter (· ∣ w), ∑ pl ∈ ((Finset.Iic ⌊x ^ v (Fin.last d)⌋₊).filter
        fun p : ℕ => p.Prime ∧ x ^ u (Fin.last d) < p).filter (· ∣ w / ps), cf (w / ps / pl) :=
    rfl
  -- both ranges are trivial if `L^{B'} > T₀`; otherwise apply the general bound
  have hboth : ∀ t₁ t₂ : ℝ, (∀ t ∈ Set.Icc t₁ t₂, L ^ B' ≤ |t| ∧ |t| ≤ x * L ^ (Cm + 2)) →
      ∫ t in t₁..t₂, ‖twistedPoly Y (tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t‖ ^ 2 ≤
        CT * L ^ (-A₀) := by
    intro t₁ t₂ hrange
    rcases le_or_gt t₁ t₂ with h₁₂ | h₁₂
    swap
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h₁₂.le]
      have : 0 ≤ ∫ t in Set.Ioc t₂ t₁,
          ‖twistedPoly Y (tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t‖ ^ 2 :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun t _ => by positivity
      have : 0 ≤ CT * L ^ (-A₀) := by positivity
      linarith
    -- an empty weighted slot makes `𝒜_B` vanish
    by_cases hslot : ∃ i : Fin d, v i.castSucc ≤ u i.castSucc
    · obtain ⟨i, hi⟩ := hslot
      have h𝒜 : ∀ n, weightedSlotCount x u v Bc n = 0 := by
        intro n
        rw [weightedSlotCount]
        refine Finset.sum_eq_zero fun Q hQ => absurd hQ ?_
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        rintro ⟨hQ, -⟩
        obtain ⟨hQ₁, -, hQ₂⟩ := Finset.mem_filter.1 (hQ i)
        have h₁ : (Q i : ℝ) ≤ x ^ v i.castSucc := by
          have hle := Finset.mem_Iic.1 hQ₁
          exact (Nat.cast_le.2 hle).trans (Nat.floor_le (by positivity))
        have h₂ : x ^ v i.castSucc ≤ x ^ u i.castSucc := Real.rpow_le_rpow_of_exponent_le hx1 hi
        linarith
      have h0 : ∀ t, twistedPoly Y (tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t = 0 := by
        intro t
        rw [twistedPoly]
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun w _ => ?_)
        rw [tupleCoeff]
        simp only [h𝒜, mul_zero, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
      simp only [h0, norm_zero]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t _ => by simp,
        intervalIntegral.integral_zero]
      positivity
    push Not at hslot
    -- the spare slot has `x^ε ≤ x^{u_d}` and `x^{v_d} ≤ x^{1-ε}`
    set ε := c / Real.log L ^ 20 with hε
    have hε0 : 0 < ε := by positivity
    have hu : ε ≤ u (Fin.last d) := hsl.1 _
    have hv : v (Fin.last d) ≤ 1 - ε := by
      have h := hsl.2
      change ∑ i, v i ≤ 1 - c / Real.log L ^ 20 at h
      rw [Fin.sum_univ_castSucc] at h
      have : 0 ≤ ∑ i : Fin d, v i.castSucc := Finset.sum_nonneg fun i _ =>
        (hε0.le.trans (hsl.1 _)).trans (hslot i).le
      change v (Fin.last d) ≤ 1 - c / Real.log L ^ 20
      linarith
    have hA : Real.exp (c * L / Real.log L ^ 20) ≤ x ^ u (Fin.last d) := by
      rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp, ← hLdef]
      calc c * L / Real.log L ^ 20 = L * ε := by rw [hε]; ring
        _ ≤ L * u (Fin.last d) := mul_le_mul_of_nonneg_left hu hL0.le
    have hB : x ^ v (Fin.last d) ≤ x * Real.exp (-(c * L / Real.log L ^ 20)) := by
      rw [Real.rpow_def_of_pos hx0, ← hLdef]
      calc Real.exp (L * v (Fin.last d)) ≤ Real.exp (L * (1 - ε)) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hv hL0.le)
        _ = x * Real.exp (-(c * L / Real.log L ^ 20)) := by
            have hexpL : Real.exp L = x := Real.exp_log hx0
            rw [mul_sub, mul_one, sub_eq_add_neg, Real.exp_add, hexpL, hε]
            ring_nf
    -- the small primes
    have hs : ∀ p ∈ P gs, p.Prime ∧ Real.exp (L ^ (0.27 : ℝ)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (L ^ (0.36 : ℝ)) := by
      intro p hp
      have hp' := hadm.2.2.2.2.2.2.1 gs hgs hp
      rw [primesIcc, Finset.mem_filter, Finset.mem_Icc] at hp'
      exact ⟨hp'.2, Nat.ceil_le.1 hp'.1.1, (Nat.le_floor_iff (by positivity)).1 hp'.1.2⟩
    -- the coefficient bound `|c| ≤ L^{C_U}` on `[1, x²]`
    have hcfb : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ 2 → ‖cf n‖ ≤ L ^ (1 + ((d : ℝ) + 1) + CW) := by
      intro n hn1 hnx
      obtain ⟨h𝒲0, h𝒲1⟩ := h𝒲 r a hin n
      have h𝒜 : |weightedSlotCount x u v Bc n| ≤ L ^ ((d : ℝ) + 1) := by
        rw [weightedSlotCount]
        refine (TupleHigh.abs_sum_filter_prod_dvd_le _ (fun i p hp =>
          (Finset.mem_filter.1 hp).2.1) Bc hBc hn1).trans ?_
        have hω := TupleHigh.card_primeFactors_le hn1
        have hlog : Real.log n ≤ 2 * L := by
          rw [show 2 * L = Real.log (x ^ 2) by rw [Real.log_pow]; push_cast; ring]
          exact Real.log_le_log (by exact_mod_cast hn1) hnx
        calc (n.primeFactors.card : ℝ) ^ d ≤ (4 * L) ^ d :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) d
          _ = 4 ^ d * L ^ d := mul_pow _ _ _
          _ ≤ L * L ^ d := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = L ^ ((d : ℝ) + 1) := by
              rw [Real.rpow_add hL0, Real.rpow_natCast, Real.rpow_one]
              ring
      have hW := hCW P big hadm (J + 1) (Function.update (unsharedSlots C) gs ∅) b
        (fun g => by
          rcases eq_or_ne g gs with rfl | hg
          · rw [Function.update_self, Finset.card_empty]
            omega
          · rw [Function.update_of_ne hg]
            refine (Finset.card_insert_le _ _).trans ?_
            rw [Finset.card_map]
            exact Nat.add_le_add_right (hC g) 1) hb n
      rw [hcf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg h𝒲0,
        Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
      exact mul_le_mul (mul_le_mul h𝒲1 h𝒜 (abs_nonneg _) hL0.le) hW (norm_nonneg _)
        (by positivity)
    rw [htup]
    exact hx hAP1 hAP2 (P gs) (harmonicMass (P gs)) (x ^ u (Fin.last d)) (x ^ v (Fin.last d))
      cf ψ₁ Y σ k h hs (hadm.2.2.2.2.2.1 gs).1 hA hB hcfb hψ hψs hψd hY₁ hY₂ hσ hk₁ hk₂ t₁ t₂
      h₁₂ hrange
  constructor
  · refine hboth _ _ fun t ht => ?_
    have h₁ : 0 < L ^ B' := by positivity
    rw [abs_of_pos (lt_of_lt_of_le h₁ ht.1)]
    exact ⟨ht.1, ht.2⟩
  · refine hboth _ _ fun t ht => ?_
    have h₁ : 0 < L ^ B' := by positivity
    rw [abs_of_neg (lt_of_le_of_lt ht.2 (neg_lt_zero.2 h₁))]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

end Erdos408.TwoSided
