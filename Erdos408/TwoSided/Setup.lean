import Erdos408.Extraction.Sieve.Inert
import Erdos408.OneSided.Cauchy
import Erdos408.OneSided.Decomposition.Eventually
import Erdos408.TwoSided.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Uniform facts and the reindexing

The setup of `blueprint/two_sided_correlation.md` §2.

* R1: `TwoSidedCorrelation`'s groups, indexed by the Finsets themselves, become groups
  indexed by `ι = ↥(Sg ∪ Bg)` with `P = Subtype.val` and `big = univ.filter (·.1 ∈ Bg)`. The
  marked weights and the stripped integers agree, and the (6.1) hypotheses give
  `GroupAdmissible`.
* The normalized twisted Dirichlet polynomial `Y⁻¹ ∑_{Y ≤ w ≤ 2Y} c(w) e(hw/k) w^{it}` of
  interface E, with its continuity in `t`.
* Two pieces of glue: an integral against a Mellin density, split at a frequency `R`, and
  the growth facts `(T + E₀)^n ≤ L`, `exp(-cL/T²⁰) ≤ L^{-D}`, `L^r ≤ x` and
  `K^n ≤ L^{C log K}` for `n ≤ C log L`.
* Crude forms of U7 and U9, shared by interfaces G, C and E:
  `0 ≤ 𝒲 ≤ (2/(1-q))^r ≤ L` (`markedWeight_bands_le`, `eventually_markedWeight_band_le`),
  `|F(n)| ≤ L` for `1 ≤ n ≤ x³` (`eventually_abs_centeredCore_le_log`, from the slot count
  bound `abs_slotCount_le_of_le_cube`), and `|W_S^b(n)| ≤ K^{#ι} ≤ L^{C_W}`
  (`exists_norm_markedListWeight_le_pow`, `exists_norm_markedListWeight_le_rpow`, from the
  list count `card_slotLists_le`).
* U8 in its algebraic form: the marked weights at `m` and `n` agree when the group primes
  dividing them agree (`markedWeight_congr`, `markedListWeight_congr`).
* The free labels `auxLabels`: membership, positivity of `D_S`, `D_{A ∪ B} = D_A D_B`, and the
  law `labelMass = ∏ μ_g` of total mass `1` (`sum_labelMass`); `t_g = |C g| + 1`.
* Analytic glue: Dirichlet polynomials are continuous, `ξ ↦ a(ξ) y^{2πiξ}` is integrable, and
  Cauchy–Schwarz under the integral, `∫ |∑ γ_m J_m|² ≤ #M ∑ ∫ |J_m|²` for `|γ| ≤ 1`.

The other uniform facts of §2 (U1–U11) are proved where they are used.
-/

namespace Erdos408.TwoSided

open Filter MeasureTheory

/-! ### R1. Reindexing -/

/-- R1: the marked weight of a family of Finsets is that of its coercion to a type. -/
theorem markedWeight_coe_sort (s : Finset (Finset ℕ)) (q : ℝ) (n : ℕ) :
    markedWeight s q id n = markedWeight (Finset.univ : Finset s) q Subtype.val n := by
  unfold markedWeight
  rw [Finset.card_univ, Fintype.card_coe, Finset.sum_coe_sort s fun i => primeCount i n,
    Finset.prod_coe_sort s fun i => (primeCount i n : ℝ) / harmonicMass i]
  rfl

/-- R1: the primes of a family of Finsets are those of its coercion to a type. -/
theorem biUnion_coe_sort (s : Finset (Finset ℕ)) :
    s.biUnion id = (Finset.univ : Finset s).biUnion Subtype.val := by
  ext p
  simp

/-- R1: the (6.1) hypotheses of `TwoSidedCorrelation` give `GroupAdmissible` for
`ι = ↥(Sg ∪ Bg)`, with `big = univ.filter (·.1 ∈ Bg)`. -/
theorem groupAdmissible_coe_sort {c₀ C₀ vlo vhi x : ℝ} {Sg Bg : Finset (Finset ℕ)}
    (hdisj : Disjoint Sg Bg) (hpw : (Sg ∪ Bg : Set (Finset ℕ)).PairwiseDisjoint id)
    (hS₁ : c₀ * Real.log (Real.log x) ≤ Sg.card)
    (hS₂ : (Sg.card : ℝ) ≤ C₀ * Real.log (Real.log x))
    (hB₁ : c₀ * Real.log (Real.log x) ≤ Bg.card)
    (hB₂ : (Bg.card : ℝ) ≤ C₀ * Real.log (Real.log x))
    (hV : ∀ P ∈ Sg ∪ Bg, vlo ≤ harmonicMass P ∧ harmonicMass P ≤ vhi)
    (hSr : ∀ P ∈ Sg, P ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
      (Real.exp (Real.log x ^ (0.36 : ℝ))))
    (hBr : ∀ P ∈ Bg, P ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
      (Real.exp (Real.log x ^ (0.46 : ℝ))))
    (hBi : ∀ P ∈ Bg, ∃ y z : ℝ, P = primesIcc y z) :
    GroupAdmissible c₀ C₀ vlo vhi x (Subtype.val : ↥(Sg ∪ Bg) → Finset ℕ)
      (Finset.univ.filter fun g => g.1 ∈ Bg) := by
  -- the small groups are the complement of the big ones
  have hsmall : ((Finset.univ : Finset ↥(Sg ∪ Bg)) \
      Finset.univ.filter fun g => g.1 ∈ Bg).card = Sg.card := by
    refine Finset.card_bij (fun g _ => g.1) ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hg
      rcases Finset.mem_union.1 g.2 with h | h
      · exact h
      · exact absurd h hg
    · intro g₁ _ g₂ _ h
      exact Subtype.ext h
    · intro P hP
      refine ⟨⟨P, Finset.mem_union_left _ hP⟩, ?_, rfl⟩
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
      exact Finset.disjoint_left.1 hdisj hP
  have hbig : (Finset.univ.filter fun g : ↥(Sg ∪ Bg) => g.1 ∈ Bg).card = Bg.card := by
    refine Finset.card_bij (fun g _ => g.1) ?_ ?_ ?_
    · intro g hg
      exact (Finset.mem_filter.1 hg).2
    · intro g₁ _ g₂ _ h
      exact Subtype.ext h
    · intro P hP
      exact ⟨⟨P, Finset.mem_union_right _ hP⟩, by simpa using hP, rfl⟩
  refine ⟨fun g h hgh => hpw (by rw [← Finset.coe_union]; exact g.2)
      (by rw [← Finset.coe_union]; exact h.2)
      fun h' => hgh (Subtype.ext h'), ?_, ?_, ?_, ?_,
    fun g => hV g.1 g.2, fun g hg => ?_, fun g hg => hBr g.1 (Finset.mem_filter.1 hg).2,
    fun g hg => hBi g.1 (Finset.mem_filter.1 hg).2⟩
  · rw [hsmall]; exact hS₁
  · rw [hsmall]; exact hS₂
  · rw [hbig]; exact hB₁
  · rw [hbig]; exact hB₂
  · have hg' : g.1 ∉ Bg := fun h => hg (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rcases Finset.mem_union.1 g.2 with h | h
    · exact hSr g.1 h
    · exact absurd h hg'

/-! ### The twisted Dirichlet polynomial of interface E -/

/-- The normalized twisted Dirichlet polynomial `Y⁻¹ ∑_{Y ≤ w ≤ 2Y} c(w) e(hw/k) w^{it}`, the
integrand of the mean square (6.24). -/
noncomputable def twistedPoly (Y : ℝ) (c : ℕ → ℂ) (h : ℤ) (k : ℕ) (t : ℝ) : ℂ :=
  (Y : ℂ)⁻¹ * ∑ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
    c w * Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
      (w : ℂ) ^ ((t : ℂ) * Complex.I)

/-- The twisted polynomial is linear in its coefficients. -/
theorem twistedPoly_sub_add (Y : ℝ) (c₁ c₂ c₃ : ℕ → ℂ) (h : ℤ) (k : ℕ) (t : ℝ) :
    twistedPoly Y (fun w => c₁ w - c₂ w + c₃ w) h k t =
      twistedPoly Y c₁ h k t - twistedPoly Y c₂ h k t + twistedPoly Y c₃ h k t := by
  simp only [twistedPoly, ← mul_sub, ← mul_add, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- `t ↦ |Y⁻¹ ∑ c(w) e(hw/k) w^{it}|²` is continuous for `Y > 0`. -/
theorem continuous_norm_twistedPoly_sq {Y : ℝ} (hY : 0 < Y) (c : ℕ → ℂ) (h : ℤ) (k : ℕ) :
    Continuous fun t => ‖twistedPoly Y c h k t‖ ^ 2 := by
  unfold twistedPoly
  refine ((continuous_const.mul (continuous_finsetSum _ fun w hw =>
    continuous_const.mul ?_)).norm).pow 2
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  have hw : 1 ≤ w := le_trans (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hY).ne')
    (Finset.mem_Icc.1 hw).1
  exact_mod_cast (Nat.one_le_iff_ne_zero.1 hw)

/-- `|P₁ - P₂ + P₃|² ≤ 3 (|P₁|² + |P₂|² + |P₃|²)`, integrated over `[a, b]`. -/
theorem integral_norm_twistedPoly_sub_add_le {Y : ℝ} (hY : 0 < Y) (c₁ c₂ c₃ : ℕ → ℂ) (h : ℤ)
    (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖twistedPoly Y (fun w => c₁ w - c₂ w + c₃ w) h k t‖ ^ 2 ≤
      3 * ((∫ t in a..b, ‖twistedPoly Y c₁ h k t‖ ^ 2) +
        (∫ t in a..b, ‖twistedPoly Y c₂ h k t‖ ^ 2) +
        ∫ t in a..b, ‖twistedPoly Y c₃ h k t‖ ^ 2) := by
  have hi : ∀ c, IntervalIntegrable (fun t => ‖twistedPoly Y c h k t‖ ^ 2) volume a b :=
    fun c => (continuous_norm_twistedPoly_sq hY c h k).intervalIntegrable a b
  rw [← intervalIntegral.integral_add (hi c₁) (hi c₂),
    ← intervalIntegral.integral_add ((hi c₁).add (hi c₂)) (hi c₃),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab (hi _)
    ((((hi c₁).add (hi c₂)).add (hi c₃)).const_mul 3) fun t _ => ?_
  rw [twistedPoly_sub_add]
  have h₁ := norm_nonneg (twistedPoly Y c₁ h k t)
  have h₂ := norm_nonneg (twistedPoly Y c₂ h k t)
  have h₃ := norm_nonneg (twistedPoly Y c₃ h k t)
  have hle : ‖twistedPoly Y c₁ h k t - twistedPoly Y c₂ h k t + twistedPoly Y c₃ h k t‖ ≤
      ‖twistedPoly Y c₁ h k t‖ + ‖twistedPoly Y c₂ h k t‖ + ‖twistedPoly Y c₃ h k t‖ :=
    (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
  calc ‖twistedPoly Y c₁ h k t - twistedPoly Y c₂ h k t + twistedPoly Y c₃ h k t‖ ^ 2
      ≤ (‖twistedPoly Y c₁ h k t‖ + ‖twistedPoly Y c₂ h k t‖ + ‖twistedPoly Y c₃ h k t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ ≤ 3 * (‖twistedPoly Y c₁ h k t‖ ^ 2 + ‖twistedPoly Y c₂ h k t‖ ^ 2 +
          ‖twistedPoly Y c₃ h k t‖ ^ 2) := by
        nlinarith [sq_nonneg (‖twistedPoly Y c₁ h k t‖ - ‖twistedPoly Y c₂ h k t‖),
          sq_nonneg (‖twistedPoly Y c₂ h k t‖ - ‖twistedPoly Y c₃ h k t‖),
          sq_nonneg (‖twistedPoly Y c₁ h k t‖ - ‖twistedPoly Y c₃ h k t‖)]

/-- The mean square over `[a, b]` is at most that over a larger interval `[a', b']`. -/
theorem integral_norm_twistedPoly_sq_mono {Y : ℝ} (hY : 0 < Y) (c : ℕ → ℂ) (h : ℤ) (k : ℕ)
    {a b a' b' : ℝ} (ha : a' ≤ a) (hab : a ≤ b) (hb : b ≤ b') :
    ∫ t in a..b, ‖twistedPoly Y c h k t‖ ^ 2 ≤ ∫ t in a'..b', ‖twistedPoly Y c h k t‖ ^ 2 :=
  intervalIntegral.integral_mono_interval ha hab hb
    (Eventually.of_forall fun t => by positivity)
    ((continuous_norm_twistedPoly_sq hY c h k).intervalIntegrable a' b')

/-! ### Glue -/

/-- An integral against a Mellin density `a`, split at frequency `R`: if `‖Φ‖ ≤ B₁` on
`|ξ| ≤ R` and `‖Φ‖ ≤ B₂` everywhere, then
`‖∫ a Φ‖ ≤ B₁ ∫ ‖a‖ + B₂ ∫_{|ξ| > R} ‖a‖`. -/
theorem norm_integral_mul_le_of_split {a Φ : ℝ → ℂ} (ha : Integrable a) {R B₁ B₂ : ℝ}
    (hB₁ : 0 ≤ B₁) (h₁ : ∀ ξ, |ξ| ≤ R → ‖Φ ξ‖ ≤ B₁)
    (h₂ : ∀ ξ, ‖Φ ξ‖ ≤ B₂) :
    ‖∫ ξ, a ξ * Φ ξ‖ ≤ B₁ * (∫ ξ, ‖a ξ‖) + B₂ * ∫ ξ in {ξ : ℝ | R < |ξ|}, ‖a ξ‖ := by
  have hs : MeasurableSet {ξ : ℝ | R < |ξ|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hi₁ : Integrable fun ξ => B₁ * ‖a ξ‖ := ha.norm.const_mul B₁
  have hi₂ : Integrable ({ξ : ℝ | R < |ξ|}.indicator fun ξ => B₂ * ‖a ξ‖) :=
    (ha.norm.const_mul B₂).indicator hs
  refine (norm_integral_le_of_norm_le (hi₁.add hi₂) (Eventually.of_forall fun ξ => ?_)).trans_eq
    ?_
  · rw [norm_mul]
    by_cases hξ : R < |ξ|
    · rw [Pi.add_apply, Set.indicator_of_mem (show ξ ∈ {ξ : ℝ | R < |ξ|} from hξ)]
      nlinarith [h₂ ξ, norm_nonneg (a ξ), norm_nonneg (Φ ξ)]
    · rw [Pi.add_apply, Set.indicator_of_notMem (show ξ ∉ {ξ : ℝ | R < |ξ|} from hξ)]
      nlinarith [h₁ ξ (not_lt.1 hξ), norm_nonneg (a ξ)]
  · rw [integral_add' hi₁ hi₂, integral_indicator hs, integral_const_mul, integral_const_mul]

/-- Eventually `0 ≤ T + E₀` and `(T + E₀)^n ≤ L`. -/
theorem eventually_logLog_add_pow_le (E₀ : ℝ) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 ≤ Real.log (Real.log x) + E₀ ∧
      (Real.log (Real.log x) + E₀) ^ n ≤ Real.log x := by
  have hT := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hT.eventually_ge_atTop (|E₀| + 1),
    ((Real.tendsto_exp_div_pow_atTop n).comp hT).eventually_ge_atTop (2 ^ n),
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x h₁ h₂ hL
  simp only [Function.comp_apply] at h₁ h₂
  set T := Real.log (Real.log x)
  have hT0 : 0 < T := by linarith [abs_nonneg E₀]
  refine ⟨by linarith [neg_abs_le E₀], ?_⟩
  rw [le_div_iff₀ (by positivity)] at h₂
  calc (T + E₀) ^ n ≤ (2 * T) ^ n :=
        pow_le_pow_left₀ (by linarith [neg_abs_le E₀]) (by linarith [le_abs_self E₀]) n
    _ = 2 ^ n * T ^ n := mul_pow _ _ _
    _ ≤ Real.exp T := h₂
    _ = Real.log x := Real.exp_log hL

/-- Eventually `exp(-c L / T²⁰) ≤ L^{-D}`, for `c > 0`: the slot margin `x^{-ε}` beats every
power of `L`. -/
theorem eventually_exp_neg_margin_le {c : ℝ} (hc : 0 < c) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-(c * Real.log x / Real.log (Real.log x) ^ 20)) ≤ Real.log x ^ (-D) := by
  have hT := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hT.eventually_gt_atTop 0,
    ((Real.tendsto_exp_div_pow_atTop 21).comp hT).eventually_ge_atTop ((|D| + 1) / c),
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hT0 h₂ hL
  simp only [Function.comp_apply] at hT0 h₂
  rw [Real.rpow_def_of_pos hL, Real.exp_le_exp]
  set T := Real.log (Real.log x)
  rw [Real.exp_log hL, div_le_iff₀ (by positivity)] at h₂
  -- `D T ≤ (|D| + 1) T ≤ c L / T²⁰`
  have h₃ : (|D| + 1) * T ^ 21 ≤ c * Real.log x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h₂
    linarith
  have key : D * T ≤ c * Real.log x / T ^ 20 := by
    rw [le_div_iff₀ (by positivity)]
    have h21 : T ^ 21 = T * T ^ 20 := by ring
    have hT20 : 0 < T ^ 20 := by positivity
    nlinarith [le_abs_self D, mul_pos hT0 hT20]
  linarith

/-- Eventually `L^r ≤ x`. -/
theorem eventually_log_rpow_le_self (r : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ r ≤ x := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop r one_pos).bound one_pos,
    Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hL hx0
  rwa [Real.norm_of_nonneg (Real.rpow_nonneg hL.le r), Real.rpow_one,
    Real.norm_of_nonneg hx0.le, one_mul] at hx

/-- `K^n ≤ L^{C log K}` for `K ≥ 1`, `L > 0` and `n ≤ C log L`. -/
theorem pow_le_rpow_mul_log {K L C : ℝ} (hK : 1 ≤ K) (hL : 0 < L) {n : ℕ}
    (hn : (n : ℝ) ≤ C * Real.log L) : K ^ n ≤ L ^ (C * Real.log K) := by
  rw [← Real.rpow_natCast]
  calc K ^ (n : ℝ) ≤ K ^ (C * Real.log L) := Real.rpow_le_rpow_of_exponent_le hK hn
    _ = L ^ (C * Real.log K) := by
        rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hL]
        ring_nf

/-! ### Crude U7 -/

section

open Finset

/-- **U7 (pointwise).** `0 ≤ 𝒲(n) ≤ (2/(1-q))^r` when every band has mass at least `1/2`. -/
theorem markedWeight_bands_le {q x : ℝ} (hq : 0 < q) (hq₁ : q < 1) {r : ℕ} (a : Fin r → ℝ)
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (a i))) (n : ℕ) :
    0 ≤ markedWeight Finset.univ q (fun i => band x (a i)) n ∧
      markedWeight Finset.univ q (fun i => band x (a i)) n ≤ (2 / (1 - q)) ^ r := by
  rw [TypeII.markedWeight_eq_prod hq.ne']
  refine ⟨prod_nonneg fun i _ => TypeII.bandWeight_nonneg hq _ _ _, ?_⟩
  calc ∏ i, bandWeight q x (a i) n ≤ ∏ _i : Fin r, 2 / (1 - q) := by
        refine prod_le_prod₀ (fun i _ => TypeII.bandWeight_nonneg hq _ _ _) fun i _ => ?_
        have hVi := hV i
        calc bandWeight q x (a i) n
            ≤ 1 / ((1 - q) * harmonicMass (band x (a i))) :=
              TypeII.bandWeight_le hq hq₁ _ _ _ (by linarith)
          _ ≤ 2 / (1 - q) := by
              rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
              nlinarith
    _ = (2 / (1 - q)) ^ r := by rw [prod_const, card_univ, Fintype.card_fin]

/-- **U7 (inert weight).** Eventually `0 ≤ 𝒲(n) ≤ L` for all `n`, uniformly in at most
`K₀ + C_N s` bands with exponents at least `a₋ > 1/10`: every band has mass `≥ 1/2`, so
`𝒲 ≤ (2/(1 - q))^r`, and `r log(2/(1 - q)) ≤ T`. -/
theorem eventually_markedWeight_band_le (q alo ahi : ℝ) (K₀ : ℕ) (CN : ℝ) (hq : 0 < q)
    (hq₁ : q < 1) (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ (r : ℕ) (a : Fin r → ℝ), InertAdmissible K₀ CN alo ahi x a →
      ∀ n : ℕ, 0 ≤ markedWeight Finset.univ q (fun i => band x (a i)) n ∧
        markedWeight Finset.univ q (fun i => band x (a i)) n ≤ Real.log x := by
  set ℓ := Real.log (2 / (1 - q)) with hℓ
  have hq2 : 1 < 2 / (1 - q) := by rw [one_lt_div (by linarith)]; linarith
  have hℓ0 : 0 < ℓ := Real.log_pos hq2
  have hT : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlog := Real.isLittleO_log_id_atTop.bound
    (by positivity : (0 : ℝ) < 1 / (2 * (|CN| * ℓ + 1)))
  filter_upwards [hT.eventually hlog, hT.eventually_ge_atTop (2 * K₀ * ℓ + 1),
    Real.tendsto_log_atTop.eventually_gt_atTop 0,
    OneSided.eventually_harmonicMass_band halo.le] with x hlx hTK hL hV
  intro r a ha n
  set T := Real.log (Real.log x) with hTdef
  have hT1 : 1 ≤ T := le_trans (by nlinarith [Nat.cast_nonneg (α := ℝ) K₀]) hTK
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT1
  rw [Real.norm_of_nonneg hlT, id, Real.norm_of_nonneg (by linarith)] at hlx
  obtain ⟨h₀, h₁⟩ := markedWeight_bands_le hq hq₁ a (fun i => (hV (a i) (ha.2.1 i).1).1) n
  refine ⟨h₀, h₁.trans ?_⟩
  calc (2 / (1 - q)) ^ r = Real.exp (r * ℓ) := by
        rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    _ ≤ Real.exp T := by
        rw [Real.exp_le_exp]
        -- `r ℓ ≤ (K₀ + |C_N| log T) ℓ ≤ T`
        have hr : (r : ℝ) ≤ K₀ + |CN| * Real.log T := ha.1.trans (by
          gcongr
          exact le_abs_self CN)
        have h₁ : |CN| * ℓ * Real.log T ≤ T / 2 := by
          have h := mul_le_mul_of_nonneg_left hlx (by positivity : 0 ≤ |CN| * ℓ)
          calc |CN| * ℓ * Real.log T ≤ |CN| * ℓ * (1 / (2 * (|CN| * ℓ + 1)) * T) := h
            _ ≤ T / 2 := by
                rw [← mul_assoc, mul_one_div, div_mul_eq_mul_div, div_le_div_iff₀
                  (by positivity) (by norm_num)]
                nlinarith [abs_nonneg CN]
        calc (r : ℝ) * ℓ ≤ (K₀ + |CN| * Real.log T) * ℓ := mul_le_mul_of_nonneg_right hr hℓ0.le
          _ = K₀ * ℓ + |CN| * ℓ * Real.log T := by ring
          _ ≤ T := by linarith
    _ = Real.log x := Real.exp_log hL

/-- The slot count at `0 < n ≤ x³` is at most `(3 / ε)^{k+1}` in absolute value, when the
lower slot endpoints exceed `x^ε` and `|𝔟| ≤ 1`; `Sieve.abs_slotCount_le` at `x^{3/2}`. -/
theorem abs_slotCount_le_of_le_cube {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) {k : ℕ}
    {u v : Fin (k + 1) → ℝ} (hu : ∀ i, ε ≤ u i) {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, |B Q| ≤ 1)
    {n : ℕ} (hn : 0 < n) (hnx : (n : ℝ) ≤ x ^ 3) :
    |slotCount x u v B n| ≤ (3 / ε) ^ (k + 1) := by
  -- `x³ = (x^{3/2})²` and `x^ε = (x^{3/2})^{2ε/3}`
  have hy : 1 < x ^ (3 / 2 : ℝ) := Real.one_lt_rpow hx (by norm_num)
  have hε' : 0 < 2 * ε / 3 := by positivity
  have hpow : (x ^ (3 / 2 : ℝ)) ^ (2 * ε / 3) = x ^ ε := by
    rw [← Real.rpow_mul (by linarith)]
    congr 1
    ring
  have hsq : (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have hcard := Sieve.card_primeFactors_gt_le hy hε' hn (by rw [hsq]; exact hnx)
  rw [hpow, show 2 / (2 * ε / 3) = 3 / ε by field_simp] at hcard
  set P := n.primeFactors.filter fun p : ℕ => x ^ ε < (p : ℝ)
  have hsub : (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n) ⊆
      Fintype.piFinset fun _ => P := by
    intro Q hQ
    obtain ⟨hQ, hdvd⟩ := mem_filter.1 hQ
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨-, hp, hlt⟩ := (Sieve.mem_slotTuples.1 hQ).1 i
    refine mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp, (dvd_prod_of_mem _ (mem_univ i)).trans hdvd,
      hn.ne'⟩, lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx.le (hu i)) hlt⟩
  calc |slotCount x u v B n|
      ≤ ∑ Q ∈ (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n), |B (Fin.init Q)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q ∈ (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ n), (1 : ℝ) :=
        sum_le_sum fun _ _ => hB _
    _ ≤ #(Fintype.piFinset fun _ : Fin (k + 1) => P) := by
        rw [sum_const, nsmul_one]
        exact_mod_cast card_le_card hsub
    _ = (#P : ℝ) ^ (k + 1) := by rw [Fintype.card_piFinset]; simp
    _ ≤ (3 / ε) ^ (k + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _

/-- **Crude U7.** Eventually `|F(n)| ≤ L` for `1 ≤ n ≤ x³`, uniformly in at most `K₀ + C_N s`
bands, the admissible slots and `|B| ≤ 1`. The inert weight is at most
`(2/(1-q))^r ≤ T^{O(1)}`, the slot count at most `(3T²⁰/c)^{d+1}` and the harmonic constant at
most `(T + E₀)^{d+1}`, and `T^N ≤ L`. -/
theorem eventually_abs_centeredCore_le_log (q alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ)
    (hq : 0 < q) (hq₁ : q < 1) (halo : 1 / 10 < alo) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ)
      (Bc : (Fin d → ℕ) → ℝ),
      InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ 3 →
        |centeredCore x q a u v Bc n| ≤ Real.log x := by
  obtain ⟨E, -, hmert⟩ := Sieve.abs_sum_inv_primes_sub_le
  set β := Real.log (2 / (1 - q))
  set N₁ := ⌈β * (K₀ + max CN 0)⌉₊
  have hβ : 0 < β := Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
  have hT := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hs := Real.tendsto_log_atTop.comp hT
  filter_upwards [OneSided.eventually_harmonicMass_band halo.le, eventually_ge_atTop 2,
    hs.eventually_ge_atTop 1, hT.eventually_ge_atTop (max (3 / c) (max E 2)),
    eventually_logLog_add_pow_le 0 (N₁ + (21 * (d + 1) + 1))]
    with x hV hx2 hs1 hT2 hpow r a u v Bc ha hslot hB n hn1 hnx
  simp only [Function.comp_apply] at hs1 hT2
  rw [add_zero] at hpow
  set T := Real.log (Real.log x) with hTdef
  set s := Real.log T
  have hT3c : 3 / c ≤ T := (le_max_left _ _).trans hT2
  have hTE : E ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT2
  have hT2' : 2 ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT2
  have hT0 : 0 < T := by linarith
  -- the inert weight: `0 ≤ 𝒲 ≤ (2/(1-q))^r ≤ T^{N₁}`
  obtain ⟨hW0, hW1⟩ := markedWeight_bands_le hq hq₁ a (fun i => (hV (a i) (ha.2.1 i).1).1) n
  have hW : markedWeight Finset.univ q (fun i => band x (a i)) n ≤ T ^ N₁ := by
    refine hW1.trans ?_
    have hr : (r : ℝ) * β ≤ N₁ * s := by
      have h₁ : (r : ℝ) ≤ (K₀ + max CN 0) * s := by
        have hK : (K₀ : ℝ) ≤ K₀ * s := le_mul_of_one_le_right (Nat.cast_nonneg _) hs1
        nlinarith [ha.1, le_max_left CN 0, le_max_right CN 0]
      have h₂ : β * (K₀ + max CN 0) ≤ N₁ := Nat.le_ceil _
      nlinarith
    calc (2 / (1 - q)) ^ r = Real.exp (r * β) := by
          rw [Real.exp_nat_mul, Real.exp_log (by apply div_pos <;> linarith)]
      _ ≤ Real.exp (N₁ * s) := Real.exp_le_exp.2 hr
      _ = T ^ N₁ := by rw [Real.exp_nat_mul, Real.exp_log hT0]
  -- the slot count and the harmonic constant
  have hε : 0 < c / T ^ 20 := by positivity
  have hF : |slotCount x u v Bc n| ≤ T ^ (21 * (d + 1)) := by
    have h := abs_slotCount_le_of_le_cube (v := v) (by linarith) hε hslot.1 hB hn1 hnx
    refine h.trans ?_
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [div_div_eq_mul_div, div_le_iff₀ hc, pow_succ]
    rw [div_le_iff₀ hc] at hT3c
    nlinarith [pow_pos hT0 20]
  have hC : |slotMean x u v Bc| ≤ T ^ (21 * (d + 1)) := by
    have hv1 : ∑ i, v i ≤ 1 := by
      have h : ∑ i, v i ≤ 1 - c / T ^ 20 := hslot.2
      linarith
    have h1 := Sieve.sum_inv_slotTuples_le (x := x) (by linarith) hv1 (u := u)
    have h2 : ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p ≤ T + E :=
      Sieve.sum_inv_primes_le_logLog hmert hx2 le_rfl
    have h0 : 0 ≤ ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
    have h3 : |slotMean x u v Bc| ≤ ∑ Q ∈ slotTuples x u v, 1 / ∏ i, (Q i : ℝ) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q _ => ?_)
      have h0 : (0 : ℝ) ≤ ∏ i, (Q i : ℝ) := prod_nonneg fun i _ => Nat.cast_nonneg _
      rw [abs_div, abs_of_nonneg h0]
      exact div_le_div_of_nonneg_right (hB _) h0
    have h21 : 2 * T ≤ T ^ 21 := by
      have h20 : 2 ≤ T ^ 20 := hT2'.trans (le_self_pow₀ (by linarith) (by norm_num))
      rw [pow_succ']
      nlinarith [mul_le_mul_of_nonneg_left h20 hT0.le]
    calc |slotMean x u v Bc| ≤ (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (d + 1) := h3.trans h1
      _ ≤ (2 * T) ^ (d + 1) := pow_le_pow_left₀ h0 (by linarith) _
      _ ≤ (T ^ 21) ^ (d + 1) := pow_le_pow_left₀ (by positivity) h21 _
      _ = T ^ (21 * (d + 1)) := by rw [pow_mul]
  have hΔ : |slotCount x u v Bc n - slotMean x u v Bc| ≤ T ^ (21 * (d + 1) + 1) := by
    rw [pow_succ]
    calc |slotCount x u v Bc n - slotMean x u v Bc|
        ≤ |slotCount x u v Bc n| + |slotMean x u v Bc| := abs_sub _ _
      _ ≤ T ^ (21 * (d + 1)) * T := by nlinarith [pow_pos hT0 (21 * (d + 1))]
  unfold centeredCore
  rw [abs_mul, abs_of_nonneg hW0]
  calc markedWeight Finset.univ q (fun i => band x (a i)) n *
        |slotCount x u v Bc n - slotMean x u v Bc|
      ≤ T ^ N₁ * T ^ (21 * (d + 1) + 1) := mul_le_mul hW hΔ (abs_nonneg _) (by positivity)
    _ = T ^ (N₁ + (21 * (d + 1) + 1)) := (pow_add _ _ _).symm
    _ ≤ Real.log x := hpow.2

/-! ### Crude U9 -/

/-- There are at most `∏_g ω_g(n)^{|S g|}` represented lists at `n`. -/
theorem card_slotLists_le {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) {M : ℕ}
    (S : ι → Finset (Fin M)) (n : ℕ) :
    #(slotLists P S n) ≤ ∏ g, primeCount (P g) n ^ #(S g) := by
  calc #(slotLists P S n)
      ≤ #(Fintype.piFinset fun g => Fintype.piFinset fun i =>
          if i ∈ S g then (P g).filter (· ∣ n) else {1}) := by
        refine card_le_card fun p hp => ?_
        obtain ⟨hmem, hp⟩ := mem_filter.1 hp
        rw [Fintype.mem_piFinset] at hmem ⊢
        intro g
        have hg := Fintype.mem_piFinset.1 (hmem g)
        rw [Fintype.mem_piFinset]
        intro i
        have hi := hg i
        split_ifs at hi ⊢ with h
        · exact mem_filter.2 ⟨hi, (hp g).2 i h⟩
        · exact hi
    _ = ∏ g, primeCount (P g) n ^ #(S g) := by
        rw [Fintype.card_piFinset]
        refine prod_congr rfl fun g _ => ?_
        rw [Fintype.card_piFinset]
        rw [show (∏ i, #(if i ∈ S g then (P g).filter (· ∣ n) else {1})) =
            ∏ i, if i ∈ S g then primeCount (P g) n else 1 from
          prod_congr rfl fun i _ => by split_ifs <;> simp [primeCount]]
        rw [Fintype.prod_ite_mem, prod_const]

/-- One factor of the marked list weight: `q₀^{z - t} z^t V^{-t} ≤ K` for `t ≤ m₀ + 1` and
`V ≥ v₋`. -/
theorem exists_markedListWeight_factor_le {q₀ vlo : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hvlo : 0 < vlo) (m₀ : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ z t : ℕ, t ≤ m₀ + 1 → ∀ V : ℝ, vlo ≤ V →
      q₀ ^ ((z : ℤ) - t) * (z : ℝ) ^ t * V⁻¹ ^ t ≤ K := by
  obtain ⟨B, hB⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one (m₀ + 1)
    (by rw [abs_of_pos hq₀]; exact hq₀₁)).bddAbove_range
  set β := q₀⁻¹ * max 1 vlo⁻¹ with hβ
  have hβ1 : 1 ≤ β := one_le_mul_of_one_le_of_one_le (one_le_inv₀ hq₀ |>.2 hq₀₁.le)
    (le_max_left _ _)
  refine ⟨(1 + max B 0) * β ^ (m₀ + 1),
    one_le_mul_of_one_le_of_one_le (by linarith [le_max_right B 0]) (one_le_pow₀ hβ1),
    fun z t ht V hV => ?_⟩
  have hV0 : 0 < V := hvlo.trans_le hV
  -- `z^t q₀^z ≤ 1 + max B 0`
  have hz : (z : ℝ) ^ t * q₀ ^ z ≤ 1 + max B 0 := by
    rcases Nat.eq_zero_or_pos z with rfl | hz
    · rw [pow_zero, mul_one, Nat.cast_zero]
      linarith [pow_le_one₀ (le_refl (0 : ℝ)) zero_le_one (n := t), le_max_right B 0]
    · have h₁ : (z : ℝ) ^ t ≤ (z : ℝ) ^ (m₀ + 1) :=
        pow_le_pow_right₀ (by exact_mod_cast hz) ht
      have h₂ : (z : ℝ) ^ (m₀ + 1) * q₀ ^ z ≤ B := hB ⟨z, rfl⟩
      nlinarith [pow_pos hq₀ z, le_max_left B 0]
  -- `(q₀⁻¹ V⁻¹)^t ≤ β^{m₀+1}`
  have hq : (q₀⁻¹ * V⁻¹) ^ t ≤ β ^ (m₀ + 1) := by
    have h₁ : q₀⁻¹ * V⁻¹ ≤ β := by
      refine mul_le_mul_of_nonneg_left ((inv_anti₀ hvlo hV).trans (le_max_right _ _))
        (inv_nonneg.2 hq₀.le)
    calc (q₀⁻¹ * V⁻¹) ^ t ≤ β ^ t := pow_le_pow_left₀ (by positivity) h₁ t
      _ ≤ β ^ (m₀ + 1) := pow_le_pow_right₀ hβ1 ht
  have hsplit : q₀ ^ ((z : ℤ) - t) * (z : ℝ) ^ t * V⁻¹ ^ t =
      ((z : ℝ) ^ t * q₀ ^ z) * (q₀⁻¹ * V⁻¹) ^ t := by
    rw [zpow_sub₀ hq₀.ne', zpow_natCast, zpow_natCast]
    ring
  rw [hsplit]
  exact mul_le_mul hz hq (by positivity) (by linarith [le_max_right B 0])

/-- **U9 (per group).** There is `K ≥ 1` such that `|W_S^b(n)| ≤ K^{#ι}` for all groups with
`V_g ≥ v₋`, all `S` with `|S g| ≤ m₀ + 1`, all `|b| ≤ 1` and all `n`. -/
theorem exists_norm_markedListWeight_le_pow {q₀ vlo : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hvlo : 0 < vlo) (m₀ : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ),
      (∀ g, vlo ≤ harmonicMass (P g)) → ∀ (M : ℕ) (S : ι → Finset (Fin M))
        (b : (ι → Fin M → ℕ) → ℂ), (∀ g, (S g).card ≤ m₀ + 1) → (∀ p, ‖b p‖ ≤ 1) →
        ∀ n : ℕ, ‖markedListWeight P q₀ S b n‖ ≤ K ^ Fintype.card ι := by
  obtain ⟨K, hK1, hK⟩ := exists_markedListWeight_factor_le hq₀ hq₀₁ hvlo m₀
  refine ⟨K, hK1, fun {ι} _ _ P hV M S b hS hb n => ?_⟩
  set ω : ι → ℕ := fun g => primeCount (P g) n with hω
  -- the lists are at most `∏_g ω_g^{|S g|}`
  have hcard : ((slotLists P S n).card : ℝ) ≤ ∏ g, (ω g : ℝ) ^ (S g).card := by
    exact_mod_cast card_slotLists_le P S n
  have hexp : ((groupPrimeCount P n : ℤ) - ∑ g, ((S g).card : ℤ)) =
      ∑ g, ((ω g : ℤ) - (S g).card) := by
    rw [sum_sub_distrib]
    unfold groupPrimeCount
    push_cast
    rfl
  have hpos : 0 ≤ q₀ ^ ((groupPrimeCount P n : ℤ) - ∑ g, ((S g).card : ℤ)) *
      ∏ g, (harmonicMass (P g))⁻¹ ^ (S g).card := by
    have : ∀ g, 0 ≤ (harmonicMass (P g))⁻¹ := fun g =>
      inv_nonneg.2 (hvlo.le.trans (hV g))
    exact mul_nonneg (zpow_nonneg hq₀.le _) (prod_nonneg fun g _ => pow_nonneg (this g) _)
  unfold markedListWeight
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos]
  calc _ ≤ (q₀ ^ ((groupPrimeCount P n : ℤ) - ∑ g, ((S g).card : ℤ)) *
        ∏ g, (harmonicMass (P g))⁻¹ ^ (S g).card) * ∏ g, (ω g : ℝ) ^ (S g).card := by
        refine mul_le_mul_of_nonneg_left ?_ hpos
        refine (norm_sum_le _ _).trans ?_
        refine (sum_le_sum fun p _ => hb p).trans ?_
        rw [sum_const, nsmul_eq_mul, mul_one]
        exact hcard
    _ = ∏ g, (q₀ ^ ((ω g : ℤ) - (S g).card) * (ω g : ℝ) ^ (S g).card *
        (harmonicMass (P g))⁻¹ ^ (S g).card) := by
        rw [hexp, ← TypeII.prod_zpow_eq _ hq₀.ne', prod_mul_distrib, prod_mul_distrib]
        ring
    _ ≤ ∏ _g : ι, K := by
        refine prod_le_prod₀ (fun g _ => ?_) fun g _ =>
          hK (ω g) (S g).card (hS g) _ (hV g)
        have : 0 ≤ (harmonicMass (P g))⁻¹ := inv_nonneg.2 (hvlo.le.trans (hV g))
        positivity
    _ = K ^ Fintype.card ι := by rw [prod_const, card_univ]

/-- **Crude U9.** There is `C_W` such that eventually `|W_S^b(n)| ≤ L^{C_W}` for all `n`,
all `S` with `|S g| ≤ m₀ + 1` and all `|b| ≤ 1`: `|W_S^b(n)| ≤ K^{#ι}`, and there are at most
`2 C₀ T` groups. -/
theorem exists_norm_markedListWeight_le_rpow (q₀ c₀ C₀ vlo vhi : ℝ) (hq₀ : 0 < q₀)
    (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo) (m₀ : ℕ) :
    ∃ CW : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (M : ℕ) (S : ι → Finset (Fin M)) (b : (ι → Fin M → ℕ) → ℂ),
          (∀ g, (S g).card ≤ m₀ + 1) → (∀ p, ‖b p‖ ≤ 1) →
          ∀ n : ℕ, ‖markedListWeight P q₀ S b n‖ ≤ Real.log x ^ CW := by
  obtain ⟨K, hK1, hK⟩ := exists_norm_markedListWeight_le_pow hq₀ hq₀₁ hvlo m₀
  refine ⟨2 * |C₀| * Real.log K, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 0]
    with x hL hT
  simp only [Function.comp_apply] at hT
  intro ι _ _ P big hadm M S b hS hb n
  -- `|ι| ≤ 2 |C₀| T`
  have hcard : (Fintype.card ι : ℝ) ≤ 2 * |C₀| * Real.log (Real.log x) := by
    have h := card_sdiff_add_card_eq_card (subset_univ big)
    rw [card_univ] at h
    rw [← h]
    push_cast
    have h₁ := hadm.2.2.1
    have h₂ := hadm.2.2.2.2.1
    nlinarith [le_abs_self C₀]
  exact (hK P (fun g => (hadm.2.2.2.2.2.1 g).1) M S b hS hb n).trans
    (pow_le_rpow_mul_log hK1 hL hcard)

/-! ### U8, algebraically -/

/-- A marked weight depends on `n` only through the primes of its groups dividing `n`. -/
theorem markedWeight_congr {κ : Type*} (s : Finset κ) (q : ℝ) (G : κ → Finset ℕ) {m n : ℕ}
    (h : ∀ i ∈ s, ∀ p ∈ G i, p ∣ m ↔ p ∣ n) :
    markedWeight s q G m = markedWeight s q G n := by
  have hc : ∀ i ∈ s, primeCount (G i) m = primeCount (G i) n := fun i hi =>
    Sieve.primeCount_congr (h i hi)
  unfold markedWeight
  rw [sum_congr rfl hc, prod_congr rfl fun i hi => by rw [hc i hi]]

/-- The marked list weight depends on `n` only through the group primes dividing `n`. -/
theorem markedListWeight_congr {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ}
    (q₀ : ℝ) {M : ℕ} (S : ι → Finset (Fin M)) (b : (ι → Fin M → ℕ) → ℂ) {m n : ℕ}
    (h : ∀ g, ∀ p ∈ P g, p ∣ m ↔ p ∣ n) :
    markedListWeight P q₀ S b m = markedListWeight P q₀ S b n := by
  have hc : groupPrimeCount P m = groupPrimeCount P n := by
    unfold groupPrimeCount
    exact sum_congr rfl fun g _ => Sieve.primeCount_congr (h g)
  have hl : slotLists P S m = slotLists P S n := by
    unfold slotLists
    refine filter_congr fun p hp => ?_
    have hmem : ∀ g, ∀ i ∈ S g, p g i ∈ P g := by
      intro g i hi
      have := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hp g) i
      rwa [ite_eq_left hi] at this
    exact forall_congr' fun g => and_congr Iff.rfl
      (forall₂_congr fun i hi => h g _ (hmem g i hi))
  unfold markedListWeight
  rw [hc, hl]

/-! ### The free labels -/

/-- The unshared slots of group `g`: `t_g = |C g| + 1`. -/
theorem card_unsharedSlots {ι : Type} {J : ℕ} (C : ι → Finset (Fin J)) (g : ι) :
    (unsharedSlots C g).card = (C g).card + 1 := by
  rw [unsharedSlots, card_insert_of_notMem, card_map]
  simp [Fin.castSucc_ne_last]

/-- Membership in `auxLabels`, slot by slot. -/
theorem mem_auxLabels {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ} {J : ℕ}
    {C : ι → Finset (Fin J)} {l : ι → Fin J → ℕ} :
    l ∈ auxLabels P C ↔ ∀ g i, l g i ∈ if i ∈ C g then P g else {1} := by
  simp only [auxLabels, Fintype.mem_piFinset]

/-- The mass `∏_g ∏_{i ∈ C g} μ_g(a_{g,i})`, `μ_g(p) = 1/(V_g p)`, of a free label. -/
noncomputable def labelMass {ι : Type} [Fintype ι] (P : ι → Finset ℕ) {J : ℕ}
    (C : ι → Finset (Fin J)) (a : ι → Fin J → ℕ) : ℝ :=
  ∏ g, ∏ i ∈ C g, (harmonicMass (P g) * a g i)⁻¹

/-- The label mass is nonnegative. -/
theorem labelMass_nonneg {ι : Type} [Fintype ι] (P : ι → Finset ℕ) {J : ℕ}
    (C : ι → Finset (Fin J)) (a : ι → Fin J → ℕ) : 0 ≤ labelMass P C a := by
  unfold labelMass harmonicMass
  refine prod_nonneg fun g _ => prod_nonneg fun i _ => inv_nonneg.2 (mul_nonneg ?_ ?_)
  · exact sum_nonneg fun p _ => by positivity
  · exact Nat.cast_nonneg _

/-- The free labels have total mass `1`. -/
theorem sum_labelMass {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ}
    (hV : ∀ g, harmonicMass (P g) ≠ 0) {J : ℕ} (C : ι → Finset (Fin J)) :
    ∑ a ∈ auxLabels P C, labelMass P C a = 1 := by
  unfold auxLabels labelMass
  have hslot : ∀ g (y : Fin J → ℕ), ∏ i ∈ C g, (harmonicMass (P g) * y i)⁻¹ =
      ∏ i, if i ∈ C g then (harmonicMass (P g) * y i)⁻¹ else 1 := fun g y => by
    rw [prod_ite_mem, univ_inter]
  simp_rw [hslot]
  rw [← prod_univ_sum (fun g => Fintype.piFinset fun i => if i ∈ C g then P g else {1})
    (fun g y => ∏ i, if i ∈ C g then (harmonicMass (P g) * y i)⁻¹ else 1)]
  refine prod_eq_one fun g _ => ?_
  rw [← prod_univ_sum (fun i => if i ∈ C g then P g else {1})
    (fun i p => if i ∈ C g then (harmonicMass (P g) * p)⁻¹ else 1)]
  refine prod_eq_one fun i _ => ?_
  split_ifs with hi
  · simp_rw [mul_inv, ← mul_sum]
    rw [show ∑ p ∈ P g, ((p : ℕ) : ℝ)⁻¹ = harmonicMass (P g) by simp [harmonicMass]]
    exact inv_mul_cancel₀ (hV g)
  · simp

/-- The group primes of admissible groups are prime. -/
theorem prime_of_groupAdmissible {c₀ C₀ vlo vhi x : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Finset ℕ} {big : Finset ι} (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big) {g : ι}
    {p : ℕ} (hp : p ∈ P g) : p.Prime := by
  by_cases hg : g ∈ big
  · exact (mem_filter.1 (hadm.2.2.2.2.2.2.2.1 g hg hp)).2
  · exact (mem_filter.1 (hadm.2.2.2.2.2.2.1 g hg hp)).2

/-- Free labels of admissible groups have positive slot products. -/
theorem slotProduct_pos {c₀ C₀ vlo vhi x : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Finset ℕ} {big : Finset ι} (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big) {J : ℕ}
    {C : ι → Finset (Fin J)} {l : ι → Fin J → ℕ} (hl : l ∈ auxLabels P C)
    (S : ι → Finset (Fin J)) : 0 < slotProduct S l := by
  rw [mem_auxLabels] at hl
  refine prod_pos fun g _ => prod_pos fun i _ => ?_
  have := hl g i
  split_ifs at this with hi
  · exact (prime_of_groupAdmissible hadm this).pos
  · rw [mem_singleton.1 this]
    exact one_pos

/-- `D_{A ∪ B} = D_A D_B` for disjoint slots. -/
theorem slotProduct_union {ι : Type} [Fintype ι] {J : ℕ} {A B : ι → Finset (Fin J)}
    (hAB : ∀ g, Disjoint (A g) (B g)) (l : ι → Fin J → ℕ) :
    slotProduct (fun g => A g ∪ B g) l = slotProduct A l * slotProduct B l := by
  simp only [slotProduct, prod_union (hAB _), prod_mul_distrib]

/-! ### Analytic glue -/

/-- A Dirichlet polynomial `t ↦ ∑_{n ∈ s} c_n n^{it}` over positive integers is continuous. -/
theorem continuous_sum_cpow {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (c : ℕ → ℂ) :
    Continuous fun t : ℝ => ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) :=
  continuous_finsetSum _ fun n hn => continuous_const.mul
    (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hs n hn)))

/-- `ξ ↦ a(ξ) y^{2πiξ}` is integrable for `y > 0`. -/
theorem integrable_mul_cpow {a : ℝ → ℂ} (ha : Integrable a) {y : ℝ} (hy : 0 < y) :
    Integrable fun ξ : ℝ => a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
  refine ha.mul_bdd (c := 1)
    ((Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hy.ne'))).aestronglyMeasurable)
    (ae_of_all _ fun ξ => ?_)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

/-- Cauchy–Schwarz under the integral: for `|γ_m| ≤ 1` and continuous `J_m`,
`∫_{t₁}^{t₂} |∑_m γ_m J_m|² ≤ #M ∑_m ∫_{t₁}^{t₂} |J_m|²`. -/
theorem integral_norm_sum_sq_le {ι : Type*} (M : Finset ι) (γ : ι → ℂ)
    (hγ : ∀ m ∈ M, ‖γ m‖ ≤ 1) (J : ι → ℝ → ℂ) (hJ : ∀ m ∈ M, Continuous (J m)) {t₁ t₂ : ℝ}
    (h₁₂ : t₁ ≤ t₂) :
    ∫ t in t₁..t₂, ‖∑ m ∈ M, γ m * J m t‖ ^ 2 ≤
      #M * ∑ m ∈ M, ∫ t in t₁..t₂, ‖J m t‖ ^ 2 := by
  have hc : Continuous fun t => ‖∑ m ∈ M, γ m * J m t‖ ^ 2 :=
    ((continuous_finsetSum _ fun m hm => continuous_const.mul (hJ m hm)).norm).pow 2
  have hc' : ∀ m ∈ M, Continuous fun t => ‖J m t‖ ^ 2 := fun m hm => ((hJ m hm).norm).pow 2
  have hpt : ∀ t, ‖∑ m ∈ M, γ m * J m t‖ ^ 2 ≤ #M * ∑ m ∈ M, ‖J m t‖ ^ 2 := by
    intro t
    have h₁ : ‖∑ m ∈ M, γ m * J m t‖ ≤ ∑ m ∈ M, ‖J m t‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hγ m hm)
    calc ‖∑ m ∈ M, γ m * J m t‖ ^ 2 ≤ (∑ m ∈ M, ‖J m t‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h₁ 2
      _ ≤ #M * ∑ m ∈ M, ‖J m t‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  calc ∫ t in t₁..t₂, ‖∑ m ∈ M, γ m * J m t‖ ^ 2
      ≤ ∫ t in t₁..t₂, (#M : ℝ) * ∑ m ∈ M, ‖J m t‖ ^ 2 :=
        intervalIntegral.integral_mono_on h₁₂ (hc.intervalIntegrable _ _)
          ((continuous_const.mul (continuous_finsetSum _ hc')).intervalIntegrable _ _)
          fun t _ => hpt t
    _ = #M * ∑ m ∈ M, ∫ t in t₁..t₂, ‖J m t‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
          fun m hm => (hc' m hm).intervalIntegrable _ _]

end

end Erdos408.TwoSided
