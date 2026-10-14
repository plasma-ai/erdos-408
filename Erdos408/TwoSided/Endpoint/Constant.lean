import Erdos408.TwoSided.Endpoint.Constant.Bounds
import Erdos408.TwoSided.Endpoint.Constant.Growth
import Erdos408.TwoSided.Endpoint.Tuple

/-!
# The constant part at high times

S19 of `blueprint/two_sided_correlation.md` §6.6 (E10), in place of PD (6.40)–(6.42). The
constant residual `N(t') = R⁻¹ ∑_{n ≡ β} c'(n) n^{it'}` has scale `R ≍ Y/P > x`, so its
progression sums at scales `R/d > x` are beyond the premise `IntegerKernelBound`; the
unconditional `IntegerKernel.norm_sum_filter_modEq_le` has no upper scale bound and covers
them.

* `eventually_norm_modelProgression_le`: the model part `N₀` of the constant residual is
  `≤ L^{C₈} (12/|t'| + x^{-1/150})` pointwise.
* `exists_integral_const_high_le`: the part of the mean square (6.24) of `𝒰_con` over
  `L^{B'} ≤ |t| ≤ T₀` is `O(L^{-A₀})` for `B' ≥ B_con`, unconditionally.

The proof lives in `Constant/`: E10.2 on intervals (`Kernel`), the boxes of E6 with an
elementary separation along a geometric grid in place of the Mellin cutoff (`Boxes`), one box
(`Piece`, `High`), the size facts U6 (`Bounds`), elementary facts (`Glue`) and the exponents
(`Growth`); U7 and U9 are in `Setup.lean`.
-/

namespace Erdos408.TwoSided

open Filter

/-- **E10.2 (pointwise model bound).** For `C_m, C₈`, eventually: for a model `A`
supported on `d ≤ exp(2L^{0.47})` coprime to `k` with `∑ |A_d|/d ≤ L^{C₈}`, a scale
`R ∈ [x^{0.99}, x²]`, a class `β` mod `k ≤ L^{C_m}` and `1 ≤ |t| ≤ x³`,
`|R⁻¹ ∑_{n ∈ (⌊R⌋, ⌊2R⌋], n ≡ β} (∑_{d ∣ n} A_d) n^{it}| ≤ L^{C₈} (12/|t| + x^{-1/150})`.
This is `ConstHigh.eventually_norm_modelProgression_Ioc_le` on `(⌊R⌋, ⌊2R⌋]`. -/
theorem eventually_norm_modelProgression_le (Cm C₈ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (A : ℕ → ℂ) (R : ℝ) (k β : ℕ) (t : ℝ),
      (∀ d, A d ≠ 0 →
        1 ≤ d ∧ (d : ℝ) ≤ Real.exp (2 * Real.log x ^ (0.47 : ℝ)) ∧ Nat.Coprime d k) →
      ∑ d ∈ Finset.Icc 1 ⌊Real.exp (2 * Real.log x ^ (0.47 : ℝ))⌋₊, ‖A d‖ / d ≤
        Real.log x ^ C₈ →
      x ^ (99 / 100 : ℝ) ≤ R → R ≤ x ^ 2 → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
      1 ≤ |t| → |t| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A d) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |t| + x ^ (-(1 / 150 : ℝ))) := by
  filter_upwards [ConstHigh.eventually_norm_modelProgression_Ioc_le Cm C₈,
    eventually_gt_atTop 0] with x hx hx0
  intro A R k β t hA hmass hR₁ _ hk hkl ht₁ ht₂
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR₁
  exact hx A R k β ⌊R⌋₊ ⌊2 * R⌋₊ t hA hmass hR₁ (Nat.lt_floor_add_one R).le
    (Nat.floor_le (by positivity)) hk hkl ht₁ ht₂

namespace ConstHigh

open scoped Classical in
/-- **S19 on one side, for fixed `x`.** The inputs of `exists_integral_const_high_le` at a fixed
`x` (the growth facts, E10.2, U6, U7, U9, S16 and a divisor model of the marks), for an interval
`[t₁, t₂]` of times `L^{B'} ≤ |t| ≤ T₀`: the mean square of `𝒰_con` is at most
`256 (8 M₁(0)² c₁ + 2 c₂) L^{-A₀}`. -/
theorem integral_constCoeff_side_le {q q₀ c₀ C₀ vlo vhi alo ahi : ℝ} {K₀ : ℕ} {CN c : ℝ}
    {d : ℕ} (halo : 1 / 10 < alo) {Cm A₀ C₈ CW CNN KJ B' D As G : ℝ} {N : ℕ}
    {M₁ : ℕ → ℝ} (hD : 1 ≤ D) (hB'1 : 1 ≤ B') (hB'Cm : Cm + 1 ≤ B')
    (eA : -(2 * As) + 3 - D + 2 * CW ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm))
    (eB : -(2 * D) + 2 * C₈ - B' ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm))
    (eC : -(2 * D) + 2 * C₈ - G ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm))
    (eE : -(2 * D) + 1 - N ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm))
    (eF : -(5 * D) + 2 * ((d : ℝ) + 3) + 2 * (CW + 1) + 1 ≤ -(A₀ + 4 + 4 * D)) {x : ℝ}
    (hsc : 2 ≤ x ∧ 4 ≤ Real.log x ∧ x ^ (-(1 / 100 : ℝ)) ≤ Real.log x ^ (-G) ∧
      Real.exp (KJ * (Real.log x ^ (0.36 : ℝ) + Real.log x ^ (0.73 : ℝ) *
        Real.log (Real.log x))) * x ^ (-(1 / 150 : ℝ)) ≤ Real.log x ^ (-G) ∧
      Real.log x ^ (Cm + 2) * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤
        Real.exp (Real.log x ^ (0.38 : ℝ)) ∧
      16 * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ x ∧
      2 * Real.log x ^ D ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) ∧
      4 * Real.log x ^ D ≤ x ∧ Real.log x ^ B' ≤ x * Real.log x ^ (Cm + 2))
    (hE10 : ∀ (A : ℕ → ℂ) (R : ℝ) (k β lo hi : ℕ) (t : ℝ),
      (∀ d, A d ≠ 0 →
        1 ≤ d ∧ (d : ℝ) ≤ Real.exp (2 * Real.log x ^ (0.47 : ℝ)) ∧ Nat.Coprime d k) →
      ∑ d ∈ Finset.Icc 1 ⌊Real.exp (2 * Real.log x ^ (0.47 : ℝ))⌋₊, ‖A d‖ / d ≤
        Real.log x ^ C₈ →
      x ^ (99 / 100 : ℝ) ≤ R → R ≤ lo + 1 → (hi : ℝ) ≤ 2 * R → 1 ≤ k →
      (k : ℝ) ≤ Real.log x ^ Cm → 1 ≤ |t| → |t| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc lo hi).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A d) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |t| + x ^ (-(1 / 150 : ℝ))))
    (h𝒲 : ∀ (r : ℕ) (a : Fin r → ℝ), InertAdmissible K₀ CN alo ahi x a →
      ∀ n, 0 ≤ markedWeight Finset.univ q (fun i => band x (a i)) n ∧
        markedWeight Finset.univ q (fun i => band x (a i)) n ≤ Real.log x)
    (hκ : ∀ (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
      AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) → ∀ V : ℝ, vlo ≤ V →
        |slotMean x u v Bc / V| ≤ Real.log x ^ ((d + 3 : ℕ) : ℝ))
    (hcop : ∀ d k : ℕ, d ≠ 0 → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
      (∀ p ∈ d.primeFactors, Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤ p) → Nat.Coprime d k)
    (hS16 : ∀ (Y P Tmax : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
        x ^ (1 / 2 : ℝ) ≤ Y → Y ≤ x ^ 2 → 0 ≤ Tmax → Tmax ≤ Y →
        Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P → P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
        (∀ p ∈ s, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) → (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
        (((Finset.Icc (-⌈Tmax⌉ - 1) ⌈Tmax⌉).filter fun j : ℤ =>
            ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ Tmax ∧
              Real.log x ^ (-As) <
                ‖(P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖).card : ℝ) ≤
          Real.exp (KJ * (Real.log x ^ (0.36 : ℝ) +
            Real.log x ^ (0.73 : ℝ) * Real.log (Real.log x))))
    {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ} {big : Finset ι}
    (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big) {gs : ι} (hgs : gs ∉ big) {r : ℕ}
    {a : Fin r → ℝ} {u v : Fin (d + 1) → ℝ} {Bc : (Fin d → ℕ) → ℝ}
    (hin : InertAdmissible K₀ CN alo ahi x a) (hsl : AdmissibleSlots c x u v)
    (hBc : ∀ Q, |Bc Q| ≤ 1) {J : ℕ} {C : ι → Finset (Fin J)} {b : (ι → Fin (J + 1) → ℕ) → ℂ}
    (hW : ∀ n, ‖markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b n‖ ≤
      Real.log x ^ CW)
    {ψ₁ : ℝ → ℂ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁)
    (hψs : ∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (hψd : ∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j)
    {Y σ : ℝ} {k : ℕ} {h : ℤ} (hY₁ : x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y)
    (hY₂ : Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ))) (hσ : |σ| ≤ Real.log x ^ Cm)
    (hk₁ : 1 ≤ k) (hk₂ : (k : ℝ) ≤ Real.log x ^ Cm) {A : ℕ → ℂ}
    (hA : DivisorModel x q q₀ a P (Function.update (unsharedSlots C) gs ∅) b C₈ CNN N A)
    {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hint : ∀ t ∈ Set.Icc t₁ t₂, Real.log x ^ B' ≤ |t| ∧ |t| ≤ x * Real.log x ^ (Cm + 2))
    (hlen : t₂ - t₁ ≤ x * Real.log x ^ (Cm + 2)) :
    ∫ t in t₁..t₂, ‖twistedPoly Y (constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t‖ ^ 2 ≤
      256 * (8 * M₁ 0 ^ 2 * (195 + 18 * (2304 + 629 + 65 * CNN)) +
        2 * (3888 * 258 * M₁ 1 ^ 2)) * Real.log x ^ (-A₀) := by
  obtain ⟨hx2, hL4, hxC, hxD, h38, h47, h27, h4D, -⟩ := hsc
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hcc : constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ = fun w : ℕ =>
      ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) *
        ((slotMean x u v Bc / harmonicMass (P gs) : ℝ) : ℂ) * ∑ p ∈ (P gs).filter (· ∣ w),
          (fun n => (markedWeight Finset.univ q (fun i => band x (a i)) n : ℂ) *
            markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b n) (w / p) := rfl
  rw [hcc]
  obtain ⟨hYx, hYx3, hxh, hYsq, hT₀E, hT₀0, hT₀Y, h2Y⟩ :=
    ConstHigh.time_scales (Cm := Cm) hx2 hL1 h38 h47 hY₁ hY₂
  obtain ⟨hδ0, hδ, hδx, hδx'⟩ := ConstHigh.grid_scales hL4 hD h27 h4D
  have hκ' : ‖((slotMean x u v Bc / harmonicMass (P gs) : ℝ) : ℂ)‖ ≤
      Real.log x ^ ((d : ℝ) + 3) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := hκ u v Bc hsl hBc _ (hadm.2.2.2.2.2.1 gs).1
    push_cast at this
    exact this
  have hH : ∀ n, ‖(markedWeight Finset.univ q (fun i => band x (a i)) n : ℂ) *
      markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b n‖ ≤
        Real.log x ^ (CW + 1) := by
    intro n
    obtain ⟨h0, h1⟩ := h𝒲 r a hin n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, Real.rpow_add hL0, Real.rpow_one,
      mul_comm (Real.log x ^ CW)]
    exact mul_le_mul h1 (hW n) (norm_nonneg _) hL0.le
  have hsupp : ∀ d, A d ≠ 0 →
      1 ≤ d ∧ (d : ℝ) ≤ Real.exp (2 * Real.log x ^ (0.47 : ℝ)) ∧ Nat.Coprime d k := by
    intro d hd
    obtain ⟨hsq, hdE, hpr⟩ := hA.1 d hd
    exact ⟨Nat.pos_of_ne_zero hsq.ne_zero, hdE, hcop d k hsq.ne_zero hk₁ hk₂ fun p hp =>
      ConstHigh.exp_le_of_mem_active_or_band hadm hin halo.le hL1 (hpr p hp)⟩
  have hCNN : 0 ≤ CNN := by
    have h1 := hA.2.2 1 le_rfl
    have h2 := (Finset.sum_nonneg fun _ _ => sq_nonneg _).trans h1
    rw [mul_one] at h2
    exact nonneg_of_mul_nonneg_left h2 (Real.rpow_pos_of_pos hL0 _)
  have hcB : 4 ≤ Real.log x ^ B' := by
    calc (4 : ℝ) ≤ Real.log x := hL4
      _ = Real.log x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log x ^ B' := Real.rpow_le_rpow_of_exponent_le hL1 hB'1
  have hσB : |σ| ≤ Real.log x ^ B' / 2 := by
    have h1 : Real.log x ^ (Cm + 1) ≤ Real.log x ^ B' :=
      Real.rpow_le_rpow_of_exponent_le hL1 hB'Cm
    rw [Real.rpow_add hL0, Real.rpow_one] at h1
    have h2 : 0 ≤ Real.log x ^ Cm := Real.rpow_nonneg hL0.le _
    have h3 := mul_le_mul_of_nonneg_left hL4 h2
    linarith
  exact ConstHigh.integral_twistedPoly_const_le_rpow (x := x) (Y := Y) (σ := σ)
    (T₀ := x * Real.log x ^ (Cm + 2)) (C₈ := C₈) (CNN := CNN) (Nexp := (N : ℝ)) (D := D)
    (As := As) (B' := B') (G := G) (CW := CW) (d' := (d : ℝ) + 3) (Cm := Cm) (A₀ := A₀)
    (M₀ := M₁ 0) (M₁ := M₁ 1) (h := h) (k := k) (Ps := P gs) (A₀' := A) (ψ := ψ₁)
    (κ := ((slotMean x u v Bc / harmonicMass (P gs) : ℝ) : ℂ))
    (H := fun n => (markedWeight Finset.univ q (fun i => band x (a i)) n : ℂ) *
      markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b n) h12 (by linarith)
    hint hlen hσB hx2 hL1 hδ0
    hδ (by linarith) hψs hψ (fun y => by simpa using hψd 0 y) (hψd 1) hκ'
    (ConstHigh.mem_smallGroup_bounds hadm hgs) hk₁ hk₂ hH hYx hYx3 hT₀E hδx hδx'
    (fun R β lo hi t h1 h2 h3 h4 h5 => hE10 A R k β lo hi t hsupp hA.2.1 h1 h2 h3 hk₁ hk₂ h4 h5)
    hA.2.2 (fun s cs N cq _ _ _ hab => TupleHigh.setIntegral_ordinary_le s cs N cq hab)
    (Real.exp_pos _).le
    (fun Pr s coeff h1 h2 h3 h4 => hS16 Y Pr _ s coeff hxh hYsq hT₀0 hT₀Y h1 h2 h3 h4)
    h2Y hCNN hxC hxD eA eB eC eE eF

end ConstHigh

/-- **The constant part at high times (S13–S16, S19).** There is `B_con` such that for every
`B' ≥ B_con` there is `C_K` with: eventually, for all data as in package E and a small group
`g_s`, the mean square of `𝒰_con` over `L^{B'} ≤ t ≤ T₀` and over `-T₀ ≤ t ≤ -L^{B'}` is at
most `C_K L^{-A₀}`. Split `p_s` and `n = w/p_s` along the geometric grid of step
`δ = L^{-D}` and fix the class of `n` mod `k`. In each box, E7 bounds the ordinary times
`|A_β| ≤ L^{-A_s}`; elsewhere the marks are replaced by their divisor model (E1), whose error
is bounded in mean square (E10.1) and whose main part pointwise (E10.2), integrated as `t^{-2}`
on the medium range `|t| ≤ x^{1/300}` and over the exceptional intervals of S16 beyond. The
corner error of the grid is `O(δ)` per box, and `|C_B/V| ≤ L^{d+3}` (U6) is absorbed. -/
theorem exists_integral_const_high_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ)
    (d : ℕ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo)
    (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c) (m₀ : ℕ)
    (Cm A₀ : ℝ) (M₁ : ℕ → ℝ) :
    ∃ Bcon : ℝ, ∀ B' : ℝ, Bcon ≤ B' → ∃ CK : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big → ∀ gs ∉ big,
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
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
              ‖twistedPoly Y (constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t‖ ^ 2 ≤
            CK * Real.log x ^ (-A₀)) ∧
          ∫ t in -(x * Real.log x ^ (Cm + 2))..-(Real.log x ^ B'),
              ‖twistedPoly Y (constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ) h k t‖ ^ 2 ≤
            CK * Real.log x ^ (-A₀) := by
  obtain ⟨C₈, hE1⟩ := exists_divisorModel q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN hq hq₁ hq₀ hq₀₁ hvlo
    halo hahi m₀
  obtain ⟨CW, hU9⟩ := exists_norm_markedListWeight_le_rpow q₀ c₀ C₀ vlo vhi hq₀ hq₀₁ hvlo
    m₀
  -- the exponents: `δ = L^{-D}`, `θ = L^{-A_s}`, the saving `L^{-G}` and the model precision
  set D : ℝ := |A₀| + 2 * ((d : ℝ) + 3) + 2 * |CW| + 10 with hD
  set Z : ℝ := A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm with hZ
  set As : ℝ := |Z| + 2 * |CW| + 4 with hAs
  set G : ℝ := |Z| + 2 * |C₈| with hG
  set N : ℕ := ⌈|Z| + 1⌉₊ with hN
  obtain ⟨CNN, hE1N⟩ := hE1 N
  obtain ⟨KJ, hKJ, hS16⟩ := TupleHigh.exists_card_exceptional_le As (by positivity)
  refine ⟨|Z| + 2 * |C₈| + |Cm| + 2, fun B' hB' => ⟨256 * (8 * M₁ 0 ^ 2 *
    (195 + 18 * (2304 + 629 + 65 * CNN)) + 2 * (3888 * 258 * M₁ 1 ^ 2)), ?_⟩⟩
  have hZa := le_abs_self Z
  have hZb := neg_abs_le Z
  have hCW := le_abs_self CW
  have hC8 := le_abs_self C₈
  have hCm := le_abs_self Cm
  have hA0 := le_abs_self A₀
  have hD0 : 0 ≤ D := by positivity
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hD1 : 1 ≤ D := by linarith [abs_nonneg A₀, abs_nonneg CW]
  have hNZ : |Z| + 1 ≤ N := Nat.le_ceil _
  have eA : -(2 * As) + 3 - D + 2 * CW ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm) := by
    rw [← hZ]
    linarith [abs_nonneg CW]
  have eB : -(2 * D) + 2 * C₈ - B' ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm) := by
    rw [← hZ]
    linarith [abs_nonneg Cm]
  have eC : -(2 * D) + 2 * C₈ - G ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm) := by
    rw [← hZ]
    linarith
  have eE : -(2 * D) + 1 - N ≤ -(A₀ + 4 + 4 * D + 2 * ((d : ℝ) + 3) + 2 * Cm) := by
    rw [← hZ]
    linarith
  have eF : -(5 * D) + 2 * ((d : ℝ) + 3) + 2 * (CW + 1) + 1 ≤ -(A₀ + 4 + 4 * D) := by
    rw [hD]
    linarith [abs_nonneg A₀, abs_nonneg CW]
  have hB'1 : 1 ≤ B' := by linarith [abs_nonneg Z, abs_nonneg C₈, abs_nonneg Cm]
  have hB'Cm : Cm + 1 ≤ B' := by linarith [abs_nonneg Z, abs_nonneg C₈]
  filter_upwards [hE1N, hU9, hS16, ConstHigh.eventually_norm_modelProgression_Ioc_le Cm C₈,
    eventually_markedWeight_band_le q alo ahi K₀ CN hq hq₁ halo,
    ConstHigh.eventually_abs_slotMean_div_le c vlo d hc hvlo, ConstHigh.eventually_coprime Cm,
    ConstHigh.eventually_constScales Cm D G KJ B' hKJ.le]
    with x hE1x hU9x hS16x hE10x h𝒲x hκx hcopx hsc
  intro ι _ _ P big hadm gs hgs r a u v Bc hin hsl hBc J C b hC _ hb _ ψ₁ hψ hψs hψd Y σ k h
    hY₁ hY₂ hσ hk₁ hk₂
  have hS' : ∀ g, (Function.update (unsharedSlots C) gs ∅ g).card ≤ m₀ + 1 := by
    intro g
    by_cases hg : g = gs
    · subst hg
      simp
    · rw [Function.update_of_ne hg]
      rw [card_unsharedSlots]
      exact Nat.add_le_add_right (hC g) 1
  obtain ⟨A, hA⟩ := hE1x P big hadm r a hin (J + 1) _ b hS' hb
  have hW := hU9x P big hadm (J + 1) _ b hS' hb
  have hBT : Real.log x ^ B' ≤ x * Real.log x ^ (Cm + 2) := hsc.2.2.2.2.2.2.2.2
  have hLB : 0 ≤ Real.log x ^ B' := Real.rpow_nonneg (by linarith [hsc.2.1]) _
  constructor
  · refine ConstHigh.integral_constCoeff_side_le halo hD1 hB'1 hB'Cm eA eB eC eE eF hsc hE10x
      h𝒲x hκx hcopx hS16x hadm hgs hin hsl hBc hW hψ hψs hψd hY₁ hY₂ hσ hk₁ hk₂ hA hBT
      (fun t ht => ?_) (by linarith)
    have h0 : 0 ≤ t := hLB.trans ht.1
    rw [abs_of_nonneg h0]
    exact ⟨ht.1, ht.2⟩
  · refine ConstHigh.integral_constCoeff_side_le halo hD1 hB'1 hB'Cm eA eB eC eE eF hsc hE10x
      h𝒲x hκx hcopx hS16x hadm hgs hin hsl hBc hW hψ hψs hψd hY₁ hY₂ hσ hk₁ hk₂ hA
      (by linarith) (fun t ht => ?_) (by linarith)
    have h0 : t ≤ 0 := ht.2.trans (by linarith)
    rw [abs_of_nonpos h0]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

end Erdos408.TwoSided
