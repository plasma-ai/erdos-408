import Erdos408.TwoSided.Endpoint.Constant.Boxes
import Erdos408.TwoSided.Endpoint.Constant.Piece

/-!
# The constant part at high times, for fixed `x`

The estimate of S19 (`blueprint/two_sided_correlation.md` §6.6, E10) at a fixed large `x`, with
its inputs at this `x` as hypotheses: the ordinary-time bound E7, the exceptional-set count S16,
the model bound E10.2 and the divisor model E1 of the marks `H`.

* `integral_boxSmall_mul_le`: one class `β` of a box with corner `r ∈ [Y, 2Y]`: E7 on the
  ordinary times, and on the others the model part pointwise (E10.2) and the model error in
  mean square (E10.1).
* `integral_boxSum_le`: one box, including the corner error of the separation.
* `integral_twistedPoly_const_le`: the sum over the `I²` boxes.
-/

namespace Erdos408.TwoSided.ConstHigh

open Finset MeasureTheory

/-- The bound of one class of a box, `integral_boxSmall_mul_le`. -/
noncomputable def classBound (x δ θ c C₈ CNN Nexp JB Hc : ℝ) : ℝ :=
  θ ^ 2 * ((17 + 48 * Real.log x) * (3 * δ * Hc ^ 2)) + 2 * (3 * δ) ^ 2 *
    ((Real.log x ^ C₈) ^ 2 * (2304 / c + 4 * (x ^ (-(1 / 150 : ℝ))) ^ 2 * x ^ (1 / 300 : ℝ)) +
      JB * (Real.log x ^ C₈ * (24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ)))) ^ 2 +
      (17 + 48 * Real.log x) * (CNN * Real.log x ^ (-Nexp)))

/-- The bound of the corner error of a box, `integral_boxErr_le_of_corner`. -/
noncomputable def errBound (x δ Kc M Hc : ℝ) : ℝ :=
  3888 * δ ^ 5 * Kc ^ 2 * M ^ 2 * Hc ^ 2 * (66 + 192 * Real.log x)

/-- The bound of one box, `integral_boxSum_le`. -/
noncomputable def boxBound (x δ θ c C₈ CNN Nexp JB Hc Kc M₀ M₁ : ℝ) (k : ℕ) : ℝ :=
  2 * ((2 * Kc * M₀) ^ 2 * (k * (k * classBound x δ θ c C₈ CNN Nexp JB Hc))) +
    2 * errBound x δ Kc M₁ Hc

/-- The class bound is nonnegative. -/
theorem classBound_nonneg {x δ θ c C₈ CNN Nexp JB Hc : ℝ} (hx : 1 ≤ x) (hδ : 0 ≤ δ)
    (hc : 0 < c) (hCNN : 0 ≤ CNN) (hJB : 0 ≤ JB) :
    0 ≤ classBound x δ θ c C₈ CNN Nexp JB Hc := by
  have hL := Real.log_nonneg hx
  have h1 : 0 ≤ 17 + 48 * Real.log x := by linarith
  have h2 : 0 ≤ CNN * Real.log x ^ (-Nexp) := mul_nonneg hCNN (Real.rpow_nonneg hL _)
  have h3 : 0 ≤ JB * (Real.log x ^ C₈ * (24 / x ^ (1 / 300 : ℝ) + x ^ (-(1 / 150 : ℝ)))) ^ 2 :=
    mul_nonneg hJB (sq_nonneg _)
  have h4 : 0 ≤ (Real.log x ^ C₈) ^ 2 * (2304 / c + 4 * (x ^ (-(1 / 150 : ℝ))) ^ 2 *
      x ^ (1 / 300 : ℝ)) := by
    have : 0 ≤ x ^ (1 / 300 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity
  have h5 : 0 ≤ θ ^ 2 * ((17 + 48 * Real.log x) * (3 * δ * Hc ^ 2)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg h1 (by positivity))
  have h6 : 0 ≤ (17 + 48 * Real.log x) * (CNN * Real.log x ^ (-Nexp)) := mul_nonneg h1 h2
  rw [classBound]
  have : 0 ≤ 2 * (3 * δ) ^ 2 := by positivity
  have := mul_nonneg this (add_nonneg (add_nonneg h4 h3) h6)
  linarith

/-- The corner-error bound is nonnegative. -/
theorem errBound_nonneg {x δ Kc M Hc : ℝ} (hx : 1 ≤ x) (hδ : 0 ≤ δ) :
    0 ≤ errBound x δ Kc M Hc := by
  have hL := Real.log_nonneg hx
  rw [errBound]
  have h1 : 0 ≤ 66 + 192 * Real.log x := by linarith
  have h2 : 0 ≤ 3888 * δ ^ 5 * Kc ^ 2 * M ^ 2 * Hc ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hδ 5))
      (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)
  exact mul_nonneg h2 h1

section Fixed

variable {x Y σ δ θ T₀ c a b C₈ CNN Nexp JB Hc : ℝ} {h : ℤ} {k : ℕ} {Ps : Finset ℕ}
  {H A₀ : ℕ → ℂ}

/-- The primes of a nonempty box `j` lie in `(e^{jδ}, 2e^{jδ}]`, so
`e^{L^{0.27}}/2 ≤ e^{jδ} ≤ e^{L^{0.36}}`. -/
theorem boxPrimes_scale (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    {j : ℕ} (hs : (boxPrimes δ Ps j).Nonempty) :
    Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ Real.exp (j * δ) ∧
      Real.exp (j * δ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) := by
  obtain ⟨p₀, hp₀⟩ := hs
  obtain ⟨hp₀j, hp₀P⟩ := mem_filter.1 hp₀
  obtain ⟨-, hp₀lo, hp₀hi⟩ := hPs p₀ hp₀P
  obtain ⟨hp₁, hp₂⟩ := mem_gridPiece hp₀j
  rw [exp_succ_mul] at hp₂
  have heδ : Real.exp δ ≤ 2 := by linarith [exp_sub_one_le_two_mul hδ0 (by linarith)]
  have : (p₀ : ℝ) ≤ 2 * Real.exp (j * δ) :=
    hp₂.trans (mul_le_mul_of_nonneg_right heδ (Real.exp_pos _).le)
  constructor <;> linarith

/-- A nonempty box `j` has at most `3δ e^{jδ}` primes. -/
theorem card_boxPrimes_le (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hδx : 1 ≤ δ * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2))
    {j : ℕ} (hs : (boxPrimes δ Ps j).Nonempty) :
    ((boxPrimes δ Ps j).card : ℝ) ≤ 3 * δ * Real.exp (j * δ) := by
  refine (show ((boxPrimes δ Ps j).card : ℝ) ≤ (gridPiece δ j).card by
    exact_mod_cast card_filter_le _ _).trans (card_gridPiece_le hδ0 hδ ?_)
  exact hδx.trans (mul_le_mul_of_nonneg_left (boxPrimes_scale hδ0 hδ hPs hs).1 hδ0)

/-- On a nonempty box the small-prime polynomial is at most `3δ`. -/
theorem norm_boxSmall_le_three (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hδx : 1 ≤ δ * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2))
    {j : ℕ} (hs : (boxPrimes δ Ps j).Nonempty) (β : ℕ) (t : ℝ) :
    ‖boxSmall σ δ h k Ps j β t‖ ≤ 3 * δ := by
  refine (norm_boxSmall_le j β t).trans ?_
  have h1 := card_boxPrimes_le hδ0 hδ hPs hδx hs
  have h2 : 0 < Real.exp (j * δ) := Real.exp_pos _
  calc ((boxPrimes δ Ps j).card : ℝ) * (Real.exp (j * δ))⁻¹
      ≤ 3 * δ * Real.exp (j * δ) * (Real.exp (j * δ))⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 h2.le)
    _ = 3 * δ := by field_simp

/-- The length factor of the mean value theorem at the residual scale `e^{iδ} ≥ T₀`:
`b - a + 8N(1 + log N) ≤ e^{iδ} (17 + 48L)` for `N = ⌊e^{(i+1)δ}⌋`, `2e^{iδ} ≤ x³`. -/
theorem length_factor_le (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hba : b - a ≤ T₀) {i : ℕ}
    (hT : T₀ ≤ Real.exp (i * δ))
    (hix : 2 * Real.exp (i * δ) ≤ x ^ 3) :
    b - a + 8 * grid δ (i + 1) * (1 + Real.log (grid δ (i + 1))) ≤
      Real.exp (i * δ) * (17 + 48 * Real.log x) := by
  have hN2 : (grid δ (i + 1) : ℝ) ≤ 2 * Real.exp (i * δ) := grid_succ_le hδ0 hδ i
  have hN1 : (1 : ℝ) ≤ grid δ (i + 1) := by exact_mod_cast one_le_grid hδ0 (i + 1)
  have hlogN : Real.log (grid δ (i + 1)) ≤ 3 * Real.log x := by
    calc Real.log (grid δ (i + 1)) ≤ Real.log (x ^ 3) :=
          Real.log_le_log (by linarith) (hN2.trans hix)
      _ = 3 * Real.log x := by rw [Real.log_pow]; push_cast; ring
  have hlog0 := Real.log_nonneg hN1
  have h1 : 8 * (grid δ (i + 1) : ℝ) * (1 + Real.log (grid δ (i + 1))) ≤
      8 * (2 * Real.exp (i * δ)) * (1 + 3 * Real.log x) := by
    gcongr
  have h2 : 8 * (2 * Real.exp (i * δ)) * (1 + 3 * Real.log x) + Real.exp (i * δ) =
      Real.exp (i * δ) * (17 + 48 * Real.log x) := by ring
  linarith

/-- **E10.2 in a box.** The model part of the residual,
`|e^{-iδ} ∑_{n ≡ β} (∑_{d ∣ n} A_d) n^{iσ} n^{it}| ≤ L^{C₈} (24/|t| + x^{-1/150})`, at times
`c ≤ |t| ≤ T₀` with `|σ| ≤ c/2`, `c ≥ 2` and `2T₀ ≤ x³`. -/
theorem norm_boxResidual_model_le
    (hE10 : ∀ (R : ℝ) (β lo hi : ℕ) (u : ℝ), x ^ (99 / 100 : ℝ) ≤ R → R ≤ lo + 1 →
      (hi : ℝ) ≤ 2 * R → 1 ≤ |u| → |u| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc lo hi).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A₀ d) * (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |u| + x ^ (-(1 / 150 : ℝ))))
    (hx : 1 ≤ x) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hc : 2 ≤ c) (hσ : |σ| ≤ c / 2)
    (hT₀ : 2 * T₀ ≤ x ^ 3) {i : ℕ} (hi : x ^ (99 / 100 : ℝ) ≤ Real.exp (i * δ)) (β : ℕ) {t : ℝ}
    (ht : c ≤ |t|)
    (ht' : |t| ≤ T₀) :
    ‖boxResidual σ δ k (fun n => ∑ d ∈ n.divisors, A₀ d) i β t‖ ≤
      Real.log x ^ C₈ * (24 / |t| + x ^ (-(1 / 150 : ℝ))) := by
  have hrepr : boxResidual σ δ k (fun n => ∑ d ∈ n.divisors, A₀ d) i β t =
      ((Real.exp (i * δ) : ℝ) : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc (grid δ i) (grid δ (i + 1))).filter
        (· ≡ β [MOD k]), (∑ d ∈ n.divisors, A₀ d) *
          (n : ℂ) ^ (((t + σ : ℝ) : ℂ) * Complex.I) := by
    rw [boxResidual, mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast gridPiece_pos (mem_filter.1 hn).1
    rw [show ((t + σ : ℝ) : ℂ) * Complex.I = (σ : ℂ) * Complex.I + (t : ℂ) * Complex.I by
      push_cast; ring, Complex.cpow_add _ _ hn0, Complex.ofReal_inv]
    ring
  have hσt : |σ| ≤ |t| / 2 := by linarith
  have hts : |t| / 2 ≤ |t + σ| := by
    have := abs_add_le (t + σ) (-σ)
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  have hts1 : 1 ≤ |t + σ| := by linarith
  have hts2 : |t + σ| ≤ x ^ 3 := by
    have := abs_add_le t σ
    linarith [abs_nonneg t]
  rw [hrepr]
  refine (hE10 (Real.exp (i * δ)) β (grid δ i) (grid δ (i + 1)) (t + σ) hi
    (Nat.lt_floor_add_one _).le (grid_succ_le hδ0 hδ i) hts1 hts2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Real.log_nonneg hx) _)
  gcongr ?_ + _
  have ht0 : 0 < |t| := by linarith
  rw [div_le_div_iff₀ (by linarith) ht0]
  linarith

open scoped Classical in
/-- The exceptional times of a box lie in the unit intervals counted by S16. -/
theorem exists_mem_exceptional {θ' : ℝ} (A : ℝ → ℂ) {P : ℝ} {s : Finset ℕ} {coeff : ℕ → ℂ}
    (hA : ∀ t, A t = (P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I))
    (hint : ∀ t ∈ Set.Icc a b, |t| ≤ T₀) :
    ∀ t ∈ Set.Ioc a b, θ' < ‖A t‖ → ∃ j ∈ (Finset.Icc (-⌈T₀⌉ - 1) ⌈T₀⌉).filter fun j : ℤ =>
      ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ T₀ ∧
        θ' < ‖(P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖,
      (j : ℝ) ≤ t ∧ t ≤ j + 1 := by
  intro t ht hθ
  have htT := hint t (Set.Ioc_subset_Icc_self ht)
  have hfl := Int.floor_le t
  have hfl' := Int.lt_floor_add_one t
  refine ⟨⌊t⌋, mem_filter.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, t, hfl, hfl'.le, htT, by rwa [← hA]⟩,
    hfl, hfl'.le⟩
  · have h1 : -(T₀ : ℝ) ≤ t := by linarith [neg_abs_le t]
    have h2 : (-⌈T₀⌉ - 1 : ℤ) ≤ ⌊t⌋ := by
      have : ((-⌈T₀⌉ - 1 : ℤ) : ℝ) < ⌊t⌋ + 1 := by
        push_cast
        linarith [Int.le_ceil T₀]
      exact_mod_cast (show ((-⌈T₀⌉ - 1 : ℤ) : ℝ) ≤ ⌊t⌋ by
        have h3 : (-⌈T₀⌉ - 1 : ℤ) < ⌊t⌋ + 1 := by exact_mod_cast this
        exact_mod_cast Int.lt_add_one_iff.1 h3)
    exact h2
  · have : (⌊t⌋ : ℝ) ≤ ⌈T₀⌉ := by linarith [le_abs_self t, Int.le_ceil T₀]
    exact_mod_cast this

/-- **E7 in a box.** The ordinary times of one class:
`∫_{|A_β| ≤ θ} |A_β B_β|² ≤ θ² (17 + 48L) 3δ H_max²`. -/
theorem setIntegral_boxOrdinary_le
    (hOrd : ∀ (s : Finset ℕ) (cs : ℕ → ℂ) (N : ℕ) (cq : ℕ → ℂ) {a b θ : ℝ}, a ≤ b →
      ∫ t in {t ∈ Set.Ioc a b | ‖∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ θ},
          ‖(∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) *
            ∑ n ∈ Finset.Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
        θ ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖cq n‖ ^ 2))
    (hab : a ≤ b) (hH : ∀ n, ‖H n‖ ≤ Hc) {j i β : ℕ}
    (hfac : b - a + 8 * grid δ (i + 1) * (1 + Real.log (grid δ (i + 1))) ≤
      Real.exp (i * δ) * (17 + 48 * Real.log x))
    (hfac0 : 0 ≤ b - a + 8 * grid δ (i + 1) * (1 + Real.log (grid δ (i + 1))))
    (hcS : (((gridPiece δ i).filter (· ≡ β [MOD k])).card : ℝ) ≤ 3 * δ * Real.exp (i * δ)) :
    ∫ t in {t ∈ Set.Ioc a b | ‖boxSmall σ δ h k Ps j β t‖ ≤ θ},
        ‖boxSmall σ δ h k Ps j β t * boxResidual σ δ k H i β t‖ ^ 2 ≤
      θ ^ 2 * ((17 + 48 * Real.log x) * (3 * δ * Hc ^ 2)) := by
  set S := (gridPiece δ i).filter (· ≡ β [MOD k]) with hS
  set N := grid δ (i + 1) with hN
  set ei := Real.exp (i * δ) with hei
  have hei0 : 0 < ei := Real.exp_pos _
  have hSN : S ⊆ Icc 1 N := (filter_subset _ _).trans (gridPiece_subset_Icc δ i)
  set c : ℕ → ℂ := fun n => ((ei⁻¹ : ℝ) : ℂ) * H n * (n : ℂ) ^ ((σ : ℂ) * Complex.I) with hc
  set cq : ℕ → ℂ := fun n => if n ∈ S then c n else 0 with hcq
  set cs : ℕ → ℂ := fun p => (((Real.exp (j * δ))⁻¹ : ℝ) : ℂ) * twist h k (p * β) *
    (p : ℂ) ^ ((σ : ℂ) * Complex.I) with hcs
  have hB : ∀ t, boxResidual σ δ k H i β t =
      ∑ n ∈ Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := fun t => by
    rw [boxResidual]
    exact sum_cpow_eq_sum_Icc_ite N S hSN c t
  have hA : ∀ t, boxSmall σ δ h k Ps j β t =
      ∑ p ∈ boxPrimes δ Ps j, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I) := fun t => rfl
  simp_rw [hA, hB]
  refine (hOrd (boxPrimes δ Ps j) cs N cq hab).trans ?_
  have hcn : ∑ n ∈ Icc 1 N, ‖cq n‖ ^ 2 ≤ S.card * (ei⁻¹ * Hc) ^ 2 := by
    rw [hcq, sum_norm_ite_sq N S hSN c]
    calc ∑ n ∈ S, ‖c n‖ ^ 2 ≤ ∑ n ∈ S, (ei⁻¹ * Hc) ^ 2 := by
          refine sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          rw [hc]
          simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hei0.le)]
          have h1 := IntegerKernel.norm_natCast_cpow_I_mul_le σ n
          have h2 : 0 ≤ ei⁻¹ := inv_nonneg.2 hei0.le
          calc ei⁻¹ * ‖H n‖ * ‖(n : ℂ) ^ ((σ : ℂ) * Complex.I)‖ ≤ ei⁻¹ * Hc * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hH n) h2) h1 (norm_nonneg _)
                  (mul_nonneg h2 ((norm_nonneg _).trans (hH n)))
            _ = ei⁻¹ * Hc := mul_one _
      _ = S.card * (ei⁻¹ * Hc) ^ 2 := by rw [sum_const, nsmul_eq_mul]
  have hθ : 0 ≤ θ ^ 2 := sq_nonneg θ
  refine mul_le_mul_of_nonneg_left ?_ hθ
  calc (b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Icc 1 N, ‖cq n‖ ^ 2
      ≤ (ei * (17 + 48 * Real.log x)) * (3 * δ * ei * (ei⁻¹ * Hc) ^ 2) := by
        refine mul_le_mul hfac (hcn.trans ?_) (sum_nonneg fun _ _ => sq_nonneg _)
          (le_trans hfac0 hfac)
        exact mul_le_mul_of_nonneg_right hcS (sq_nonneg _)
    _ = (17 + 48 * Real.log x) * (3 * δ * Hc ^ 2) := by
        field_simp

/-- **E10.1 in a box.** The model error of one class:
`∫_a^b |e^{-iδ} ∑_{n ≡ β} (H - ∑_{d ∣ n} A_d)(n) n^{iσ} n^{it}|² ≤ (17 + 48L) C_N L^{-N}`. -/
theorem integral_boxResidual_error_le
    (hmodel : ∀ R : ℝ, 1 ≤ R → ∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
      ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 ≤ CNN * R * Real.log x ^ (-Nexp))
    (hx : 1 < x) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) {i : ℕ}
    (hfac : b - a + 8 * grid δ (i + 1) * (1 + Real.log (grid δ (i + 1))) ≤
      Real.exp (i * δ) * (17 + 48 * Real.log x))
    (hfac0 : 0 ≤ b - a + 8 * grid δ (i + 1) * (1 + Real.log (grid δ (i + 1)))) (β : ℕ) :
    ∫ t in a..b, ‖boxResidual σ δ k (fun n => H n - ∑ d ∈ n.divisors, A₀ d) i β t‖ ^ 2 ≤
      (17 + 48 * Real.log x) * (CNN * Real.log x ^ (-Nexp)) := by
  set S := (gridPiece δ i).filter (· ≡ β [MOD k]) with hS
  set N := grid δ (i + 1) with hN
  set ei := Real.exp (i * δ) with hei
  have hei0 : 0 < ei := Real.exp_pos _
  have hei1 : 1 ≤ ei := Real.one_le_exp (by positivity)
  have hSN : S ⊆ Icc 1 N := (filter_subset _ _).trans (gridPiece_subset_Icc δ i)
  have hLN : 0 < Real.log x ^ (-Nexp) := Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hCNN : 0 ≤ CNN := by
    have h1 := hmodel 1 le_rfl
    have h0 : 0 ≤ ∑ n ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊2 * (1 : ℝ)⌋₊,
        ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have h2 := h0.trans h1
    rw [mul_one] at h2
    exact nonneg_of_mul_nonneg_left h2 hLN
  have hSsub : S ⊆ Finset.Ioc ⌊ei⌋₊ ⌊2 * ei⌋₊ := by
    intro n hn
    have hn' := (mem_filter.1 hn).1
    rw [gridPiece, mem_Ioc] at hn'
    refine mem_Ioc.2 ⟨hn'.1, hn'.2.trans (Nat.floor_mono ?_)⟩
    rw [exp_succ_mul]
    have := exp_sub_one_le_two_mul hδ0 (by linarith)
    exact mul_le_mul_of_nonneg_right (by linarith) hei0.le
  simp only [boxResidual]
  refine (integral_norm_sum_cpow_sq_le N S hSN _ a b).trans ?_
  have hsum : ∑ n ∈ S, ‖((ei⁻¹ : ℝ) : ℂ) * (H n - ∑ d ∈ n.divisors, A₀ d) *
      (n : ℂ) ^ ((σ : ℂ) * Complex.I)‖ ^ 2 ≤ ei⁻¹ ^ 2 * (CNN * ei * Real.log x ^ (-Nexp)) := by
    calc ∑ n ∈ S, ‖((ei⁻¹ : ℝ) : ℂ) * (H n - ∑ d ∈ n.divisors, A₀ d) *
          (n : ℂ) ^ ((σ : ℂ) * Complex.I)‖ ^ 2
        ≤ ∑ n ∈ S, ei⁻¹ ^ 2 * ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 := by
          refine sum_le_sum fun n _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hei0.le),
            mul_pow, mul_pow]
          have h1 := IntegerKernel.norm_natCast_cpow_I_mul_le σ n
          have h2 : ‖(n : ℂ) ^ ((σ : ℂ) * Complex.I)‖ ^ 2 ≤ 1 := by
            have := norm_nonneg ((n : ℂ) ^ ((σ : ℂ) * Complex.I))
            nlinarith
          have h3 : 0 ≤ ei⁻¹ ^ 2 * ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 := by positivity
          calc ei⁻¹ ^ 2 * ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 *
                ‖(n : ℂ) ^ ((σ : ℂ) * Complex.I)‖ ^ 2
              ≤ ei⁻¹ ^ 2 * ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left h2 h3
            _ = _ := mul_one _
      _ = ei⁻¹ ^ 2 * ∑ n ∈ S, ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 := by rw [mul_sum]
      _ ≤ ei⁻¹ ^ 2 * ∑ n ∈ Finset.Ioc ⌊ei⌋₊ ⌊2 * ei⌋₊, ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 := by
          gcongr
      _ ≤ ei⁻¹ ^ 2 * (CNN * ei * Real.log x ^ (-Nexp)) := by gcongr; exact hmodel ei hei1
  calc (b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ S, ‖((ei⁻¹ : ℝ) : ℂ) *
        (H n - ∑ d ∈ n.divisors, A₀ d) * (n : ℂ) ^ ((σ : ℂ) * Complex.I)‖ ^ 2
      ≤ (ei * (17 + 48 * Real.log x)) * (ei⁻¹ ^ 2 * (CNN * ei * Real.log x ^ (-Nexp))) :=
        mul_le_mul hfac hsum (sum_nonneg fun _ _ => sq_nonneg _) (hfac0.trans hfac)
    _ = (17 + 48 * Real.log x) * (CNN * Real.log x ^ (-Nexp)) := by
        field_simp

open scoped Classical in
/-- **One class of a box (E7, E10).** For a box `(j, i)` with primes and corner
`r = e^{jδ} e^{iδ} ∈ [Y, 2Y]`, and a class `β`,
`∫_a^b |A_β B_β|² ≤ θ² (17 + 48L) 3δ H_max² + 2(3δ)² (L^{2C₈} (2304/c + 4ε²X) +
  J_B (L^{C₈} (24/X + ε))² + (17 + 48L) C_N L^{-N})`, `ε = x^{-1/150}`, `X = x^{1/300}`. -/
theorem integral_boxSmall_mul_le (hab : a ≤ b) (hc : 2 ≤ c)
    (hint : ∀ t ∈ Set.Icc a b, c ≤ |t| ∧ |t| ≤ T₀) (hba : b - a ≤ T₀) (hσ : |σ| ≤ c / 2)
    (hx : 1 < x) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hH : ∀ n, ‖H n‖ ≤ Hc)
    (hY₁ : x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y) (hY₂ : 8 * Y ≤ x ^ 3)
    (hT₀ : T₀ * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y)
    (hδx : 1 ≤ δ * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2)) (hδx' : 1 ≤ δ * x)
    (hE10 : ∀ (R : ℝ) (β lo hi : ℕ) (u : ℝ), x ^ (99 / 100 : ℝ) ≤ R → R ≤ lo + 1 →
      (hi : ℝ) ≤ 2 * R → 1 ≤ |u| → |u| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc lo hi).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A₀ d) * (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |u| + x ^ (-(1 / 150 : ℝ))))
    (hmodel : ∀ R : ℝ, 1 ≤ R → ∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
      ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 ≤ CNN * R * Real.log x ^ (-Nexp))
    (hOrd : ∀ (s : Finset ℕ) (cs : ℕ → ℂ) (N : ℕ) (cq : ℕ → ℂ) {a b θ : ℝ}, a ≤ b →
      ∫ t in {t ∈ Set.Ioc a b | ‖∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ θ},
          ‖(∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) *
            ∑ n ∈ Finset.Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
        θ ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖cq n‖ ^ 2))
    (hS16 : ∀ (P : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
      Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P → P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
      (∀ p ∈ s, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) → (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
      (((Finset.Icc (-⌈T₀⌉ - 1) ⌈T₀⌉).filter fun j : ℤ =>
          ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ T₀ ∧
            θ < ‖(P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖).card : ℝ) ≤
        JB)
    {j i : ℕ} (hs : (boxPrimes δ Ps j).Nonempty)
    (hr₁ : Y ≤ Real.exp (j * δ) * Real.exp (i * δ))
    (hr₂ : Real.exp (j * δ) * Real.exp (i * δ) ≤ 2 * Y) (β : ℕ) :
    ∫ t in a..b, ‖boxSmall σ δ h k Ps j β t * boxResidual σ δ k H i β t‖ ^ 2 ≤
      classBound x δ θ c C₈ CNN Nexp JB Hc := by
  rw [classBound]
  set L := Real.log x with hLdef
  set ej := Real.exp (j * δ) with hej
  set ei := Real.exp (i * δ) with hei
  set s := boxPrimes δ Ps j with hsdef
  set Sβ := (gridPiece δ i).filter (· ≡ β [MOD k]) with hSβ
  set N := grid δ (i + 1) with hN
  set ε := x ^ (-(1 / 150 : ℝ)) with hε
  set X := x ^ (1 / 300 : ℝ) with hX
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos hx
  have hej0 : 0 < ej := Real.exp_pos _
  have hei0 : 0 < ei := Real.exp_pos _
  have hc0 : 0 < c := by linarith
  obtain ⟨hej₁, hej₂⟩ := boxPrimes_scale hδ0.le hδ hPs hs
  have hE36 : 0 < Real.exp (L ^ (0.36 : ℝ)) := Real.exp_pos _
  have hYE : Y ≤ Real.exp (L ^ (0.36 : ℝ)) * ei :=
    hr₁.trans (mul_le_mul_of_nonneg_right hej₂ hei0.le)
  have hei₁ : x ≤ ei := by
    have h1 : x * Real.exp (L ^ (0.36 : ℝ)) ≤ ei * Real.exp (L ^ (0.36 : ℝ)) := by
      linarith [mul_comm ei (Real.exp (L ^ (0.36 : ℝ)))]
    exact le_of_mul_le_mul_right h1 hE36
  have hT₀ei : T₀ ≤ ei := by
    have h1 : T₀ * Real.exp (L ^ (0.36 : ℝ)) ≤ ei * Real.exp (L ^ (0.36 : ℝ)) := by
      linarith [mul_comm ei (Real.exp (L ^ (0.36 : ℝ)))]
    exact le_of_mul_le_mul_right h1 hE36
  have hei₂ : ei ≤ 4 * Y := by
    have h1 : (1 : ℝ) / 2 ≤ ej := by
      have : (1 : ℝ) ≤ Real.exp (L ^ (0.27 : ℝ)) := Real.one_le_exp (by positivity)
      linarith
    have : ei * (1 / 2) ≤ ej * ei := by
      rw [mul_comm ej]
      exact mul_le_mul_of_nonneg_left h1 hei0.le
    linarith
  -- counts and lengths
  have hcS : (Sβ.card : ℝ) ≤ 3 * δ * ei := by
    refine (show (Sβ.card : ℝ) ≤ (gridPiece δ i).card by exact_mod_cast card_filter_le _ _).trans
      (card_gridPiece_le hδ0.le hδ (hδx'.trans (mul_le_mul_of_nonneg_left hei₁ hδ0.le)))
  have hSβ1 : Sβ ⊆ Icc 1 N := (filter_subset _ _).trans (gridPiece_subset_Icc δ i)
  have hfac : b - a + 8 * N * (1 + Real.log N) ≤ ei * (17 + 48 * L) :=
    length_factor_le hδ0.le hδ hba hT₀ei (by linarith)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast one_le_grid hδ0.le (i + 1)
  have hfac0 : 0 ≤ b - a + 8 * N * (1 + Real.log N) := by
    have := Real.log_nonneg hN1
    have : 0 ≤ 8 * (N : ℝ) * (1 + Real.log N) := by positivity
    linarith
  -- the small-prime polynomial is at most `3δ`
  have hAmax : ∀ t, ‖boxSmall σ δ h k Ps j β t‖ ≤ 3 * δ :=
    norm_boxSmall_le_three hδ0.le hδ hPs hδx hs β
  -- the model part and the model error
  set H₀ : ℕ → ℂ := fun n => ∑ d ∈ n.divisors, A₀ d with hH₀
  set B₀ := boxResidual σ δ k H₀ i β with hB₀
  set B₁ := boxResidual σ δ k (fun n => H n - H₀ n) i β with hB₁
  have hsplit : ∀ t, boxResidual σ δ k H i β t = B₀ t + B₁ t := by
    intro t
    rw [hB₀, hB₁, ← boxResidual_add]
    congr 1
    funext n
    ring
  -- E10.2: the model part pointwise
  have hei99 : x ^ (99 / 100 : ℝ) ≤ ei := by
    refine le_trans ?_ hei₁
    calc x ^ (99 / 100 : ℝ) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num)
      _ = x := Real.rpow_one x
  have hB₀pt : ∀ t ∈ Set.Icc a b, ‖B₀ t‖ ≤ L ^ C₈ * (24 / |t| + ε) := fun t ht =>
    norm_boxResidual_model_le hE10 hx.le hδ0.le hδ hc hσ (by linarith) hei99 β (hint t ht).1
      (hint t ht).2
  -- E7: the ordinary times
  have hord := setIntegral_boxOrdinary_le (σ := σ) (h := h) (Ps := Ps) (θ := θ) (j := j)
    hOrd hab hH hfac hfac0 hcS
  simp_rw [hsplit] at hord
  -- S16: the exceptional unit intervals
  set coeff : ℕ → ℂ := fun p => twist h k (p * β) * (p : ℂ) ^ ((σ : ℂ) * Complex.I) with hcoeff
  have hAform : ∀ t, boxSmall σ δ h k Ps j β t =
      (ej : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro t
    rw [boxSmall, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [hcoeff, Complex.ofReal_inv]
    ring
  have hbad := exists_mem_exceptional (θ' := θ) (boxSmall σ δ h k Ps j β) hAform
    (fun t ht => (hint t ht).2)
  have hcard := hS16 ej s coeff hej₁ hej₂ (fun p hp => by
      obtain ⟨hpj, hpP⟩ := mem_filter.1 hp
      obtain ⟨hp1, hp2⟩ := mem_gridPiece hpj
      rw [exp_succ_mul] at hp2
      have heδ : Real.exp δ ≤ 2 := by linarith [exp_sub_one_le_two_mul hδ0.le (by linarith)]
      exact ⟨(hPs p hpP).1, hp1.le,
        hp2.trans (mul_le_mul_of_nonneg_right heδ hej0.le)⟩)
    (fun p _ => by
      rw [hcoeff]
      simp only
      rw [norm_mul, norm_twist, one_mul]
      exact IntegerKernel.norm_natCast_cpow_I_mul_le σ p)
  -- E10.1: the model error
  have hME := integral_boxResidual_error_le (σ := σ) (k := k) hmodel hx hδ0.le hδ hfac hfac0 β
  have hX0 : 0 < X := by positivity
  have hΛ : 0 ≤ L ^ C₈ := Real.rpow_nonneg hL0.le _
  have hpiece := integral_piece_le hab hc0 (fun t ht => (hint t ht).1) hX0 hΛ
    (continuous_boxSmall (σ := σ) (δ := δ) (h := h) (k := k) (Ps := Ps) j β)
    (continuous_boxResidual (σ := σ) (δ := δ) (k := k) _ i β)
    (continuous_boxResidual (σ := σ) (δ := δ) (k := k) _ i β) hAmax hB₀pt hord _
    (fun t ht hθ _ => hbad t ht hθ) hME
  simp_rw [hsplit]
  refine hpiece.trans ?_
  have hG : 0 ≤ (L ^ C₈ * (24 / X + ε)) ^ 2 := sq_nonneg _
  have hδ2 : 0 ≤ 2 * (3 * δ) ^ 2 := by positivity
  gcongr

/-- **The corner error of a relevant box.** For a box with primes and corner
`r ∈ [Y/4, 2Y]`, `∫_a^b |E_{ji}|² ≤ 3888 δ⁵ K_c² M₁² H_max² (66 + 192L)`. -/
theorem integral_boxErr_le_of_corner {κ : ℂ} {ψ : ℝ → ℂ} {M Kc : ℝ} (hab : a ≤ b)
    (hba : b - a ≤ T₀) (hx : 1 < x) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hM : ∀ y, ‖iteratedDeriv 1 ψ y‖ ≤ M) (hκ : ‖κ‖ ≤ Kc) (hH : ∀ n, ‖H n‖ ≤ Hc)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hY₁ : x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y) (hY₂ : 8 * Y ≤ x ^ 3)
    (hT₀ : T₀ * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y)
    (hδx : 1 ≤ δ * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2)) (hδx' : 4 ≤ δ * x)
    {j i : ℕ} (hs : (boxPrimes δ Ps j).Nonempty)
    (hr₁ : Y / 4 ≤ Real.exp (j * δ) * Real.exp (i * δ))
    (hr₂ : Real.exp (j * δ) * Real.exp (i * δ) ≤ 2 * Y) :
    ∫ t in a..b, ‖boxErr Y σ δ h k Ps κ H ψ j i t‖ ^ 2 ≤
      3888 * δ ^ 5 * Kc ^ 2 * M ^ 2 * Hc ^ 2 * (66 + 192 * Real.log x) := by
  set L := Real.log x with hLdef
  set ej := Real.exp (j * δ) with hej
  set ei := Real.exp (i * δ) with hei
  set N := grid δ (i + 1) with hN
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.log_pos hx
  have hej0 : 0 < ej := Real.exp_pos _
  have hei0 : 0 < ei := Real.exp_pos _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hKc : 0 ≤ Kc := (norm_nonneg _).trans hκ
  have hHc : 0 ≤ Hc := (norm_nonneg _).trans (hH 0)
  have hE36 : 0 < Real.exp (L ^ (0.36 : ℝ)) := Real.exp_pos _
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  obtain ⟨hej₁, hej₂⟩ := boxPrimes_scale hδ0.le hδ hPs hs
  -- `x/4 ≤ e^{iδ} ≤ 4Y`
  have hei₁ : x / 4 ≤ ei := by
    have h1 : Y / 4 ≤ Real.exp (L ^ (0.36 : ℝ)) * ei :=
      hr₁.trans (mul_le_mul_of_nonneg_right hej₂ hei0.le)
    have h2 : x / 4 * Real.exp (L ^ (0.36 : ℝ)) ≤ ei * Real.exp (L ^ (0.36 : ℝ)) := by
      linarith [mul_comm ei (Real.exp (L ^ (0.36 : ℝ)))]
    exact le_of_mul_le_mul_right h2 hE36
  have hei₂ : ei ≤ 4 * Y := by
    have h1 : (1 : ℝ) / 2 ≤ ej := by
      have : (1 : ℝ) ≤ Real.exp (L ^ (0.27 : ℝ)) := Real.one_le_exp (by positivity)
      linarith
    have : ei * (1 / 2) ≤ ej * ei := by
      rw [mul_comm ej]
      exact mul_le_mul_of_nonneg_left h1 hei0.le
    linarith
  have hcs := card_boxPrimes_le hδ0.le hδ hPs hδx hs
  have hcP : ((gridPiece δ i).card : ℝ) ≤ 3 * δ * ei :=
    card_gridPiece_le hδ0.le hδ (by nlinarith [mul_le_mul_of_nonneg_left hei₁ hδ0.le])
  -- the length factor
  have hN2 : (N : ℝ) ≤ 2 * ei := grid_succ_le hδ0.le hδ i
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast one_le_grid hδ0.le (i + 1)
  have hlogN : Real.log N ≤ 3 * L := by
    calc Real.log N ≤ Real.log (x ^ 3) := Real.log_le_log (by linarith) (by linarith)
      _ = 3 * L := by rw [Real.log_pow]; push_cast; ring
  have hlog0 := Real.log_nonneg hN1
  have hfac : b - a + 8 * N * (1 + Real.log N) ≤ T₀ + 16 * ei * (1 + 3 * L) := by
    have : 8 * (N : ℝ) * (1 + Real.log N) ≤ 8 * (2 * ei) * (1 + 3 * L) := by gcongr
    linarith
  have hfac0 : 0 ≤ b - a + 8 * N * (1 + Real.log N) := by
    have : 0 ≤ 8 * (N : ℝ) * (1 + Real.log N) := by positivity
    linarith
  refine (integral_boxErr_le hab hY0 hδ0.le hδ hψ hψd hM hκ hH j i).trans ?_
  set c₀ := Kc * Y⁻¹ * (12 * δ * M) * Hc with hc₀
  have hT₀0 : 0 ≤ T₀ := (sub_nonneg.2 hab).trans hba
  -- `e^{jδ} T₀ ≤ Y` and `r ≤ 2Y`
  have hejT : ej * T₀ ≤ Y := by
    calc ej * T₀ ≤ Real.exp (L ^ (0.36 : ℝ)) * T₀ := mul_le_mul_of_nonneg_right hej₂ hT₀0
      _ ≤ Y := by linarith [mul_comm T₀ (Real.exp (L ^ (0.36 : ℝ)))]
  calc ((boxPrimes δ Ps j).card : ℝ) ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) *
        ((gridPiece δ i).card * c₀ ^ 2))
      ≤ (3 * δ * ej) ^ 2 * ((T₀ + 16 * ei * (1 + 3 * L)) * (3 * δ * ei * c₀ ^ 2)) := by
        gcongr
    _ = 27 * δ ^ 3 * c₀ ^ 2 * ((ej * ei) * (ej * T₀) +
          16 * (1 + 3 * L) * (ej * ei) ^ 2) := by ring
    _ ≤ 27 * δ ^ 3 * c₀ ^ 2 * ((2 * Y) * Y + 16 * (1 + 3 * L) * (2 * Y) ^ 2) := by
        gcongr
    _ = 3888 * δ ^ 5 * Kc ^ 2 * M ^ 2 * Hc ^ 2 * (66 + 192 * L) := by
        rw [hc₀]
        field_simp
        ring

open scoped Classical in
/-- **One box (E6, E7, E10).** Every box `(j, i)` has
`∫_a^b |T_{ji}|² ≤ 2 (2K_c M₀)² k² · classBound + 2 · errBound`: the boxes without primes or with
corner outside `[Y/4, 2Y]` vanish; otherwise `T_{ji} = W ∑_β A_β B_β + E_{ji}` with
`|W| ≤ 2K_c M₀`, and `W = 0` unless `r ∈ [Y, 2Y]`. -/
theorem integral_boxSum_le {κ : ℂ} {ψ : ℝ → ℂ} {M₀ M₁ Kc : ℝ} (hab : a ≤ b) (hc : 2 ≤ c)
    (hint : ∀ t ∈ Set.Icc a b, c ≤ |t| ∧ |t| ≤ T₀) (hba : b - a ≤ T₀) (hσ : |σ| ≤ c / 2)
    (hx : 1 < x) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hM₀ : ∀ y, ‖ψ y‖ ≤ M₀) (hM₁ : ∀ y, ‖iteratedDeriv 1 ψ y‖ ≤ M₁) (hκ : ‖κ‖ ≤ Kc)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hk : 1 ≤ k) (hH : ∀ n, ‖H n‖ ≤ Hc)
    (hY₁ : x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y) (hY₂ : 8 * Y ≤ x ^ 3)
    (hT₀ : T₀ * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y)
    (hδx : 1 ≤ δ * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2)) (hδx' : 4 ≤ δ * x)
    (hE10 : ∀ (R : ℝ) (β lo hi : ℕ) (u : ℝ), x ^ (99 / 100 : ℝ) ≤ R → R ≤ lo + 1 →
      (hi : ℝ) ≤ 2 * R → 1 ≤ |u| → |u| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc lo hi).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A₀ d) * (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |u| + x ^ (-(1 / 150 : ℝ))))
    (hmodel : ∀ R : ℝ, 1 ≤ R → ∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
      ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 ≤ CNN * R * Real.log x ^ (-Nexp))
    (hOrd : ∀ (s : Finset ℕ) (cs : ℕ → ℂ) (N : ℕ) (cq : ℕ → ℂ) {a b θ : ℝ}, a ≤ b →
      ∫ t in {t ∈ Set.Ioc a b | ‖∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ θ},
          ‖(∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) *
            ∑ n ∈ Finset.Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
        θ ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖cq n‖ ^ 2))
    (hJB : 0 ≤ JB)
    (hS16 : ∀ (P : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
      Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P → P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
      (∀ p ∈ s, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) → (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
      (((Finset.Icc (-⌈T₀⌉ - 1) ⌈T₀⌉).filter fun j : ℤ =>
          ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ T₀ ∧
            θ < ‖(P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖).card : ℝ) ≤
        JB)
    (j i : ℕ) :
    ∫ t in a..b, ‖boxSum Y σ δ h k Ps κ H ψ j i t‖ ^ 2 ≤
      boxBound x δ θ c C₈ CNN Nexp JB Hc Kc M₀ M₁ k := by
  have hc0 : 0 < c := by linarith
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  have hCNN : 0 ≤ CNN := by
    have h1 := hmodel 1 le_rfl
    have h0 : 0 ≤ ∑ n ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊2 * (1 : ℝ)⌋₊,
        ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have h2 := h0.trans h1
    rw [mul_one] at h2
    exact nonneg_of_mul_nonneg_left h2 (Real.rpow_pos_of_pos (Real.log_pos hx) _)
  have hPB := classBound_nonneg (θ := θ) (C₈ := C₈) (Nexp := Nexp) (Hc := Hc) hx.le hδ0.le hc0
    hCNN hJB
  have hEB := errBound_nonneg (Kc := Kc) (M := M₁) (Hc := Hc) hx.le hδ0.le
  have hBB : 0 ≤ boxBound x δ θ c C₈ CNN Nexp JB Hc Kc M₀ M₁ k := by
    rw [boxBound]
    have : 0 ≤ (2 * Kc * M₀) ^ 2 * (k * (k * classBound x δ θ c C₈ CNN Nexp JB Hc)) := by
      positivity
    linarith
  set r := Real.exp (j * δ) * Real.exp (i * δ) with hr
  by_cases hrel : (boxPrimes δ Ps j).Nonempty ∧ Y / 4 ≤ r ∧ r ≤ 2 * Y
  swap
  · -- the box vanishes
    have h0 : ∀ t, boxSum Y σ δ h k Ps κ H ψ j i t = 0 := by
      intro t
      refine boxSum_eq_zero hY0 hδ hψ ?_ t
      rcases not_and_or.1 hrel with h1 | h1
      · exact Or.inl (Finset.not_nonempty_iff_eq_empty.1 h1)
      · rcases not_and_or.1 h1 with h2 | h2
        · exact Or.inr (Or.inl (lt_of_not_ge h2))
        · exact Or.inr (Or.inr (lt_of_not_ge h2))
    simp_rw [h0, norm_zero]
    simpa using hBB
  obtain ⟨hs, hr₁, hr₂⟩ := hrel
  have hk0 : k ≠ 0 := by omega
  simp_rw [boxSum_eq hk0]
  have hMain : Continuous fun t => boxWeight Y δ κ ψ j i * ∑ β ∈ range k,
      boxSmall σ δ h k Ps j β t * boxResidual σ δ k H i β t :=
    continuous_const.mul (continuous_finsetSum (range k) fun β _ =>
    (continuous_boxSmall (σ := σ) (δ := δ) (h := h) (k := k) (Ps := Ps) j β).mul
      (continuous_boxResidual (σ := σ) (δ := δ) (k := k) H i β))
  refine (integral_norm_add_sq_le hMain (continuous_boxErr j i) hab).trans ?_
  rw [boxBound]
  have hErr := integral_boxErr_le_of_corner (σ := σ) (h := h) (k := k) hab hba hx hδ0 hδ hψ hψd
    hM₁ hκ hH hPs hY₁ hY₂ hT₀ hδx hδx' hs hr₁ hr₂
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left hErr (by norm_num))
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (integral_corner_le hab _ _ _ (fun β => continuous_boxSmall j β)
    (fun β => continuous_boxResidual H i β)).trans ?_
  by_cases hψr : ψ (r / Y) = 0
  · have hW : boxWeight Y δ κ ψ j i = 0 := by
      rw [boxWeight, ← hr, hψr, mul_zero, zero_mul]
    rw [hW, norm_zero]
    have : 0 ≤ (2 * Kc * M₀) ^ 2 * (k * (k * classBound x δ θ c C₈ CNN Nexp JB Hc)) := by
      positivity
    simpa using this
  have hr₃ : Y ≤ r := by
    have := (hψ _ hψr).1
    rwa [le_div_iff₀ hY0, one_mul] at this
  have hW : ‖boxWeight Y δ κ ψ j i‖ ≤ 2 * Kc * M₀ := by
    rw [boxWeight, ← hr, norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hY0.le, Real.norm_of_nonneg (by positivity)]
    have hKc : 0 ≤ Kc := (norm_nonneg _).trans hκ
    have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
    have hYi : 0 ≤ Y⁻¹ := inv_nonneg.2 hY0.le
    calc ‖κ‖ * Y⁻¹ * ‖ψ (r / Y)‖ * r ≤ Kc * Y⁻¹ * M₀ * (2 * Y) :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hκ hYi) (hM₀ _) (norm_nonneg _)
            (mul_nonneg hKc hYi)) hr₂ (by positivity) (mul_nonneg (mul_nonneg hKc hYi) hM₀0)
      _ = 2 * Kc * M₀ := by field_simp
  have hcls : ∀ β ∈ range k, ∫ t in a..b,
      ‖boxSmall σ δ h k Ps j β t * boxResidual σ δ k H i β t‖ ^ 2 ≤
        classBound x δ θ c C₈ CNN Nexp JB Hc := fun β _ =>
    integral_boxSmall_mul_le hab hc hint hba hσ hx hδ0 hδ hPs hH hY₁ hY₂ hT₀ hδx
      (by linarith) hE10 hmodel hOrd hS16 hs hr₃ hr₂ β
  have hsum := sum_le_sum hcls
  rw [sum_const, card_range, nsmul_eq_mul] at hsum
  have hW2 : ‖boxWeight Y δ κ ψ j i‖ ^ 2 ≤ (2 * Kc * M₀) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hW 2
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hI0 : 0 ≤ ∑ β ∈ range k, ∫ t in a..b,
      ‖boxSmall σ δ h k Ps j β t * boxResidual σ δ k H i β t‖ ^ 2 :=
    sum_nonneg fun β _ => intervalIntegral.integral_nonneg hab fun t _ => by positivity
  exact mul_le_mul hW2 (mul_le_mul_of_nonneg_left hsum hk') (mul_nonneg hk' hI0) (sq_nonneg _)

open scoped Classical in
/-- **The constant part at high times, for fixed `x` (S19).** With the inputs E7, S16, E10.2
and E1 at this `x` and a grid reaching `2Y`, the mean square of the constant part over
`[a, b]` is at most `I⁴ · boxBound`: Cauchy–Schwarz over the `I²` boxes. -/
theorem integral_twistedPoly_const_le {κ : ℂ} {ψ : ℝ → ℂ} {M₀ M₁ Kc : ℝ} (hab : a ≤ b) (hc : 2 ≤ c)
    (hint : ∀ t ∈ Set.Icc a b, c ≤ |t| ∧ |t| ≤ T₀) (hba : b - a ≤ T₀) (hσ : |σ| ≤ c / 2)
    (hx : 1 < x) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (hψ : ∀ y, ψ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hM₀ : ∀ y, ‖ψ y‖ ≤ M₀) (hM₁ : ∀ y, ‖iteratedDeriv 1 ψ y‖ ≤ M₁) (hκ : ‖κ‖ ≤ Kc)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hk : 1 ≤ k) (hH : ∀ n, ‖H n‖ ≤ Hc)
    (hY₁ : x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y) (hY₂ : 8 * Y ≤ x ^ 3)
    (hT₀ : T₀ * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Y)
    (hδx : 1 ≤ δ * (Real.exp (Real.log x ^ (0.27 : ℝ)) / 2)) (hδx' : 4 ≤ δ * x)
    (hE10 : ∀ (R : ℝ) (β lo hi : ℕ) (u : ℝ), x ^ (99 / 100 : ℝ) ≤ R → R ≤ lo + 1 →
      (hi : ℝ) ≤ 2 * R → 1 ≤ |u| → |u| ≤ x ^ 3 →
      ‖(R : ℂ)⁻¹ * ∑ n ∈ (Finset.Ioc lo hi).filter (· ≡ β [MOD k]),
          (∑ d ∈ n.divisors, A₀ d) * (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
        Real.log x ^ C₈ * (12 / |u| + x ^ (-(1 / 150 : ℝ))))
    (hmodel : ∀ R : ℝ, 1 ≤ R → ∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
      ‖H n - ∑ d ∈ n.divisors, A₀ d‖ ^ 2 ≤ CNN * R * Real.log x ^ (-Nexp))
    (hOrd : ∀ (s : Finset ℕ) (cs : ℕ → ℂ) (N : ℕ) (cq : ℕ → ℂ) {a b θ : ℝ}, a ≤ b →
      ∫ t in {t ∈ Set.Ioc a b | ‖∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ θ},
          ‖(∑ p ∈ s, cs p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) *
            ∑ n ∈ Finset.Icc 1 N, cq n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
        θ ^ 2 * ((b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖cq n‖ ^ 2))
    (hJB : 0 ≤ JB)
    (hS16 : ∀ (P : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
      Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P → P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
      (∀ p ∈ s, p.Prime ∧ P ≤ p ∧ (p : ℝ) ≤ 2 * P) → (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
      (((Finset.Icc (-⌈T₀⌉ - 1) ⌈T₀⌉).filter fun j : ℤ =>
          ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ j + 1 ∧ |t| ≤ T₀ ∧
            θ < ‖(P : ℂ)⁻¹ * ∑ p ∈ s, coeff p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖).card : ℝ) ≤
        JB)
    (hx2 : 2 ≤ x) {I : ℕ} (hI : 2 * Y ≤ grid δ I) :
    ∫ t in a..b, ‖twistedPoly Y (fun w => ψ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * κ *
        ∑ p ∈ Ps.filter (· ∣ w), H (w / p)) h k t‖ ^ 2 ≤
      (I : ℝ) ^ 2 * ((I : ℝ) ^ 2 * boxBound x δ θ c C₈ CNN Nexp JB Hc Kc M₀ M₁ k) := by
  have hPs2 : ∀ p ∈ Ps, 2 ≤ p ∧ 2 * (p : ℝ) ≤ Y := by
    intro p hp
    obtain ⟨hpr, -, hp36⟩ := hPs p hp
    refine ⟨hpr.two_le, ?_⟩
    have : 2 * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ x * Real.exp (Real.log x ^ (0.36 : ℝ)) :=
      mul_le_mul_of_nonneg_right hx2 (Real.exp_pos _).le
    linarith
  simp_rw [twistedPoly_eq_sum_boxSum hδ0.le hψ hPs2 hI, ← Finset.sum_product']
  have hCS := integral_norm_sum_sq_le (range I ×ˢ range I) (fun _ => 1)
    (fun _ _ => norm_one.le) (fun z t => boxSum Y σ δ h k Ps κ H ψ z.1 z.2 t)
    (fun z _ => continuous_boxSum z.1 z.2) hab
  simp only [one_mul] at hCS
  refine hCS.trans ?_
  have hbox : ∀ z ∈ range I ×ˢ range I, ∫ t in a..b, ‖boxSum Y σ δ h k Ps κ H ψ z.1 z.2 t‖ ^ 2 ≤
      boxBound x δ θ c C₈ CNN Nexp JB Hc Kc M₀ M₁ k := fun z _ =>
    integral_boxSum_le hab hc hint hba hσ hx hδ0 hδ hψ hψd hM₀ hM₁ hκ hPs hk hH hY₁ hY₂ hT₀ hδx
      hδx' hE10 hmodel hOrd hJB hS16 z.1 z.2
  have hsum := sum_le_sum hbox
  rw [sum_const, nsmul_eq_mul] at hsum
  rw [card_product, card_range]
  push_cast
  have hI0 : (0 : ℝ) ≤ I * I := by positivity
  calc (I : ℝ) * I * ∑ z ∈ range I ×ˢ range I,
        ∫ t in a..b, ‖boxSum Y σ δ h k Ps κ H ψ z.1 z.2 t‖ ^ 2
      ≤ I * I * ((range I ×ˢ range I).card * boxBound x δ θ c C₈ CNN Nexp JB Hc Kc M₀ M₁ k) :=
        mul_le_mul_of_nonneg_left hsum hI0
    _ = (I : ℝ) ^ 2 * ((I : ℝ) ^ 2 * boxBound x δ θ c C₈ CNN Nexp JB Hc Kc M₀ M₁ k) := by
        rw [card_product, card_range]
        push_cast
        ring

end Fixed

end Erdos408.TwoSided.ConstHigh
