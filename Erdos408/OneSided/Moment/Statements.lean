import Erdos408.OneSided.Moment.Lines
import Erdos408.OneSided.Moment.RootReplacement.Assembly
import Erdos408.OneSided.Moment.RootReplacement.Budget
import Erdos408.OneSided.RootResidue

/-!
# The moment: root replacement

The first analytic statement behind the moment bound (`blueprint/one_sided_type_ii.md` §11).

* `eventually_root_replacement` (PD Lemma 3.4, blueprint §5.4). The normalized physical
  moment `(UV)⁻¹ detMoment` is within `exp(-L^{0.76})` of
  `c₂ n⁻³ ∑_cubes 𝔼_ℓ rootMoment(ϱ_Q, ℓ)`. The sum runs over the grid of side `1/n`,
  `n = ⌈m_*^{1/40}⌉`, `m_* = min(H_m, H_n)`, on `[1, 16] × [1, 2] × [0, 1]`, with `ϱ_Q` the
  lower corner of the cube. `𝔼_ℓ` is the average over independent uniform lines at the
  band primes.

Together with the memory bound `eventually_norm_lineAverage_le` (`Moment/Memory.lean`) and
`c₂ ≤ 2`, this gives `eventually_detMoment`.

The proof is assembled from `Moment/RootReplacement/` (blueprint §15): the expansion over
configurations (`Config.lean`), root equidistribution for functions of the lines
(`Lines.lean`, `Residues.lean`), Bonferroni on one box (`Bonferroni.lean`), the grid of cubes
(`Grid.lean`), the boundary cubes (`Boundary.lean`), the coefficient budget (`Mass.lean`) and
the final budget (`Budget.lean`), put together in `Assembly.lean`.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-- The number `n = ⌈m_*^{1/40}⌉` of grid steps per unit, `m_* = min(H_m, H_n)`. -/
def gridSteps (d : Data K) : ℕ := ⌈min d.Hm d.Hn ^ (1 / 40 : ℝ)⌉₊

/-- The Riemann sum `n⁻³ ∑_cubes 𝔼_ℓ rootMoment(ϱ_Q, ℓ)` over the lower corners
`ϱ_Q = (U(1 + i₁/n), V(1 + i₂/n), i₃/n)`, with `U = d₀ Y H_m`, `V = H_n`. -/
def rootRiemannSum (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) : ℂ :=
  ((gridSteps d : ℂ) ^ 3)⁻¹ * ∑ i₁ ∈ range (15 * gridSteps d), ∑ i₂ ∈ range (gridSteps d),
    ∑ i₃ ∈ range (gridSteps d),
      lineAverage x d fun ℓ => rootMoment q A₀ x d Y d₀
        (d₀ * Y * d.Hm * (1 + i₁ / gridSteps d)) (d.Hn * (1 + i₂ / gridSteps d))
        (i₃ / gridSteps d) ℓ

/-- PD Lemma 3.4 (root replacement), with the budgets of blueprint §5.4. -/
theorem eventually_root_replacement {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hg : 0 < g) (A₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ‖(((2 : ℝ) ^ k * 2 ^ j * d.X : ℝ) : ℂ)⁻¹ * detMoment q A₀ x d (2 ^ j) (2 ^ k) -
          (primitiveDensity : ℂ) * rootRiemannSum q A₀ x d (2 ^ j) (2 ^ k)‖ ≤
        Real.exp (-Real.log x ^ (76 / 100 : ℝ)) := by
  obtain ⟨C₀, hC₀, hE⟩ := exists_rootEquidist K
  filter_upwards [eventually_sum_norm_confCoeff_le (K := K) (C := C) (CX := CX) (g := g)
      halo hahi A₀,
    eventually_card_badCubes_le (K := K) (C := C) (CX := CX) (alo := alo) (g := g) hahi A₀,
    eventually_dampMass_le (K := K) (ahi := ahi) hq hq₁ halo, eventually_budget K hC₀,
    eventually_band_disjoint hg, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop 0] with x hmass hbad hdamp hbud hdisj hL hx0 d hd j k
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hdisj' : ∀ i i', i ≠ i' → Disjoint (band x (d.a i)) (band x (d.a i')) := by
    intro i i' h
    rcases lt_or_gt_of_ne h with h | h
    · exact hdisj _ _ (hd.gap i i' h)
    · exact (hdisj _ _ (hd.gap i' i h)).symm
  have hR : 0 < momentPower x := Nat.ceil_pos.2 (by positivity)
  -- step: the scales, `m = min(H_m, H_n) ≥ x^γ ≥ exp(L^{0.99})`
  have hxγ : Real.exp (L ^ (99 / 100 : ℝ)) ≤ x ^ d.γ := by
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.2 ?_
    have h1 : L ^ (99 / 100 : ℝ) = L * L ^ (-(1 / 100 : ℝ)) := by
      rw [← Real.rpow_one_add' hL0.le (by norm_num)]
      norm_num
    rw [h1]
    exact mul_le_mul_of_nonneg_left hd.γ_ge hL0.le
  set m := min d.Hm d.Hn with hmdef
  have hm : Real.exp (L ^ (99 / 100 : ℝ)) ≤ m :=
    le_min (hxγ.trans hd.Hm_ge) (hxγ.trans hd.Hn_ge)
  have hm2 : 2 ≤ m := by
    have h1 : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
    have h2 := Real.add_one_le_exp (L ^ (99 / 100 : ℝ))
    linarith
  have hY1 : (1 : ℝ) ≤ 2 ^ k * 2 ^ j :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hmU : m ≤ 2 ^ k * 2 ^ j * d.Hm :=
    (min_le_left _ _).trans (le_mul_of_one_le_left (by linarith [min_le_left d.Hm d.Hn]) hY1)
  have hmV : m ≤ d.Hn := min_le_right _ _
  have hU2 : 2 ≤ (2 : ℝ) ^ k * 2 ^ j * d.Hm := hm2.trans hmU
  have hV2 : 2 ≤ d.Hn := hm2.trans hmV
  -- step: the grid, `m^{1/40} ≤ n ≤ 2 m^{1/40}`
  set n := gridSteps d with hndef
  have hm40 : 1 ≤ m ^ (1 / 40 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hn₁ : m ^ (1 / 40 : ℝ) ≤ n := Nat.le_ceil _
  have hn₂ : (n : ℝ) ≤ 2 * m ^ (1 / 40 : ℝ) :=
    (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith)
  have hn : 1 ≤ n := by exact_mod_cast hm40.trans hn₁
  -- step: the band primes are at most `p_max = exp(2 L^{1/5})`, and number at most `K p_max`
  set pmax := Real.exp (2 * L ^ (1 / 5 : ℝ)) with hpmaxdef
  have hpmax₁ : 1 ≤ pmax := Real.one_le_exp (by positivity)
  have hexp_le : ∀ i, Real.exp (2 * L ^ d.a i) ≤ pmax := fun i => by
    have := Real.rpow_le_rpow_of_exponent_le hL ((hd.window i).2.trans hahi.le)
    exact Real.exp_le_exp.2 (by linarith)
  have hpmax : ∀ p ∈ bandPrimes x d, (p : ℝ) ≤ pmax := fun p hp => by
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hp
    exact (le_exp_of_mem_band hi).trans (hexp_le i)
  have hnP : ((bandPrimes x d).card : ℝ) ≤ K * pmax := by
    calc ((bandPrimes x d).card : ℝ) ≤ ∑ i, ((band x (d.a i)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _i : Fin K, pmax := sum_le_sum fun i _ => (card_band_le x (d.a i)).trans (hexp_le i)
      _ = K * pmax := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- step: `N + 1 ≤ L^{1/2} + 3` and `J + 1 ≤ L^{1/100} + 1`
  have hN : ((2 * momentPower x + 1 : ℕ) : ℝ) ≤ L ^ (1 / 2 : ℝ) + 3 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ L ^ (1 / 2 : ℝ) / 2 by positivity)
    push_cast
    unfold momentPower at *
    linarith
  have hJ : ((padCount x + 1 : ℕ) : ℝ) ≤ L ^ (1 / 100 : ℝ) + 1 := by
    unfold padCount
    push_cast
    linarith [Nat.floor_le (show 0 ≤ L ^ (1 / 100 : ℝ) by positivity)]
  -- step: rewrite as the configuration estimate
  have hX : (2 : ℝ) ^ k * 2 ^ j * d.X = 2 ^ k * 2 ^ j * d.Hm * d.Hn := by
    rw [Data.X]
    ring
  have hRS : rootRiemannSum q A₀ x d (2 ^ j) (2 ^ k) = ((n : ℂ) ^ 3)⁻¹ *
      ∑ i ∈ cubeIndices n, lineAverage x d fun ℓ => rootMoment q A₀ x d (2 ^ j) (2 ^ k)
        (2 ^ k * 2 ^ j * d.Hm * (1 + i.1 / n)) (d.Hn * (1 + i.2.1 / n)) (i.2.2 / n) ℓ := by
    rw [rootRiemannSum, cubeIndices, sum_product]
    congr 1
    refine sum_congr rfl fun i₁ _ => ?_
    rw [sum_product]
  have hexp : 0 < Real.exp (L ^ (74 / 100 : ℝ)) := Real.exp_pos _
  rw [hX, hRS]
  refine (norm_sub_le_of_conf hq (by positivity) (by positivity) hR hdisj' hn
    (div_nonneg (Real.exp_pos _).le hexp.le) (hmass d hd j k) fun ω hω hc => ?_).trans_eq
    (mul_div_cancel₀ _ hexp.ne')
  -- step: one live configuration, by the grid estimate and the budget
  rw [le_div_iff₀' hexp]
  have hlam : ∀ p ∈ bandPrimes x d, ∀ l, 0 ≤ confLineFactor q p ω l ∧ confLineFactor q p ω l ≤ 1 :=
    fun p _ l => confLineFactor_mem_Icc hq hq₁ p ω l
  have hgrid := norm_sum_positions_sub_le hC₀ hE x d hU2 hV2 hn (confInd x d (2 ^ j) (2 ^ k) ω)
    (fun u v r => by
      obtain ⟨h₀, h₁⟩ := confInd_mem_Icc x d (2 ^ j) (2 ^ k) ω u v r
      rw [abs_le]
      constructor <;> linarith)
    (fun p l => confLineFactor q p ω l) hlam (confActive ω) (confActive_subset ω)
    ⌈L ^ (76 / 100 : ℝ)⌉₊ hpmax₁ hpmax (badCubes x d (2 ^ j) (2 ^ k) n ω)
    (fun i hi hib P₀ hP₀ => by
      by_contra hne
      exact hib (mem_filter.2 ⟨hi, P₀, hP₀, hne⟩))
  refine (mul_le_mul_of_nonneg_left hgrid hexp.le).trans ?_
  have hσ := hdamp d hd.window (2 ^ j) (2 ^ k) ω
  have ha := card_confActive_le ω
  refine hbud n (confActive ω).card m _ _ _ _ pmax _ hn hn₂ hn₁ hm hmU hmV
    (dampMass_nonneg fun p hp l => (hlam p hp l).2) (hσ.trans ?_) (Nat.cast_nonneg _)
    (hnP.trans_eq (by rw [hpmaxdef])) hpmax₁ le_rfl ?_ (Nat.cast_nonneg _)
    (hbad d hd j k n hn ω hω hc)
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (Nat.cast_nonneg _)
  · calc ((confActive ω).card : ℝ) ≤ ((2 * momentPower x + 1) * (K * (padCount x + 1)) : ℕ) := by
          exact_mod_cast ha
      _ ≤ (L ^ (1 / 2 : ℝ) + 3) * (K * (L ^ (1 / 100 : ℝ) + 1)) := by
          rw [Nat.cast_mul, Nat.cast_mul]
          exact mul_le_mul hN (mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _))
            (by positivity) (by positivity)

end Erdos408.OneSided
