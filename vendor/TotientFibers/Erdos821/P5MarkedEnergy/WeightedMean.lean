import Erdos821.P5.Basic
import Erdos821.Classical.DirichletMean

/-! A weighted mean value for Dirichlet polynomials, uniform under shifts,
from the proved mean-square input on unit-scale intervals. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- The quadratic decay weight `(1+|h t|)⁻²`. -/
def wt (h t : ℝ) : ℝ := ((1 + |h * t|) ^ 2)⁻¹

theorem wt_nonneg (h t : ℝ) : 0 ≤ wt h t := by unfold wt; positivity

theorem wt_le_one (h t : ℝ) : wt h t ≤ 1 := by
  unfold wt
  apply inv_le_one_of_one_le₀
  have : 1 ≤ 1 + |h * t| := by linarith [abs_nonneg (h * t)]
  nlinarith

theorem continuous_wt (h : ℝ) : Continuous (wt h) := by
  unfold wt
  apply Continuous.inv₀ (by fun_prop)
  intro t; positivity

theorem wt_le_inv_one_add_sq (h t : ℝ) : wt h t ≤ (1 + (h * t) ^ 2)⁻¹ := by
  unfold wt
  apply inv_anti₀ (by positivity)
  nlinarith [sq_abs (h * t), abs_nonneg (h * t)]

theorem wt_le_of_le_abs (h t d : ℝ) (hd : 0 ≤ d) (hdt : d ≤ |h * t|) :
    wt h t ≤ ((1 + d) ^ 2)⁻¹ := by
  unfold wt
  apply inv_anti₀ (by positivity)
  have : 1 + d ≤ 1 + |h * t| := by linarith
  nlinarith

theorem integrable_inv_one_add_sq_mul {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun t : ℝ => (1 + (h * t) ^ 2)⁻¹) :=
  integrable_inv_one_add_sq.comp_mul_left' hh

theorem integral_inv_one_add_sq_mul {h : ℝ} (hh : 0 < h) :
    ∫ t : ℝ, (1 + (h * t) ^ 2)⁻¹ = Real.pi / h := by
  have := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) h
  rw [this, integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr hh), smul_eq_mul]
  field_simp

theorem intervalIntegral_inv_one_add_sq_mul {h : ℝ} (hh : 0 < h) (T : ℝ) :
    ∫ t in (-T)..T, (1 + (h * t) ^ 2)⁻¹ = 2 * Real.arctan (h * T) / h := by
  have := intervalIntegral.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹)
    (a := -T) (b := T) hh.ne'
  rw [this, integral_inv_one_add_sq, smul_eq_mul, mul_neg, Real.arctan_neg]
  field_simp
  ring

theorem norm_dp_le_sum (s : Finset ℕ) (g : ℕ → ℂ) (t : ℝ) :
    ‖dp s g t‖ ≤ ∑ n ∈ s, ‖g n‖ := by
  unfold dp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, P5Core.norm_mellin, mul_one]

theorem sum_norm_sq_le_card (s : Finset ℕ) (g : ℕ → ℂ) :
    (∑ n ∈ s, ‖g n‖) ^ 2 ≤ (s.card : ℝ) * sqNorm s g := by
  unfold sqNorm
  exact sq_sum_le_card_mul_sum_sq

theorem sum_inv_succ_sq_le_two (n : ℕ) :
    ∑ m ∈ Finset.range n, (((m : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have key : ∀ n : ℕ, ∑ m ∈ Finset.range (n + 1), (((m : ℝ) + 1) ^ 2)⁻¹ ≤
      2 - ((n : ℝ) + 1)⁻¹ := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h1 : (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by push_cast; ring
      rw [h1]
      push_cast
      have hstep : (((k : ℝ) + 2) ^ 2)⁻¹ ≤ ((k : ℝ) + 1)⁻¹ - ((k : ℝ) + 2)⁻¹ := by
        have e : ((k : ℝ) + 1)⁻¹ - ((k : ℝ) + 2)⁻¹ = (((k : ℝ) + 1) * ((k : ℝ) + 2))⁻¹ := by
          field_simp; ring
        rw [e]
        exact inv_anti₀ (by positivity) (by nlinarith)
      linarith
  rcases n with _ | n
  · simp
  · have := key n
    have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    linarith

theorem nat_mul_log_nonneg' (N : ℕ) : 0 ≤ (N : ℝ) * Real.log (2 * N) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))

/-- Weighted mean value, uniform in the shift `c`. -/
theorem weighted_mean_value : ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (g : ℕ → ℂ) (h c : ℝ), 0 < h →
    Integrable (fun t => wt h t * ‖dp (Finset.Icc 1 N) g (t + c)‖ ^ 2) ∧
    ∫ t, wt h t * ‖dp (Finset.Icc 1 N) g (t + c)‖ ^ 2 ≤
      K * (1 / h + N * Real.log (2 * N)) * sqNorm (Finset.Icc 1 N) g := by
  obtain ⟨KMS, hKMS, hMS⟩ := Erdos821.Classical.blueprint_meanSquares
  refine ⟨4 * KMS + 2, by positivity, ?_⟩
  intro N g h c hh
  set s := Finset.Icc 1 N with hs
  set D : ℝ → ℂ := fun t => dp s g (t + c) with hD
  set M := ∑ n ∈ s, ‖g n‖ with hMdef
  set q := sqNorm s g with hqdef
  have hq : 0 ≤ q := Finset.sum_nonneg (fun _ _ => by positivity)
  have hNlog := nat_mul_log_nonneg' N
  have hDc : Continuous D := (P5Core.continuous_dp s g).comp (continuous_id.add continuous_const)
  have hDle : ∀ t, ‖D t‖ ≤ M := fun t => norm_dp_le_sum s g _
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM2 : M ^ 2 ≤ N * q := by
    have := sum_norm_sq_le_card s g
    simpa [s, Nat.card_Icc] using this
  set f : ℝ → ℝ := fun t => wt h t * ‖D t‖ ^ 2 with hfdef
  have hfc : Continuous f := (continuous_wt h).mul (hDc.norm.pow 2)
  have hfnn : ∀ t, 0 ≤ f t := fun t => mul_nonneg (wt_nonneg h t) (by positivity)
  have hv : Integrable (fun t : ℝ => (1 + (h * t) ^ 2)⁻¹) := integrable_inv_one_add_sq_mul hh.ne'
  have hfle : ∀ t, f t ≤ M ^ 2 * (1 + (h * t) ^ 2)⁻¹ := by
    intro t
    have h1 := wt_le_inv_one_add_sq h t
    have h2 : ‖D t‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hDle t) 2
    have h3 : 0 ≤ (1 + (h * t) ^ 2)⁻¹ := by positivity
    calc f t = wt h t * ‖D t‖ ^ 2 := rfl
      _ ≤ (1 + (h * t) ^ 2)⁻¹ * M ^ 2 :=
          mul_le_mul h1 h2 (by positivity) h3
      _ = _ := mul_comm _ _
  have hfi : Integrable f := by
    refine (hv.const_mul (M ^ 2)).mono' hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnn t)]
    exact hfle t
  refine ⟨hfi, ?_⟩
  set n : ℕ := N + 1 with hn
  have hnpos : (0 : ℝ) < n := by positivity
  set T : ℝ := (n : ℝ) / h with hT
  have hT0 : 0 ≤ T := by positivity
  have hhT : h * T = n := by rw [hT]; field_simp
  rw [← integral_add_compl measurableSet_Icc hfi]
  -- tail
  have htail : ∫ t in (Set.Icc (-T) T)ᶜ, f t ≤ 2 * q / h := by
    have h1 : ∫ t in (Set.Icc (-T) T)ᶜ, f t ≤
        ∫ t in (Set.Icc (-T) T)ᶜ, M ^ 2 * (1 + (h * t) ^ 2)⁻¹ :=
      setIntegral_mono hfi.integrableOn (hv.const_mul _).integrableOn hfle
    have h2 : ∫ t in (Set.Icc (-T) T)ᶜ, (1 + (h * t) ^ 2)⁻¹ =
        Real.pi / h - 2 * Real.arctan (h * T) / h := by
      have hsplit := integral_add_compl (measurableSet_Icc (a := -T) (b := T)) hv
      rw [integral_inv_one_add_sq_mul hh] at hsplit
      have hI : ∫ t in Set.Icc (-T) T, (1 + (h * t) ^ 2)⁻¹ = 2 * Real.arctan (h * T) / h := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
          intervalIntegral_inv_one_add_sq_mul hh]
      linarith
    have h3 : Real.pi / h - 2 * Real.arctan (h * T) / h ≤ 2 / (n * h) := by
      rw [hhT]
      have harc := Real.arctan_inv_of_pos hnpos
      have hle := Real.arctan_le_self (inv_nonneg.mpr hnpos.le)
      have : Real.pi / h - 2 * Real.arctan n / h = 2 * Real.arctan (n : ℝ)⁻¹ / h := by
        rw [harc]; ring
      rw [this]
      calc 2 * Real.arctan (n : ℝ)⁻¹ / h ≤ 2 * (n : ℝ)⁻¹ / h := by gcongr
        _ = 2 / (n * h) := by field_simp
    rw [integral_const_mul, h2] at h1
    have hNn : (N : ℝ) ≤ n := by rw [hn]; push_cast; linarith
    have hpos3 : 0 ≤ Real.pi / h - 2 * Real.arctan (h * T) / h := by
      have := Real.arctan_lt_pi_div_two (h * T)
      have e : Real.pi / h - 2 * Real.arctan (h * T) / h =
          (Real.pi - 2 * Real.arctan (h * T)) / h := by ring
      rw [e]
      apply div_nonneg _ hh.le
      linarith
    have hfrac : (N : ℝ) / n ≤ 1 := (div_le_one hnpos).mpr hNn
    calc ∫ t in (Set.Icc (-T) T)ᶜ, f t ≤ M ^ 2 * (Real.pi / h - 2 * Real.arctan (h * T) / h) := h1
      _ ≤ (N * q) * (2 / (n * h)) := mul_le_mul hM2 h3 hpos3 (by positivity)
      _ = 2 * q / h * (N / n) := by field_simp
      _ ≤ 2 * q / h * 1 := by
          apply mul_le_mul_of_nonneg_left hfrac
          positivity
      _ = 2 * q / h := mul_one _
  -- middle
  set B := KMS * (1 / h + N * Real.log (2 * N)) * q with hBdef
  have hB0 : 0 ≤ B := by positivity
  let a : ℕ → ℝ := fun k => ((k : ℝ) - n) / h
  let d : ℕ → ℕ := fun k => if n ≤ k then k - n else n - 1 - k
  let sk : ℕ → ℝ := fun k => ((1 + (d k : ℝ)) ^ 2)⁻¹
  have hpiece : ∀ k : ℕ, ∫ t in (a k)..(a (k + 1)), f t ≤ sk k * B := by
    intro k
    have hak : a k ≤ a (k + 1) := by
      simp only [a]; apply div_le_div_of_nonneg_right _ hh.le; push_cast; linarith
    have hw : ∀ t ∈ Set.Icc (a k) (a (k + 1)), f t ≤ sk k * ‖D t‖ ^ 2 := by
      intro t ht
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply wt_le_of_le_abs h t _ (Nat.cast_nonneg _)
      simp only [d]
      split_ifs with hk
      · have : ((k : ℝ) - n) ≤ h * t := by
          have := ht.1; simp only [a] at this
          rw [div_le_iff₀ hh] at this; linarith
        rw [Nat.cast_sub hk]
        exact this.trans (le_abs_self _)
      · have hk' : k + 1 ≤ n := by omega
        have : h * t ≤ ((k : ℝ) + 1 - n) := by
          have := ht.2; simp only [a] at this
          rw [le_div_iff₀ hh] at this; push_cast at this; linarith
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have hk'' : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk'
        rw [Nat.cast_one]
        calc (n : ℝ) - 1 - k ≤ -(h * t) := by linarith
          _ ≤ |h * t| := neg_le_abs _
    calc ∫ t in (a k)..(a (k + 1)), f t ≤ ∫ t in (a k)..(a (k + 1)), sk k * ‖D t‖ ^ 2 :=
          intervalIntegral.integral_mono_on hak (hfc.intervalIntegrable _ _)
            ((continuous_const.mul (hDc.norm.pow 2)).intervalIntegrable _ _) hw
      _ = sk k * ∫ t in (a k + c)..(a (k + 1) + c), ‖dp s g t‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul]
          congr 1
          exact intervalIntegral.integral_comp_add_right (fun t => ‖dp s g t‖ ^ 2) c
      _ ≤ sk k * (KMS * ((a (k + 1) + c) - (a k + c) + N * Real.log (2 * N)) * q) :=
          mul_le_mul_of_nonneg_left (hMS N g _ _ (by linarith)).1 (by positivity)
      _ = sk k * B := by
          congr 1
          simp only [hBdef, a]
          congr 2
          push_cast
          field_simp
          ring
  have hsum : ∑ k ∈ Finset.range (n + n), sk k ≤ 4 := by
    rw [Finset.sum_range_add]
    have e1 : ∑ k ∈ Finset.range n, sk k = ∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹ := by
      rw [← Finset.sum_range_reflect (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) n]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      simp only [sk, d, if_neg (show ¬ n ≤ k by omega)]
      ring_nf
    have e2 : ∑ k ∈ Finset.range n, sk (n + k) =
        ∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [sk, d, if_pos (show n ≤ n + k by omega), Nat.add_sub_cancel_left]
      ring_nf
    rw [e1, e2]
    linarith [sum_inv_succ_sq_le_two n]
  have hmid : ∫ t in Set.Icc (-T) T, f t ≤ 4 * B := by
    have ha0 : a 0 = -T := by simp only [a, hT]; push_cast; ring
    have ha2 : a (n + n) = T := by simp only [a, hT]; push_cast; ring
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      ← ha0, ← ha2, ← intervalIntegral.sum_integral_adjacent_intervals
        (fun k _ => hfc.intervalIntegrable _ _)]
    calc ∑ k ∈ Finset.range (n + n), ∫ t in (a k)..(a (k + 1)), f t
        ≤ ∑ k ∈ Finset.range (n + n), sk k * B := Finset.sum_le_sum fun k _ => hpiece k
      _ = (∑ k ∈ Finset.range (n + n), sk k) * B := by rw [Finset.sum_mul]
      _ ≤ 4 * B := mul_le_mul_of_nonneg_right hsum hB0
  have hfin : 2 * q / h ≤ 2 * (1 / h + N * Real.log (2 * N)) * q := by
    have : 2 * q / h = 2 * (1 / h) * q := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hq
    linarith
  calc (∫ t in Set.Icc (-T) T, f t) + ∫ t in (Set.Icc (-T) T)ᶜ, f t
      ≤ 4 * B + 2 * q / h := add_le_add hmid htail
    _ ≤ 4 * B + 2 * (1 / h + N * Real.log (2 * N)) * q := by linarith
    _ = (4 * KMS + 2) * (1 / h + N * Real.log (2 * N)) * q := by rw [hBdef]; ring

end Erdos821.P5Marked
