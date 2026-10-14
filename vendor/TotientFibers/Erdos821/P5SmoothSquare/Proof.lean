import Erdos821.P5.SmoothEndpointSquareTask
import Erdos821.P5.EndpointPrefix

noncomputable section
open scoped BigOperators
open Filter

namespace Erdos821.P5Ssq
open Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

theorem comparisonSmoothSource_sq_le
    (G : PrimeGroups) (x Y a v lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (hY : 0 < Y) (hL : 1 ≤ L x) (E : Endpoint) (mark : ℕ → ℂ) (M : ℝ)
    (hmark : ∀ n, ‖mark n‖ ≤ L x ^ M) (n : ℕ) :
    ‖comparisonSmoothSource G x Y a v lo hi hlo hhi E mark n‖ ^ 2 ≤
      ((2 / lo) ^ 2 * L x ^ (2 * M)) * ‖endpoint G x E n‖ ^ 2 := by
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  have hcutnorm :
      ‖(comparisonSourceSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    exact comparisonSourceSizeCutoff_norm_le lo hi hlo hhi _
  by_cases hcut : comparisonSourceSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) = 0
  · simp [comparisonSmoothSource, hcut]
    positivity
  · have hsupp := comparisonSourceSizeCutoff_support lo hi hlo hhi
      (Function.mem_support.mpr hcut)
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      simp at hsupp
      linarith [hlo]
    have hnNat : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnNat
    have hratioLower : lo / 2 ≤ (n : ℝ) / Y := hsupp.1
    have hratio : Y / (n : ℝ) ≤ 2 / lo := by
      apply (div_le_iff₀ hnR).2
      have hlow : (lo / 2) * Y ≤ (n : ℝ) := (le_div_iff₀ hY).mp hratioLower
      have hmul : Y * lo ≤ 2 * (n : ℝ) := by nlinarith [hlow]
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hlo).2 hmul
    have hnormEq :
        ‖comparisonSmoothSource G x Y a v lo hi hlo hhi E mark n‖ =
          ‖(comparisonSourceSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ)‖ *
            (|Y| / (n : ℝ) * ‖endpoint G x E n‖ * ‖mark n‖) := by
      rw [comparisonSmoothSource, norm_mul, comparisonMellinSource_norm]
    have hratioAbs : |Y| / (n : ℝ) ≤ 2 / lo := by
      simpa [abs_of_nonneg hY.le] using hratio
    have hnorm :
        ‖comparisonSmoothSource G x Y a v lo hi hlo hhi E mark n‖ ≤
          (2 / lo) * ‖endpoint G x E n‖ * L x ^ M := by
      rw [hnormEq]
      have hinner : |Y| / (n : ℝ) * ‖endpoint G x E n‖ * ‖mark n‖ ≤
          (2 / lo) * ‖endpoint G x E n‖ * L x ^ M := by
        calc
          _ ≤ ((2 / lo) * ‖endpoint G x E n‖) * ‖mark n‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hratioAbs (norm_nonneg _)) (norm_nonneg _)
          _ ≤ ((2 / lo) * ‖endpoint G x E n‖) * L x ^ M :=
            mul_le_mul_of_nonneg_left (hmark n) (by positivity)
          _ = _ := by ring
      calc
        _ ≤ 1 * ((2 / lo) * ‖endpoint G x E n‖ * L x ^ M) := by
          simpa only [one_mul] using
            mul_le_mul hcutnorm hinner (by positivity) (by positivity)
        _ = _ := by ring
    have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
    have hpow : (L x ^ M) ^ 2 = L x ^ (2 * M) := by
      rw [pow_two, ← Real.rpow_add hLpos]
      congr 1
      ring
    calc
      _ ≤ (((2 / lo) * ‖endpoint G x E n‖) * L x ^ M) ^ 2 := by
        simpa only [pow_two] using hsq
      _ = ((2 / lo) ^ 2 * L x ^ (2 * M)) * ‖endpoint G x E n‖ ^ 2 := by
        rw [mul_pow, mul_pow, hpow]
        ring

theorem comparisonSmoothTarget_sq_le
    (G : PrimeGroups) (x Y a lo hi : ℝ) (hlo : 0 < lo) (hhi : lo < hi)
    (hL : 1 ≤ L x) (E : Endpoint) (mark : ℕ → ℂ) (M : ℝ)
    (hmark : ∀ n, ‖mark n‖ ≤ L x ^ M) (n : ℕ) :
    ‖comparisonSmoothTarget G x Y a lo hi hlo hhi E mark n‖ ^ 2 ≤
      (L x ^ (2 * M)) * ‖endpoint G x E n‖ ^ 2 := by
  have hcutnorm :
      ‖(comparisonTargetSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    exact comparisonTargetSizeCutoff_norm_le lo hi hlo hhi _
  have hnormEq :
      ‖comparisonSmoothTarget G x Y a lo hi hlo hhi E mark n‖ =
        ‖(comparisonTargetSizeCutoff lo hi hlo hhi ((n : ℝ) / Y) : ℂ)‖ *
          (‖endpoint G x E n‖ * ‖mark n‖) := by
    rw [comparisonSmoothTarget, norm_mul, comparisonMellinTarget_norm]
  have hnorm :
      ‖comparisonSmoothTarget G x Y a lo hi hlo hhi E mark n‖ ≤
        ‖endpoint G x E n‖ * L x ^ M := by
    rw [hnormEq]
    have hinner : ‖endpoint G x E n‖ * ‖mark n‖ ≤
        ‖endpoint G x E n‖ * L x ^ M :=
      mul_le_mul_of_nonneg_left (hmark n) (norm_nonneg _)
    calc
      _ ≤ 1 * (‖endpoint G x E n‖ * L x ^ M) := by
        simpa only [one_mul] using
          mul_le_mul hcutnorm hinner (by positivity) (by positivity)
      _ = _ := by ring
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  have hpow : (L x ^ M) ^ 2 = L x ^ (2 * M) := by
    rw [pow_two, ← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    _ ≤ (‖endpoint G x E n‖ * L x ^ M) ^ 2 := by
      simpa only [pow_two] using hsq
    _ = (L x ^ (2 * M)) * ‖endpoint G x E n‖ ^ 2 := by
      rw [mul_pow, hpow]
      ring

theorem comparison_interval_subset_prefix (lo hi U : ℝ) (hlo : 1 ≤ lo)
    (hhi : hi ≤ U) :
    Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ ⊆ Finset.Icc 1 ⌊U⌋₊ := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨hnlo, hnhi⟩
  have hceilR : (1 : ℝ) ≤ (⌈lo⌉₊ : ℝ) := hlo.trans (Nat.le_ceil lo)
  have hceil : 1 ≤ ⌈lo⌉₊ := by exact_mod_cast hceilR
  have hfloor : ⌊hi⌋₊ ≤ ⌊U⌋₊ := Nat.floor_mono hhi
  exact Finset.mem_Icc.mpr ⟨hceil.trans hnlo, hnhi.trans hfloor⟩

/-- The two smooth comparison endpoint sequences have uniform fixed-power
square norms. Their supports lie in one fixed multiple of `Y`, where the
endpoint prefix divisor moment with `D = 1` applies. -/
theorem smoothEndpointSquareTask_proof : SmoothEndpointSquareTask := by
  intro P m C τ η lo hi hC hlo hhi
  obtain ⟨M, hmark⟩ := eventual_comparisonMarkedEndpoint_bound P m
  obtain ⟨c, K₀, hc, hK₀, hprefix⟩ := endpoint_square_sum_prefix_multiples
  let B : ℝ := max (2 * hi + lo) (2 * hi + 5 * lo / 4)
  let A : ℝ := max 1 ((2 / lo) ^ 2)
  let H : ℝ := max 1 (2 * B)
  let R : ℝ := Real.log H + 2
  let Ctotal : ℝ := 2 * M + 4 * C + c
  let C₂ : ℝ := max 0 Ctotal
  let K : ℝ := K₀ * B * R ^ c * A
  have hB₁ : 2 * hi + lo ≤ B := le_max_left _ _
  have hB₂ : 2 * hi + 5 * lo / 4 ≤ B := le_max_right _ _
  have hhiPos : 0 < hi := hlo.trans hhi
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hBlo : lo / 4 ≤ B := (by linarith : lo / 4 ≤ 2 * hi + lo).trans hB₁
  have hA₁ : 1 ≤ A := le_max_left _ _
  have hA₂ : (2 / lo) ^ 2 ≤ A := le_max_right _ _
  have hApos : 0 < A := by positivity
  have hH₁ : 1 ≤ H := le_max_left _ _
  have hH₂ : 2 * B ≤ H := le_max_right _ _
  have hHpos : 0 < H := by linarith
  have hRpos : 0 < R := by
    dsimp [R]
    have := Real.log_nonneg hH₁
    linarith
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; exact le_max_left _ _
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (mul_pos hK₀ hBpos)
      (Real.rpow_pos_of_pos hRpos c)) hApos
  refine ⟨C₂, K, hC₂, hK, ?_⟩
  have hlargePower : ∀ᶠ x : ℝ in atTop, 4 / lo ≤ x ^ (0.99 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (0.99 : ℝ))).eventually_ge_atTop (4 / lo)
  filter_upwards [hmark, eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ), hlargePower] with x hxmark hx hxL hxpow
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hL : 1 ≤ L x := hxL
  have hLpos : 0 < L x := lt_of_lt_of_le zero_lt_one hL
  intro G J Q ν block h j χ E Y a v hlo' hhi' hG hE hYlo hYhi
  have hYpos : 0 < Y := by
    have hxpowpos : 0 < x ^ (0.99 : ℝ) := Real.rpow_pos_of_pos hxpos _
    exact hxpowpos.trans_le hYlo
  have hYlarge : 1 ≤ lo / 4 * Y := by
    have hlo4 : 0 ≤ lo / 4 := by positivity
    calc
      1 = (lo / 4) * (4 / lo) := by field_simp [hlo.ne']
      _ ≤ (lo / 4) * x ^ (0.99 : ℝ) := mul_le_mul_of_nonneg_left hxpow hlo4
      _ ≤ (lo / 4) * Y := mul_le_mul_of_nonneg_left hYlo hlo4
  have hU : 1 ≤ B * Y := by
    calc
      1 ≤ lo / 4 * Y := hYlarge
      _ ≤ B * Y := mul_le_mul_of_nonneg_right hBlo hYpos.le
  let U : ℝ := B * Y
  have hUpos : 0 < U := mul_pos hBpos hYpos
  have hY2 : Y ≤ x ^ (2 : ℝ) := by
    exact hYhi.trans (Real.rpow_le_rpow_of_exponent_le hx (by norm_num))
  have hUarg : 2 * U ≤ H * x ^ (2 : ℝ) := by
    dsimp [U]
    calc
      2 * (B * Y) = (2 * B) * Y := by ring
      _ ≤ H * Y := mul_le_mul_of_nonneg_right hH₂ hYpos.le
      _ ≤ H * x ^ (2 : ℝ) := mul_le_mul_of_nonneg_left hY2 (by positivity)
  have hlogU : Real.log (2 * U) ≤ R * L x := by
    have hlog := Real.log_le_log (by positivity : 0 < 2 * U) hUarg
    have hlogRight : Real.log (H * x ^ (2 : ℝ)) = Real.log H + 2 * Real.log x := by
      rw [Real.log_mul hHpos.ne' (Real.rpow_pos_of_pos hxpos _).ne', Real.log_rpow hxpos]
    rw [hlogRight] at hlog
    have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH₁
    have hLlog : 1 ≤ Real.log x := by simpa only [L] using hL
    dsimp [R]
    rw [L]
    nlinarith
  have hlogU_nonneg : 0 ≤ Real.log (2 * U) :=
    Real.log_nonneg (by nlinarith [hU])
  have hlogpow : Real.log (2 * U) ^ c ≤ R ^ c * L x ^ c := by
    calc
      _ ≤ (R * L x) ^ c := Real.rpow_le_rpow hlogU_nonneg hlogU hc
      _ = _ := by rw [Real.mul_rpow hRpos.le hLpos.le]
  have hUge : 1 ≤ U := by change 1 ≤ B * Y; exact hU
  have hUgeCast : ((1 : ℕ) : ℝ) ≤ U := by exact_mod_cast hUge
  have hprefixE := hprefix G x C τ η U E 1 hL hE (by norm_num) hUgeCast (by simp)
  have hprefixE' :
      (∑ n ∈ Finset.Icc 1 ⌊U⌋₊, ‖endpoint G x E n‖ ^ 2) ≤
        K₀ * U * L x ^ (4 * C) * Real.log (2 * U) ^ c := by
    simpa [Nat.one_dvd] using hprefixE
  have hrootsS : comparisonCommonRoots lo hi Y ⊆ Finset.Icc 1 ⌊U⌋₊ := by
    change Finset.Icc ⌈lo / 2 * Y⌉₊ ⌊(2 * hi + lo) * Y⌋₊ ⊆ _
    apply comparison_interval_subset_prefix
    · nlinarith [hYlarge]
    · exact mul_le_mul_of_nonneg_right hB₁ hYpos.le
  have hrootsT :
      Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊ ⊆ Finset.Icc 1 ⌊U⌋₊ := by
    apply comparison_interval_subset_prefix
    · exact hYlarge
    · exact mul_le_mul_of_nonneg_right hB₂ hYpos.le
  have hmarkS (n : ℕ) :
      ‖comparisonMarkedEndpoint ν block true h j χ n‖ ≤ L x ^ M :=
    hxmark G J Q ν block true h j χ n hG
  have hmarkT (n : ℕ) :
      ‖comparisonMarkedEndpoint ν block false h j χ n‖ ≤ L x ^ M :=
    hxmark G J Q ν block false h j χ n hG
  have hcoefS : (2 / lo) ^ 2 * L x ^ (2 * M) ≤ A * L x ^ (2 * M) :=
    mul_le_mul_of_nonneg_right hA₂ (Real.rpow_nonneg hLpos.le _)
  have hcoefT : L x ^ (2 * M) ≤ A * L x ^ (2 * M) :=
    le_mul_of_one_le_left (Real.rpow_nonneg hLpos.le _) hA₁
  have hsumS_nonneg :
      0 ≤ ∑ n ∈ comparisonCommonRoots lo hi Y, ‖endpoint G x E n‖ ^ 2 := by positivity
  have hsumT_nonneg :
      0 ≤ ∑ n ∈ Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊,
        ‖endpoint G x E n‖ ^ 2 := by positivity
  have hsourcePrefix :
      sqNorm (comparisonCommonRoots lo hi Y)
        (comparisonSmoothSource G x Y a v lo hi hlo' hhi' E
          (comparisonMarkedEndpoint ν block true h j χ)) ≤
        A * L x ^ (2 * M) * (∑ n ∈ Finset.Icc 1 ⌊U⌋₊, ‖endpoint G x E n‖ ^ 2) := by
    change (∑ n ∈ comparisonCommonRoots lo hi Y,
        ‖comparisonSmoothSource G x Y a v lo hi hlo' hhi' E
          (comparisonMarkedEndpoint ν block true h j χ) n‖ ^ 2) ≤ _
    calc
      _ ≤ ∑ n ∈ comparisonCommonRoots lo hi Y,
          ((2 / lo) ^ 2 * L x ^ (2 * M)) * ‖endpoint G x E n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact comparisonSmoothSource_sq_le G x Y a v lo hi hlo' hhi'
          hYpos hL E (comparisonMarkedEndpoint ν block true h j χ) M hmarkS n
      _ = ((2 / lo) ^ 2 * L x ^ (2 * M)) *
          ∑ n ∈ comparisonCommonRoots lo hi Y, ‖endpoint G x E n‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ A * L x ^ (2 * M) *
          ∑ n ∈ comparisonCommonRoots lo hi Y, ‖endpoint G x E n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefS hsumS_nonneg
      _ ≤ A * L x ^ (2 * M) *
          ∑ n ∈ Finset.Icc 1 ⌊U⌋₊, ‖endpoint G x E n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hrootsS (by intros; positivity)
  have htargetPrefix :
      sqNorm (Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊)
        (comparisonSmoothTarget G x Y a lo hi hlo' hhi' E
          (comparisonMarkedEndpoint ν block false h j χ)) ≤
        A * L x ^ (2 * M) * (∑ n ∈ Finset.Icc 1 ⌊U⌋₊, ‖endpoint G x E n‖ ^ 2) := by
    change (∑ n ∈ Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊,
        ‖comparisonSmoothTarget G x Y a lo hi hlo' hhi' E
          (comparisonMarkedEndpoint ν block false h j χ) n‖ ^ 2) ≤ _
    calc
      _ ≤ ∑ n ∈ Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊,
          L x ^ (2 * M) * ‖endpoint G x E n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact comparisonSmoothTarget_sq_le G x Y a lo hi hlo' hhi' hL E
          (comparisonMarkedEndpoint ν block false h j χ) M hmarkT n
      _ = L x ^ (2 * M) *
          ∑ n ∈ Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊,
            ‖endpoint G x E n‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ A * L x ^ (2 * M) *
          ∑ n ∈ Finset.Icc ⌈lo / 4 * Y⌉₊ ⌊(2 * hi + 5 * lo / 4) * Y⌋₊,
            ‖endpoint G x E n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefT hsumT_nonneg
      _ ≤ A * L x ^ (2 * M) *
          ∑ n ∈ Finset.Icc 1 ⌊U⌋₊, ‖endpoint G x E n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hrootsT (by intros; positivity)
  have hcommonBound :
      A * L x ^ (2 * M) * (K₀ * U * L x ^ (4 * C) * Real.log (2 * U) ^ c) ≤
        K * Y * L x ^ C₂ := by
    have hpowtotal : L x ^ (2 * M) * L x ^ (4 * C) * L x ^ c = L x ^ Ctotal := by
      calc
        _ = L x ^ (2 * M + 4 * C) * L x ^ c := by rw [← Real.rpow_add hLpos]
        _ = L x ^ (2 * M + 4 * C + c) := by rw [← Real.rpow_add hLpos]
        _ = _ := by simp [Ctotal]
    calc
      _ ≤ A * L x ^ (2 * M) * (K₀ * U * L x ^ (4 * C) * (R ^ c * L x ^ c)) := by
        calc
          _ = (A * L x ^ (2 * M) * (K₀ * U * L x ^ (4 * C))) *
              Real.log (2 * U) ^ c := by ring
          _ ≤ (A * L x ^ (2 * M) * (K₀ * U * L x ^ (4 * C))) *
              (R ^ c * L x ^ c) :=
            mul_le_mul_of_nonneg_left hlogpow (by positivity)
          _ = _ := by ring
      _ = K * Y * L x ^ Ctotal := by
        rw [show K = K₀ * B * R ^ c * A by rfl, show U = B * Y by rfl,
          ← hpowtotal]
        ring
      _ ≤ K * Y * L x ^ C₂ := by
        apply mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL (le_max_right 0 Ctotal))
        positivity
  constructor
  · exact hsourcePrefix.trans (mul_le_mul_of_nonneg_left hprefixE' (by positivity)) |>.trans hcommonBound
  · exact htargetPrefix.trans (mul_le_mul_of_nonneg_left hprefixE' (by positivity)) |>.trans hcommonBound

end Erdos821.P5Ssq
