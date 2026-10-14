import Erdos408.BlockSieve
import Erdos408.Extraction.Allocation
import Erdos408.Extraction.Sieve.Budget
import Erdos408.Extraction.TypeII

/-!
# The smoothed rectangle statistic

Steps E0–E3 and E9–E11 of the blueprint. For slots with margin `c T⁻²⁰`,
coefficients `|𝔟| ≤ 1`, and cutoffs `Φ` in the class,

  `(L / x) |∑_p Φ((p - 1)/x) (f_𝔟(p - 1) - C_𝔟)| ≤ C T⁻³⁰⁰`.

* E0. Split `𝔟 = 𝔟⁺ - 𝔟⁻` into nonnegative parts. Then `C_𝔟 ≤ T⁴` and
  `|f_𝔟| ≤ T⁶¹` on `n ≤ x²` (`Sieve.eventually_slot_size`).
* E1. The progression lemma for the inert polynomial
  (`Sieve.eventually_progression`): at level `r ≤ x^{ε/4}`,
  `∑_r |∑_{r ∣ u+1} Φ(u/x) f_𝔟(u) H(u) - (x/r) I C_𝔟 M_x(H)|` is `O(x / L²)`
  for every `|H| ≤ 1` determined by the band primes, with the cutoff mass
  `I = x⁻¹ ∑_{u ≤ κ x} Φ(u/x)`. In each progression the band set of `u` has
  the law of the independent divisor model `M_x`, by `BlockSieve` on each
  fiber and Rankin's bound for large band parts (`Sieve.Kubilius`).
* E2. Presieve with `BlockSieve` at depth `h` on the weights `Φ P f_𝔟` and
  `Φ P` (`Sieve.eventually_presieve`). The main terms cancel; the relative
  error is `O(e^{-h} γ⁻¹) C_𝔟 = O(T²⁶ e^{-h})`.
* E3. In the surviving `z`-rough `u + 1`, discard nonsquarefree `u + 1`
  (`O(x/z)`) and `ω(u + 1) > J_c` (Rankin, `O(T⁴⁴ 2^{-J_c} x / L)`) in
  `Sieve.eventually_composite`. The rest is `∑_{2 ≤ j ≤ J_c} Comp_j / j!`,
  which is `eventually_compositeSum_sub_proxySum` plus
  `eventually_abs_proxySum_le`.
* E9–E10. This gives the statistic weighted by `P`. Remove `P` by the upper
  sieve (`BlockSieve` at `h = 2`) on `1 - P` (`Sieve.eventually_mark_removal`),
  whose divisor-model mean is `≤ K exp(-N / (12 e))`.
* E11. With `h = 2 ⌈200 s⌉`, `J_c = ⌈1001 s⌉` and `N = ⌈30000 s⌉` bands per
  cluster, every error is `≤ T⁻³⁰⁰` (`Sieve.final_budget`).
-/

namespace Erdos408

open Filter Real Finset Sieve

/-- The statistic for coefficients `0 ≤ 𝔟 ≤ 1`, with the parameters `q = 1/2`,
`c_w = 1/12`, `K = max K₀ 1`, `C_h = 200`, `C_j = 1001` and `C_N = 30000 K`. -/
lemma eventually_smooth_rectangle_nonneg (h₁ : OneSidedTypeII) (h₂ : TwoSidedCorrelation)
    (h₃ : BlockSieve) (c κ CΦ : ℝ) (M : ℕ → ℝ) (hc : 0 < c) (hκ : 1 < κ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (Φ : ℝ → ℝ),
        AdmissibleSlots c x u v → (∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) → IsCutoff κ CΦ M x Φ →
        Real.log x / x *
            |∑ p ∈ primesIcc 2 (κ * x + 1),
              Φ (((p : ℝ) - 1) / x) * (slotCount x u v B (p - 1) - slotMean x u v B)| ≤
          7 * (logLog x ^ 300)⁻¹ := by
  obtain ⟨K₀, hK₀⟩ := eventually_compositeSum_sub_proxySum h₁ (1 / 2) (1 / 12) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  set K := max K₀ 1
  have hK : 1 ≤ K := le_max_right _ _
  obtain ⟨C₁, c₁, hc₁, hTII⟩ := hK₀ K (le_max_left _ _) (30000 * K) c 200 1001 κ CΦ M hc hκ
  obtain ⟨C₂, c₂, hc₂, hAll⟩ := eventually_abs_proxySum_le h₂ (1 / 2) (1 / 12) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) K (30000 * K) c 200 1001 κ CΦ M hK hc hκ
  obtain ⟨C₁₀, h10⟩ := eventually_mark_removal h₃ hK (30000 * K) (CΦ := CΦ) M hc
    (by norm_num : (0 : ℝ) < 200) hκ
  obtain ⟨CP, hpre⟩ := eventually_presieve h₃ hK (30000 * K) (CΦ := CΦ) M hc
    (by norm_num : (0 : ℝ) < 200) hκ
  obtain ⟨C₃, htail⟩ := eventually_composite h₃ hK (30000 * K) (CΦ := CΦ) M 1001 hc
    (by norm_num : (0 : ℝ) < 200) hκ
  filter_upwards [hTII, hAll, h10, hpre, htail, eventually_savings hK hc (lt_min hc₁ hc₂),
    eventually_slot_size hc, eventually_inertPoly_mem hK (30000 * K),
    tendsto_logLog.eventually_ge_atTop (|CP| + |C₃| + (|C₁| + |C₂|) + |C₁₀| + 2),
    eventually_ge_atTop (κ + 1), tendsto_log_atTop.eventually_ge_atTop 1]
    with x hTIIx hAllx h10x hprex htailx ⟨hT, heh, hj2, he1, hiL, hLz, hLc, hJ⟩ hsize hP hTC
      hxκ hL k hk u v B Φ hslot hB hΦ
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hB' : ∀ Q, |B Q| ≤ 1 := fun Q => by rw [abs_le]; constructor <;> linarith [hB Q]
  set T := logLog x
  set J := compositeCutoff 1001 x
  set Pw := inertPoly (1 / 2) (1 / 12) K (30000 * K) x
  set c' := min c₁ c₂
  set C₁₂ := |C₁| + |C₂|
  -- E4–E8: each composite sum is `O((x / L) L^{-c'})`
  have hcomp : ∀ j ∈ Icc 2 J, |((j.factorial : ℝ))⁻¹ *
      compositeSum (1 / 2) (1 / 12) K (30000 * K) x (presieveExponent c 200 x) κ j Φ u v B| ≤
      C₁₂ * (x / Real.log x * Real.log x ^ (-c')) := by
    intro j hj
    obtain ⟨hj2', hjJ⟩ := mem_Icc.1 hj
    have h1 := hTIIx k hk u v B Φ j hslot hB hΦ hj2' hjJ
    have h2 := hAllx k hk u v B Φ j hslot hB hΦ hj2' hjJ
    have hLc₁ : Real.log x ^ (-c₁) ≤ Real.log x ^ (-c') :=
      rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_left _ _))
    have hLc₂ : Real.log x ^ (-c₂) ≤ Real.log x ^ (-c') :=
      rpow_le_rpow_of_exponent_le hL (neg_le_neg (min_le_right _ _))
    have hpos : 0 ≤ x / Real.log x := by positivity
    have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hf1 : (1 : ℝ) ≤ j.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
    have hfi : ((j.factorial : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hf1
    rw [abs_mul, abs_of_pos (inv_pos.2 hf)]
    set Comp := compositeSum (1 / 2) (1 / 12) K (30000 * K) x (presieveExponent c 200 x) κ j Φ u v B
    set Prox := proxySum (1 / 2) (1 / 12) K (30000 * K) x (presieveExponent c 200 x) κ j Φ u v B
    have h3 : |Comp| ≤ C₁₂ * (x / Real.log x * Real.log x ^ (-c')) := by
      have e1 : C₁ * (x / Real.log x) * Real.log x ^ (-c₁) ≤
          |C₁| * (x / Real.log x * Real.log x ^ (-c')) := by
        rw [mul_assoc]
        exact mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left hLc₁ hpos) (by positivity)
          (abs_nonneg _)
      have e2 : C₂ * (x / Real.log x) * Real.log x ^ (-c₂) ≤
          |C₂| * (x / Real.log x * Real.log x ^ (-c')) := by
        rw [mul_assoc]
        exact mul_le_mul (le_abs_self _) (mul_le_mul_of_nonneg_left hLc₂ hpos) (by positivity)
          (abs_nonneg _)
      have e3 := abs_sub_abs_le_abs_sub Comp Prox
      simp only [C₁₂]
      linarith
    calc (j.factorial : ℝ)⁻¹ * |Comp| ≤ 1 * |Comp| := mul_le_mul_of_nonneg_right hfi (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h3
  have hcompsum : |∑ j ∈ Icc 2 J, ((j.factorial : ℝ))⁻¹ *
      compositeSum (1 / 2) (1 / 12) K (30000 * K) x (presieveExponent c 200 x) κ j Φ u v B| ≤
      x / Real.log x * (J * (C₁₂ * Real.log x ^ (-c'))) := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hcomp).trans ?_)
    rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : ((J + 1 - 2 : ℕ) : ℝ) ≤ J := by exact_mod_cast (by omega : J + 1 - 2 ≤ J)
    have : 0 ≤ C₁₂ * (x / Real.log x * Real.log x ^ (-c')) := by positivity
    calc ((J + 1 - 2 : ℕ) : ℝ) * (C₁₂ * (x / Real.log x * Real.log x ^ (-c')))
        ≤ J * (C₁₂ * (x / Real.log x * Real.log x ^ (-c'))) :=
          mul_le_mul_of_nonneg_right hcard this
      _ = _ := by ring
  -- E10: the mark removal
  have hfC : ∀ p ∈ primesIcc 2 (κ * x + 1),
      |slotCount x u v B (p - 1) - slotMean x u v B| ≤ T ^ 62 := by
    intro p hp
    obtain ⟨hpp, hpY⟩ := mem_primesIcc_two.1 hp
    have hp2 := hpp.two_le
    have hpx : ((p - 1 : ℕ) : ℝ) ≤ x ^ 2 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      nlinarith
    have h1 := (hsize k hk u v B hslot hB').1 (p - 1) (by omega) hpx
    have h2 := (hsize k hk u v B hslot hB').2
    have h61 : T ^ 4 ≤ T ^ 61 := pow_le_pow_right₀ hT (by norm_num)
    have h62 : 2 * T ^ 61 ≤ T ^ 62 := by
      have : T ^ 62 = T ^ 61 * T := pow_succ T 61
      have hT2 : (2 : ℝ) ≤ T := by
        have := abs_nonneg CP
        have := abs_nonneg C₃
        have := abs_nonneg C₁₀
        have := abs_nonneg C₁
        have := abs_nonneg C₂
        linarith
      have hT61 : 0 ≤ T ^ 61 := by positivity
      nlinarith
    calc _ ≤ |slotCount x u v B (p - 1)| + |slotMean x u v B| := abs_sub _ _
      _ ≤ T ^ 62 := by linarith
  have hR : |∑ p ∈ primesIcc 2 (κ * x + 1),
      Φ (((p : ℝ) - 1) / x) * (1 - Pw (p - 1)) * (slotCount x u v B (p - 1) - slotMean x u v B)| ≤
      x / Real.log x * (T ^ 62 * (C₁₀ * (T ^ 22 *
        exp (-(inertPerCluster K (30000 * K) x / (12 * exp 1))) + 1 / Real.log x))) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ p ∈ primesIcc 2 (κ * x + 1), |Φ (((p : ℝ) - 1) / x) * (1 - Pw (p - 1)) *
        (slotCount x u v B (p - 1) - slotMean x u v B)| ≤
        T ^ 62 * (Φ (((p : ℝ) - 1) / x) * (1 - Pw (p - 1))) := by
      intro p hp
      have h0 : 0 ≤ Φ (((p : ℝ) - 1) / x) * (1 - Pw (p - 1)) :=
        mul_nonneg (hΦ.2.1 _) (by linarith [(hP (p - 1)).2])
      rw [abs_mul, abs_of_nonneg h0, mul_comm]
      exact mul_le_mul_of_nonneg_right (hfC p hp) h0
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum]
    calc T ^ 62 * ∑ p ∈ primesIcc 2 (κ * x + 1), Φ (((p : ℝ) - 1) / x) * (1 - Pw (p - 1))
        ≤ T ^ 62 * (C₁₀ * (x / Real.log x) * (T ^ 22 *
          exp (-(inertPerCluster K (30000 * K) x / (12 * exp 1))) + 1 / Real.log x)) :=
          mul_le_mul_of_nonneg_left (h10x Φ hΦ) (by positivity)
      _ = _ := by ring
  -- E2 and E3
  have hpre' := hprex k hk u v B Φ hslot hB hΦ
  have htail' := htailx k hk u v B Φ hslot hB' hΦ
  set S₀ := presieved κ x (x ^ presieveExponent c 200 x)
    (fun m => Φ (m / x) * endpoint (1 / 2) (1 / 12) K (30000 * K) x u v B m)
  set Sc := ∑ j ∈ Icc 2 J, ((j.factorial : ℝ))⁻¹ *
    compositeSum (1 / 2) (1 / 12) K (30000 * K) x (presieveExponent c 200 x) κ j Φ u v B
  set A := ∑ p ∈ primesIcc 2 (κ * x + 1),
    Φ (((p : ℝ) - 1) / x) * endpoint (1 / 2) (1 / 12) K (30000 * K) x u v B (p - 1)
  set R := ∑ p ∈ primesIcc 2 (κ * x + 1),
    Φ (((p : ℝ) - 1) / x) * (1 - Pw (p - 1)) * (slotCount x u v B (p - 1) - slotMean x u v B)
  have hdec : ∑ p ∈ primesIcc 2 (κ * x + 1),
      Φ (((p : ℝ) - 1) / x) * (slotCount x u v B (p - 1) - slotMean x u v B) =
      (S₀ - (S₀ - A - Sc) - Sc) + R := by
    have : A + R = ∑ p ∈ primesIcc 2 (κ * x + 1),
        Φ (((p : ℝ) - 1) / x) * (slotCount x u v B (p - 1) - slotMean x u v B) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun p _ => ?_
      simp only [endpoint, Pw]
      ring
    rw [← this]
    ring
  rw [hdec]
  have hbound : |(S₀ - (S₀ - A - Sc) - Sc) + R| ≤ x / Real.log x *
      (CP * (T ^ 4 * T ^ 22 * exp (-(sieveDepth 200 x : ℝ)) + T ^ 4 * (1 / Real.log x)) +
        C₃ * (T ^ 62 * (Real.log x / x ^ presieveExponent c 200 x) +
          T ^ 62 * T ^ 44 * ((2 : ℝ) ^ J)⁻¹) +
        J * (C₁₂ * Real.log x ^ (-c')) + T ^ 62 * (C₁₀ * (T ^ 22 *
          exp (-(inertPerCluster K (30000 * K) x / (12 * exp 1))) + 1 / Real.log x))) := by
    have h1 : |(S₀ - (S₀ - A - Sc) - Sc) + R| ≤ |S₀| + |S₀ - A - Sc| + |Sc| + |R| := by
      have := abs_add_le (S₀ - (S₀ - A - Sc) - Sc) R
      have := abs_sub (S₀ - (S₀ - A - Sc)) Sc
      have := abs_sub S₀ (S₀ - A - Sc)
      linarith
    have e1 : CP * (x / Real.log x) * (T ^ 4 * T ^ 22 * exp (-(sieveDepth 200 x : ℝ)) +
        T ^ 4 * (1 / Real.log x)) = x / Real.log x * (CP * (T ^ 4 * T ^ 22 *
          exp (-(sieveDepth 200 x : ℝ)) + T ^ 4 * (1 / Real.log x))) := by ring
    have e2 : C₃ * (x / Real.log x) * (T ^ 62 * (Real.log x / x ^ presieveExponent c 200 x) +
        T ^ 62 * T ^ 44 * ((2 : ℝ) ^ J)⁻¹) = x / Real.log x * (C₃ * (T ^ 62 *
          (Real.log x / x ^ presieveExponent c 200 x) + T ^ 62 * T ^ 44 * ((2 : ℝ) ^ J)⁻¹)) := by
      ring
    rw [e1] at hpre'
    rw [e2] at htail'
    rw [mul_add, mul_add, mul_add]
    linarith
  have hfin := final_budget hT (exp_pos _).le heh (by positivity) hiL (by positivity) hLz
    (by positivity) hj2 (exp_pos _).le he1 (by positivity) hLc hJ
    (by linarith [abs_nonneg CP, abs_nonneg C₃, abs_nonneg C₁₀, abs_nonneg C₁, abs_nonneg C₂])
    (by linarith [abs_nonneg CP, abs_nonneg C₃, abs_nonneg C₁₀, abs_nonneg C₁, abs_nonneg C₂])
    (by rw [abs_of_nonneg (by positivity)]; linarith [abs_nonneg CP, abs_nonneg C₃,
      abs_nonneg C₁₀])
    (by positivity)
    (by linarith [abs_nonneg CP, abs_nonneg C₃, abs_nonneg C₁₀, abs_nonneg C₁, abs_nonneg C₂])
    (C₂ := CP) (C₃ := C₃) (C₁₂ := C₁₂) (C₁₀ := C₁₀)
  calc Real.log x / x * |(S₀ - (S₀ - A - Sc) - Sc) + R|
      ≤ Real.log x / x * (x / Real.log x * _) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by field_simp
    _ ≤ 7 * (T ^ 300)⁻¹ := hfin

/-- The smoothed rectangle statistic. -/
theorem eventually_smooth_rectangle (h₁ : OneSidedTypeII) (h₂ : TwoSidedCorrelation)
    (c κ CΦ : ℝ) (M : ℕ → ℝ) (hc : 0 < c) (hκ : 1 < κ) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ k ≤ 2, ∀ (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ) (Φ : ℝ → ℝ),
        AdmissibleSlots c x u v → (∀ Q, |B Q| ≤ 1) → IsCutoff κ CΦ M x Φ →
        Real.log x / x *
            |∑ p ∈ primesIcc 2 (κ * x + 1),
              Φ (((p : ℝ) - 1) / x) * (slotCount x u v B (p - 1) - slotMean x u v B)| ≤
          C * logLog x ^ (-300 : ℝ) := by
  refine ⟨14, ?_⟩
  filter_upwards [eventually_smooth_rectangle_nonneg h₁ h₂ blockSieve c κ CΦ M hc hκ,
    tendsto_logLog.eventually_gt_atTop 0, eventually_ge_atTop 1]
    with x hx hT hx1 k hk u v B Φ hslot hB hΦ
  -- E0: split `𝔟 = 𝔟⁺ - 𝔟⁻` into nonnegative parts
  set B₁ : (Fin k → ℕ) → ℝ := fun Q => max (B Q) 0
  set B₂ : (Fin k → ℕ) → ℝ := fun Q => max (-B Q) 0
  have hB₁ : ∀ Q, 0 ≤ B₁ Q ∧ B₁ Q ≤ 1 := fun Q =>
    ⟨le_max_right _ _, max_le (le_abs_self _ |>.trans (hB Q)) zero_le_one⟩
  have hB₂ : ∀ Q, 0 ≤ B₂ Q ∧ B₂ Q ≤ 1 := fun Q =>
    ⟨le_max_right _ _, max_le (neg_le_abs _ |>.trans (hB Q)) zero_le_one⟩
  have hBeq : B = fun Q => B₁ Q - B₂ Q := funext fun Q => (max_zero_sub_max_neg_zero_eq_self _).symm
  have hsplit : ∑ p ∈ primesIcc 2 (κ * x + 1),
      Φ (((p : ℝ) - 1) / x) * (slotCount x u v B (p - 1) - slotMean x u v B) =
      ∑ p ∈ primesIcc 2 (κ * x + 1),
        Φ (((p : ℝ) - 1) / x) * (slotCount x u v B₁ (p - 1) - slotMean x u v B₁) -
      ∑ p ∈ primesIcc 2 (κ * x + 1),
        Φ (((p : ℝ) - 1) / x) * (slotCount x u v B₂ (p - 1) - slotMean x u v B₂) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [hBeq, slotCount_sub, slotMean_sub]
    ring
  have h1 := hx k hk u v B₁ Φ hslot hB₁ hΦ
  have h2 := hx k hk u v B₂ Φ hslot hB₂ hΦ
  have hLx : 0 ≤ Real.log x / x := div_nonneg (Real.log_nonneg hx1) (by linarith)
  rw [rpow_neg hT.le, show (300 : ℝ) = ((300 : ℕ) : ℝ) by norm_num, rpow_natCast, hsplit]
  calc Real.log x / x * |_ - _| ≤ Real.log x / x * (|_| + |_|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hLx
    _ ≤ 7 * (logLog x ^ 300)⁻¹ + 7 * (logLog x ^ 300)⁻¹ := by rw [mul_add]; linarith
    _ = 14 * (logLog x ^ 300)⁻¹ := by ring

end Erdos408
