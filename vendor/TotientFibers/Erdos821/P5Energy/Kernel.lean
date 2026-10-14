import Erdos821.P5Energy.Additive

/-! Derivative bounds for the dilated Fourier amplitude and the resulting decay of the
`u`-Fourier transform of the compact Mellin amplitude product. -/

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap Nat
open MeasureTheory

namespace Erdos821.P5Energy
open Blueprint.Analytic

/-- The dilated amplitude `u ↦ K̂(c e^{-u})`. -/
def amp (c u : ℝ) : ℂ := localKernelFourier (c * Real.exp (-u))

theorem amp_contDiff (c : ℝ) : ContDiff ℝ ∞ (amp c) := by
  unfold amp
  exact localKernelFourier_contDiff.comp (by fun_prop)

theorem localKernelFourier_iter_bound (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ i ≤ 2, ∀ ξ : ℝ,
    ‖iteratedFDeriv ℝ i localKernelFourier ξ‖ ≤ C / (1 + |ξ|) ^ N := by
  obtain ⟨C0, hC0, h0⟩ := localKernelFourier_iterated_decay 0 N
  obtain ⟨C1, hC1, h1⟩ := localKernelFourier_iterated_decay 1 N
  obtain ⟨C2, hC2, h2⟩ := localKernelFourier_iterated_decay 2 N
  refine ⟨C0 + C1 + C2, by positivity, ?_⟩
  intro i hi ξ
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hp : 0 < (1 + |ξ|) ^ N := by positivity
  interval_cases i
  · exact (h0 ξ).trans (div_le_div_of_nonneg_right (by linarith) hp.le)
  · exact (h1 ξ).trans (div_le_div_of_nonneg_right (by linarith) hp.le)
  · exact (h2 ξ).trans (div_le_div_of_nonneg_right (by linarith) hp.le)

theorem iteratedDeriv_scaled_exp (c : ℝ) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (fun u : ℝ => c * Real.exp (-u)) u = c * ((-1) ^ k * Real.exp (-u)) := by
  have heq : (fun u : ℝ => c * Real.exp (-u)) = fun u => c * Real.exp ((-1) * u) := by
    funext x; congr 2; ring
  rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  ring_nf

theorem amp_iter_bound (N : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ i ≤ 2, ∀ c u : ℝ,
    ‖iteratedFDeriv ℝ i (amp c) u‖ ≤ B / (1 + |c * Real.exp (-u)|) ^ N := by
  obtain ⟨C, hC, hbound⟩ := localKernelFourier_iter_bound (N + 2)
  refine ⟨2 * C, by positivity, ?_⟩
  intro i hi c u
  set x : ℝ := c * Real.exp (-u) with hx
  set D : ℝ := 1 + |x| with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith [abs_nonneg x]
  have hDpos : 0 < D := by linarith
  have hf : ContDiff ℝ ∞ (fun u : ℝ => c * Real.exp (-u)) := by fun_prop
  have hcomp := norm_iteratedFDeriv_comp_le (g := localKernelFourier)
    (f := fun u : ℝ => c * Real.exp (-u)) (n := i) localKernelFourier_contDiff hf
    (by exact_mod_cast le_top) u (C := C / D ^ (N + 2)) (D := D)
    (fun k hk => by simpa [hD, hx] using hbound k (hk.trans hi) x)
    (fun k hk1 hk2 => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_scaled_exp]
      have hnorm : ‖c * ((-1) ^ k * Real.exp (-u))‖ = |x| := by
        rw [hx, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [hnorm]
      calc |x| ≤ D := by rw [hD]; linarith
        _ ≤ D ^ k := le_self_pow₀ hD1 (by omega))
  have hamp : amp c = localKernelFourier ∘ (fun u : ℝ => c * Real.exp (-u)) := rfl
  rw [hamp]
  refine hcomp.trans ?_
  have hfact : (i ! : ℝ) ≤ 2 := by
    interval_cases i <;> norm_num [Nat.factorial]
  have hpowi : D ^ i ≤ D ^ 2 := pow_le_pow_right₀ hD1 hi
  have hsplit : D ^ (N + 2) = D ^ N * D ^ 2 := pow_add D N 2
  have hDN : 0 < D ^ N := pow_pos hDpos N
  have hD2 : 0 < D ^ 2 := pow_pos hDpos 2
  calc (i ! : ℝ) * (C / D ^ (N + 2)) * D ^ i ≤ 2 * (C / D ^ (N + 2)) * D ^ 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hfact (by positivity)) hpowi
          (by positivity) (by positivity)
    _ = 2 * C / D ^ N := by
        rw [hsplit]; field_simp

/-- On `u ≤ 2` the dilation `e^{-u}` is bounded below, giving decay in the scale `c`. -/
theorem amp_iter_bound_le_two (N : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ i ≤ 2, ∀ c u : ℝ, u ≤ 2 →
    ‖iteratedFDeriv ℝ i (amp c) u‖ ≤ B / (1 + |c|) ^ N := by
  obtain ⟨B, hB, hbound⟩ := amp_iter_bound N
  refine ⟨B * Real.exp 2 ^ N, by positivity, ?_⟩
  intro i hi c u hu
  refine (hbound i hi c u).trans ?_
  have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  have heu : Real.exp u ≤ Real.exp 2 := Real.exp_le_exp.mpr hu
  have he1 : 1 ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2; linarith
  have hcx : 1 + |c| ≤ Real.exp 2 * (1 + |c * Real.exp (-u)|) := by
    have hc : |c| = |c * Real.exp (-u)| * Real.exp u := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc, he, mul_one]
    rw [hc]
    have h0 : 0 ≤ |c * Real.exp (-u)| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left heu h0]
  have hpos : 0 < 1 + |c * Real.exp (-u)| := by positivity
  have hpow : (1 + |c|) ^ N ≤ Real.exp 2 ^ N * (1 + |c * Real.exp (-u)|) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcx N
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc B * (1 + |c|) ^ N ≤ B * (Real.exp 2 ^ N * (1 + |c * Real.exp (-u)|) ^ N) :=
        mul_le_mul_of_nonneg_left hpow hB.le
    _ = B * Real.exp 2 ^ N * (1 + |c * Real.exp (-u)|) ^ N := by ring

/-- Binomial bookkeeping for second-order Leibniz bounds. -/
theorem choose_sum_bound {n : ℕ} (hn : n ≤ 2) (a b : ℕ → ℝ) (A B : ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i) (ha : ∀ i ≤ n, a i ≤ A) (hb : ∀ i ≤ n, b i ≤ B) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i * b (n - i) ≤ 4 * A * B := by
  have hA : 0 ≤ A := (ha0 0).trans (ha 0 (Nat.zero_le _))
  have hB : 0 ≤ B := (hb0 0).trans (hb 0 (Nat.zero_le _))
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a i * b (n - i)
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        apply mul_le_mul (mul_le_mul_of_nonneg_left (ha i hi') (by positivity))
          (hb (n - i) (Nat.sub_le n i)) (hb0 _) (by positivity)
    _ = (2 : ℝ) ^ n * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        have := Nat.sum_range_choose n
        exact_mod_cast this
    _ ≤ 4 * A * B := by
        have : (2 : ℝ) ^ n ≤ 4 := by
          calc (2 : ℝ) ^ n ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hn
            _ = 4 := by norm_num
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hA) hB

theorem mul_iter_bound {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (u : ℝ)
    {A B : ℝ} (hA : ∀ i ≤ 2, ‖iteratedFDeriv ℝ i f u‖ ≤ A)
    (hB : ∀ i ≤ 2, ‖iteratedFDeriv ℝ i g u‖ ≤ B) :
    ∀ n ≤ 2, ‖iteratedFDeriv ℝ n (fun y => f y * g y) u‖ ≤ 4 * A * B := by
  intro n hn
  refine (norm_iteratedFDeriv_mul_le hf hg u (by exact_mod_cast le_top)).trans ?_
  exact choose_sum_bound hn (fun i => ‖iteratedFDeriv ℝ i f u‖)
    (fun i => ‖iteratedFDeriv ℝ i g u‖) A B (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun i hi => hA i (hi.trans hn)) (fun i hi => hB i (hi.trans hn))

/-- Iterated derivatives vanish off a closed interval containing the support. -/
theorem iteratedFDeriv_eq_zero_of_notMem {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Set.Icc (-2) 2) (i : ℕ) {u : ℝ} (hu : u ∉ Set.Icc (-2 : ℝ) 2) :
    iteratedFDeriv ℝ i g u = 0 := by
  have hts : tsupport g ⊆ Set.Icc (-2) 2 := closure_minimal hsupp isClosed_Icc
  by_contra hne
  exact hu (hts (support_iteratedFDeriv_subset i (Function.mem_support.mpr hne)))

theorem iteratedDeriv_eq_zero_of_notMem {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Set.Icc (-2) 2) (i : ℕ) {u : ℝ} (hu : u ∉ Set.Icc (-2 : ℝ) 2) :
    iteratedDeriv i g u = 0 := by
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedFDeriv_eq_zero_of_notMem hsupp i hu, norm_zero]

/-- The Fourier transform of a function supported in `[-2,2]` and bounded by `A`. -/
theorem norm_fourier_le_of_support {f : ℝ → ℂ} (hsupp : ∀ u ∉ Set.Icc (-2 : ℝ) 2, f u = 0)
    {A : ℝ} (hA : ∀ u, ‖f u‖ ≤ A) (η : ℝ) : ‖𝓕 f η‖ ≤ 4 * A := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-2 : ℝ) 2)
    (fun u hu => by simp [hsupp u hu])]
  have hfin : volume (Set.Icc (-2 : ℝ) 2) < ⊤ := by simp [Real.volume_Icc]
  refine (norm_setIntegral_le_of_norm_le_const hfin (C := A) (fun u _ => ?_)).trans ?_
  · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact hA u
  · have : volume.real (Set.Icc (-2 : ℝ) 2) = 4 := by
      simp [Measure.real, Real.volume_Icc]; norm_num
    rw [this]; linarith

/-- Two integrations by parts: decay of the Fourier transform of a compactly supported `C²`
function, quantified by sup bounds of its derivatives of order at most two. -/
theorem fourier_decay_of_compact {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hsupp : Function.support g ⊆ Set.Icc (-2) 2) {A : ℝ}
    (hA : ∀ i ≤ 2, ∀ u, ‖iteratedFDeriv ℝ i g u‖ ≤ A) (η : ℝ) :
    (1 + (2 * Real.pi * η) ^ 2) * ‖𝓕 g η‖ ≤ 8 * A := by
  have hzero : ∀ n : ℕ, ∀ u ∉ Set.Icc (-2 : ℝ) 2, iteratedDeriv n g u = 0 :=
    fun n u hu => iteratedDeriv_eq_zero_of_notMem hsupp n hu
  have hbd : ∀ n ≤ 2, ∀ u, ‖iteratedDeriv n g u‖ ≤ A := by
    intro n hn u
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hA n hn u
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n g) := by
    intro n
    apply Continuous.integrable_of_hasCompactSupport
    · exact hg.continuous_iteratedDeriv n (by exact_mod_cast le_top)
    · apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      intro u hu
      by_contra hnot
      exact hu (hzero n u hnot)
  have h0 : ‖𝓕 g η‖ ≤ 4 * A := by
    have := norm_fourier_le_of_support (f := iteratedDeriv 0 g) (hzero 0) (hbd 0 (by norm_num)) η
    simpa using this
  have h2 : ‖𝓕 (iteratedDeriv 2 g) η‖ ≤ 4 * A :=
    norm_fourier_le_of_support (hzero 2) (hbd 2 le_rfl) η
  have hF := Real.fourier_iteratedDeriv (f := g) (N := 2) (n := 2) (hg.of_le (by exact_mod_cast le_top))
    (fun n _ => hint n) le_rfl
  rw [hF] at h2
  have hnorm : ‖(2 * (Real.pi : ℂ) * Complex.I * (η : ℂ)) ^ 2 • 𝓕 g η‖ =
      (2 * Real.pi * η) ^ 2 * ‖𝓕 g η‖ := by
    rw [norm_smul, norm_pow]
    congr 1
    have : ‖2 * (Real.pi : ℂ) * Complex.I * (η : ℂ)‖ = |2 * Real.pi * η| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      simp
    rw [this, sq_abs]
  simp only at h2
  rw [hnorm] at h2
  nlinarith

/-- The compact amplitude product whose `u`-Fourier transform is the Mellin kernel. -/
def gfun (c c' u : ℝ) : ℂ := logCompactWeight u * (amp c u * (starRingEnd ℂ) (amp c' u))

theorem conj_amp_eq (c : ℝ) :
    (fun u => (starRingEnd ℂ) (amp c u)) = (Complex.conjLIE : ℂ → ℂ) ∘ amp c := by
  funext u; simp

theorem conj_amp_contDiff (c : ℝ) : ContDiff ℝ ∞ (fun u => (starRingEnd ℂ) (amp c u)) := by
  rw [conj_amp_eq]
  exact Complex.conjLIE.toContinuousLinearEquiv.contDiff.comp (amp_contDiff c)

theorem gfun_contDiff (c c' : ℝ) : ContDiff ℝ ∞ (gfun c c') :=
  logCompactWeight_contDiff.mul ((amp_contDiff c).mul (conj_amp_contDiff c'))

theorem gfun_support (c c' : ℝ) : Function.support (gfun c c') ⊆ Set.Icc (-2) 2 := by
  intro u hu
  apply logCompactWeight_support_subset
  intro hz
  apply hu
  simp [gfun, hz]

theorem gfun_iter_bound (N : ℕ) : ∃ A : ℝ, 0 < A ∧ ∀ c c' : ℝ, ∀ i ≤ 2, ∀ u : ℝ,
    ‖iteratedFDeriv ℝ i (gfun c c') u‖ ≤ A / ((1 + |c|) ^ N * (1 + |c'|) ^ N) := by
  obtain ⟨B, hB, hamp⟩ := amp_iter_bound_le_two N
  let W : ℝ := SchwartzMap.seminorm ℝ 0 0 logCompactWeightSchwartz +
    SchwartzMap.seminorm ℝ 0 1 logCompactWeightSchwartz +
    SchwartzMap.seminorm ℝ 0 2 logCompactWeightSchwartz
  have hW0 : 0 ≤ W := by positivity
  refine ⟨16 * (W + 1) * B ^ 2, by positivity, ?_⟩
  intro c c' i hi u
  have hpc : 0 < (1 + |c|) ^ N := by positivity
  have hpc' : 0 < (1 + |c'|) ^ N := by positivity
  by_cases hu : u ∈ Set.Icc (-2 : ℝ) 2
  · have hu2 : u ≤ 2 := hu.2
    have hw : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k logCompactWeight u‖ ≤ W := by
      intro k hk
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      refine (logCompactWeight_deriv_bound k u).trans ?_
      have h0 := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) logCompactWeightSchwartz
      have h1 := apply_nonneg (SchwartzMap.seminorm ℝ 0 1) logCompactWeightSchwartz
      have h2 := apply_nonneg (SchwartzMap.seminorm ℝ 0 2) logCompactWeightSchwartz
      interval_cases k <;> simp only [W] <;> linarith
    have hconj : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k (fun u => (starRingEnd ℂ) (amp c' u)) u‖ ≤
        B / (1 + |c'|) ^ N := by
      intro k hk
      rw [conj_amp_eq, Complex.conjLIE.norm_iteratedFDeriv_comp_left]
      exact hamp k hk c' u hu2
    have hprod := mul_iter_bound (amp_contDiff c) (conj_amp_contDiff c') u
      (fun k hk => hamp k hk c u hu2) hconj
    have hall := mul_iter_bound logCompactWeight_contDiff
      ((amp_contDiff c).mul (conj_amp_contDiff c')) u hw hprod i hi
    refine hall.trans ?_
    rw [le_div_iff₀ (by positivity)]
    have hexp : 4 * W * (4 * (B / (1 + |c|) ^ N) * (B / (1 + |c'|) ^ N)) *
        ((1 + |c|) ^ N * (1 + |c'|) ^ N) = 16 * W * B ^ 2 := by
      field_simp
      ring
    rw [hexp]
    nlinarith [sq_nonneg B]
  · rw [iteratedFDeriv_eq_zero_of_notMem (gfun_support c c') i hu, norm_zero]
    positivity

end Erdos821.P5Energy
