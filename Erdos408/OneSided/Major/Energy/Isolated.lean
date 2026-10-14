module

public import Erdos408.OneSided.Major.Sparse

/-!
# The isolated energy

`blueprint/one_sided_type_ii.md` §6.3 step 7, PD `maj:isolated-energy`. Let
`P_s(t) = P⁻¹ ∑_{p ∈ PS} χ(p) p^{i(t + ξ)}` be the polynomial of one dyad `[P, 2P)` of
primes, and let `M` be continuous with `|M| ≤ ε` on `[-T, T]`, `T ≤ 2 X L^B`. Then
`∫_{-T}^T |P_s M N_β|² ≤ L^{-2A_s} ∫_{-T}^T |M N_β|² + 4 ε² C₀ L^{2C + 1}`:

* where `|P_s(t)| ≤ L^{-A_s}`, bound `|P_s|² ≤ L^{-2A_s}`;
* elsewhere `t` lies in a unit interval `[m, m + 1]` of the sparse family `𝓘`, and there
  `|P_s M N_β|² ≤ 4 ε² sup_{[m, m + 1]} |N_β|²`. By (G) these suprema sum to at most
  `C₀ L^{2C + 1}` (`sum_norm_sq_le_of_sparse`).

The function `M` is generic. In `Major/Energy.lean` it is `M_α`, with `ε = c₄ L^{-A}` from P4,
and the mean square of `M_α N_β` comes from `maj:product-mean`.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset Real MeasureTheory

variable {K : ℕ}

/-! ### Continuity and size of the polynomials -/

/-- `t ↦ n^{it}` is continuous for `n ≠ 0`. -/
theorem continuous_natCast_cpow_mul_I {n : ℕ} (hn : n ≠ 0) :
    Continuous fun t : ℝ => (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  simp_rw [natCast_cpow_mul_I hn]
  fun_prop

/-- `N_β` is continuous. -/
theorem continuous_unmarkedPoly {d : Data K} (hHn : 0 < d.Hn) {k : ℕ}
    (ψ : DirichletCharacter ℂ k) : Continuous (unmarkedPoly d ψ) := by
  unfold unmarkedPoly
  refine continuous_const.mul (continuous_finsetSum _ fun n hn => ?_)
  have h : 0 < n := lt_of_lt_of_le (Nat.ceil_pos.2 hHn) (mem_Icc.1 hn).1
  exact continuous_const.mul (continuous_natCast_cpow_mul_I h.ne')

/-- `(ξ, t) ↦ P_s(t)` with shift `ξ` is continuous. -/
theorem continuous_primePoly {P : ℝ} {PS : Finset ℕ} (hPS : ∀ p ∈ PS, p ≠ 0) {k : ℕ}
    (χ : DirichletCharacter ℂ k) :
    Continuous fun z : ℝ × ℝ => primePoly P PS χ z.1 z.2 := by
  unfold primePoly
  refine continuous_const.mul (continuous_finsetSum _ fun p hp => ?_)
  exact continuous_const.mul
    ((continuous_natCast_cpow_mul_I (hPS p hp)).comp (continuous_snd.add continuous_fst))

/-- `|P_s(t)| ≤ 2` for a set of primes in `[P, 2P)` with `P ≥ 1`: there are at most `P + 1`
integers in `[P, 2P)`. -/
theorem norm_primePoly_le_two {P : ℝ} (hP : 1 ≤ P) {PS : Finset ℕ}
    (hPS : ∀ p ∈ PS, p.Prime ∧ P ≤ p ∧ (p : ℝ) < 2 * P) {k : ℕ} (χ : DirichletCharacter ℂ k)
    (ξ t : ℝ) : ‖primePoly P PS χ ξ t‖ ≤ 2 := by
  have hP0 : 0 < P := by linarith
  -- `|PS| ≤ P + 1`
  have hcard : (#PS : ℝ) ≤ P + 1 := by
    have hsub : PS ⊆ Ico ⌈P⌉₊ ⌈2 * P⌉₊ := fun p hp => by
      obtain ⟨-, h₁, h₂⟩ := hPS p hp
      exact mem_Ico.2 ⟨Nat.ceil_le.2 h₁, Nat.lt_ceil.2 h₂⟩
    have h := card_le_card hsub
    rw [Nat.card_Ico] at h
    have h₁ : (⌈2 * P⌉₊ : ℝ) < 2 * P + 1 := Nat.ceil_lt_add_one (by linarith)
    have h₂ : P ≤ (⌈P⌉₊ : ℝ) := Nat.le_ceil P
    have h₃ : ((⌈2 * P⌉₊ - ⌈P⌉₊ : ℕ) : ℝ) = ⌈2 * P⌉₊ - ⌈P⌉₊ :=
      Nat.cast_sub (Nat.ceil_mono (by linarith))
    have h₄ : (#PS : ℝ) ≤ ((⌈2 * P⌉₊ - ⌈P⌉₊ : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  unfold primePoly
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hP0.le]
  calc P⁻¹ * ‖∑ p ∈ PS, χ p * (p : ℂ) ^ (((t + ξ : ℝ) : ℂ) * Complex.I)‖
      ≤ P⁻¹ * ∑ p ∈ PS, (1 : ℝ) := by
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun p hp => ?_)
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hPS p hp).1.pos]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, Real.rpow_zero, mul_one]
        exact DirichletCharacter.norm_le_one χ _
    _ ≤ P⁻¹ * (P + 1) := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        gcongr
    _ ≤ 2 := by
        rw [mul_add, inv_mul_cancel₀ hP0.ne']
        have : P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP
        linarith

/-- `∫_{-T}^T 1_{[m, m + 1]} c ≤ c` for `c ≥ 0`. -/
theorem integral_indicator_Icc_le {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c) (m : ℝ) :
    ∫ τ in (-T)..T, Set.indicator (Set.Icc m (m + 1)) (fun _ => c) τ ≤ c := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_indicator_const _ measurableSet_Icc,
    measureReal_restrict_apply measurableSet_Icc, smul_eq_mul]
  have h : volume.real (Set.Icc m (m + 1) ∩ Set.Ioc (-T) T) ≤ 1 := by
    calc volume.real (Set.Icc m (m + 1) ∩ Set.Ioc (-T) T) ≤ volume.real (Set.Icc m (m + 1)) :=
          measureReal_mono Set.inter_subset_left measure_Icc_lt_top.ne
      _ = 1 := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  exact mul_le_of_le_one_left hc h

/-! ### The isolated energy -/

/-- PD `maj:isolated-energy`, for a generic continuous `M` with `|M| ≤ ε` on `[-T, T]`:
`∫_{-T}^T |P_s M N_β|² ≤ L^{-2A_s} E + 4 ε² C₀ L^{2C + 1}` whenever
`∫_{-T}^T |M N_β|² ≤ E`. The constant `C₀` is that of `sum_norm_sq_le_of_sparse`. -/
theorem eventually_integral_isolated_le {C CX alo ahi g B As cG : ℝ} (halo : 1 / 10 < alo)
    (hahi : ahi < 1 / 5) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      KernelBound B cG x d →
      ∀ P : ℝ, Real.exp (Real.log x ^ alo) ≤ P → P ≤ Real.exp (2 * Real.log x ^ ahi) →
      ∀ PS : Finset ℕ, (∀ p ∈ PS, p.Prime ∧ P ≤ p ∧ (p : ℝ) < 2 * P) →
      ∀ (k : ℕ) (χ ψ : DirichletCharacter ℂ k) (ξ : ℝ) (M : ℝ → ℂ), Continuous M →
      ∀ T ε E : ℝ, 0 ≤ T → T ≤ 2 * d.X * Real.log x ^ B → (∀ τ, |τ| ≤ T → ‖M τ‖ ≤ ε) →
        ∫ τ in (-T)..T, ‖M τ * unmarkedPoly d ψ τ‖ ^ 2 ≤ E →
        ∫ τ in (-T)..T, (‖primePoly P PS χ ξ τ‖ * ‖M τ * unmarkedPoly d ψ τ‖) ^ 2 ≤
          Real.log x ^ (-(2 * As)) * E + 4 * ε ^ 2 * (C₀ * Real.log x ^ (2 * C + 1)) := by
  obtain ⟨C₀, hC₀⟩ := sum_norm_sq_le_of_sparse (K := K) (C := C) (CX := CX) (g := g) (B := B)
    (As := As) (cG := cG) halo hahi
  refine ⟨C₀, ?_⟩
  filter_upwards [hC₀, eventually_ge_atTop 1] with x hC₀ hx d hd hKB P hP1 hP2 PS hPS k χ ψ ξ M
    hM T ε E hT0 hTZ hMε hE
  set L := Real.log x
  set N := unmarkedPoly d ψ
  set Z := 2 * d.X * L ^ B
  set S := sparseSet x Z As P PS χ ξ
  have hL0 : 0 ≤ L := Real.log_nonneg hx
  have hHn : 0 < d.Hn := (Real.rpow_pos_of_pos (by linarith) _).trans_le hd.Hn_ge
  have hN : Continuous N := continuous_unmarkedPoly hHn ψ
  have hP : 1 ≤ P := (Real.one_le_exp (Real.rpow_nonneg hL0 _)).trans hP1
  have hPS0 : ∀ p ∈ PS, p ≠ 0 := fun p hp => (hPS p hp).1.ne_zero
  have hPc : Continuous fun τ => primePoly P PS χ ξ τ := by
    have h := (continuous_primePoly (P := P) hPS0 χ).comp (Continuous.prodMk_right ξ)
    exact h
  -- a maximizer `τ_m` of `|N_β|` on each unit interval `[m, m + 1]`
  have hmax : ∀ m : ℤ, ∃ t : ℝ, (m : ℝ) ≤ t ∧ t ≤ m + 1 ∧
      ∀ s, (m : ℝ) ≤ s → s ≤ m + 1 → ‖N s‖ ≤ ‖N t‖ := by
    intro m
    obtain ⟨t, ht, htmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.2 (by linarith : (m : ℝ) ≤ m + 1)) hN.norm.continuousOn
    exact ⟨t, ht.1, ht.2, fun s hs₁ hs₂ => htmax ⟨hs₁, hs₂⟩⟩
  choose τm hτm₁ hτm₂ hτmax using hmax
  have hsp := hC₀ d hd hKB P hP1 hP2 PS hPS k χ ψ ξ τm fun m => ⟨hτm₁ m, hτm₂ m⟩
  -- the pointwise bound
  set G : ℝ → ℝ := fun τ => L ^ (-(2 * As)) * ‖M τ * N τ‖ ^ 2 +
    ∑ m ∈ S, Set.indicator (Set.Icc (m : ℝ) (m + 1)) (fun _ => 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2) τ
  have hpt : ∀ τ ∈ Set.Icc (-T) T,
      (‖primePoly P PS χ ξ τ‖ * ‖M τ * N τ‖) ^ 2 ≤ G τ := by
    intro τ hτ
    have hτT : |τ| ≤ T := abs_le.2 hτ
    have hind : 0 ≤ ∑ m ∈ S, Set.indicator (Set.Icc (m : ℝ) (m + 1))
        (fun _ => 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2) τ :=
      sum_nonneg fun m _ => Set.indicator_nonneg (fun _ _ => by positivity) _
    rcases le_or_gt ‖primePoly P PS χ ξ τ‖ (L ^ (-As)) with hsmall | hlarge
    -- where `P_s` is small
    · have h₁ : (L ^ (-As)) ^ 2 = L ^ (-(2 * As)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
        norm_num
        ring_nf
      calc (‖primePoly P PS χ ξ τ‖ * ‖M τ * N τ‖) ^ 2
          = ‖primePoly P PS χ ξ τ‖ ^ 2 * ‖M τ * N τ‖ ^ 2 := by ring
        _ ≤ (L ^ (-As)) ^ 2 * ‖M τ * N τ‖ ^ 2 := by gcongr
        _ = L ^ (-(2 * As)) * ‖M τ * N τ‖ ^ 2 := by rw [h₁]
        _ ≤ G τ := le_add_of_nonneg_right hind
    -- where `P_s` is large, `⌊τ⌋` is in the sparse family
    · set m₀ := ⌊τ⌋
      have hm₀ : (m₀ : ℝ) ≤ τ := Int.floor_le τ
      have hm₀' : τ ≤ m₀ + 1 := (Int.lt_floor_add_one τ).le
      have hTZ' : |τ| ≤ Z := hτT.trans hTZ
      have hmS : m₀ ∈ S := by
        simp only [S, sparseSet, mem_filter, mem_Icc]
        refine ⟨⟨?_, ?_⟩, τ, hm₀, hm₀', hTZ', hlarge⟩
        · have h₁ : -(⌈Z⌉ : ℝ) ≤ τ := by
            linarith [Int.le_ceil Z, (abs_le.1 hTZ').1]
          have h₂ : -⌈Z⌉ ≤ m₀ := Int.le_floor.2 (by exact_mod_cast h₁)
          linarith
        · have h₁ : τ ≤ (⌈Z⌉ : ℝ) := by linarith [Int.le_ceil Z, (abs_le.1 hTZ').2]
          exact Int.floor_le_iff.2 (by linarith)
      have hε : ‖M τ‖ ≤ ε := hMε τ hτT
      have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
      have hNτ : ‖N τ‖ ≤ ‖N (τm m₀)‖ := hτmax m₀ τ hm₀ hm₀'
      have hPs := norm_primePoly_le_two hP hPS χ ξ τ
      calc (‖primePoly P PS χ ξ τ‖ * ‖M τ * N τ‖) ^ 2
          ≤ (2 * (ε * ‖N (τm m₀)‖)) ^ 2 := by
            rw [norm_mul]
            gcongr
        _ = Set.indicator (Set.Icc (m₀ : ℝ) (m₀ + 1))
              (fun _ => 4 * ε ^ 2 * ‖N (τm m₀)‖ ^ 2) τ := by
            rw [Set.indicator_of_mem (Set.mem_Icc.2 ⟨hm₀, hm₀'⟩)]
            ring
        _ ≤ ∑ m ∈ S, Set.indicator (Set.Icc (m : ℝ) (m + 1))
              (fun _ => 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2) τ :=
            single_le_sum (f := fun m : ℤ => Set.indicator (Set.Icc (m : ℝ) (m + 1))
              (fun _ => 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2) τ)
              (fun m _ => Set.indicator_nonneg (fun _ _ => by positivity) _) hmS
        _ ≤ G τ := le_add_of_nonneg_left (by positivity)
  -- integrate
  have hMN : Continuous fun τ => ‖M τ * N τ‖ ^ 2 := by fun_prop
  have hind : ∀ m : ℤ, IntervalIntegrable (Set.indicator (Set.Icc (m : ℝ) (m + 1))
      (fun _ => 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2)) volume (-T) T := fun m =>
    ⟨(intervalIntegrable_const (c := 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2)).1.indicator measurableSet_Icc,
      (intervalIntegrable_const (c := 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2)).2.indicator measurableSet_Icc⟩
  have hsum : IntervalIntegrable (fun τ => ∑ m ∈ S, Set.indicator (Set.Icc (m : ℝ) (m + 1))
      (fun _ => 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2) τ) volume (-T) T := by
    convert IntervalIntegrable.sum S fun m _ => hind m using 1
    ext τ
    rw [Finset.sum_apply]
  have hGi : IntervalIntegrable G volume (-T) T :=
    ((hMN.intervalIntegrable _ _).const_mul _).add hsum
  calc ∫ τ in (-T)..T, (‖primePoly P PS χ ξ τ‖ * ‖M τ * N τ‖) ^ 2
      ≤ ∫ τ in (-T)..T, G τ :=
        intervalIntegral.integral_mono_on (by linarith)
          ((by fun_prop : Continuous fun τ =>
            (‖primePoly P PS χ ξ τ‖ * ‖M τ * N τ‖) ^ 2).intervalIntegrable _ _) hGi hpt
    _ = L ^ (-(2 * As)) * (∫ τ in (-T)..T, ‖M τ * N τ‖ ^ 2) +
          ∑ m ∈ S, ∫ τ in (-T)..T, Set.indicator (Set.Icc (m : ℝ) (m + 1))
            (fun _ => 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2) τ := by
        simp only [G]
        rw [intervalIntegral.integral_add ((hMN.intervalIntegrable _ _).const_mul _) hsum,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_finsetSum fun m _ => hind m]
    _ ≤ L ^ (-(2 * As)) * E + ∑ m ∈ S, 4 * ε ^ 2 * ‖N (τm m)‖ ^ 2 := by
        gcongr with m
        exact integral_indicator_Icc_le hT0 (by positivity) _
    _ = L ^ (-(2 * As)) * E + 4 * ε ^ 2 * ∑ m ∈ S, ‖N (τm m)‖ ^ 2 := by rw [mul_sum]
    _ ≤ L ^ (-(2 * As)) * E + 4 * ε ^ 2 * (C₀ * L ^ (2 * C + 1)) := by gcongr

end Erdos408.OneSided
