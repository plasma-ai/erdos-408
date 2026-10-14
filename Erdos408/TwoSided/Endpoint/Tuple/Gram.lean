module

public import Erdos408.OneSided.Analysis.Divisor
public import Erdos408.TwoSided.Setup

/-!
# The sparse Gram bound

E8 of `blueprint/two_sided_correlation.md` §6.5 (PD (6.37)). Choose a maximizer
`τ_j ∈ [j, j + 1]` of `|R⁻¹ ∑ c_u u^{it}|²` for each `j ∈ 𝒥`. By the `TT*` bound it suffices
to bound the absolute row sums of the Gram matrix of `u ↦ u^{iτ_j}` on `(⌊R⌋, ⌊2R⌋]`, as in
`OneSided.sum_norm_unmarkedPoly_sq_le` (`Erdos408/OneSided/Major/Sparse.lean`). Its entries
are at most `R + 1`, which is used for `|j - j'| ≤ 1`. Otherwise `1 ≤ |Δ| ≤ 4T₀ + 2 ≤ x³`, and
by `IntegerKernelBound` at `k = 1`, `a = 0`, `H = lo = R`, `hi = 2R` they are at most
`|κ'| R (2 |j - j'|⁻¹ + exp(-L^{0.95}))`. The row sums are at most `9 (1 + |κ'|) R L / 2`, and
`∑ |c_u|² ≤ 2 R L^{2C_U}`.
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset

/-- The duality (`TT*`) bound: if each row of the Gram matrix
`G_{ii'} = ∑_n e_i(n) \overline{e_{i'}(n)}` has absolute sum at most `R`, then
`∑_i |∑_n c_n e_i(n)|² ≤ R ∑_n |c_n|²`. -/
theorem sum_norm_sq_le_of_gram_rowSum {ι : Type*} (I : Finset ι) (S : Finset ℕ)
    (e : ι → ℕ → ℂ) (c : ℕ → ℂ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ i ∈ I, ∑ i' ∈ I, ‖∑ n ∈ S, e i n * starRingEnd ℂ (e i' n)‖ ≤ R) :
    ∑ i ∈ I, ‖∑ n ∈ S, c n * e i n‖ ^ 2 ≤ R * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  set b : ι → ℂ := fun i => ∑ n ∈ S, c n * e i n
  set G : ι → ι → ℂ := fun i i' => ∑ n ∈ S, e i n * starRingEnd ℂ (e i' n)
  set v : ℕ → ℂ := fun n => ∑ i ∈ I, starRingEnd ℂ (b i) * e i n
  set Q := ∑ i ∈ I, ‖b i‖ ^ 2
  have hQ0 : 0 ≤ Q := sum_nonneg fun i _ => by positivity
  have hc0 : 0 ≤ ∑ n ∈ S, ‖c n‖ ^ 2 := sum_nonneg fun n _ => by positivity
  -- `Q = ∑_n c_n v_n`
  have hQv : (Q : ℂ) = ∑ n ∈ S, c n * v n := by
    simp only [Q, v, Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.conj_mul', mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    simp only [b, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  -- `∑_n |v_n|² = ∑_{i, i'} \bar b_i b_{i'} G_{ii'}`
  have hvG : ((∑ n ∈ S, ‖v n‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ I, ∑ i' ∈ I, starRingEnd ℂ (b i) * b i' * G i i' := by
    simp only [Complex.ofReal_sum, Complex.ofReal_pow, ← Complex.conj_mul', v, G, map_sum,
      map_mul, Complex.conj_conj, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun i' _ => sum_congr rfl fun n _ => by ring
  -- the Gram matrix is Hermitian
  have hGsymm : ∀ i i', ‖G i' i‖ = ‖G i i'‖ := by
    intro i i'
    have h : G i' i = starRingEnd ℂ (G i i') := by
      simp only [G, map_sum, map_mul, Complex.conj_conj]
      exact sum_congr rfl fun n _ => mul_comm _ _
    rw [h, Complex.norm_conj]
  -- `∑_n |v_n|² ≤ R Q`, by `2|ab| ≤ |a|² + |b|²`
  have hv : ∑ n ∈ S, ‖v n‖ ^ 2 ≤ R * Q := by
    have h₁ : ∑ n ∈ S, ‖v n‖ ^ 2 ≤
        ∑ i ∈ I, ∑ i' ∈ I, (‖b i‖ ^ 2 * ‖G i i'‖ + ‖b i'‖ ^ 2 * ‖G i' i‖) / 2 := by
      have h := congrArg norm hvG
      rw [Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun n _ => by positivity)] at h
      rw [h]
      refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => (norm_sum_le _ _).trans
        (sum_le_sum fun i' _ => ?_))
      rw [norm_mul, norm_mul, Complex.norm_conj, hGsymm]
      nlinarith [mul_nonneg (sq_nonneg (‖b i‖ - ‖b i'‖)) (norm_nonneg (G i' i))]
    have h₂ : ∑ i ∈ I, ∑ i' ∈ I, (‖b i‖ ^ 2 * ‖G i i'‖ + ‖b i'‖ ^ 2 * ‖G i' i‖) / 2 =
        ∑ i ∈ I, ‖b i‖ ^ 2 * ∑ i' ∈ I, ‖G i i'‖ := by
      simp only [add_div, sum_add_distrib]
      rw [sum_comm (f := fun i i' => ‖b i'‖ ^ 2 * ‖G i' i‖ / 2), ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib, mul_sum]
      exact sum_congr rfl fun i' _ => by ring
    rw [h₂] at h₁
    refine h₁.trans ?_
    rw [mul_comm R, sum_mul]
    exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hR i hi) (by positivity)
  -- `Q² ≤ (∑ |c_n|²)(∑ |v_n|²)`, by Cauchy–Schwarz
  have hQ : Q ^ 2 ≤ (∑ n ∈ S, ‖c n‖ ^ 2) * (R * Q) := by
    have h : Q ≤ ∑ n ∈ S, ‖c n‖ * ‖v n‖ := by
      have := congrArg norm hQv
      rw [Complex.norm_real, Real.norm_of_nonneg hQ0] at this
      rw [this]
      exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun n _ => norm_mul _ _)
    calc Q ^ 2 ≤ (∑ n ∈ S, ‖c n‖ * ‖v n‖) ^ 2 := pow_le_pow_left₀ hQ0 h 2
      _ ≤ (∑ n ∈ S, ‖c n‖ ^ 2) * ∑ n ∈ S, ‖v n‖ ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hv hc0
  rcases hQ0.eq_or_lt with h | h
  · rw [← h]
    positivity
  · nlinarith

/-- `∑_{m' ∈ S} 1/|m - m'| ≤ 2 (1 + log N)` for `S` and `m` in an integer interval of
length `N`, the term `m' = m` being `0`. -/
theorem sum_inv_abs_intCast_sub_le {S : Finset ℤ} {lo hi m : ℤ} (hS : S ⊆ Icc lo hi)
    (hm : m ∈ Icc lo hi) :
    ∑ m' ∈ S, |((m - m' : ℤ) : ℝ)|⁻¹ ≤ 2 * (1 + Real.log (hi - lo + 1).toNat) := by
  -- shift `[lo, hi]` to `[1, N]`
  set f : ℤ → ℕ := fun l => (l - lo + 1).toNat
  have hf : ∀ l ∈ Icc lo hi, ((f l : ℕ) : ℤ) = l - lo + 1 := fun l hl =>
    Int.toNat_of_nonneg (by rw [mem_Icc] at hl; omega)
  have hfmem : ∀ l ∈ Icc lo hi, f l ∈ Icc 1 (hi - lo + 1).toNat := by
    intro l hl
    have h := hf l hl
    rw [mem_Icc] at hl ⊢
    omega
  have hcast : ∀ l ∈ Icc lo hi, ((f l : ℕ) : ℝ) = ((l - lo + 1 : ℤ) : ℝ) := fun l hl => by
    rw [← hf l hl, Int.cast_natCast]
  have hinj : Set.InjOn f S := fun l hl l' hl' h => by
    have h₁ := hf l (hS hl)
    have h₂ := hf l' (hS hl')
    rw [h] at h₁
    omega
  calc ∑ m' ∈ S, |((m - m' : ℤ) : ℝ)|⁻¹ = ∑ m' ∈ S, |((f m : ℕ) : ℝ) - f m'|⁻¹ := by
        refine sum_congr rfl fun m' hm' => ?_
        rw [hcast m hm, hcast m' (hS hm')]
        push_cast
        ring_nf
    _ = ∑ n ∈ S.image f, |((f m : ℕ) : ℝ) - n|⁻¹ :=
        (sum_image (f := fun n : ℕ => |((f m : ℕ) : ℝ) - n|⁻¹) hinj).symm
    _ ≤ ∑ n ∈ Icc 1 (hi - lo + 1).toNat, |((f m : ℕ) : ℝ) - n|⁻¹ := by
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity
        obtain ⟨l, hl, rfl⟩ := mem_image.1 hn
        exact hfmem l (hS hl)
    _ ≤ _ := OneSided.sum_inv_abs_sub_le (hfmem m hm)

/-- `n^{ia} \overline{n^{ib}} = n^{i(a - b)}` for `n ≠ 0`. -/
theorem natCast_cpow_mul_I_mul_conj_cpow {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    (n : ℂ) ^ ((a : ℂ) * Complex.I) * starRingEnd ℂ ((n : ℂ) ^ ((b : ℂ) * Complex.I)) =
      (n : ℂ) ^ (((a - b : ℝ) : ℂ) * Complex.I) := by
  rw [OneSided.natCast_cpow_mul_I hn, OneSided.natCast_cpow_mul_I hn,
    OneSided.natCast_cpow_mul_I hn, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `|n^{it}| = 1` for `n ≥ 1`. -/
theorem norm_natCast_cpow_ofReal_mul_I {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- `|(⌊R⌋, ⌊2R⌋]| ≤ R + 1` for `R ≥ 0`. -/
theorem card_Ioc_floor_le {R : ℝ} (hR : 0 ≤ R) : (#(Ioc ⌊R⌋₊ ⌊2 * R⌋₊) : ℝ) ≤ R + 1 := by
  rw [Nat.card_Ioc]
  rcases le_or_gt ⌊R⌋₊ ⌊2 * R⌋₊ with h | h
  · rw [Nat.cast_sub h]
    linarith [Nat.floor_le (show 0 ≤ 2 * R by linarith), Nat.lt_floor_add_one R]
  · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
    linarith

/-- **Lemma E8 (sparse Gram bound from AP2).** For `C_m ≥ 0` and `C_U`, eventually, under
`IntegerKernelBound x C_m κ'`: for `R ∈ [exp(L/T²²), x]`, coefficients `|c_u| ≤ L^{C_U}` and a
set `𝒥` of integers with `#𝒥 e^{-L^{0.95}} ≤ 1` and `|j| ≤ 2T₀`, there are bounds `s_j` of
`sup_{[j, j+1]} |R|²` with `∑_{j ∈ 𝒥} s_j ≤ 9(1 + |κ'|) L^{2C_U + 4}`. -/
theorem eventually_sum_sup_normSq_le (Cm CU : ℝ) (hCm : 0 ≤ Cm) :
    ∀ᶠ x : ℝ in atTop, ∀ κ' : ℝ, IntegerKernelBound x Cm κ' →
      ∀ (R : ℝ) (c : ℕ → ℂ) (𝒥 : Finset ℤ),
        Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤ R → R ≤ x →
        (∀ u, ‖c u‖ ≤ Real.log x ^ CU) →
        (𝒥.card : ℝ) * Real.exp (-Real.log x ^ (0.95 : ℝ)) ≤ 1 →
        (∀ j ∈ 𝒥, |(j : ℝ)| ≤ 2 * (x * Real.log x ^ (Cm + 2))) →
        ∃ s : ℤ → ℝ,
          (∀ j ∈ 𝒥, ∀ t ∈ Set.Icc (j : ℝ) (j + 1),
            ‖(R : ℂ)⁻¹ * ∑ u ∈ Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊,
                c u * (u : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤ s j) ∧
          ∑ j ∈ 𝒥, s j ≤ 9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4) := by
  filter_upwards [eventually_log_rpow_le_self (Cm + 3),
    Real.tendsto_log_atTop.eventually_ge_atTop 10, eventually_ge_atTop (5 : ℝ)]
    with x hxL hL hx5
  intro κ' hK R c 𝒥 hR₁ hR₂ hc h𝒥 h𝒥T
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hR0 : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hR₁
  have hR1 : 1 ≤ R := le_trans (Real.one_le_exp (by
    have : 0 < Real.log L := Real.log_pos (by linarith)
    positivity)) hR₁
  set T₀ := x * L ^ (Cm + 2) with hT₀
  -- `L^{C_m + 2} ≤ x / 9`
  have hT₀x : 9 * L ^ (Cm + 2) ≤ x := by
    have h : L ^ (Cm + 3) = L ^ (Cm + 2) * L := by
      rw [show Cm + 3 = (Cm + 2) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    have : 0 ≤ L ^ (Cm + 2) := by positivity
    nlinarith
  have hT₀0 : 0 ≤ T₀ := by positivity
  set S := Ioc ⌊R⌋₊ ⌊2 * R⌋₊ with hS
  have hSpos : ∀ u ∈ S, 0 < u := fun u hu => by
    rw [mem_Ioc] at hu
    omega
  set f : ℝ → ℝ := fun t => ‖(R : ℂ)⁻¹ * ∑ u ∈ S, c u * (u : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2
  have hf : Continuous f := by
    refine ((continuous_const.mul (continuous_finsetSum _ fun u hu =>
      continuous_const.mul ?_)).norm).pow 2
    simp_rw [OneSided.natCast_cpow_mul_I (hSpos u hu).ne']
    fun_prop
  -- the maximizers `τ_j ∈ [j, j + 1]`
  have hmax : ∀ j : ℤ, ∃ τ ∈ Set.Icc (j : ℝ) (j + 1), ∀ t ∈ Set.Icc (j : ℝ) (j + 1),
      f t ≤ f τ := fun j =>
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (by linarith)) hf.continuousOn
  choose τ hτ hτmax using hmax
  refine ⟨fun j => f (τ j), fun j _ t ht => hτmax j t ht, ?_⟩
  -- the integer window
  set M := ⌊2 * T₀⌋ with hM
  have h𝒥M : 𝒥 ⊆ Icc (-M) M := by
    intro j hj
    have h := abs_le.1 (h𝒥T j hj)
    rw [mem_Icc]
    constructor
    · have : -j ≤ M := Int.le_floor.2 (by push_cast; linarith)
      omega
    · exact Int.le_floor.2 h.2
  set e : ℤ → ℕ → ℂ := fun j u => (u : ℂ) ^ ((τ j : ℂ) * Complex.I)
  set Rw := 3 * (R + 1) + |κ'| * R * (4 * (1 + Real.log (M - -M + 1).toNat) + 1) with hRw
  have hRw0 : 0 ≤ Rw := by positivity
  -- a Gram entry
  have hentry : ∀ j ∈ 𝒥, ∀ j' ∈ 𝒥, ‖∑ u ∈ S, e j u * starRingEnd ℂ (e j' u)‖ ≤
      (if |j - j'| ≤ 1 then R + 1 else 0) +
        |κ'| * R * (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ))) := by
    intro j hj j' hj'
    have hG : ∑ u ∈ S, e j u * starRingEnd ℂ (e j' u) =
        ∑ u ∈ S, (u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I) :=
      sum_congr rfl fun u hu => natCast_cpow_mul_I_mul_conj_cpow (hSpos u hu).ne' _ _
    rw [hG]
    have hsecond : 0 ≤ |κ'| * R *
        (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ))) := by positivity
    obtain ⟨hτj₁, hτj₂⟩ := hτ j
    obtain ⟨hτj'₁, hτj'₂⟩ := hτ j'
    have hjj' : |((j - j' : ℤ) : ℝ)| ≤ |τ j - τ j'| + 1 := by
      push_cast
      rw [abs_le]
      constructor <;> cases abs_cases (τ j - τ j') <;> linarith
    by_cases h₁ : |j - j'| ≤ 1
    · rw [ite_eq_left h₁]
      refine le_add_of_le_of_nonneg ((norm_sum_le _ _).trans ?_) hsecond
      calc ∑ u ∈ S, ‖(u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I)‖ = #S := by
            rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
            exact sum_congr rfl fun u hu => norm_natCast_cpow_ofReal_mul_I (hSpos u hu) _
        _ ≤ R + 1 := card_Ioc_floor_le hR0.le
    · rw [ite_eq_right h₁, zero_add]
      have h₂ : (2 : ℝ) ≤ |((j - j' : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast (show (2 : ℤ) ≤ |j - j'| by omega)
      have h : 1 ≤ |τ j - τ j'| := by linarith
      have hΔ : |τ j - τ j'| ≤ x ^ 3 := by
        have h₃ := h𝒥T j hj
        have h₄ := h𝒥T j' hj'
        have h₅ : |τ j - τ j'| ≤ 4 * T₀ + 2 := by
          rw [abs_le] at h₃ h₄ ⊢
          constructor <;> linarith
        have h₆ : 4 * T₀ + 2 ≤ x ^ 3 := by
          have : 4 * T₀ ≤ x * x := by
            rw [hT₀]
            nlinarith
          nlinarith
        linarith
      have hk1 : ((1 : ℕ) : ℝ) ≤ L ^ Cm := by
        rw [Nat.cast_one]
        exact Real.one_le_rpow (by linarith) hCm
      have hK' := hK R R (2 * R) hR₁ hR₂ le_rfl le_rfl 1 0 le_rfl hk1 (τ j - τ j') h hΔ
      have hfil : S.filter (· ≡ 0 [MOD 1]) = S :=
        filter_true_of_mem fun u _ => Nat.modEq_one
      rw [hfil] at hK'
      have hinv : (1 + |τ j - τ j'|)⁻¹ ≤ 2 * |((j - j' : ℤ) : ℝ)|⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by linarith)]
        calc (1 + |τ j - τ j'|)⁻¹ * |((j - j' : ℤ) : ℝ)|
            ≤ (1 + |τ j - τ j'|)⁻¹ * (2 * (1 + |τ j - τ j'|)) := by
              gcongr
              linarith
          _ = 2 := by field_simp
      calc ‖∑ u ∈ S, (u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I)‖
          = R * (R⁻¹ * ‖∑ u ∈ S, (u : ℂ) ^ (((τ j - τ j' : ℝ) : ℂ) * Complex.I)‖) := by
            field_simp
        _ ≤ R * (κ' * ((1 + |τ j - τ j'|)⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))) :=
            mul_le_mul_of_nonneg_left hK' hR0.le
        _ ≤ R * (|κ'| * (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))) := by
            refine mul_le_mul_of_nonneg_left ?_ hR0.le
            calc κ' * ((1 + |τ j - τ j'|)⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))
                ≤ |κ'| * ((1 + |τ j - τ j'|)⁻¹ + Real.exp (-L ^ (0.95 : ℝ))) :=
                  mul_le_mul_of_nonneg_right (le_abs_self κ') (by positivity)
              _ ≤ _ := by gcongr
        _ = _ := by ring
  -- the Gram rows are at most `Rw`
  have hrow : ∀ j ∈ 𝒥, ∑ j' ∈ 𝒥, ‖∑ u ∈ S, e j u * starRingEnd ℂ (e j' u)‖ ≤ Rw := by
    intro j hj
    have hnear : ∑ j' ∈ 𝒥, (if |j - j'| ≤ 1 then R + 1 else 0) ≤ 3 * (R + 1) := by
      rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
      have hsub : {j' ∈ 𝒥 | |j - j'| ≤ 1} ⊆ Icc (j - 1) (j + 1) := fun j' hj' => by
        rw [mem_filter] at hj'
        rw [mem_Icc]
        constructor <;> cases abs_cases (j - j') <;> omega
      have hcard : (#{j' ∈ 𝒥 | |j - j'| ≤ 1} : ℝ) ≤ 3 := by
        have h := card_le_card hsub
        rw [Int.card_Icc, show j + 1 + 1 - (j - 1) = 3 by ring] at h
        exact_mod_cast h
      nlinarith
    have hfar := sum_inv_abs_intCast_sub_le h𝒥M (h𝒥M hj)
    calc ∑ j' ∈ 𝒥, ‖∑ u ∈ S, e j u * starRingEnd ℂ (e j' u)‖
        ≤ ∑ j' ∈ 𝒥, ((if |j - j'| ≤ 1 then R + 1 else 0) +
            |κ'| * R * (2 * |((j - j' : ℤ) : ℝ)|⁻¹ + Real.exp (-L ^ (0.95 : ℝ)))) :=
          sum_le_sum fun j' hj' => hentry j hj j' hj'
      _ = ∑ j' ∈ 𝒥, (if |j - j'| ≤ 1 then R + 1 else 0) + |κ'| * R *
            (2 * ∑ j' ∈ 𝒥, |((j - j' : ℤ) : ℝ)|⁻¹ + #𝒥 * Real.exp (-L ^ (0.95 : ℝ))) := by
          rw [sum_add_distrib, ← mul_sum, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ Rw := by
          have h := mul_le_mul_of_nonneg_left (show 2 * ∑ j' ∈ 𝒥, |((j - j' : ℤ) : ℝ)|⁻¹ +
            #𝒥 * Real.exp (-L ^ (0.95 : ℝ)) ≤
              4 * (1 + Real.log (M - -M + 1).toNat) + 1 by linarith)
            (by positivity : 0 ≤ |κ'| * R)
          rw [hRw]
          linarith
  -- `log(2M + 1) ≤ 2L`
  have hlogM : Real.log (M - -M + 1).toNat ≤ 2 * L := by
    have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by positivity)
    have hcast : (((M - -M + 1).toNat : ℕ) : ℝ) = 2 * M + 1 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    have hMle : (M : ℝ) ≤ 2 * T₀ := Int.floor_le _
    rw [hcast]
    have hpos : (0 : ℝ) < 2 * M + 1 := by
      have : (0 : ℝ) ≤ M := by exact_mod_cast hM0
      linarith
    rw [show 2 * L = Real.log (x ^ 2) by rw [Real.log_pow]; push_cast; ring]
    refine Real.log_le_log hpos ?_
    have : 4 * T₀ ≤ x * x / 2 := by
      rw [hT₀]
      nlinarith
    nlinarith
  -- `Rw ≤ 9 (1 + |κ'|) R L`
  have hRwle : Rw ≤ 9 * (1 + |κ'|) * R * L := by
    rw [hRw]
    have hk0 := abs_nonneg κ'
    have h₁ : 4 * (1 + Real.log (M - -M + 1).toNat) + 1 ≤ 9 * L := by
      nlinarith
    have h₂ : |κ'| * R * (4 * (1 + Real.log (M - -M + 1).toNat) + 1) ≤
        |κ'| * R * (9 * L) := mul_le_mul_of_nonneg_left h₁ (by positivity)
    nlinarith [mul_nonneg hk0 hR0.le]
  -- the coefficients have `∑ |c_u|² ≤ 2 R L^{2C_U}`
  have hcoef : ∑ u ∈ S, ‖c u‖ ^ 2 ≤ 2 * R * L ^ (2 * CU) := by
    have hcu : ∀ u, ‖c u‖ ^ 2 ≤ L ^ (2 * CU) := by
      intro u
      calc ‖c u‖ ^ 2 ≤ (L ^ CU) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc u) 2
        _ = L ^ (2 * CU) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
            ring_nf
    calc ∑ u ∈ S, ‖c u‖ ^ 2 ≤ ∑ _u ∈ S, L ^ (2 * CU) := sum_le_sum fun u _ => hcu u
      _ = #S * L ^ (2 * CU) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (R + 1) * L ^ (2 * CU) := by
          gcongr
          exact card_Ioc_floor_le hR0.le
      _ ≤ 2 * R * L ^ (2 * CU) := by
          gcongr
          linarith
  have hgram := sum_norm_sq_le_of_gram_rowSum 𝒥 S e c hRw0 hrow
  have hL4 : L ^ (2 * CU + 4) = L ^ (2 * CU) * L ^ (4 : ℕ) := by
    rw [Real.rpow_add hL0, ← Real.rpow_natCast]
    norm_num
  calc ∑ j ∈ 𝒥, f (τ j) = R⁻¹ ^ 2 * ∑ j ∈ 𝒥, ‖∑ u ∈ S, c u * e j u‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        simp only [f, e]
        rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR0.le]
    _ ≤ R⁻¹ ^ 2 * (9 * (1 + |κ'|) * R * L * (2 * R * L ^ (2 * CU))) := by
        gcongr
        exact hgram.trans (mul_le_mul hRwle hcoef (by positivity) (by positivity))
    _ = 9 * (1 + |κ'|) * L ^ (2 * CU) * (2 * L) := by
        field_simp
    _ ≤ 9 * (1 + |κ'|) * L ^ (2 * CU + 4) := by
        rw [hL4]
        have : 2 * L ≤ L ^ 4 := by
          have h₁ : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
          nlinarith
        have : 0 ≤ 9 * (1 + |κ'|) * L ^ (2 * CU) := by positivity
        nlinarith

end Erdos408.TwoSided.TupleHigh
