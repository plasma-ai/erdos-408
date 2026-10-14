import Erdos408.Extraction.Unsmooth
import Erdos408.OneSided.Bands
import Erdos408.OneSided.Analysis.Divisor
import Erdos408.TwoSided.Setup

/-!
# Pointwise bounds for the constant part

The size facts of `blueprint/two_sided_correlation.md` §2 used in S19, in the form needed
there.

* U6: `|C_B / V| ≤ (2L)^{d+1}/v₋ ≤ L^{d+3}`.
* The primes of a divisor model exceed `k ≤ L^{C_m}`, so its support is coprime to `k`.
-/

namespace Erdos408.TwoSided.ConstHigh

open Filter Finset

/-- **U6.** Eventually `|C_B / V| ≤ L^{d+3}` for admissible slots, `|B| ≤ 1` and `V ≥ v₋`:
`|C_B| ≤ (∑_{p ≤ x} 1/p)^{d+1} ≤ (2L)^{d+1}`. -/
theorem eventually_abs_slotMean_div_le (c vlo : ℝ) (d : ℕ) (hc : 0 < c) (hvlo : 0 < vlo) :
    ∀ᶠ x : ℝ in atTop, ∀ (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
      AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) → ∀ V : ℝ, vlo ≤ V →
        |slotMean x u v Bc / V| ≤ Real.log x ^ ((d + 3 : ℕ) : ℝ) := by
  filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (tendsto_pow_atTop (two_ne_zero)).comp Real.tendsto_log_atTop
      |>.eventually_ge_atTop (2 ^ (d + 1) / vlo)] with x hx hL1 hL2
  intro u v Bc hsl hB V hV
  simp only [Function.comp_apply] at hL2
  set L := Real.log x with hL
  have hu : ∀ i, 0 ≤ u i := fun i => le_trans (by positivity) (hsl.1 i)
  have hv : ∑ i, v i ≤ 1 := by
    have : 0 ≤ c / logLog x ^ 20 := by positivity
    linarith [hsl.2]
  have hC := Unsmooth.abs_slotMean_le hx hu hv hB
  -- `∑_{p ≤ x} 1/p ≤ 1 + log x ≤ 2L`
  have hsum : ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p ≤ 2 * L := by
    have hsub : primesIoc 1 x ⊆ Icc 1 ⌊x⌋₊ := by
      intro p hp
      obtain ⟨hpr, hpx⟩ := mem_primesIoc_one.1 hp
      exact mem_Icc.2 ⟨hpr.one_lt.le, Nat.le_floor hpx⟩
    calc ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p ≤ ∑ p ∈ Icc 1 ⌊x⌋₊, ((p : ℝ))⁻¹ := by
          simp_rw [one_div]
          exact sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ 1 + Real.log ⌊x⌋₊ := OneSided.sum_Icc_inv_le _
      _ ≤ 1 + L := by
          have h0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.2 hx.le
          linarith [Real.log_le_log h0 (Nat.floor_le (by linarith))]
      _ ≤ 2 * L := by linarith
  have hV0 : 0 < V := by linarith
  rw [abs_div, abs_of_pos hV0, div_le_iff₀ hV0, Real.rpow_natCast]
  have hs0 : 0 ≤ ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p := sum_nonneg fun _ _ => by positivity
  calc |slotMean x u v Bc| ≤ (2 * L) ^ (d + 1) :=
        hC.trans (pow_le_pow_left₀ hs0 hsum _)
    _ = 2 ^ (d + 1) / vlo * L ^ (d + 1) * vlo := by field_simp; ring
    _ ≤ L ^ 2 * L ^ (d + 1) * V := by gcongr
    _ = L ^ (d + 3) * V := by ring

/-- Eventually, every `d ≠ 0` whose prime factors exceed `exp(L^{1/10})` is coprime to every
modulus `k ≤ L^{C_m}`. -/
theorem eventually_coprime (Cm : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ d k : ℕ, d ≠ 0 → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
      (∀ p ∈ d.primeFactors, Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤ p) → Nat.Coprime d k := by
  filter_upwards [Real.tendsto_log_atTop.eventually
      (IntegerKernel.eventually_log_le_mul_rpow (b := 1 / 10) (by norm_num)
        (ε := 1 / (|Cm| + 1)) (by positivity)),
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hlog hL1
  intro d k hd hk1 hk hp
  set L := Real.log x with hL
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 < Real.log L := Real.log_pos hL1
  -- `L^{C_m} < exp(L^{1/10})`
  have hlt : L ^ Cm < Real.exp (L ^ (1 / 10 : ℝ)) := by
    rw [Real.rpow_def_of_pos hL0]
    refine Real.exp_lt_exp.2 ?_
    have h1 : Real.log L * Cm ≤ |Cm| * Real.log L := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hlog0.le
    have h2 : |Cm| * Real.log L ≤ |Cm| * (1 / (|Cm| + 1) * L ^ (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    have h3 : |Cm| * (1 / (|Cm| + 1) * L ^ (1 / 10 : ℝ)) < L ^ (1 / 10 : ℝ) := by
      have hp10 : 0 < L ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hL0 _
      rw [show |Cm| * (1 / (|Cm| + 1) * L ^ (1 / 10 : ℝ)) =
        |Cm| / (|Cm| + 1) * L ^ (1 / 10 : ℝ) by field_simp]
      have : |Cm| / (|Cm| + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
      nlinarith
    linarith
  refine Nat.coprime_of_dvd fun p hpr hpd hpk => ?_
  have hk0 : k ≠ 0 := by omega
  have hpk' : (p : ℝ) ≤ k := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hpk
  have := hp p (Nat.mem_primeFactors.2 ⟨hpr, hpd, hd⟩)
  linarith

/-- The primes of a small group lie in `[exp(L^{0.27}), exp(L^{0.36})]`. -/
theorem mem_smallGroup_bounds {c₀ C₀ vlo vhi x : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Finset ℕ} {big : Finset ι} (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big)
    {gs : ι} (hgs : gs ∉ big) :
    ∀ p ∈ P gs, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) := fun _ hp =>
  mem_primesIcc.1 (hadm.2.2.2.2.2.2.1 gs hgs hp)

/-- Every active or band prime is at least `exp(L^{1/10})`. -/
theorem exp_le_of_mem_active_or_band {c₀ C₀ vlo vhi x : ℝ} {ι : Type} [Fintype ι]
    [DecidableEq ι] {P : ι → Finset ℕ} {big : Finset ι}
    (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big) {K₀ : ℕ} {CN alo ahi : ℝ} {r : ℕ}
    {a : Fin r → ℝ} (hin : InertAdmissible K₀ CN alo ahi x a) (halo : 1 / 10 ≤ alo)
    (hL : 1 ≤ Real.log x) {p : ℕ} (hp : p ∈ Finset.univ.biUnion P ∨ ∃ i, p ∈ band x (a i)) :
    Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤ p := by
  have hpow : ∀ e : ℝ, 1 / 10 ≤ e →
      Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤ Real.exp (Real.log x ^ e) := fun e he =>
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL he)
  rcases hp with hp | ⟨i, hp⟩
  · obtain ⟨g, -, hpg⟩ := mem_biUnion.1 hp
    by_cases hg : g ∈ big
    · have := (mem_primesIcc.1 (hadm.2.2.2.2.2.2.2.1 g hg hpg)).2.1
      exact (hpow 0.39 (by norm_num)).trans this
    · exact (hpow 0.27 (by norm_num)).trans (mem_smallGroup_bounds hadm hg p hpg).2.1
  · exact (hpow (a i) (halo.trans (hin.2.1 i).1)).trans (OneSided.exp_le_of_mem_band hp)

end Erdos408.TwoSided.ConstHigh
