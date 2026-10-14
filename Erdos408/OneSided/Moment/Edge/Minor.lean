import Erdos408.OneSided.Moment.Edge.Gram
import Erdos408.OneSided.Major.Mellin.Smooth
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Minor arcs

The analytic inputs of PD `mem:cutoff-fourier` and `mem:dirichlet-minor` for the clean edge.
Write `P = L^{A₀}`, `δ = 2P/Y` and `Q₀ = ⌊P⌋`. The major arcs are `|θ - h/k| ≤ δ` with
`1 ≤ k ≤ Q₀`, `0 ≤ h < k` and `(h, k) = 1`.

* `minorWeight`: one minus the number of major arcs containing `θ`. On the period
  `(-2δ, 1 - 2δ]` the arcs are disjoint once `Y ≥ 8P³` (`minorWeight_spec`), so the weight is
  the indicator of the minor arcs: it has modulus at most one, and where it is nonzero `θ` is
  at distance more than `δ` from every rational of denominator at most `Q₀`.
* `sub_arcIntegral_eq`: `[n = 0] - ∫_𝔐 e(θ n) = ∫_{-2δ}^{1-2δ} w(θ) e(θ n) dθ`.
* `exists_dirichlet_minor` (`mem:dirichlet-minor`): for `θ` minor and `|u| ≤ P/2`, the point
  `ϑ = θ + u/Y` has a reduced approximation `|ϑ - c/d| ≤ 1/(dQ)` with
  `P < d ≤ Q = ⌈Y/P⌉`.
* `exists_plateau_fourier` (`mem:cutoff-fourier`): `ψ(s) = ∫ e(s ξ) ψ̂(ξ) dξ`, with
  `|ψ̂(ξ)| ≤ C g(ξ)` and `|ψ̂(ξ)| ≤ (C/U) g(ξ)` for `|ξ| > U ≥ 1`, where
  `g(ξ) = (1 + (2πξ)²)⁻¹` has integral `1/2`.
-/

noncomputable section

namespace Erdos408.OneSided

open MeasureTheory Finset Real
open scoped ContDiff

/-! ### Periods -/

/-- `∫_a^{a+1} e(θ n) dθ = [n = 0]` for an integer `n`. -/
theorem integral_ephase_period (a : ℝ) (n : ℤ) :
    ∫ θ in a..a + 1, ephase (θ * n) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · simp [hn, ephase_zero]
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
        Complex.I_ne_zero) (Int.cast_ne_zero.2 hn)
    have e : ∀ θ : ℝ, ephase (θ * n) = Complex.exp ((2 * π * Complex.I * n) * θ) := by
      intro θ
      rw [ephase]
      congr 1
      push_cast
      ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * n * a) := by
      have := ephase_add (a * n) n
      rw [ephase_intCast, mul_one] at this
      rw [← e, ← e, show (a + 1) * (n : ℝ) = a * n + n by ring]
      exact this
    rw [h1, sub_self, zero_div]

/-! ### The major arcs -/

section Arcs

variable (A₀ x Y : ℝ)

/-- The arc radius `δ = 2 L^{A₀} / Y`. -/
def arcRadius : ℝ := 2 * Real.log x ^ A₀ / Y

/-- The minor-arc weight: one minus the number of arcs `|θ - h/k| ≤ δ` containing `θ`. -/
def minorWeight (θ : ℝ) : ℝ :=
  1 - ∑ k ∈ Icc 1 ⌊Real.log x ^ A₀⌋₊, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k),
    (Set.Icc ((h : ℝ) / k - arcRadius A₀ x Y) ((h : ℝ) / k + arcRadius A₀ x Y)).indicator 1 θ

end Arcs

variable {A₀ x Y : ℝ}

/-- The minor-arc weight is measurable. -/
theorem measurable_minorWeight : Measurable (minorWeight A₀ x Y) :=
  (Finset.measurable_sum _ fun _ _ => Finset.measurable_sum _ fun _ _ =>
    measurable_const.indicator measurableSet_Icc).const_sub 1

/-- Distinct reduced fractions with denominators at most `Q₀` differ by at least `1/Q₀²`. -/
private theorem one_div_sq_le_abs_sub {Q₀ k k' h h' : ℕ} (hk : k ∈ Icc 1 Q₀) (hk' : k' ∈ Icc 1 Q₀)
    (hh : Nat.Coprime h k) (hh' : Nat.Coprime h' k') (hne : (k, h) ≠ (k', h')) :
    1 / (Q₀ : ℝ) ^ 2 ≤ |(h : ℝ) / k - h' / k'| := by
  rw [mem_Icc] at hk hk'
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hk0' : (0 : ℝ) < k' := by exact_mod_cast hk'.1
  -- `h k' ≠ h' k`
  have hcross : (h * k' : ℤ) - h' * k ≠ 0 := by
    intro he
    have he' : h * k' = h' * k := by exact_mod_cast (sub_eq_zero.1 he)
    have h1 : k ∣ k' := (Nat.Coprime.symm hh).dvd_of_dvd_mul_left ⟨h', by linarith [he']⟩
    have h2 : k' ∣ k := (Nat.Coprime.symm hh').dvd_of_dvd_mul_left ⟨h, by linarith [he']⟩
    have hkk : k = k' := Nat.dvd_antisymm h1 h2
    subst hkk
    have : h = h' := by
      have := Nat.eq_of_mul_eq_mul_right hk.1 he'
      exact this
    exact hne (by rw [this])
  have h1 : (1 : ℝ) ≤ |((h * k' - h' * k : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hcross
  have e : (h : ℝ) / k - h' / k' = ((h * k' - h' * k : ℤ) : ℝ) / (k * k') := by
    push_cast
    field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hk0 hk0')]
  have hQ : (k : ℝ) * k' ≤ (Q₀ : ℝ) ^ 2 := by
    have : (k : ℝ) ≤ Q₀ := by exact_mod_cast hk.2
    have : (k' : ℝ) ≤ Q₀ := by exact_mod_cast hk'.2
    nlinarith
  calc 1 / (Q₀ : ℝ) ^ 2 ≤ 1 / (k * k') := one_div_le_one_div_of_le (by positivity) hQ
    _ ≤ _ := div_le_div_of_nonneg_right h1 (by positivity)

/-- With `Y ≥ 8P³` and `P ≥ 1`, the arcs are disjoint and lie in `(-2δ, 1 - 2δ)`; hence the minor
weight has modulus at most one, and where it is nonzero on that period, `θ` is at distance more
than `δ` from every reduced `c/d` with `1 ≤ d ≤ Q₀`. -/
theorem minorWeight_spec (hP : 1 ≤ Real.log x ^ A₀) (hY : 8 * (Real.log x ^ A₀) ^ 3 ≤ Y)
    (θ : ℝ) :
    |minorWeight A₀ x Y θ| ≤ 1 ∧
      (θ ∈ Set.Ioc (-(2 * arcRadius A₀ x Y)) (-(2 * arcRadius A₀ x Y) + 1) →
        minorWeight A₀ x Y θ ≠ 0 → ∀ (c : ℤ) (d : ℕ), 1 ≤ d → d ≤ ⌊Real.log x ^ A₀⌋₊ →
        Int.gcd c d = 1 → arcRadius A₀ x Y < |θ - c / d|) := by
  set P := Real.log x ^ A₀ with hPdef
  set δ := arcRadius A₀ x Y with hδ
  set Q₀ := ⌊P⌋₊ with hQ₀
  have hP3 : 1 ≤ P ^ 3 := one_le_pow₀ hP
  have hY0 : 0 < Y := by linarith
  have hδ0 : 0 < δ := by rw [hδ, arcRadius]; positivity
  have hQP : (Q₀ : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hQ1 : 1 ≤ Q₀ := Nat.le_floor (by exact_mod_cast hP)
  have hQ1' : (1 : ℝ) ≤ Q₀ := by exact_mod_cast hQ1
  -- `4 δ Q₀² ≤ 1`
  have hδQ : 4 * δ * (Q₀ : ℝ) ^ 2 ≤ 1 := by
    have hq2 : (Q₀ : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (by positivity) hQP 2
    have e : 4 * δ * (Q₀ : ℝ) ^ 2 = 8 * P * Q₀ ^ 2 / Y := by rw [hδ, arcRadius]; ring
    rw [e, div_le_one hY0]
    have : 8 * P * (Q₀ : ℝ) ^ 2 ≤ 8 * P * P ^ 2 := by gcongr
    have e2 : 8 * P * P ^ 2 = 8 * P ^ 3 := by ring
    linarith
  have hsep : 2 * δ < 1 / (Q₀ : ℝ) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    have : 0 < δ * (Q₀ : ℝ) ^ 2 := by positivity
    linarith
  -- the indicators: at most one arc contains `θ`
  set ind : ℕ → ℕ → ℝ := fun k h =>
    (Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator 1 θ with hind
  have hind01 : ∀ k h, ind k h = 0 ∨ ind k h = 1 := by
    intro k h
    simp only [hind, Set.indicator]
    split_ifs <;> simp
  have hpair : ∀ k ∈ Icc 1 Q₀, ∀ h ∈ (range k).filter (fun h => Nat.Coprime h k),
      ∀ k' ∈ Icc 1 Q₀, ∀ h' ∈ (range k').filter (fun h => Nat.Coprime h k'),
      ind k h = 1 → ind k' h' = 1 → (k, h) = (k', h') := by
    intro k hk h hh k' hk' h' hh' h1 h2
    by_contra hne
    simp only [hind, Set.indicator] at h1 h2
    split_ifs at h1 h2 with m1 m2
    · rw [Set.mem_Icc] at m1 m2
      have := one_div_sq_le_abs_sub hk hk' (mem_filter.1 hh).2 (mem_filter.1 hh').2 hne
      have : |(h : ℝ) / k - h' / k'| ≤ 2 * δ := by
        rw [abs_le]
        constructor <;> linarith
      linarith
    all_goals simp_all
  set N := ∑ k ∈ Icc 1 Q₀, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k), ind k h with hN
  have hN01 : N = 0 ∨ N = 1 := by
    by_cases hex : ∃ k ∈ Icc 1 Q₀, ∃ h ∈ (range k).filter (fun h => Nat.Coprime h k),
        ind k h = 1
    · obtain ⟨k, hk, h, hh, h1⟩ := hex
      right
      rw [hN, ← add_sum_erase _ _ hk, ← add_sum_erase _ _ hh, h1]
      have hz1 : ∑ h' ∈ ((range k).filter fun h => Nat.Coprime h k).erase h, ind k h' = 0 :=
        sum_eq_zero fun h' hh' => by
          rcases hind01 k h' with h0 | h0
          · exact h0
          · have := hpair k hk h hh k hk h' (mem_of_mem_erase hh') h1 h0
            simp only [Prod.mk.injEq] at this
            exact ((ne_of_mem_erase hh') this.2.symm).elim
      have hz2 : ∑ k' ∈ (Icc 1 Q₀).erase k,
          ∑ h' ∈ (range k').filter (fun h => Nat.Coprime h k'), ind k' h' = 0 :=
        sum_eq_zero fun k' hk' => sum_eq_zero fun h' hh' => by
          rcases hind01 k' h' with h0 | h0
          · exact h0
          · have := hpair k hk h hh k' (mem_of_mem_erase hk') h' hh' h1 h0
            simp only [Prod.mk.injEq] at this
            exact ((ne_of_mem_erase hk') this.1.symm).elim
      rw [hz1, hz2]
      ring
    · left
      push Not at hex
      refine sum_eq_zero fun k hk => sum_eq_zero fun h hh => ?_
      rcases hind01 k h with h0 | h0
      · exact h0
      · exact (hex k hk h hh h0).elim
  have hw : minorWeight A₀ x Y θ = 1 - N := rfl
  refine ⟨?_, fun hθ hne c d hd1 hdQ hcop => ?_⟩
  · rw [hw]
    rcases hN01 with h | h <;> rw [h] <;> norm_num
  · -- no arc contains `θ`
    have hN0 : N = 0 := by
      rcases hN01 with h | h
      · exact h
      · exact (hne (by rw [hw, h]; ring)).elim
    by_contra hclose
    push Not at hclose
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdQ' : (d : ℝ) ≤ Q₀ := by exact_mod_cast hdQ
    rw [Set.mem_Ioc] at hθ
    rw [abs_le] at hclose
    -- `0 ≤ c < d`
    have h3δ : 3 * δ < 1 / (d : ℝ) := by
      rw [lt_div_iff₀ hd0]
      have h1 : (d : ℝ) ≤ (Q₀ : ℝ) ^ 2 := by nlinarith
      have : 3 * δ * d ≤ 3 * δ * (Q₀ : ℝ) ^ 2 := by gcongr
      linarith
    have hc0 : 0 ≤ c := by
      have : (c : ℝ) / d > -(1 / d) := by linarith
      have : (c : ℝ) > -1 := by
        rw [gt_iff_lt, lt_div_iff₀ hd0] at this
        field_simp at this
        linarith
      have : (-1 : ℤ) < c := by exact_mod_cast this
      omega
    have hcd : c < d := by
      have : (c : ℝ) / d < 1 := by linarith
      rw [div_lt_one hd0] at this
      exact_mod_cast this
    -- the arc `(d, c)` contains `θ`
    have hmem : ind d c.toNat = 1 := by
      simp only [hind]
      rw [Set.indicator_of_mem]
      · rfl
      rw [Set.mem_Icc]
      have : ((c.toNat : ℕ) : ℝ) = c := by exact_mod_cast Int.toNat_of_nonneg hc0
      rw [this]
      constructor <;> linarith
    have hmemf : c.toNat ∈ (range d).filter (fun h => Nat.Coprime h d) := by
      refine mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩
      have : Int.gcd c d = Nat.gcd c.toNat d := by
        rw [Int.gcd, show c.natAbs = c.toNat by omega, Int.natAbs_natCast]
      rw [Nat.Coprime, ← this, hcop]
    have hnn : ∀ k h, 0 ≤ ind k h := fun k h => by
      rcases hind01 k h with h0 | h0 <;> norm_num [h0]
    have hle1 : ind d c.toNat ≤ ∑ h ∈ (range d).filter (fun h => Nat.Coprime h d), ind d h :=
      single_le_sum (f := fun h => ind d h) (fun h _ => hnn d h) hmemf
    have hle2 : ∑ h ∈ (range d).filter (fun h => Nat.Coprime h d), ind d h ≤ N :=
      single_le_sum (f := fun k => ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k), ind k h)
        (fun k _ => sum_nonneg fun h _ => hnn k h) (mem_Icc.2 ⟨hd1, hdQ⟩)
    linarith

/-- **The minor-arc kernel**: with `Y ≥ 8P³` and `P ≥ 1`,
`[n = 0] - ∫_𝔐 e(θ n) dθ = ∫_{-2δ}^{1-2δ} w(θ) e(θ n) dθ`. -/
theorem sub_arcIntegral_eq (hP : 1 ≤ Real.log x ^ A₀) (hY : 8 * (Real.log x ^ A₀) ^ 3 ≤ Y)
    (n : ℤ) :
    (if n = 0 then 1 else 0) - arcIntegral A₀ x Y n =
      ∫ θ in -(2 * arcRadius A₀ x Y)..-(2 * arcRadius A₀ x Y) + 1,
        (minorWeight A₀ x Y θ : ℂ) * ephase (θ * n) := by
  set P := Real.log x ^ A₀ with hPdef
  set δ := arcRadius A₀ x Y with hδ
  set Q₀ := ⌊P⌋₊ with hQ₀
  set lo := -(2 * δ) with hlo
  have hP3 : 1 ≤ P ^ 3 := one_le_pow₀ hP
  have hY0 : 0 < Y := by linarith
  have hδ0 : 0 < δ := by rw [hδ, arcRadius]; positivity
  have hQP : (Q₀ : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hδQ : 4 * δ * (Q₀ : ℝ) ^ 2 ≤ 1 := by
    have hq2 : (Q₀ : ℝ) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (by positivity) hQP 2
    have e : 4 * δ * (Q₀ : ℝ) ^ 2 = 8 * P * Q₀ ^ 2 / Y := by rw [hδ, arcRadius]; ring
    rw [e, div_le_one hY0]
    have : 8 * P * (Q₀ : ℝ) ^ 2 ≤ 8 * P * P ^ 2 := by gcongr
    have e2 : 8 * P * P ^ 2 = 8 * P ^ 3 := by ring
    linarith
  -- each arc lies in the period `(lo, lo + 1]`
  have hsub : ∀ k ∈ Icc 1 Q₀, ∀ h ∈ (range k).filter (fun h => Nat.Coprime h k),
      Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ) ⊆ Set.Ioc lo (lo + 1) := by
    intro k hk h hh
    rw [mem_Icc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hkQ : (k : ℝ) ≤ Q₀ := by exact_mod_cast hk.2
    have hhk : (h : ℝ) + 1 ≤ k := by exact_mod_cast mem_range.1 (mem_filter.1 hh).1
    have h1 : 0 ≤ (h : ℝ) / k := by positivity
    have h2 : (h : ℝ) / k ≤ 1 - 1 / k := by
      rw [div_le_iff₀ hk0, sub_mul, one_div_mul_cancel hk0.ne']
      linarith
    have h3 : 3 * δ < 1 / (k : ℝ) := by
      rw [lt_div_iff₀ hk0]
      have : (k : ℝ) ≤ (Q₀ : ℝ) ^ 2 := by nlinarith
      have : 3 * δ * k ≤ 3 * δ * (Q₀ : ℝ) ^ 2 := by gcongr
      linarith
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    rw [Set.mem_Ioc]
    constructor <;> linarith
  -- the integral of one indicator is the arc integral
  have harc : ∀ k ∈ Icc 1 Q₀, ∀ h ∈ (range k).filter (fun h => Nat.Coprime h k),
      ∫ θ in lo..lo + 1, (((Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator 1 θ : ℝ) : ℂ) *
        ephase (θ * n) =
      ∫ θ in (-(2 * Real.log x ^ A₀ / Y))..(2 * Real.log x ^ A₀ / Y),
        Complex.exp (2 * π * Complex.I * ((((h : ℝ) / k + θ) * n : ℝ) : ℂ)) := by
    intro k hk h hh
    have e1 : ∀ θ, (((Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator 1 θ : ℝ) : ℂ) *
        ephase (θ * n) = (Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator
          (fun θ => ephase (θ * n)) θ := by
      intro θ
      simp only [Set.indicator]
      split_ifs <;> simp
    simp_rw [e1]
    rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.2 (hsub k hk h hh), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
    have e2 := intervalIntegral.integral_comp_add_left (a := -δ) (b := δ)
      (fun θ => ephase (θ * n)) ((h : ℝ) / k)
    rw [show (h : ℝ) / k + -δ = (h : ℝ) / k - δ by ring] at e2
    rw [← e2]
    rfl
  -- integrability
  have hcont : Continuous fun θ : ℝ => ephase (θ * n) := by
    unfold ephase
    fun_prop
  have hint : ∀ k h, IntervalIntegrable (fun θ =>
      (((Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator 1 θ : ℝ) : ℂ) *
        ephase (θ * n)) volume lo (lo + 1) := by
    intro k h
    have e1 : (fun θ => (((Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator 1 θ : ℝ) : ℂ) *
        ephase (θ * n)) = (Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator
          (fun θ => ephase (θ * n)) := by
      funext θ
      simp only [Set.indicator]
      split_ifs <;> simp
    rw [e1]
    exact ⟨(hcont.intervalIntegrable lo (lo + 1)).1.indicator measurableSet_Icc,
      (hcont.intervalIntegrable lo (lo + 1)).2.indicator measurableSet_Icc⟩
  set term : ℕ → ℕ → ℝ → ℂ := fun k h θ =>
    (((Set.Icc ((h : ℝ) / k - δ) ((h : ℝ) / k + δ)).indicator 1 θ : ℝ) : ℂ) * ephase (θ * n)
    with hterm
  set G : ℝ → ℂ := fun θ => ∑ k ∈ Icc 1 Q₀, ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k),
    term k h θ with hG
  have hexp : (fun θ => (minorWeight A₀ x Y θ : ℂ) * ephase (θ * n)) =
      fun θ => ephase (θ * n) - G θ := by
    funext θ
    rw [minorWeight]
    push_cast
    rw [sub_mul, one_mul, hG, sum_mul]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    rw [sum_mul]
  have hki : ∀ k, IntervalIntegrable (fun θ => ∑ h ∈ (range k).filter (fun h => Nat.Coprime h k),
      term k h θ) volume lo (lo + 1) := by
    intro k
    have h := IntervalIntegrable.sum ((range k).filter (fun h => Nat.Coprime h k))
      fun h _ => hint k h
    convert h using 1
    funext θ
    simp only [Finset.sum_apply, hterm]
  have hGi : IntervalIntegrable G volume lo (lo + 1) := by
    have h := IntervalIntegrable.sum (Icc 1 Q₀) fun k _ => hki k
    convert h using 1
    funext θ
    simp only [hG, Finset.sum_apply]
  rw [hexp, intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) hGi]
  rw [intervalIntegral.integral_finsetSum fun k _ => hki k]
  rw [integral_ephase_period, arcIntegral]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [intervalIntegral.integral_finsetSum (f := fun h θ => term k h θ) fun h _ => hint k h]
  exact sum_congr rfl fun h hh => (harc k hk h hh).symm

/-- **Dirichlet approximation on the minor arcs** (PD `mem:dirichlet-minor`): if `θ` is at
distance more than `δ = 2P/Y` from every reduced `c/d` with `d ≤ Q₀ = ⌊P⌋`, and `|u| ≤ P/2`,
then `ϑ = θ + u/Y` has a reduced approximation `|ϑ - c/d| ≤ 1/(dQ)` with `P < d ≤ Q`,
`Q = ⌈Y/P⌉`. -/
theorem exists_dirichlet_minor {P Y θ u : ℝ} (hP : 0 < P) (hY : 0 < Y)
    (hθ : ∀ (c : ℤ) (d : ℕ), 1 ≤ d → d ≤ ⌊P⌋₊ → Int.gcd c d = 1 → 2 * P / Y < |θ - c / d|)
    (hu : |u| ≤ P / 2) :
    ∃ (c : ℤ) (d : ℕ), Int.gcd c d = 1 ∧ P < d ∧ d ≤ ⌈Y / P⌉₊ ∧
      |θ + u / Y - c / d| ≤ 1 / (d * ⌈Y / P⌉₊) := by
  set Q := ⌈Y / P⌉₊ with hQ
  have hQ0 : 0 < Q := Nat.ceil_pos.2 (by positivity)
  have hQr : Y / P ≤ Q := Nat.le_ceil _
  obtain ⟨j, k, hk0, hkQ, hjk⟩ := Real.exists_int_int_abs_mul_sub_le (θ + u / Y) hQ0
  -- reduce `j/k` to lowest terms `c/d`
  set g := Int.gcd j k with hg
  have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_right _ hk0.ne'
  obtain ⟨c, hc⟩ := Int.gcd_dvd_left (a := j) (b := k)
  obtain ⟨d', hd'⟩ := Int.gcd_dvd_right (a := j) (b := k)
  rw [← hg] at hc hd'
  have hd'0 : 0 < d' := by
    rcases lt_trichotomy d' 0 with h | h | h
    · have : (g : ℤ) * d' < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hg0) h
      omega
    · rw [h, mul_zero] at hd'
      omega
    · exact h
  set d := d'.toNat with hd
  have hdd : (d : ℤ) = d' := Int.toNat_of_nonneg hd'0.le
  have hcop : Int.gcd c d = 1 := by
    have := Int.gcd_div_gcd_div_gcd (i := j) (j := k) hg0
    rw [hdd]
    have e1 : j / (g : ℤ) = c := by rw [hc]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0.ne')
    have e2 : k / (g : ℤ) = d' := by rw [hd']; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0.ne')
    rw [← e1, ← e2]
    exact this
  have hd0 : 0 < d := by omega
  have hdk : (d : ℤ) ≤ k := by
    rw [hdd, hd']
    have : (1 : ℤ) ≤ g := by exact_mod_cast hg0
    nlinarith
  have hdQ : d ≤ Q := by
    have : (d : ℤ) ≤ Q := hdk.trans (by exact_mod_cast hkQ)
    exact_mod_cast this
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  -- `|ϑ - c/d| = |kϑ - j|/k ≤ 1/(k(Q+1)) ≤ 1/(dQ)`
  have happ : |θ + u / Y - c / d| ≤ 1 / (d * Q) := by
    have e : θ + u / Y - c / d = (k * (θ + u / Y) - j) / k := by
      have hjr : (j : ℝ) = g * c := by exact_mod_cast hc
      have hkr : (k : ℝ) = g * d := by
        have : (k : ℤ) = g * (d : ℤ) := by rw [hdd]; exact hd'
        exact_mod_cast this
      rw [hjr, hkr]
      have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
      field_simp
    rw [e, abs_div, abs_of_pos hk0']
    have hdk' : (d : ℝ) ≤ k := by exact_mod_cast hdk
    calc |(k : ℝ) * (θ + u / Y) - j| / k ≤ (1 / ((Q : ℝ) + 1)) / k :=
          div_le_div_of_nonneg_right hjk hk0'.le
      _ ≤ 1 / (d * Q) := by
          rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
          have : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
          nlinarith
  refine ⟨c, d, hcop, ?_, hdQ, happ⟩
  -- `d ≤ P` would put `θ` within `δ` of `c/d`
  by_contra hdP
  push Not at hdP
  have hdQ₀ : d ≤ ⌊P⌋₊ := Nat.le_floor hdP
  have h1 := hθ c d hd0 hdQ₀ hcop
  have h2 : |θ - c / d| ≤ |θ + u / Y - c / d| + |u / Y| := by
    calc |θ - c / d| = |(θ + u / Y - c / d) - u / Y| := by ring_nf
      _ ≤ _ := abs_sub _ _
  have h3 : 1 / ((d : ℝ) * Q) ≤ P / Y := by
    rw [div_le_div_iff₀ (by positivity) hY]
    have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have : Y ≤ P * Q := by rwa [div_le_iff₀ hP, mul_comm] at hQr
    nlinarith
  have h4 : |u / Y| ≤ P / 2 / Y := by
    rw [abs_div, abs_of_pos hY]
    exact div_le_div_of_nonneg_right hu hY.le
  have : 2 * P / Y = P / Y + P / Y := by ring
  have : P / 2 / Y < P / Y := by
    rw [div_lt_div_iff_of_pos_right hY]
    linarith
  linarith

/-! ### The cutoff in Fourier space -/

/-- The comparison function `g(ξ) = (1 + (2πξ)²)⁻¹`. -/
def fourierDecay (ξ : ℝ) : ℝ := (1 + (2 * π * ξ) ^ 2)⁻¹

/-- `g` is integrable with integral `1/2`. -/
theorem integrable_fourierDecay :
    Integrable fourierDecay ∧ ∫ ξ, fourierDecay ξ = 1 / 2 := by
  have hpi : 2 * π ≠ 0 := by positivity
  refine ⟨integrable_inv_one_add_sq.comp_mul_left' hpi, ?_⟩
  unfold fourierDecay
  rw [Measure.integral_comp_mul_left (fun y => (1 + y ^ 2)⁻¹), integral_univ_inv_one_add_sq,
    smul_eq_mul, abs_of_pos (by positivity)]
  field_simp

/-- **The cutoff in Fourier space** (PD `mem:cutoff-fourier`): `ψ(s) = ∫ e(s ξ) ψ̂(ξ) dξ`, the
transform is continuous, `|ψ̂| ≤ C g`, and `|ψ̂(ξ)| ≤ (C/U) g(ξ)` for `|ξ| > U ≥ 1`. -/
theorem exists_plateau_fourier :
    ∃ C : ℝ, 0 ≤ C ∧ Continuous (ft fun t => (plateau t : ℂ)) ∧
      (∀ ξ, ‖ft (fun t => (plateau t : ℂ)) ξ‖ ≤ C * fourierDecay ξ) ∧
      (∀ U ξ, 1 ≤ U → U < |ξ| → ‖ft (fun t => (plateau t : ℂ)) ξ‖ ≤ C / U * fourierDecay ξ) ∧
      ∀ s : ℝ, ∫ ξ : ℝ, Complex.exp (2 * π * Complex.I * (s : ℂ) * (ξ : ℂ)) *
        ft (fun t => (plateau t : ℂ)) ξ = (plateau s : ℂ) := by
  set f : ℝ → ℂ := fun t => (plateau t : ℂ) with hfdef
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp Mellin.contDiff_plateau
  have hsupp : ∀ t, 5 < |t| → f t = 0 := fun t ht => by
    simp only [hfdef, Mellin.plateau_eq_zero ht.le, Complex.ofReal_zero]
  have hbd : ∀ k : ℕ, ∃ M, 0 ≤ M ∧ ∀ t, ‖iteratedDeriv k f t‖ ≤ M := by
    intro k
    obtain ⟨M, hM⟩ := (hf.continuous_iteratedDeriv k (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_of_lt_abs (iteratedDeriv_eq_zero_of_lt_abs hsupp k))
    exact ⟨M, (norm_nonneg _).trans (hM 0), hM⟩
  obtain ⟨M₀, hM₀0, hM₀⟩ := hbd 0
  obtain ⟨M₂, hM₂0, hM₂⟩ := hbd 2
  obtain ⟨M₄, hM₄0, hM₄⟩ := hbd 4
  have h0 : ∀ ξ, ‖ft f ξ‖ ≤ 10 * M₀ := fun ξ => by
    have := norm_ft_mul_le (k := 0)
      (hf.of_le (by simp)) (by norm_num) hsupp
      (fun t => by simpa using hM₀ t) ξ
    simpa using this.trans (le_of_eq (by ring))
  have h2 : ∀ ξ, (2 * π * ξ) ^ 2 * ‖ft f ξ‖ ≤ 10 * M₂ := fun ξ => by
    have := norm_ft_mul_le (k := 2) (hf.of_le (by simp)) (by norm_num) hsupp
      hM₂ ξ
    rw [mul_pow, sq_abs, ← mul_pow] at this
    linarith
  have h4 : ∀ ξ, ((2 * π * ξ) ^ 2) ^ 2 * ‖ft f ξ‖ ≤ 10 * M₄ := fun ξ => by
    have := norm_ft_mul_le (k := 4)
      (hf.of_le (by simp)) (by norm_num) hsupp
      hM₄ ξ
    have e : (2 * π * |ξ|) ^ 2 = (2 * π * ξ) ^ 2 := by rw [mul_pow, sq_abs, ← mul_pow]
    rw [show (2 * π * |ξ|) ^ 4 = ((2 * π * |ξ|) ^ 2) ^ 2 by ring, e] at this
    linarith
  refine ⟨10 * (M₀ + M₂) + 20 * M₄, by positivity, ?_, fun ξ => ?_, fun U ξ hU hUξ => ?_, ?_⟩
  · have hfi : Integrable f :=
      hf.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_lt_abs hsupp)
    exact ft_eq_fourier f ▸
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hfi
  · -- `(1 + (2πξ)²) |ψ̂| ≤ 10 (M₀ + M₂)`
    have hpos : 0 < 1 + (2 * π * ξ) ^ 2 := by positivity
    rw [fourierDecay, ← div_eq_mul_inv, le_div_iff₀ hpos]
    have := h0 ξ
    have := h2 ξ
    nlinarith [norm_nonneg (ft f ξ)]
  · -- `|ψ̂| ≤ 10 M₄ / s² ≤ (20 M₄ / U) g` with `s = (2πξ)² ≥ U`
    set s := (2 * π * ξ) ^ 2 with hs
    have hξ : 1 < |ξ| := lt_of_le_of_lt hU hUξ
    have hpi : 1 < 2 * π := by linarith [Real.two_le_pi]
    have hsU : U ≤ s := by
      rw [hs, mul_pow, ← sq_abs ξ]
      have h1 : 1 ≤ (2 * π) ^ 2 := one_le_pow₀ hpi.le
      have : U ≤ |ξ| ^ 2 := by nlinarith
      calc U ≤ |ξ| ^ 2 := this
        _ = 1 * |ξ| ^ 2 := (one_mul _).symm
        _ ≤ (2 * π) ^ 2 * |ξ| ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hs1 : 1 ≤ s := hU.trans hsU
    have hU0 : 0 < U := by linarith
    have hspos : 0 < s := by linarith
    rw [fourierDecay, ← hs, ← div_eq_mul_inv, le_div_iff₀ (by linarith)]
    have h4' := h4 ξ
    rw [← hs] at h4'
    -- `‖ψ̂‖ (1 + s) ≤ 2 s ‖ψ̂‖ ≤ 20 M₄ / s ≤ 20 M₄ / U`
    have hn := norm_nonneg (ft f ξ)
    have e1 : ‖ft f ξ‖ * (1 + s) ≤ 2 * (s * ‖ft f ξ‖) := by nlinarith
    have e2 : s * ‖ft f ξ‖ ≤ 10 * M₄ / s := by
      rw [le_div_iff₀ hspos]
      nlinarith
    have e3 : 10 * M₄ / s ≤ 10 * M₄ / U := div_le_div_of_nonneg_left (by positivity) hU0 hsU
    have hM02 : 0 ≤ 10 * (M₀ + M₂) := by positivity
    have e4 : 20 * M₄ / U ≤ (10 * (M₀ + M₂) + 20 * M₄) / U :=
      div_le_div_of_nonneg_right (by linarith) hU0.le
    have : 2 * (10 * M₄ / U) = 20 * M₄ / U := by ring
    linarith
  · exact fun s => ft_inversion (hf.of_le (by simp)) hsupp s

end Erdos408.OneSided
