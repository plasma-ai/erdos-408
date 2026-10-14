import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Divisor moments and mean values of Dirichlet polynomials

PD Lemma 2.2 and (3.9), with explicit constants.

* `sum_card_divisors_sq_le`: `∑_{n ≤ Y} τ(n)² ≤ Y (1 + log Y)³`.
* `sum_card_divisors_one_add_mul_sq_le` (PD (3.9)): the same moment along the progression
  `1 + l h`, `h ≤ Z`, is at most `4 (Z + (1 + lZ)^{3/4}) (1 + log(1 + lZ))³`.
* `integral_norm_dirichlet_sq_le` (PD (2.4)): the mean square of a Dirichlet polynomial of
  length `N` over an interval of length `T` is at most `(T + 8N(1 + log N)) ∑ |c_n|²`.
* `sum_norm_dirichlet_sq_le` (PD (2.5)): the same at points of mutual spacing at least one,
  with the extra factor `2(1 + log N)²`.

The constants do not depend on the coefficients. This matters in PD Lemma 5.3, where the
polynomial is raised to a growing power.
-/

namespace Erdos408.OneSided

open Finset

/-! ### Divisor moments -/

/-- The harmonic bound `∑_{k ≤ Y} 1/k ≤ 1 + log Y`. -/
theorem sum_Icc_inv_le (Y : ℕ) : ∑ k ∈ Icc 1 Y, (k : ℝ)⁻¹ ≤ 1 + Real.log Y := by
  have h := harmonic_le_one_add_log Y
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

/-- `∑_{t ∈ [1, Y]³} 1 / (t₀ t₁ t₂) ≤ (1 + log Y)³`. -/
theorem sum_inv_prod_le (Y : ℕ) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin 3 => Icc 1 Y), ((∏ i, t i : ℕ) : ℝ)⁻¹ ≤
      (1 + Real.log Y) ^ 3 := by
  have h : ∑ t ∈ Fintype.piFinset (fun _ : Fin 3 => Icc 1 Y), ((∏ i, t i : ℕ) : ℝ)⁻¹ =
      (∑ k ∈ Icc 1 Y, (k : ℝ)⁻¹) ^ 3 := by
    rw [← Fin.prod_const, prod_univ_sum]
    simp [Nat.cast_prod, prod_inv_distrib]
  rw [h]
  exact pow_le_pow_left₀ (sum_nonneg fun k _ => by positivity) (sum_Icc_inv_le Y) 3

/-- `τ(n)² ≤ τ₄(n)`: a pair of divisors `(d, e)` with `g = gcd(d, e)` gives the
factorization `n = g · (d / g) · (e / g) · (n / lcm(d, e))`, from which `d` and `e` are
recovered. -/
theorem card_divisors_sq_le (n : ℕ) : n.divisors.card ^ 2 ≤ (Nat.finMulAntidiag 4 n).card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [sq, ← card_product]
  refine card_le_card_of_injOn
    (fun p => ![p.1.gcd p.2, p.1 / p.1.gcd p.2, p.2 / p.1.gcd p.2, n / p.1.lcm p.2]) ?_ ?_
  · rintro ⟨d, e⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors] at hp
    rw [mem_coe, Nat.mem_finMulAntidiag]
    refine ⟨?_, hn.ne'⟩
    -- `lcm(d, e) = g · (d / g) · (e / g)`
    set g := d.gcd e with hg_def
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos hp.1.1 hn)
    obtain ⟨a, ha⟩ := Nat.gcd_dvd_left d e
    obtain ⟨b, hb⟩ := Nat.gcd_dvd_right d e
    rw [← hg_def] at ha hb
    have hl : d.lcm e = g * a * b := by
      refine Nat.eq_of_mul_eq_mul_left hg ?_
      rw [hg_def, Nat.gcd_mul_lcm, ← hg_def]
      calc d * e = g * a * (g * b) := by rw [← ha, ← hb]
        _ = g * (g * a * b) := by ring
    have hda : d / g = a := by
      rw [ha]
      exact Nat.mul_div_cancel_left _ hg
    have hdb : e / g = b := by
      rw [hb]
      exact Nat.mul_div_cancel_left _ hg
    simp only [Fin.prod_univ_four, Matrix.cons_val]
    rw [hda, hdb, ← hg_def, ← hl, mul_comm]
    exact Nat.div_mul_cancel (Nat.lcm_dvd hp.1.1 hp.2.1)
  · rintro ⟨d, e⟩ hp ⟨d', e'⟩ hp' h
    simp only [coe_product, Set.mem_prod, mem_coe, Nat.mem_divisors] at hp hp'
    -- `d = g · (d / g)` and `e = g · (e / g)`
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    simp only [Matrix.cons_val] at h₀ h₁ h₂
    have hd : d = d' :=
      calc d = d.gcd e * (d / d.gcd e) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)).symm
        _ = d'.gcd e' * (d' / d'.gcd e') := by rw [h₁, h₀]
        _ = d' := Nat.mul_div_cancel' (Nat.gcd_dvd_left d' e')
    have he : e = e' :=
      calc e = d.gcd e * (e / d.gcd e) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
        _ = d'.gcd e' * (e' / d'.gcd e') := by rw [h₂, h₀]
        _ = e' := Nat.mul_div_cancel' (Nat.gcd_dvd_right d' e')
    rw [hd, he]

/-- Deleting coordinate `i` of a factorization `n = f₀ f₁ f₂ f₃` leaves a triple in `[1, Q]³`
whose product is `n / fᵢ`. -/
theorem removeNth_mem_of_mem_finMulAntidiag {n Q : ℕ} (hnQ : n ≤ Q) {f : Fin 4 → ℕ}
    (hf : f ∈ Nat.finMulAntidiag 4 n) (i : Fin 4) :
    Fin.removeNth i f ∈ Fintype.piFinset (fun _ : Fin 3 => Icc 1 Q) ∧
      f i * ∏ j, Fin.removeNth i f j = n := by
  rw [Nat.mem_finMulAntidiag] at hf
  have hprod : f i * ∏ j, Fin.removeNth i f j = n := by
    rw [← hf.1, Fin.prod_univ_succAbove _ i]
    rfl
  refine ⟨Fintype.mem_piFinset.2 fun j => ?_, hprod⟩
  -- each factor divides `n ≠ 0`
  have hdvd : f (i.succAbove j) ∣ n := hf.1 ▸ dvd_prod_of_mem f (mem_univ _)
  have hpos := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hf.2)
  rw [mem_Icc, Fin.removeNth_apply]
  exact ⟨hpos, (Nat.le_of_dvd (Nat.pos_of_ne_zero hf.2) hdvd).trans hnQ⟩

/-- Deleting one coordinate of a factorization of `n ≠ 0` into four factors loses no
information: the deleted factor is `n` divided by the product of the others. -/
theorem injOn_removeNth (n : ℕ) (i : Fin 4) :
    Set.InjOn (Fin.removeNth i) (Nat.finMulAntidiag 4 n : Set (Fin 4 → ℕ)) := by
  intro f hf f' hf' h
  have h₁ := (removeNth_mem_of_mem_finMulAntidiag le_rfl hf i).2
  have h₂ := (removeNth_mem_of_mem_finMulAntidiag le_rfl hf' i).2
  have hn := (Nat.mem_finMulAntidiag.1 hf).2
  rw [h] at h₁
  have hi : f i = f' i := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero fun h0 => hn ?_) (h₁.trans h₂.symm)
    rw [← h₂, h0, mul_zero]
  rw [← Fin.insertNth_self_removeNth i f, ← Fin.insertNth_self_removeNth i f', h, hi]

/-- `τ₄(n)` counts the triples in `[1, Y]³` whose product divides `n`, for `n ≤ Y`. -/
theorem card_finMulAntidiag_le {n Y : ℕ} (hnY : n ≤ Y) :
    (Nat.finMulAntidiag 4 n).card ≤
      #{t ∈ Fintype.piFinset (fun _ : Fin 3 => Icc 1 Y) | ∏ i, t i ∣ n} := by
  refine card_le_card_of_injOn (Fin.removeNth 3) (fun f hf => ?_) (injOn_removeNth n 3)
  obtain ⟨hmem, hprod⟩ := removeNth_mem_of_mem_finMulAntidiag hnY hf 3
  rw [mem_coe, mem_filter]
  exact ⟨hmem, Dvd.intro_left _ hprod⟩

/-- `τ₄(n) ≤ 4 #{t ∈ [1, Q]³ : t₀ t₁ t₂ ∣ n, (t₀ t₁ t₂)⁴ ≤ Q³}` for `n ≤ Q`: deleting a
largest factor of a factorization into four leaves a product at most `n^{3/4}`. -/
theorem card_finMulAntidiag_le_four {n Q : ℕ} (hnQ : n ≤ Q) :
    (Nat.finMulAntidiag 4 n).card ≤
      4 * #{t ∈ Fintype.piFinset (fun _ : Fin 3 => Icc 1 Q) |
        ∏ i, t i ∣ n ∧ (∏ i, t i) ^ 4 ≤ Q ^ 3} := by
  -- every factorization has a factor `fᵢ` with `n ≤ fᵢ⁴`
  have hcover : Nat.finMulAntidiag 4 n ⊆
      univ.biUnion fun i => {f ∈ Nat.finMulAntidiag 4 n | n ≤ f i ^ 4} := by
    intro f hf
    obtain ⟨i, -, hi⟩ := exists_max_image univ f univ_nonempty
    have hle : ∏ j, f j ≤ f i ^ 4 := by
      simpa using prod_le_pow_card univ f (f i) fun j _ => hi j (mem_univ j)
    rw [(Nat.mem_finMulAntidiag.1 hf).1] at hle
    exact mem_biUnion.2 ⟨i, mem_univ i, mem_filter.2 ⟨hf, hle⟩⟩
  refine (card_le_card hcover).trans (card_biUnion_le.trans ?_)
  rw [show 4 * #{t ∈ Fintype.piFinset (fun _ : Fin 3 => Icc 1 Q) |
        ∏ i, t i ∣ n ∧ (∏ i, t i) ^ 4 ≤ Q ^ 3} =
      ∑ _i : Fin 4, #{t ∈ Fintype.piFinset (fun _ : Fin 3 => Icc 1 Q) |
        ∏ i, t i ∣ n ∧ (∏ i, t i) ^ 4 ≤ Q ^ 3} by simp]
  refine sum_le_sum fun i _ => card_le_card_of_injOn (Fin.removeNth i) (fun f hf => ?_)
    ((injOn_removeNth n i).mono (filter_subset _ _))
  rw [mem_coe, mem_filter] at hf
  obtain ⟨hmem, hprod⟩ := removeNth_mem_of_mem_finMulAntidiag hnQ hf.1 i
  have hn := Nat.pos_of_ne_zero (Nat.mem_finMulAntidiag.1 hf.1).2
  rw [mem_coe, mem_filter]
  refine ⟨hmem, Dvd.intro_left _ hprod, ?_⟩
  -- `P⁴ n ≤ P⁴ fᵢ⁴ = n⁴`
  have h₄ : (∏ j, Fin.removeNth i f j) ^ 4 * n ≤ n ^ 3 * n :=
    calc (∏ j, Fin.removeNth i f j) ^ 4 * n
        ≤ (∏ j, Fin.removeNth i f j) ^ 4 * f i ^ 4 := Nat.mul_le_mul_left _ hf.2
      _ = (f i * ∏ j, Fin.removeNth i f j) ^ 4 := by ring
      _ = n ^ 3 * n := by rw [hprod]; ring
  exact (Nat.le_of_mul_le_mul_right h₄ hn).trans (Nat.pow_le_pow_left hnQ 3)

/-- `∑_{n ≤ Y} τ(n)² ≤ Y (1 + log Y)³`. -/
theorem sum_card_divisors_sq_le (Y : ℕ) :
    ∑ n ∈ Icc 1 Y, ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ Y * (1 + Real.log Y) ^ 3 := by
  set B := Fintype.piFinset (fun _ : Fin 3 => Icc 1 Y)
  -- `τ(n)² ≤ #{t ∈ [1, Y]³ : t₀ t₁ t₂ ∣ n}`
  have h₁ : ∑ n ∈ Icc 1 Y, ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤
      ∑ n ∈ Icc 1 Y, (#{t ∈ B | ∏ i, t i ∣ n} : ℝ) := by
    refine sum_le_sum fun n hn => ?_
    exact_mod_cast (card_divisors_sq_le n).trans (card_finMulAntidiag_le (mem_Icc.1 hn).2)
  -- swap the sums and count the multiples of `t₀ t₁ t₂`
  have h₂ : ∑ n ∈ Icc 1 Y, #{t ∈ B | ∏ i, t i ∣ n} = ∑ t ∈ B, Y / ∏ i, t i := by
    have hIcc : Icc 1 Y = Ioc 0 Y := by
      ext n
      simp only [mem_Icc, mem_Ioc]
      omega
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [← card_filter, hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  rw [← Nat.cast_sum, h₂, Nat.cast_sum] at h₁
  refine h₁.trans ?_
  calc ∑ t ∈ B, ((Y / ∏ i, t i : ℕ) : ℝ) ≤ ∑ t ∈ B, Y * ((∏ i, t i : ℕ) : ℝ)⁻¹ :=
        sum_le_sum fun t _ => Nat.cast_div_le.trans_eq (div_eq_mul_inv _ _)
    _ = Y * ∑ t ∈ B, ((∏ i, t i : ℕ) : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ Y * (1 + Real.log Y) ^ 3 := by gcongr; exact sum_inv_prod_le Y

/-- At most `Z / m + 1` of the `h ∈ [1, Z]` have `m ∣ 1 + l h`: all of them lie in one
residue class mod `m`, since `l` is invertible mod `m`. -/
theorem card_filter_dvd_one_add_mul_le (l Z m : ℕ) (hm : 0 < m) :
    (#{h ∈ Icc 1 Z | m ∣ 1 + l * h} : ℝ) ≤ Z / m + 1 := by
  rcases eq_empty_or_nonempty {h ∈ Icc 1 Z | m ∣ 1 + l * h} with hA | ⟨h₀, hh₀⟩
  · rw [hA, card_empty, Nat.cast_zero]
    positivity
  -- every `h` in the set is `≡ h₀ (mod m)`
  have hmod : ∀ h ∈ {h ∈ Icc 1 Z | m ∣ 1 + l * h}, h % m = h₀ % m := by
    intro h hh
    have e₁ := (ZMod.natCast_eq_zero_iff _ m).2 (mem_filter.1 hh).2
    have e₂ := (ZMod.natCast_eq_zero_iff _ m).2 (mem_filter.1 hh₀).2
    push_cast at e₁ e₂
    refine (ZMod.natCast_eq_natCast_iff' h h₀ m).1 ?_
    linear_combination (h : ZMod m) * e₂ - (h₀ : ZMod m) * e₁
  -- so `h ↦ h / m` is injective on it, with values in `[0, Z / m]`
  have hcard : #{h ∈ Icc 1 Z | m ∣ 1 + l * h} ≤ #(range (Z / m + 1)) := by
    refine card_le_card_of_injOn (· / m) (fun h hh => ?_) (fun h hh h' hh' hhh => ?_)
    · rw [mem_coe, mem_filter, mem_Icc] at hh
      rw [mem_coe, mem_range, Nat.lt_succ_iff]
      exact Nat.div_le_div_right hh.1.2
    · rw [← Nat.div_add_mod h m, ← Nat.div_add_mod h' m, hmod h hh, hmod h' hh']
      simp only at hhh
      rw [hhh]
  rw [card_range] at hcard
  calc (#{h ∈ Icc 1 Z | m ∣ 1 + l * h} : ℝ) ≤ ((Z / m + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ Z / m + 1 := by
      push_cast
      gcongr
      exact Nat.cast_div_le

/-- PD (3.9): `∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + (1 + lZ)^{3/4}) (1 + log(1 + lZ))³`. -/
theorem sum_card_divisors_one_add_mul_sq_le (l Z : ℕ) :
    ∑ h ∈ Icc 1 Z, (((1 + l * h).divisors.card : ℕ) : ℝ) ^ 2 ≤
      4 * (Z + ((1 + l * Z : ℕ) : ℝ) ^ (3 / 4 : ℝ)) *
        (1 + Real.log ((1 + l * Z : ℕ) : ℝ)) ^ 3 := by
  set Q := 1 + l * Z
  set X := (Q : ℝ) ^ (3 / 4 : ℝ)
  set B := Fintype.piFinset (fun _ : Fin 3 => Icc 1 Q)
  set B' := {t ∈ B | (∏ i, t i) ^ 4 ≤ Q ^ 3}
  -- `τ(1 + l h)² ≤ 4 #{t ∈ B' : t₀ t₁ t₂ ∣ 1 + l h}`
  have h₁ : ∑ h ∈ Icc 1 Z, (((1 + l * h).divisors.card : ℕ) : ℝ) ^ 2 ≤
      4 * ∑ h ∈ Icc 1 Z, (#{t ∈ B' | ∏ i, t i ∣ 1 + l * h} : ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun h hh => ?_
    have hQ : 1 + l * h ≤ Q := Nat.add_le_add_left (Nat.mul_le_mul_left _ (mem_Icc.1 hh).2) 1
    have hB : {t ∈ B' | ∏ i, t i ∣ 1 + l * h} =
        {t ∈ B | ∏ i, t i ∣ 1 + l * h ∧ (∏ i, t i) ^ 4 ≤ Q ^ 3} := by
      ext t
      simp only [B', mem_filter]
      tauto
    rw [hB]
    exact_mod_cast (card_divisors_sq_le _).trans (card_finMulAntidiag_le_four hQ)
  -- swap the sums
  have h₂ : ∑ h ∈ Icc 1 Z, #{t ∈ B' | ∏ i, t i ∣ 1 + l * h} =
      ∑ t ∈ B', #{h ∈ Icc 1 Z | ∏ i, t i ∣ 1 + l * h} := by
    simp only [card_filter]
    exact sum_comm
  rw [← Nat.cast_sum, h₂, Nat.cast_sum] at h₁
  refine h₁.trans ?_
  -- each `t ∈ B'` has `1 ≤ t₀ t₁ t₂ ≤ X`
  have hB' : ∀ t ∈ B', 1 ≤ ((∏ i, t i : ℕ) : ℝ) ∧ ((∏ i, t i : ℕ) : ℝ) ≤ X := by
    intro t ht
    rw [mem_filter, Fintype.mem_piFinset] at ht
    refine ⟨?_, ?_⟩
    · exact_mod_cast Nat.one_le_iff_ne_zero.2
        (prod_ne_zero_iff.2 fun i _ => (Nat.lt_of_lt_of_le one_pos (mem_Icc.1 (ht.1 i)).1).ne')
    · refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
      rw [← Real.rpow_natCast X, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
      exact_mod_cast ht.2
  calc 4 * ∑ t ∈ B', (#{h ∈ Icc 1 Z | ∏ i, t i ∣ 1 + l * h} : ℝ)
      ≤ 4 * ∑ t ∈ B', (Z + X) * ((∏ i, t i : ℕ) : ℝ)⁻¹ := by
        gcongr with t ht
        obtain ⟨hp, hpX⟩ := hB' t ht
        refine (card_filter_dvd_one_add_mul_le l Z _ (by exact_mod_cast hp)).trans ?_
        rw [add_mul, ← div_eq_mul_inv, ← div_eq_mul_inv]
        gcongr
        rwa [one_le_div (by linarith)]
    _ ≤ 4 * ∑ t ∈ B, (Z + X) * ((∏ i, t i : ℕ) : ℝ)⁻¹ := by
        gcongr 4 * ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ => by positivity
    _ ≤ 4 * (Z + X) * (1 + Real.log Q) ^ 3 := by
        rw [← mul_sum, ← mul_assoc]
        gcongr
        exact sum_inv_prod_le Q

/-! ### Mean values of Dirichlet polynomials -/

/-- `n^{it} = exp(i t log n)` for `n ≠ 0`. -/
theorem natCast_cpow_mul_I {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ ((t : ℂ) * Complex.I) = Complex.exp ((Real.log n : ℂ) * Complex.I * t) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hn), ← Complex.natCast_log]
  ring_nf

/-- `m^{it} \overline{n^{it}} = exp(i t (log m - log n))` for `m, n ≠ 0`. -/
theorem natCast_cpow_mul_I_mul_conj {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) :
    (m : ℂ) ^ ((t : ℂ) * Complex.I) * (starRingEnd ℂ) ((n : ℂ) ^ ((t : ℂ) * Complex.I)) =
      Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * t) := by
  rw [natCast_cpow_mul_I hm, natCast_cpow_mul_I hn, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `|∫_a^b exp(i θ t) dt| ≤ 2 / |θ|` for `θ ≠ 0`. -/
theorem norm_integral_exp_mul_I_le {θ : ℝ} (hθ : θ ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp ((θ : ℂ) * Complex.I * t)‖ ≤ 2 / |θ| := by
  have hc : (θ : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hθ) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  gcongr
  refine (norm_sub_le _ _).trans_eq ?_
  -- both exponentials lie on the unit circle
  have h : ∀ x : ℝ, ‖Complex.exp ((θ : ℂ) * Complex.I * x)‖ = 1 := fun x => by
    rw [show (θ : ℂ) * Complex.I * x = ((θ * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [h, h]
  norm_num

/-- `|m - n| / N ≤ |log m - log n|` for `1 ≤ m, n ≤ N`. -/
theorem abs_sub_div_le_abs_log_sub {m n N : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hmN : m ≤ N)
    (hnN : n ≤ N) : |(m : ℝ) - n| / N ≤ |Real.log m - Real.log n| := by
  wlog h : n ≤ m generalizing m n
  · rw [abs_sub_comm, abs_sub_comm (Real.log m)]
    exact this hn hm hnN hmN (by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast h
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  -- `1 - n / m ≤ log (m / n)`
  have h₁ := Real.one_sub_inv_le_log_of_pos (div_pos hm' hn')
  rw [Real.log_div hm'.ne' hn'.ne', inv_div] at h₁
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [Real.log_le_log hn' hnm])]
  calc ((m : ℝ) - n) / N ≤ (m - n) / m := by gcongr
    _ = 1 - n / m := by field_simp
    _ ≤ _ := h₁

/-- `∑_{n ≤ N} 1 / |m - n| ≤ 2 (1 + log N)` for `1 ≤ m ≤ N`, the term `n = m` being `0`. -/
theorem sum_inv_abs_sub_le {m N : ℕ} (hm : m ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, |(m : ℝ) - n|⁻¹ ≤ 2 * (1 + Real.log N) := by
  rw [mem_Icc] at hm
  rw [← sum_erase (Icc 1 N) (f := fun n => |(m : ℝ) - n|⁻¹) (a := m) (by simp),
    ← sum_filter_add_sum_filter_not _ (· < m), two_mul]
  gcongr
  -- the terms `n < m` are `1 / (m - n)`
  · refine (sum_le_sum_of_injOn (fun n => m - n) (fun n hn n' hn' h => ?_) (fun k hk => ?_)
      (fun n hn => ?_) (fun k _ _ => by positivity)).trans (sum_Icc_inv_le N)
    · simp only [mem_coe, mem_filter, mem_erase, mem_Icc] at hn hn' h
      omega
    · simp only [mem_image, mem_filter, mem_erase, mem_Icc] at hk
      obtain ⟨n, hn, rfl⟩ := hk
      rw [mem_Icc]
      omega
    · simp only [mem_filter, mem_erase, mem_Icc] at hn
      rw [Nat.cast_sub hn.2.le, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hn.2.le))]
  -- the terms `n > m` are `1 / (n - m)`
  · refine (sum_le_sum_of_injOn (fun n => n - m) (fun n hn n' hn' h => ?_) (fun k hk => ?_)
      (fun n hn => ?_) (fun k _ _ => by positivity)).trans (sum_Icc_inv_le N)
    · simp only [mem_coe, mem_filter, mem_erase, mem_Icc] at hn hn' h
      omega
    · simp only [mem_image, mem_filter, mem_erase, mem_Icc] at hk
      obtain ⟨n, hn, rfl⟩ := hk
      rw [mem_Icc]
      omega
    · simp only [mem_filter, mem_erase, mem_Icc, not_lt] at hn
      rw [Nat.cast_sub hn.2, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hn.2))]

/-- PD (2.4): `∫_a^b |∑_{n ≤ N} c_n n^{it}|² dt ≤ (b - a + 8 N (1 + log N)) ∑ |c_n|²`. -/
theorem integral_norm_dirichlet_sq_le (N : ℕ) (c : ℕ → ℂ) (a b : ℝ) :
    ∫ t in a..b, ‖∑ n ∈ Icc 1 N, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      (b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 := by
  set J : ℕ → ℕ → ℂ := fun m n =>
    ∫ t in a..b, Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * t)
  -- expand the square: `∫ |P|² = ∑_{m, n} c_m \bar c_n ∫ (m / n)^{it}`
  have hexp : ∫ t in a..b, ‖∑ n ∈ Icc 1 N, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (c m * (starRingEnd ℂ) (c n) * J m n).re := by
    have hpt : ∀ t : ℝ,
        ((‖∑ n ∈ Icc 1 N, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
          ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, c m * (starRingEnd ℂ) (c n) *
            Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * t) := by
      intro t
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, sum_mul_sum]
      refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
      rw [map_mul, ← natCast_cpow_mul_I_mul_conj (by grind) (by grind)]
      ring
    have hint : ∀ m n : ℕ, IntervalIntegrable
        (fun t : ℝ => Complex.exp (((Real.log m - Real.log n : ℝ) : ℂ) * Complex.I * t))
        MeasureTheory.volume a b :=
      fun m n => Continuous.intervalIntegrable (by fun_prop) _ _
    rw [← Complex.ofReal_re (∫ t in a..b, _), ← intervalIntegral.integral_ofReal]
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum fun m _ => ?_, Complex.re_sum]
    · refine sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finsetSum fun n _ => (hint m n).const_mul _, Complex.re_sum]
      refine sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  -- each term is at most the diagonal part plus `N (|c_m|² + |c_n|²) / |m - n|`
  have hterm : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, (c m * (starRingEnd ℂ) (c n) * J m n).re ≤
      (if m = n then (b - a) * ‖c m‖ ^ 2 else 0) +
        N * (‖c m‖ ^ 2 + ‖c n‖ ^ 2) * |(m : ℝ) - n|⁻¹ := by
    intro m hm n hn
    rcases eq_or_ne m n with rfl | hmn
    · simp only [J, sub_self, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
        intervalIntegral.integral_const, ite_true, abs_zero, inv_zero, mul_zero, add_zero]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp [mul_comm]
      norm_cast
    rw [mem_Icc] at hm hn
    have hmn' : (m : ℝ) ≠ n := by exact_mod_cast hmn
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hd : 0 < |(m : ℝ) - n| / N := div_pos (abs_pos.2 (sub_ne_zero.2 hmn')) hN
    have hlog := abs_sub_div_le_abs_log_sub hm.1 hn.1 hm.2 hn.2
    -- `|J m n| ≤ 2 / |log m - log n| ≤ 2 N / |m - n|`
    have hJ : ‖J m n‖ ≤ 2 * N * |(m : ℝ) - n|⁻¹ :=
      calc ‖J m n‖ ≤ 2 / |Real.log m - Real.log n| :=
            norm_integral_exp_mul_I_le (abs_pos.1 (hd.trans_le hlog)) a b
        _ ≤ 2 / (|(m : ℝ) - n| / N) := by gcongr
        _ = 2 * N * |(m : ℝ) - n|⁻¹ := by field_simp
    rw [ite_eq_right hmn, zero_add]
    calc (c m * (starRingEnd ℂ) (c n) * J m n).re ≤ ‖c m * (starRingEnd ℂ) (c n) * J m n‖ :=
          Complex.re_le_norm _
      _ = ‖c m‖ * ‖c n‖ * ‖J m n‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]
      _ ≤ ‖c m‖ * ‖c n‖ * (2 * N * |(m : ℝ) - n|⁻¹) := by gcongr
      _ = N * (2 * ‖c m‖ * ‖c n‖) * |(m : ℝ) - n|⁻¹ := by ring
      _ ≤ N * (‖c m‖ ^ 2 + ‖c n‖ ^ 2) * |(m : ℝ) - n|⁻¹ := by
          gcongr
          exact two_mul_le_add_sq _ _
  -- the off-diagonal part is symmetric in `m` and `n`
  have hoff : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, N * (‖c m‖ ^ 2 + ‖c n‖ ^ 2) * |(m : ℝ) - n|⁻¹ =
      2 * N * ∑ m ∈ Icc 1 N, ‖c m‖ ^ 2 * ∑ n ∈ Icc 1 N, |(m : ℝ) - n|⁻¹ := by
    have hsym : ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, N * ‖c n‖ ^ 2 * |(m : ℝ) - n|⁻¹ =
        ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, N * ‖c m‖ ^ 2 * |(m : ℝ) - n|⁻¹ := by
      rw [sum_comm]
      exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [abs_sub_comm]
    simp_rw [mul_add, add_mul, sum_add_distrib]
    rw [hsym, ← two_mul, mul_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum, mul_sum, mul_sum]
    exact sum_congr rfl fun n _ => by ring
  have hA : 0 ≤ ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 := sum_nonneg fun n _ => by positivity
  rw [hexp]
  calc ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (c m * (starRingEnd ℂ) (c n) * J m n).re
      ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, ((if m = n then (b - a) * ‖c m‖ ^ 2 else 0) +
          N * (‖c m‖ ^ 2 + ‖c n‖ ^ 2) * |(m : ℝ) - n|⁻¹) :=
        sum_le_sum fun m hm => sum_le_sum fun n hn => hterm m hm n hn
    _ = (b - a) * ∑ m ∈ Icc 1 N, ‖c m‖ ^ 2 +
          2 * N * ∑ m ∈ Icc 1 N, ‖c m‖ ^ 2 * ∑ n ∈ Icc 1 N, |(m : ℝ) - n|⁻¹ := by
        rw [← hoff, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun m hm => ?_
        rw [sum_add_distrib, sum_ite_eq, ite_eq_left hm]
    _ ≤ (b - a) * ∑ m ∈ Icc 1 N, ‖c m‖ ^ 2 +
          2 * N * ∑ m ∈ Icc 1 N, ‖c m‖ ^ 2 * (2 * (1 + Real.log N)) := by
        gcongr with m hm
        exact sum_inv_abs_sub_le hm
    _ ≤ (b - a + 8 * N * (1 + Real.log N)) * ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 := by
        have h : 0 ≤ N * (1 + Real.log N) * ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 := by positivity
        rw [← sum_mul]
        linarith


/-- Gallagher's Sobolev inequality on a unit interval:
`|f(t)|² ≤ ∫_{t - 1/2}^{t + 1/2} (2 |f|² + |f'|²)`. By the fundamental theorem of calculus,
`|f(t)|² ≤ |f(x)|² + ∫ |(|f|²)'|` for every `x` in the interval, and
`|(|f|²)'| ≤ 2 |f| |f'| ≤ |f|² + |f'|²`; then average over `x`. -/
theorem sq_norm_le_integral {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s)
    (hf' : Continuous f') (t : ℝ) :
    ‖f t‖ ^ 2 ≤ ∫ s in (t - 1 / 2)..(t + 1 / 2), (2 * ‖f s‖ ^ 2 + ‖f' s‖ ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun s => (hf s).continuousAt
  have hg : ∀ s, HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * inner ℝ (f s) (f' s)) s :=
    fun s => (hf s).norm_sq
  have hgc : Continuous fun s => 2 * inner ℝ (f s) (f' s) := by fun_prop
  have hhc : Continuous fun s => ‖f s‖ ^ 2 + ‖f' s‖ ^ 2 := by fun_prop
  -- `|(|f|²)'| ≤ |f|² + |f'|²`
  have hbound : ∀ s, ‖2 * inner ℝ (f s) (f' s)‖ ≤ ‖f s‖ ^ 2 + ‖f' s‖ ^ 2 := by
    intro s
    rw [Real.norm_eq_abs, abs_mul, abs_two]
    calc 2 * |inner ℝ (f s) (f' s)| ≤ 2 * (‖f s‖ * ‖f' s‖) := by
          gcongr
          exact abs_real_inner_le_norm _ _
      _ = 2 * ‖f s‖ * ‖f' s‖ := by ring
      _ ≤ _ := two_mul_le_add_sq _ _
  set K := ∫ s in (t - 1 / 2)..(t + 1 / 2), (‖f s‖ ^ 2 + ‖f' s‖ ^ 2) with hK
  -- `|f(t)|² ≤ |f(x)|² + K` on the interval
  have hpt : ∀ x ∈ Set.Icc (t - 1 / 2) (t + 1 / 2), ‖f t‖ ^ 2 ≤ ‖f x‖ ^ 2 + K := by
    intro x hx
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hg s)
      (hgc.intervalIntegrable x t)
    have hsub : Set.uIoc x t ⊆ Set.Ioc (t - 1 / 2) (t + 1 / 2) := by
      rw [Set.uIoc]
      exact Set.Ioc_subset_Ioc (le_min hx.1 (by linarith)) (max_le hx.2 (by linarith))
    have hle : ∫ s in x..t, 2 * inner ℝ (f s) (f' s) ≤ K :=
      calc ∫ s in x..t, 2 * inner ℝ (f s) (f' s)
          ≤ ‖∫ s in x..t, 2 * inner ℝ (f s) (f' s)‖ := Real.le_norm_self _
        _ ≤ ∫ s in Set.uIoc x t, ‖2 * inner ℝ (f s) (f' s)‖ :=
            intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ s in Set.uIoc x t, (‖f s‖ ^ 2 + ‖f' s‖ ^ 2) :=
            MeasureTheory.setIntegral_mono hgc.norm.integrableOn_uIoc hhc.integrableOn_uIoc
              hbound
        _ ≤ ∫ s in Set.Ioc (t - 1 / 2) (t + 1 / 2), (‖f s‖ ^ 2 + ‖f' s‖ ^ 2) :=
            MeasureTheory.setIntegral_mono_set hhc.integrableOn_Ioc
              (Filter.Eventually.of_forall fun s => by positivity) hsub.eventuallySubset
        _ = K := (intervalIntegral.integral_of_le (by linarith)).symm
    linarith
  -- average over `x`
  have hint : IntervalIntegrable (fun s => ‖f s‖ ^ 2) MeasureTheory.volume
      (t - 1 / 2) (t + 1 / 2) :=
    (by fun_prop : Continuous fun s => ‖f s‖ ^ 2).intervalIntegrable _ _
  have hlen : t + 1 / 2 - (t - 1 / 2) = 1 := by ring
  calc ‖f t‖ ^ 2 = ∫ _ in (t - 1 / 2)..(t + 1 / 2), ‖f t‖ ^ 2 := by
        rw [intervalIntegral.integral_const, hlen, one_smul]
    _ ≤ ∫ s in (t - 1 / 2)..(t + 1 / 2), (‖f s‖ ^ 2 + K) :=
        intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
          (hint.add intervalIntegrable_const) hpt
    _ = ∫ s in (t - 1 / 2)..(t + 1 / 2), (2 * ‖f s‖ ^ 2 + ‖f' s‖ ^ 2) := by
        rw [intervalIntegral.integral_add hint intervalIntegrable_const,
          intervalIntegral.integral_const, hlen, one_smul, hK,
          ← intervalIntegral.integral_add hint (hhc.intervalIntegrable _ _)]
        congr 1
        ext s
        ring

/-- For continuous `G ≥ 0` and points of `[a, b]` with mutual spacing at least one, the
intervals `(t - 1/2, t + 1/2]` are disjoint inside `(a - 1/2, b + 1/2]`, so
`∑_t ∫_{t - 1/2}^{t + 1/2} G ≤ ∫_{a - 1/2}^{b + 1/2} G`. -/
theorem sum_integral_le_integral {G : ℝ → ℝ} (hG : Continuous G) (hG₀ : ∀ s, 0 ≤ G s)
    {a b : ℝ} (hab : a ≤ b) (T : Finset ℝ) (hT : ∀ t ∈ T, a ≤ t ∧ t ≤ b)
    (hsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → 1 ≤ |t - s|) :
    ∑ t ∈ T, ∫ s in (t - 1 / 2)..(t + 1 / 2), G s ≤ ∫ s in (a - 1 / 2)..(b + 1 / 2), G s := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  rw [sum_congr rfl fun t _ => intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_biUnion_finset T (fun t _ => measurableSet_Ioc) ?_
      fun t _ => hG.integrableOn_Ioc]
  · refine MeasureTheory.setIntegral_mono_set hG.integrableOn_Ioc
      (Filter.Eventually.of_forall hG₀) (LE.le.eventuallySubset ?_)
    exact Set.iUnion₂_subset fun t ht =>
      Set.Ioc_subset_Ioc (by linarith [hT t ht]) (by linarith [hT t ht])
  -- the intervals are disjoint
  · intro t ht s hs hts
    rw [Function.onFun, Set.disjoint_left]
    intro x hx₁ hx₂
    rw [Set.mem_Ioc] at hx₁ hx₂
    have h := hsep t ht s hs hts
    rcases abs_cases (t - s) with ⟨h', -⟩ | ⟨h', -⟩ <;> linarith

/-- PD (2.5): at points of `[a, b]` with mutual spacing at least one,
`∑_t |∑_{n ≤ N} c_n n^{it}|² ≤ 2 (b - a + 1 + 8N(1 + log N)) (1 + log N)² ∑ |c_n|²`. -/
theorem sum_norm_dirichlet_sq_le (N : ℕ) (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) (T : Finset ℝ)
    (hT : ∀ t ∈ T, a ≤ t ∧ t ≤ b) (hsep : ∀ t ∈ T, ∀ s ∈ T, t ≠ s → 1 ≤ |t - s|) :
    ∑ t ∈ T, ‖∑ n ∈ Icc 1 N, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      2 * (b - a + 1 + 8 * N * (1 + Real.log N)) * (1 + Real.log N) ^ 2 *
        ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 := by
  set P : ℝ → ℂ := fun t => ∑ n ∈ Icc 1 N, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)
  -- the derivative is the Dirichlet polynomial with coefficients `i c_n log n`
  set c' : ℕ → ℂ := fun n => c n * ((Real.log n : ℂ) * Complex.I)
  set P' : ℝ → ℂ := fun t => ∑ n ∈ Icc 1 N, c' n * (n : ℂ) ^ ((t : ℂ) * Complex.I)
  have hterm : ∀ n ∈ Icc 1 N, ∀ t : ℝ,
      (n : ℂ) ^ ((t : ℂ) * Complex.I) = Complex.exp ((Real.log n : ℂ) * Complex.I * t) :=
    fun n hn t => natCast_cpow_mul_I (by grind) t
  have hP : ∀ s, HasDerivAt P (P' s) s := by
    intro s
    have h : ∀ n ∈ Icc 1 N, HasDerivAt (fun t : ℝ => c n * (n : ℂ) ^ ((t : ℂ) * Complex.I))
        (c' n * (n : ℂ) ^ ((s : ℂ) * Complex.I)) s := by
      intro n hn
      have h' := (((hasDerivAt_id s).ofReal_comp.const_mul
        ((Real.log n : ℂ) * Complex.I)).cexp).const_mul (c n)
      simp only [id, Complex.ofReal_one, mul_one] at h'
      have e : (fun t : ℝ => c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)) =
          fun t : ℝ => c n * Complex.exp ((Real.log n : ℂ) * Complex.I * t) :=
        funext fun t => by rw [hterm n hn t]
      rw [e, hterm n hn s]
      convert h' using 1
      simp only [c']
      ring
    convert HasDerivAt.sum h using 1
    ext t
    simp [P]
  have hP'c : Continuous P' := by
    refine continuous_finsetSum _ fun n hn => ?_
    simp_rw [hterm n hn]
    fun_prop
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun s => (hP s).continuousAt
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hA : 0 ≤ ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 := sum_nonneg fun n _ => by positivity
  have hL : 0 ≤ b - a + 1 + 8 * N * (1 + Real.log N) := by
    have := sub_nonneg.2 hab
    positivity
  -- `∑ |c'_n|² ≤ log² N ∑ |c_n|²`
  have hA' : ∑ n ∈ Icc 1 N, ‖c' n‖ ^ 2 ≤ Real.log N ^ 2 * ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun n hn => ?_
    rw [mem_Icc] at hn
    have h₀ : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h₁ : Real.log n ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    simp only [c', norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h₀, mul_pow]
    rw [mul_comm]
    gcongr
  have hint₁ := integral_norm_dirichlet_sq_le N c (a := a - 1 / 2) (b := b + 1 / 2)
  have hint₂ := integral_norm_dirichlet_sq_le N c' (a := a - 1 / 2) (b := b + 1 / 2)
  calc ∑ t ∈ T, ‖P t‖ ^ 2
      ≤ ∑ t ∈ T, ∫ s in (t - 1 / 2)..(t + 1 / 2), (2 * ‖P s‖ ^ 2 + ‖P' s‖ ^ 2) :=
        sum_le_sum fun t _ => sq_norm_le_integral hP hP'c t
    _ ≤ ∫ s in (a - 1 / 2)..(b + 1 / 2), (2 * ‖P s‖ ^ 2 + ‖P' s‖ ^ 2) :=
        sum_integral_le_integral (by fun_prop) (fun s => by positivity) hab T hT hsep
    _ = 2 * (∫ s in (a - 1 / 2)..(b + 1 / 2), ‖P s‖ ^ 2) +
          ∫ s in (a - 1 / 2)..(b + 1 / 2), ‖P' s‖ ^ 2 := by
        rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun s =>
          2 * ‖P s‖ ^ 2).intervalIntegrable _ _) ((by fun_prop : Continuous fun s =>
          ‖P' s‖ ^ 2).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    _ ≤ 2 * ((b - a + 1 + 8 * N * (1 + Real.log N)) * ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2) +
          (b - a + 1 + 8 * N * (1 + Real.log N)) *
            (Real.log N ^ 2 * ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2) := by
        have e : b + 1 / 2 - (a - 1 / 2) = b - a + 1 := by ring
        rw [e] at hint₁ hint₂
        exact add_le_add (mul_le_mul_of_nonneg_left hint₁ (by norm_num))
          (hint₂.trans (mul_le_mul_of_nonneg_left hA' hL))
    _ ≤ _ := by
        have h : 0 ≤ (b - a + 1 + 8 * N * (1 + Real.log N)) * ∑ n ∈ Icc 1 N, ‖c n‖ ^ 2 *
            Real.log N := by positivity
        nlinarith [mul_nonneg hL hA]

end Erdos408.OneSided
