module

public import Erdos408.Extraction.TypeII.Asymp
public import Erdos408.Mertens
public import Mathlib.Tactic.NormNum.Prime

/-!
# Bands and slots

Facts about the inert bands and the slot statistic used in E4.

* `bandWeight = q^{ω - 1} ω / V ≤ 1 / ((1 - q) V)`, by Bernoulli's inequality, and the
  harmonic mass of a band is `V ≥ 1/2` once `L^{0.1}` is large (Mertens).
* `markedWeight` over `K` bands is the product of the single-band weights.
* Bands whose exponents differ by `1/T` are disjoint, since `L^{1/T} = e > 2`.
* The slot statistic and the band weights of other bands are invariant under multiplying by
  a small prime.
* `0 ≤ f_𝔟(h) ≤ (2T²⁰/c)^{k+1}` for `1 ≤ h ≤ x²`, and `0 ≤ C_𝔟 ≤ (T + E)^{k+1}`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

/-! ### Band weights -/

theorem bandWeight_eq (q x a : ℝ) (n : ℕ) :
    bandWeight q x a n = q ^ ((primeCount (band x a) n : ℤ) - 1) *
      ((primeCount (band x a) n : ℝ) / harmonicMass (band x a)) := by
  simp [bandWeight, markedWeight]

/-- `ω q^{ω - 1} ≤ 1 / (1 - q)` for `0 < q < 1`. -/
theorem zpow_mul_le {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (ω : ℕ) :
    q ^ ((ω : ℤ) - 1) * ω ≤ 1 / (1 - q) := by
  rcases Nat.eq_zero_or_pos ω with rfl | hω
  · simp only [Nat.cast_zero, mul_zero]; exact div_nonneg zero_le_one (by linarith)
  obtain ⟨n, rfl⟩ : ∃ n, ω = n + 1 := ⟨ω - 1, by omega⟩
  have hz : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
  rw [hz, zpow_natCast]
  -- Bernoulli: `(1/q)^n ≥ 1 + n (1/q - 1) ≥ (n + 1)(1 - q)`
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / q - 1 by
    have : 0 < 1 / q := by positivity
    linarith) n
  rw [add_sub_cancel, one_div_pow] at hb
  have hqn : 0 < q ^ n := by positivity
  have h1 : ((n + 1 : ℕ) : ℝ) * (1 - q) ≤ 1 + n * (1 / q - 1) := by
    have h1q : 1 - q ≤ 1 / q - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hq]
      nlinarith
    push_cast
    nlinarith
  have h2 : ((n + 1 : ℕ) : ℝ) * (1 - q) ≤ 1 / q ^ n := h1.trans hb
  rw [le_div_iff₀ hqn] at h2
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem bandWeight_nonneg {q : ℝ} (hq : 0 < q) (x a : ℝ) (n : ℕ) : 0 ≤ bandWeight q x a n := by
  rw [bandWeight_eq]
  have : 0 ≤ harmonicMass (band x a) := sum_nonneg fun p _ => by positivity
  positivity

/-- `bandWeight ≤ 1 / ((1 - q) V)`. -/
theorem bandWeight_le {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (x a : ℝ) (n : ℕ)
    (hV : 0 < harmonicMass (band x a)) :
    bandWeight q x a n ≤ 1 / ((1 - q) * harmonicMass (band x a)) := by
  rw [bandWeight_eq]
  calc q ^ ((primeCount (band x a) n : ℤ) - 1) *
        ((primeCount (band x a) n : ℝ) / harmonicMass (band x a))
      = q ^ ((primeCount (band x a) n : ℤ) - 1) * (primeCount (band x a) n : ℝ) /
          harmonicMass (band x a) := by ring
    _ ≤ 1 / (1 - q) / harmonicMass (band x a) :=
        div_le_div_of_nonneg_right (zpow_mul_le hq hq₁ _) hV.le
    _ = _ := by rw [div_div]

/-- `∏ q^{e_i} = q^{∑ e_i}` for `q ≠ 0`. -/
theorem prod_zpow_eq {ι : Type*} (s : Finset ι) {q : ℝ} (hq : q ≠ 0) (e : ι → ℤ) :
    ∏ i ∈ s, q ^ e i = q ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [prod_insert hi, sum_insert hi, ih, zpow_add₀ hq]

/-- The marked weight of `K` bands is the product of the single-band weights. -/
theorem markedWeight_eq_prod {q : ℝ} (hq : q ≠ 0) (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (n : ℕ) :
    markedWeight Finset.univ q (fun c => band x (a c)) n = ∏ c, bandWeight q x (a c) n := by
  simp only [bandWeight_eq, markedWeight, prod_mul_distrib]
  congr 1
  rw [prod_zpow_eq _ hq]
  congr 1
  push_cast
  rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin]
  simp

/-! ### Harmonic mass and disjointness of bands -/

/-- A band has harmonic mass at least `1/2` once `L^{1/10}` is large. -/
theorem harmonicMass_band_ge : ∃ L₀ : ℝ, ∀ x a : ℝ, L₀ ≤ Real.log x → 1 / 10 ≤ a →
    1 / 2 ≤ harmonicMass (band x a) := by
  obtain ⟨E, hE0, hE⟩ := mertens_second
  refine ⟨(6 * E + 3) ^ (10 : ℝ), fun x a hL ha => ?_⟩
  have hL1 : 1 ≤ Real.log x := by
    have : (1 : ℝ) ≤ (6 * E + 3) ^ (10 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    linarith
  have hLa : 6 * E + 3 ≤ Real.log x ^ a := by
    calc 6 * E + 3 = ((6 * E + 3) ^ (10 : ℝ)) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_mul (by linarith)]; norm_num
      _ ≤ Real.log x ^ (1 / 10 : ℝ) := Real.rpow_le_rpow (by positivity) hL (by norm_num)
      _ ≤ Real.log x ^ a := Real.rpow_le_rpow_of_exponent_le hL1 ha
  set y := Real.exp (Real.log x ^ a) with hy
  have hy2 : 2 ≤ y := by
    have := Real.add_one_le_exp (Real.log x ^ a)
    linarith
  have hyz : y ≤ Real.exp (2 * Real.log x ^ a) := Real.exp_le_exp.2 (by linarith)
  have hsub : primesIoc y (Real.exp (2 * Real.log x ^ a)) ⊆ band x a := by
    intro p hp
    obtain ⟨hpp, hlo, hhi⟩ := mem_primesIoc.1 hp
    unfold band
    rw [mem_filter, mem_Icc]
    exact ⟨⟨Nat.ceil_le.2 hlo.le, Nat.le_floor hhi⟩, hpp⟩
  have hmass := hE y (Real.exp (2 * Real.log x ^ a)) hy2 hyz
  rw [hy, Real.log_exp, Real.log_exp, mul_div_assoc, div_self (by linarith), mul_one] at hmass
  have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hEdiv : E / Real.log x ^ a ≤ 1 / 6 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h1 : Real.log 2 - E / Real.log x ^ a ≤
      ∑ p ∈ primesIoc y (Real.exp (2 * Real.log x ^ a)), (1 : ℝ) / p := by
    rw [abs_le] at hmass; linarith [hmass.1]
  have h2 : ∑ p ∈ primesIoc y (Real.exp (2 * Real.log x ^ a)), (1 : ℝ) / p ≤
      harmonicMass (band x a) :=
    sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => by positivity
  linarith

/-- Bands whose exponents differ by at least `1/T` are disjoint. -/
theorem band_disjoint {x a a' : ℝ} (hL : 1 < Real.log x) (h : a + 1 / logLog x ≤ a') :
    Disjoint (band x a) (band x a') := by
  have hL0 : 0 < Real.log x := by linarith
  have hT : 0 < logLog x := Real.log_pos hL
  have hgrow : 2 * Real.log x ^ a < Real.log x ^ a' := by
    have hLT : Real.log x ^ (1 / logLog x) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hL0]
      congr 1
      unfold logLog at hT ⊢
      field_simp
    calc 2 * Real.log x ^ a < Real.exp 1 * Real.log x ^ a := by
          have := Real.exp_one_gt_d9
          have : 0 < Real.log x ^ a := by positivity
          nlinarith
      _ = Real.log x ^ (a + 1 / logLog x) := by
          rw [Real.rpow_add hL0, hLT, mul_comm]
      _ ≤ Real.log x ^ a' := Real.rpow_le_rpow_of_exponent_le hL.le h
  refine disjoint_left.2 fun p hp hp' => ?_
  unfold band at hp hp'
  rw [mem_filter, mem_Icc] at hp hp'
  have h1 : (p : ℝ) ≤ Real.exp (2 * Real.log x ^ a) :=
    (Nat.le_floor_iff (by positivity)).1 hp.1.2
  have h2 : Real.exp (Real.log x ^ a') ≤ p := Nat.ceil_le.1 hp'.1.1
  have := Real.exp_lt_exp.2 hgrow
  linarith

/-! ### Invariance under a small prime -/

/-- Multiplying by a prime outside `S` does not change the number of primes of `S` dividing. -/
theorem primeCount_prime_mul {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpS : p ∉ S) (h : ℕ) : primeCount S (p * h) = primeCount S h := by
  unfold primeCount
  congr 1
  refine filter_congr fun q hq => ⟨fun hdvd => ?_, fun hdvd => dvd_mul_of_dvd_right hdvd p⟩
  rcases (Nat.Prime.dvd_mul (hS q hq)).1 hdvd with h' | h'
  · exact absurd ((Nat.prime_dvd_prime_iff_eq (hS q hq) hp).1 h' ▸ hq) hpS
  · exact h'

theorem band_prime {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) : p.Prime := by
  unfold band at hp
  exact (mem_filter.1 hp).2

/-- A band weight is invariant under the primes of a disjoint band. -/
theorem bandWeight_prime_mul {q x a a' : ℝ} (hdisj : Disjoint (band x a) (band x a')) {p : ℕ}
    (hp : p ∈ band x a') (h : ℕ) : bandWeight q x a (p * h) = bandWeight q x a h := by
  rw [bandWeight_eq, bandWeight_eq,
    primeCount_prime_mul (fun q hq => band_prime hq) (band_prime hp)
      (disjoint_right.1 hdisj hp)]

/-- The slot statistic is invariant under primes below every slot. -/
theorem slotCount_prime_mul {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) (B : (Fin k → ℕ) → ℝ)
    {p : ℕ} (hp : p.Prime) (hpu : ∀ i, (p : ℝ) ≤ x ^ u i) (h : ℕ) :
    slotCount x u v B (p * h) = slotCount x u v B h := by
  unfold slotCount
  congr 1
  refine filter_congr fun Q hQ => ?_
  have hQ' : ∀ i, (Q i).Prime ∧ x ^ u i < Q i := fun i => by
    have := Fintype.mem_piFinset.1 (mem_filter.1 hQ).1 i
    exact (mem_filter.1 this).2
  have hcop : Nat.Coprime (∏ i, Q i) p := by
    refine Nat.Coprime.symm (Nat.coprime_prod_right_iff.2 fun i _ => ?_)
    refine (Nat.coprime_primes hp (hQ' i).1).2 fun hpq => ?_
    have := (hQ' i).2
    rw [← hpq] at this
    linarith [hpu i]
  exact hcop.dvd_mul_left

/-! ### Size of the slot statistic -/

theorem slotCount_nonneg {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) {B : (Fin k → ℕ) → ℝ}
    (hB : ∀ Q, 0 ≤ B Q) (h : ℕ) : 0 ≤ slotCount x u v B h :=
  sum_nonneg fun _ _ => hB _

theorem slotMean_nonneg {x : ℝ} {k : ℕ} (u v : Fin (k + 1) → ℝ) {B : (Fin k → ℕ) → ℝ}
    (hB : ∀ Q, 0 ≤ B Q) : 0 ≤ slotMean x u v B :=
  sum_nonneg fun _ _ => div_nonneg (hB _) (prod_nonneg fun _ _ => Nat.cast_nonneg _)

/-- A slot tuple divides `h ≤ x²` only through the `≤ 2T²⁰/c` prime factors of `h` above
`x^{c/T²⁰}`, so `f_𝔟(h) ≤ (2T²⁰/c)^{k+1}`. -/
theorem slotCount_le {c x : ℝ} (hx : 1 < x) (hc : 0 < c) (hT : 0 < logLog x) {k : ℕ}
    (u v : Fin (k + 1) → ℝ) {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1)
    (hu : ∀ i, c / logLog x ^ 20 ≤ u i) {h : ℕ} (h1 : 1 ≤ h) (hh : (h : ℝ) ≤ x ^ 2) :
    slotCount x u v B h ≤ (2 * logLog x ^ 20 / c) ^ (k + 1) := by
  have hL : 0 < Real.log x := Real.log_pos hx
  set e := c / logLog x ^ 20 with he
  have he0 : 0 < e := by positivity
  set D := h.primeFactors.filter fun q : ℕ => x ^ e < q with hD
  -- the slot tuples dividing `h` have all coordinates in `D`
  have hsub : (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ h) ⊆
      Fintype.piFinset fun _ : Fin (k + 1) => D := by
    intro Q hQ
    obtain ⟨hQs, hdvd⟩ := mem_filter.1 hQ
    refine Fintype.mem_piFinset.2 fun i => ?_
    have hQi := (mem_filter.1 (Fintype.mem_piFinset.1 (mem_filter.1 hQs).1 i)).2
    rw [hD, mem_filter, Nat.mem_primeFactors]
    refine ⟨⟨hQi.1, (Finset.dvd_prod_of_mem _ (mem_univ i)).trans hdvd, by omega⟩, ?_⟩
    exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx.le (hu i)) hQi.2
  have hcount : slotCount x u v B h ≤ ((slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ h)).card := by
    unfold slotCount
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact sum_le_sum fun Q _ => (hB _).2
  have hcard : (D.card : ℝ) ≤ 2 * logLog x ^ 20 / c := by
    -- `(x^e)^{|D|} ≤ ∏_D q ≤ h ≤ x²`
    have hprod_le : ∏ q ∈ D, (q : ℝ) ≤ h := by
      have hdvd : ∏ q ∈ D, q ∣ h :=
        (Finset.prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans
          (Nat.prod_primeFactors_dvd h)
      have := Nat.le_of_dvd (by omega) hdvd
      rw [← Nat.cast_prod]
      exact_mod_cast this
    have hlow : (x ^ e) ^ D.card ≤ ∏ q ∈ D, (q : ℝ) := by
      rw [← prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun q hq =>
        (mem_filter.1 hq).2.le
    have hle : (x ^ e) ^ D.card ≤ x ^ 2 := (hlow.trans hprod_le).trans hh
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast x 2] at hle
    have := (Real.rpow_le_rpow_left_iff hx).1 hle
    rw [he] at this
    rw [le_div_iff₀ hc]
    have hT20 : 0 < logLog x ^ 20 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hT20] at this
    push_cast at this
    linarith
  calc slotCount x u v B h ≤ ((slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ h)).card := hcount
    _ ≤ (Fintype.piFinset fun _ : Fin (k + 1) => D).card := by exact_mod_cast card_le_card hsub
    _ = (D.card : ℝ) ^ (k + 1) := by
        rw [Fintype.card_piFinset_const]; push_cast; rfl
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _

/-- The sum `∑_{p ≤ x} 1/p ≤ log log x + E₂`. -/
theorem sum_inv_primes_le : ∃ E₂ : ℝ, 0 ≤ E₂ ∧ ∀ x : ℝ, 2 ≤ x →
    ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p ≤ logLog x + E₂ := by
  obtain ⟨E, hE0, hE⟩ := mertens_second
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / 2 + |Real.log (Real.log 2)| + E / Real.log 2, by positivity, fun x hx => ?_⟩
  rw [← sum_primesIoc_add _ (show (1 : ℝ) ≤ 2 by norm_num) hx]
  have h12 : primesIoc 1 2 = {2} := by
    ext p
    rw [mem_primesIoc, mem_singleton]
    constructor
    · rintro ⟨hp, h1, h2⟩
      have := hp.two_le
      have : p ≤ 2 := by exact_mod_cast h2
      omega
    · rintro rfl; norm_num
  rw [h12, sum_singleton, show ((1 : ℝ) / ((2 : ℕ) : ℝ)) = 1 / 2 by norm_num]
  have hm := hE 2 x le_rfl hx
  rw [abs_le] at hm
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.log_div hlx.ne' hl2.ne'] at hm
  have := le_abs_self (-Real.log (Real.log 2))
  rw [abs_neg] at this
  unfold logLog
  linarith [hm.2]

/-- `C_𝔟 ≤ (∑_{p ≤ x} 1/p)^{k+1}` for admissible slots and `0 ≤ 𝔟 ≤ 1`. -/
theorem slotMean_le {x : ℝ} (hx : 1 < x) {k : ℕ} (u v : Fin (k + 1) → ℝ)
    {B : (Fin k → ℕ) → ℝ} (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) (hu : ∀ i, 0 < u i)
    (hv : ∑ i, v i ≤ 1) :
    slotMean x u v B ≤ (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) := by
  set S : Fin (k + 1) → Finset ℕ := fun i =>
    (Finset.Iic ⌊x ^ v i⌋₊).filter fun q : ℕ => q.Prime ∧ x ^ u i < q with hS
  have h1 : slotMean x u v B ≤ ∏ i, ∑ q ∈ S i, (1 : ℝ) / q := by
    rw [prod_univ_sum]
    unfold slotMean slotTuples
    refine (sum_le_sum fun Q _ => ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      fun Q _ _ => prod_nonneg fun _ _ => by positivity)
    rw [prod_div_distrib, prod_const_one]
    exact div_le_div_of_nonneg_right (hB _).2 (prod_nonneg fun _ _ => Nat.cast_nonneg _)
  refine h1.trans ?_
  by_cases hne : ∀ i, (S i).Nonempty
  · -- every slot is nonempty, so `0 < u i < v i` and `v i ≤ 1`
    have hvpos : ∀ i, 0 ≤ v i := by
      intro i
      obtain ⟨q, hq⟩ := hne i
      obtain ⟨hqI, -, hqu⟩ := mem_filter.1 hq
      have hqv : (q : ℝ) ≤ x ^ v i :=
        (Nat.le_floor_iff (by positivity)).1 (mem_Iic.1 hqI)
      have := lt_of_lt_of_le hqu hqv
      have := (Real.rpow_lt_rpow_left_iff hx).1 this
      linarith [hu i]
    have hv1 : ∀ i, v i ≤ 1 := fun i =>
      (single_le_sum (fun j _ => hvpos j) (mem_univ i)).trans hv
    rw [show (∑ p ∈ primesIoc 1 x, (1 : ℝ) / p) ^ (k + 1) =
        ∏ _i : Fin (k + 1), ∑ p ∈ primesIoc 1 x, (1 : ℝ) / p by
      rw [prod_const, card_univ, Fintype.card_fin]]
    refine Finset.prod_le_prod₀ (fun _ _ => sum_nonneg fun _ _ => by positivity) fun i _ => ?_
    refine sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun _ _ _ => by positivity
    obtain ⟨hqI, hqp, -⟩ := mem_filter.1 hq
    have hqv : (q : ℝ) ≤ x ^ v i := (Nat.le_floor_iff (by positivity)).1 (mem_Iic.1 hqI)
    have hxv : x ^ v i ≤ x := by
      calc x ^ v i ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx.le (hv1 i)
        _ = x := Real.rpow_one x
    exact mem_primesIoc_one.2 ⟨hqp, hqv.trans hxv⟩
  · push Not at hne
    obtain ⟨i, hi⟩ := hne
    rw [prod_eq_zero (mem_univ i) (by rw [hi, sum_empty])]
    exact pow_nonneg (sum_nonneg fun _ _ => by positivity) _

end Erdos408.TypeII
