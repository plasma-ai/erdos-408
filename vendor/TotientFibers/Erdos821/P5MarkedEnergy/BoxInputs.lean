import Erdos821.P5MarkedEnergy.Factorization
import Erdos821.P5MarkedEnergy.Collapse
import Erdos821.P5.Exceptional
import Erdos821.P5.MellinVectors

/-! The arithmetic inputs of one box: the small-prime polynomial and its
exceptional unit intervals, the long rough-integer polynomial, and the
discrepancy-bearing `m` polynomial, all expressed as dyadic polynomials. -/

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-! ### A product character -/

theorem exists_prod_char (M r : ℕ) (χ0 : DirichletCharacter ℂ M) (χ : DirichletCharacter ℂ r) :
    ∃ ψ : DirichletCharacter ℂ (M * r), ∀ m : ℕ, Nat.Coprime m (M * r) →
      ψ (m : ZMod (M * r)) = χ0 (m : ZMod M) * χ (m : ZMod r) := by
  refine ⟨χ0.changeLevel (dvd_mul_right M r) * χ.changeLevel (dvd_mul_left r M), ?_⟩
  intro m hm
  rw [MulChar.mul_apply]
  have hc : IsCoprime (m : ℤ) ((M * r : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hm
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ0 (dvd_mul_right M r) hc
  have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ (dvd_mul_left r M) hc
  simp only [Int.cast_natCast] at h1 h2
  rw [h1, h2]

/-! ### Dyadic polynomials of the four coefficient functions -/

theorem hpoly_mul_char_eq (f : ℕ → ℂ) (i : ℕ) (t : ℝ) :
    hpoly f i t = ∑ m ∈ dyad i, f m * mellin m t / m := by
  unfold hpoly dp
  apply Finset.sum_congr rfl; intro m _; ring

/-- The small-prime polynomial is a prime polynomial. -/
theorem hpoly_S0_eq (G : PrimeGroups) (gs : Fin G.size) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (i : ℕ) (t : ℝ) :
    hpoly (fun s => S0 G gs s * χ (s : ZMod r)) i t =
      ((mass G gs)⁻¹ : ℝ) * primePolynomial ((G.primes gs).filter (fun p : ℕ => p ∈ dyad i))
        (fun p => χ (p : ZMod r)) t := by
  unfold hpoly primePolynomial dp
  have hf : (G.primes gs).filter (fun p : ℕ => p ∈ dyad i) = (dyad i).filter (fun p : ℕ => p ∈ G.primes gs) := by
    ext m; simp only [Finset.mem_filter]; tauto
  rw [hf, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  unfold S0
  by_cases h : m ∈ G.primes gs
  · simp only [h, if_true]; push_cast; ring
  · simp only [h, if_false]; ring

theorem norm_hpoly_S0_le (G : PrimeGroups) (gs : Fin G.size) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (i : ℕ) (hmass : 0 < mass G gs) (t : ℝ) :
    ‖hpoly (fun s => S0 G gs s * χ (s : ZMod r)) i t‖ ≤ 1 := by
  rw [hpoly_S0_eq]
  unfold primePolynomial dp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
  have hsum : ‖∑ p ∈ (G.primes gs).filter (fun p : ℕ => p ∈ dyad i), χ (p : ZMod r) / (p : ℂ) *
      Blueprint.Analytic.mellin p t‖ ≤ mass G gs := by
    refine (norm_sum_le _ _).trans ?_
    unfold mass
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset (fun p : ℕ => p ∈ dyad i) (G.primes gs))
      (fun p _ _ => by positivity))
    apply Finset.sum_le_sum
    intro p _
    rw [norm_mul, P5Core.norm_mellin, mul_one, norm_div, Complex.norm_natCast]
    rw [one_div]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (Nat.cast_nonneg _)
      |>.trans_eq (by rw [one_div])
  calc (mass G gs)⁻¹ * ‖∑ p ∈ (G.primes gs).filter (fun p : ℕ => p ∈ dyad i), χ (p : ZMod r) / (p : ℂ) *
      Blueprint.Analytic.mellin p t‖ ≤ (mass G gs)⁻¹ * mass G gs :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hmass.le)
    _ = 1 := inv_mul_cancel₀ hmass.ne'

/-- Off the occupied unit intervals, the small-prime polynomial is small. -/
theorem hpoly_S0_off_occ (G : PrimeGroups) (gs : Fin G.size) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (i : ℕ) (hmass : 0 < mass G gs) (thr T1 : ℝ) (occ : Finset ℤ)
    (hocc : ∀ j, j ∈ occupied ((G.primes gs).filter (fun p : ℕ => p ∈ dyad i)) (fun p => χ (p : ZMod r))
      thr T1 → j ∈ occ)
    (t : ℝ) (ht : |t| ≤ T1) (hoff : ∀ j ∈ occ, t ∉ Set.Icc (j : ℝ) (j + 1)) :
    ‖hpoly (fun s => S0 G gs s * χ (s : ZMod r)) i t‖ ≤ (mass G gs)⁻¹ * thr := by
  rw [hpoly_S0_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hmass)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hmass.le)
  by_contra hgt
  rw [not_le] at hgt
  have hj : ⌊t⌋ ∈ occupied ((G.primes gs).filter (fun p : ℕ => p ∈ dyad i)) (fun p => χ (p : ZMod r)) thr T1 :=
    ⟨t, Int.floor_le t, (Int.lt_floor_add_one t).le, ht, hgt⟩
  exact hoff _ (hocc _ hj) ⟨Int.floor_le t, (Int.lt_floor_add_one t).le⟩

theorem occupied_abs_le (s : Finset ℕ) (b : ℕ → ℂ) (thr T1 : ℝ) (j : ℤ)
    (hj : j ∈ occupied s b thr T1) : |(j : ℝ)| ≤ T1 + 1 := by
  obtain ⟨t, hjt, htj, ht, _⟩ := hj
  have := abs_le.mp ht
  rw [abs_le]; constructor <;> linarith

/-- The long rough-integer polynomial of a dyad. -/
theorem hpoly_P0_eq (E : Endpoint) (x : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r) (i : ℕ)
    (hlo : 0 ≤ E.lo) (hlohi : E.lo ≤ E.hi) (t : ℝ) :
    hpoly (fun p => P0 E x p * χ (p : ZMod r)) i t =
      ∑ n ∈ (Finset.Icc ⌈max ((2 : ℝ) ^ i) E.lo⌉₊ ⌊min ((2 : ℝ) ^ (i + 1) - 1) E.hi⌋₊).filter
        (rough (W x)), χ (n : ZMod r) * Blueprint.Analytic.mellin n (t + E.sigma₁) / n := by
  unfold hpoly dp P0
  have hset : (dyad i).filter (fun n : ℕ => E.lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ E.hi ∧ rough (W x) n) =
      (Finset.Icc ⌈max ((2 : ℝ) ^ i) E.lo⌉₊ ⌊min ((2 : ℝ) ^ (i + 1) - 1) E.hi⌋₊ : Finset ℕ).filter
        (rough (W x)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, mem_dyad]
    have hmin : 0 ≤ min ((2 : ℝ) ^ (i + 1) - 1) E.hi := by
      apply le_min _ (hlo.trans hlohi)
      have : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
      linarith
    rw [Nat.ceil_le, Nat.le_floor_iff hmin, max_le_iff, le_min_iff]
    have e1 : (2 ^ i ≤ n) ↔ ((2 : ℝ) ^ i ≤ n) := by exact_mod_cast Iff.rfl
    have e2 : (n < 2 ^ (i + 1)) ↔ ((n : ℝ) ≤ 2 ^ (i + 1) - 1) := by
      constructor
      · intro h
        have : n + 1 ≤ 2 ^ (i + 1) := h
        have : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      · intro h
        have : ((n : ℕ) : ℝ) < ((2 ^ (i + 1) : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast this
    rw [e1, e2]
    tauto
  rw [← hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : E.lo ≤ (n : ℝ) ∧ (n : ℝ) ≤ E.hi ∧ rough (W x) n
  · simp only [h, and_self, if_true]
    rw [P5Core.mellin_add (n : ℝ) t E.sigma₁]; ring
  · simp only [h, if_false]; ring

/-- The `m` polynomial of a dyad, with the product character. -/
theorem hpoly_A0_eq (E : Endpoint) (r : ℕ) (χ : DirichletCharacter ℂ r) (i : ℕ)
    (ψ : DirichletCharacter ℂ (E.modulus * r))
    (hψ : ∀ m : ℕ, Nat.Coprime m (E.modulus * r) →
      ψ (m : ZMod (E.modulus * r)) = E.chi (m : ZMod E.modulus) * χ (m : ZMod r))
    (hcop : ∀ m, E.alpha m ≠ 0 → Nat.Coprime m (E.modulus * r)) (t : ℝ) :
    hpoly (fun m => A0 E m * χ (m : ZMod r)) i t =
      ∑ m ∈ Finset.Icc ⌈((2 : ℝ) ^ i)⌉₊ ⌊((2 : ℝ) ^ (i + 1) - 1)⌋₊,
        E.alpha m * ψ (m : ZMod (E.modulus * r)) * Blueprint.Analytic.mellin m (t + E.sigma₀) /
          (m : ℂ) := by
  unfold hpoly dp A0
  have hset : dyad i = Finset.Icc ⌈((2 : ℝ) ^ i)⌉₊ ⌊((2 : ℝ) ^ (i + 1) - 1)⌋₊ := by
    ext n
    simp only [mem_dyad, Finset.mem_Icc]
    have h1 : ⌈((2 : ℝ) ^ i)⌉₊ = 2 ^ i := by exact_mod_cast Nat.ceil_natCast (2 ^ i)
    have h2 : ⌊((2 : ℝ) ^ (i + 1) - 1)⌋₊ = 2 ^ (i + 1) - 1 := by
      have : ((2 : ℝ) ^ (i + 1) - 1) = ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; ring
      rw [this, Nat.floor_natCast]
    rw [h1, h2]
    have := Nat.one_le_two_pow (n := i + 1)
    omega
  rw [← hset]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hα : E.alpha m = 0
  · simp [hα]
  · rw [hψ m (hcop m hα), P5Core.mellin_add (m : ℝ) t E.sigma₀]
    ring

/-- Coprimality from roughness. -/
theorem coprime_of_rough {x : ℝ} {m q : ℕ} (hm : rough (W x) m) (hq : 1 ≤ q) (hqW : (q : ℝ) < W x) :
    Nat.Coprime m q := by
  apply Nat.coprime_of_dvd
  intro k hk hkm hkq
  have h1 := hm.2 k hk hkm
  have h2 : (k : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) hkq
  linarith

end Erdos821.P5Marked
