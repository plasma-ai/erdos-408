module

public import Erdos408.OneSided.Bands
public import Erdos408.TwoSided.Defs

/-!
# Pointwise bounds for the tuple coefficient

The coefficient `c(u) = 𝒲(u) 𝒜_B(u) W_{S'}^b(u)` of the tuple part (PD (6.31), (6.32)) is
`≤ L^{C_U}` for `1 ≤ u ≤ x²`, with `C_U` depending on the fixed data only
(`blueprint/two_sided_correlation.md` §2 U7, U9 and §6.3 E5). The bounds `0 ≤ 𝒲 ≤ L` (U7) and
`|W_S^b(n)| ≤ L^{C_W}` (U9) are in `Setup.lean`; here

* `abs_sum_filter_prod_dvd_le`: `|𝒜_B(n)| ≤ ω(n)^d`, with `ω(n) ≤ 2 log n`.
-/

@[expose] public section

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset

/-! ### The weighted slot count (E5) -/

/-- `ω(n) ≤ 2 log n` for `n ≥ 1`: the product of the prime factors divides `n`. -/
theorem card_primeFactors_le {n : ℕ} (hn : 1 ≤ n) :
    (#n.primeFactors : ℝ) ≤ 2 * Real.log n := by
  have h₁ : 2 ^ #n.primeFactors ≤ ∏ p ∈ n.primeFactors, p :=
    pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h₂ : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have h : ((2 ^ #n.primeFactors : ℕ) : ℝ) ≤ n := by exact_mod_cast h₁.trans h₂
  have hlog := Real.log_le_log (by positivity) h
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hlog
  have h2 := Real.log_two_gt_d9
  nlinarith [Nat.cast_nonneg (α := ℝ) #n.primeFactors]

/-- `|∑_{Q ∈ ∏ F_i, ∏ Q ∣ n} B(Q)| ≤ ω(n)^d` for prime slots `F_i`, `|B| ≤ 1` and `n ≥ 1`:
every entry of such a `Q` is a prime factor of `n`. -/
theorem abs_sum_filter_prod_dvd_le {d : ℕ} (F : Fin d → Finset ℕ)
    (hF : ∀ i, ∀ p ∈ F i, p.Prime) (Bc : (Fin d → ℕ) → ℝ) (hBc : ∀ Q, |Bc Q| ≤ 1) {n : ℕ}
    (hn : 1 ≤ n) :
    |∑ Q ∈ (Fintype.piFinset F) with ∏ i, Q i ∣ n, Bc Q| ≤ (#n.primeFactors : ℝ) ^ d := by
  have hsub : (Fintype.piFinset F).filter (fun Q => ∏ i, Q i ∣ n) ⊆
      Fintype.piFinset fun _ : Fin d => n.primeFactors := by
    intro Q hQ
    rw [mem_filter, Fintype.mem_piFinset] at hQ
    rw [Fintype.mem_piFinset]
    intro i
    exact Nat.mem_primeFactors.2 ⟨hF i _ (hQ.1 i),
      (dvd_prod_of_mem Q (mem_univ i)).trans hQ.2, by omega⟩
  have hcard := card_le_card hsub
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at hcard
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun Q _ => hBc Q).trans ?_)
  rw [sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast hcard

end Erdos408.TwoSided.TupleHigh
