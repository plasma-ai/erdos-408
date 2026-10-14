import Erdos408.OneSided.Moment.Chain
import Erdos408.OneSided.Bands

/-!
# Nonnegativity of the chain measure

The norm bounds of the edge (`Moment/Edge.lean`) add by Minkowski, which needs the chain
measure to be nonnegative. It is a product of birth weights `ν(p) = 1 / (V(p) (p + 1) b'_p)`
and a memory weight, so it suffices that the baselines `b'_p` are nonnegative at the band
primes. This holds once the band primes exceed `N = 2R`, which is eventually the case.

* `eventually_chainMeasure_nonneg`: eventually the chain measure with `N = 2R` is
  nonnegative.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Measure

variable {q x : ℝ} {d : Data K}

/-- For primes beyond `N`, the baseline `b'_p` is nonnegative: each of the `N + 1` defects is
at most `1`, and `p + 1 > N + 1`. -/
private theorem baseline_nonneg (hq : 0 < q) {N p : ℕ} (hp : N < p) : 0 ≤ baseline q N p := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  -- `∑_{j ≤ N} η'_j ≤ N + 1 ≤ p + 1`
  have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (p : ℝ) + 1 :=
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => by
            unfold dampDefect
            split_ifs <;> linarith [Real.sqrt_nonneg q]
      _ = (N : ℝ) + 1 := by simp
      _ ≤ (p : ℝ) + 1 := by gcongr
  have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 := by
    rw [inv_mul_le_iff₀ hp1, mul_one]
    exact hsum
  unfold baseline
  linarith

/-- With nonnegative baselines at the band primes, the birth weights are nonnegative; off the
band primes `V(p) = 0`. -/
private theorem primeWeight_nonneg {N : ℕ} (hb : ∀ p ∈ bandPrimes x d, 0 ≤ baseline q N p)
    (p : ℕ) : 0 ≤ primeWeight q x d N p := by
  have hV : 0 ≤ primeMass x d p :=
    sum_nonneg fun i _ => by
      split_ifs
      · exact sum_nonneg fun p _ => by positivity
      · exact le_rfl
  unfold primeWeight
  by_cases hp : p ∈ bandPrimes x d
  · exact one_div_nonneg.2 (mul_nonneg (mul_nonneg hV (by positivity)) (hb p hp))
  · have h0 : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_biUnion.2 ⟨i, mem_univ i, hpi⟩)
    rw [h0]
    simp

/-- Eventually every band prime exceeds `N = 2R`: band primes exceed `L`, and
`2R < L^{1/2} + 2 ≤ L`. -/
private theorem eventually_two_mul_momentPower_lt {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ p ∈ bandPrimes x d, 2 * momentPower x < p := by
  have hL := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) 1,
    hL.eventually_ge_atTop 2, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hbig hs2 hL0 d hd p hp
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  have hLp := hbig (d.a i) (hd.window i).1 p hpi
  rw [Real.rpow_one] at hLp
  set s := Real.log x ^ (1 / 2 : ℝ) with hs
  have hs2' : 2 ≤ s := hs2
  -- `s² = L` and `R < s/2 + 1`
  have hss : s * s = Real.log x := by
    rw [hs, ← Real.rpow_add hL0]
    norm_num
  have hR : (momentPower x : ℝ) < s / 2 + 1 := by
    unfold momentPower
    exact Nat.ceil_lt_add_one (by linarith)
  have h2 : 2 * s ≤ s * s := mul_le_mul_of_nonneg_right hs2' (by linarith)
  have : ((2 * momentPower x : ℕ) : ℝ) < p := by
    push_cast
    linarith
  exact_mod_cast this

/-- Eventually the chain measure with `N = 2R` is nonnegative. -/
theorem eventually_chainMeasure_nonneg {C CX alo ahi g : ℝ} (hq : 0 < q)
    (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ (Y d₀ u v r : ℝ) (B : ℕ) (s : ChainState x d Y d₀ u v r B),
        0 ≤ chainMeasure q x d Y d₀ u v r B (2 * momentPower x) s := by
  filter_upwards [eventually_two_mul_momentPower_lt halo] with x hbig d hd Y d₀ u v r B s
  have hν := primeWeight_nonneg fun p hp => baseline_nonneg hq (hbig d hd p hp)
  exact mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
    (memWeight_nonneg (fun xp => hν _) _)

end Measure

end Erdos408.OneSided
