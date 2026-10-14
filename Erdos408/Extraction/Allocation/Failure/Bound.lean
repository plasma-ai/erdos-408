module

public import Erdos408.Extraction.Allocation.CoreMoment
public import Erdos408.Extraction.Allocation.Failure.Scale

/-!
# The free-factor sum in Euler products

With `κ_j = ∏_{p ∈ P} (1 - 1/(j p))`, the damped density is `D_j = Π / κ_j`, so
the weight bound `W = 1/(D_j γ L)` is `κ_j / (Π γ L)`, and each core factor
contributes `∑_a b(a)/a ≤ κ_j H` with `H = (Π γ L)⁻¹ ∑_{a ≤ X rough} 1/a`. The
free-factor sum of a family `F` is then at most

`X (2/(γ L)) κ_j^j ∏_{p ∈ P} (1 - 1/p)⁻¹ ((1 - θ c₁/75)^{|F|} + δ) H^{j-1} + rounding`,

and `κ_j^j ∏_{p ∈ P} (1 - 1/p)⁻¹ ≤ exp(2 ∑_{p ∈ P} 1/p²)`: the normalization of
the proxy cancels the Euler product of the candidate part exactly, up to the
squares.
-/

@[expose] public section

namespace Erdos408

open Finset Real

noncomputable section

/-- The candidate factor `κ_j = ∏_{p ∈ P} (1 - 1/(j p))` of the damped density. -/
def candKappa (x : ℝ) (j : ℕ) : ℝ :=
  ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)

/-- `κ_j > 0` for `j ≥ 1`. -/
lemma candKappa_pos (x : ℝ) {j : ℕ} (hj : 1 ≤ j) : 0 < candKappa x j := by
  have hj1 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hj)
  refine prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).two_le
  have : (j : ℝ)⁻¹ / p < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

/-- `D_j = Π / κ_j`. -/
lemma dampedDensity_eq (x : ℝ) (j : ℕ) :
    dampedDensity x j = (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) / candKappa x j := by
  rw [dampedDensity, candKappa, div_eq_mul_inv, prod_inv_distrib]

/-- `κ_j^j ∏_{p ∈ P} (1 - 1/p)⁻¹ ≤ exp(2 ∑_{p ∈ P} 1/p²)`. -/
lemma candKappa_pow_mul_le (x : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    candKappa x j ^ j * ∏ p ∈ candidatePrimes x, (1 - (1 : ℝ) / p)⁻¹ ≤
      Real.exp (2 * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p ^ 2) := by
  rw [candKappa, ← prod_pow, ← prod_mul_distrib, mul_sum, exp_sum]
  refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).two_le
    have hj1 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hj)
    have h1 : (j : ℝ)⁻¹ / p < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h2 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
    exact mul_nonneg (pow_nonneg (by linarith) _) (inv_nonneg.2 (by linarith))
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (prime_of_mem_candidatePrimes hp).two_le
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    -- `(1 - 1/(j p))^j ≤ exp(-1/p)`
    have h1 : (1 - (j : ℝ)⁻¹ / p) ^ j ≤ Real.exp (-(1 / p)) := by
      have h0 : 0 ≤ 1 - (j : ℝ)⁻¹ / p := by
        have : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hj)
        have : (j : ℝ)⁻¹ / p ≤ 1 / 2 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
        linarith
      calc (1 - (j : ℝ)⁻¹ / p) ^ j ≤ Real.exp (-((j : ℝ)⁻¹ / p)) ^ j := by
            gcongr
            linarith [add_one_le_exp (-((j : ℝ)⁻¹ / p))]
        _ = Real.exp (-(1 / p)) := by
            rw [← exp_nat_mul]
            congr 1
            field_simp
    -- `(1 - 1/p)⁻¹ = 1 + 1/(p - 1) ≤ exp(1/p + 2/p²)`
    have h2 : (1 - (1 : ℝ) / p)⁻¹ ≤ Real.exp (1 / p + 2 * (1 / p ^ 2)) := by
      have hp1 : (0 : ℝ) < p - 1 := by linarith
      have he : (1 - (1 : ℝ) / p)⁻¹ = 1 + 1 / (p - 1) := by
        field_simp
        ring
      rw [he]
      refine (add_comm (1 : ℝ) _ ▸ add_one_le_exp (1 / (p - 1))).trans (exp_le_exp.2 ?_)
      rw [div_le_iff₀ hp1]
      field_simp
      nlinarith
    calc (1 - (j : ℝ)⁻¹ / p) ^ j * (1 - (1 : ℝ) / p)⁻¹
        ≤ Real.exp (-(1 / p)) * Real.exp (1 / p + 2 * (1 / p ^ 2)) := by
          refine mul_le_mul h1 h2 (inv_nonneg.2 ?_) (exp_pos _).le
          have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
          linarith
      _ = Real.exp (2 * (1 / p ^ 2)) := by rw [← exp_add]; ring_nf

/-- Each core factor contributes `∑_a b(a)/a ≤ κ_j H`. -/
lemma sum_coreFactor_div_le {x γ : ℝ} (hx : 0 < x) (hγL : 0 < γ * Real.log x) {j : ℕ}
    (hj : 1 ≤ j) (X : ℕ) :
    ∑ a ∈ Icc 1 X, coreFactor x γ j a / a ≤ candKappa x j *
      (1 / ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)) *
        ∑ a ∈ (Icc 1 X).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a) := by
  have hD := dampedDensity_pos x hj
  have hκ := candKappa_pos x hj
  have hPi0 : 0 < ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIcc.1 hp).1.two_le
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hW : 1 / (dampedDensity x j * (γ * Real.log x)) = candKappa x j *
      (1 / ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))) := by
    rw [dampedDensity_eq]
    field_simp
  rw [← mul_assoc, ← hW, mul_sum, sum_filter]
  refine sum_le_sum fun a ha => ?_
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (mem_Icc.1 ha).1
  unfold coreFactor
  split_ifs with h1 h2
  · have hlog : γ * Real.log x < Real.log a := by
      rw [← Real.log_rpow hx]
      exact Real.log_lt_log (rpow_pos_of_pos hx γ) h1.1
    rw [mul_one_div]
    gcongr
  · exact absurd h1.2 h2
  · rw [zero_div, mul_one_div]
    positivity
  · rw [zero_div]

/-- Real arithmetic for combining the factors of the main term. -/
lemma main_combine {Xr WP Sd Sb κ E Q δ H γL : ℝ} (m : ℕ) (hXr : 0 ≤ Xr) (hWP0 : 0 ≤ WP)
    (hWP : WP ≤ 2 * κ / γL) (hSd0 : 0 ≤ Sd) (hSd : Sd ≤ E * (Q + δ)) (hSb0 : 0 ≤ Sb)
    (hSb : Sb ≤ κ * H) (hκ : 0 ≤ κ) (hγL : 0 < γL) :
    Xr * WP * Sd * Sb ^ m ≤ Xr * (2 / γL) * (κ ^ (m + 1) * E) * (Q + δ) * H ^ m := by
  have h1 : Sb ^ m ≤ (κ * H) ^ m := pow_le_pow_left₀ hSb0 hSb m
  have h2 : Xr * WP * Sd * Sb ^ m ≤ Xr * (2 * κ / γL) * (E * (Q + δ)) * (κ * H) ^ m := by
    have hpow0 : 0 ≤ Sb ^ m := pow_nonneg hSb0 m
    have hWP' : 0 ≤ 2 * κ / γL := hWP0.trans hWP
    have hEQ : 0 ≤ E * (Q + δ) := hSd0.trans hSd
    calc Xr * WP * Sd * Sb ^ m ≤ Xr * (2 * κ / γL) * Sd * Sb ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hWP hXr) hSd0) hpow0
      _ ≤ Xr * (2 * κ / γL) * (E * (Q + δ)) * Sb ^ m :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSd (by positivity)) hpow0
      _ ≤ Xr * (2 * κ / γL) * (E * (Q + δ)) * (κ * H) ^ m :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, pow_succ]
  field_simp

/-- The free-factor sum of one family at one scale, in Euler products. -/
theorem freeFactorSum_le_at {x γ c₁ : ℝ} {j' X : ℕ} (R : ℕ) {F : Finset (Finset ℕ)}
    (hx : 0 < x) (hlogx : 1 ≤ Real.log x) (hγL : 0 < γ * Real.log x) (hc₁ : 0 ≤ c₁)
    (hc₁' : c₁ ≤ 1 / 4) (hg : ∀ g ∈ candidateGroups x, SideGroup g)
    (hFC : F ⊆ candidateGroups x) (hFS : ∀ g ∈ F, g ⊆ primesIcc 2 (proxyCutoff x))
    (hPX : ∀ p ∈ candidatePrimes x, p ≤ X) (hγ : 1 ≤ x ^ γ)
    (hb1 : ∀ e, coreFactor x γ (j' + 1) e ≤ 1) {K : ℝ} (hK1 : 1 ≤ K)
    (hwf : WeightFacts x γ (j' + 1) X (1 / (dampedDensity x (j' + 1) * (γ * Real.log x))) K)
    (hδ' : 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
      ∏ p ∈ u, (1 : ℝ) / p) * K / (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) *
        (5 / 2) ^ F.card ≤ 1) :
    freeFactorSum x γ c₁ j' X F ≤
      X * (2 / (γ * Real.log x)) * (candKappa x (j' + 1) ^ (j' + 1) *
          ∏ p ∈ candidatePrimes x, (1 - (1 : ℝ) / p)⁻¹) *
        ((1 - chernoffTheta * c₁ / 75) ^ F.card +
          8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) *
            K / (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card) *
        (1 / ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)) *
          ∑ a ∈ (Icc 1 X).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a) ^ j' +
      1 / (dampedDensity x (j' + 1) * (γ * Real.log x)) *
        (((primesIcc 2 (proxyCutoff x)).powerset.filter (·.card ≤ R + 1)).card : ℝ) *
        (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) *
        ((X : ℝ) / (⌊x ^ γ⌋₊ + 1) * (1 + Real.log X) ^ (j' + 1)) := by
  set S := primesIcc 2 (proxyCutoff x)
  set Pi := ∏ p ∈ S, (1 - (1 : ℝ) / p)
  set ε := ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p
  set κ := candKappa x (j' + 1)
  have hj : 1 ≤ j' + 1 := by omega
  have hκ0 := candKappa_pos x hj
  have hD0 := dampedDensity_pos x hj
  have hPi0 : 0 < Pi := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIcc.1 hp).1.two_le
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hε0 : 0 ≤ ε := sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  have hpow1 : (1 : ℝ) ≤ (5 / 2) ^ F.card := one_le_pow₀ (by norm_num)
  -- `8 ε / Π ≤ 1`, so `2 ε K / Π ≤ 1/2` and `ε ≤ Π / 2`
  have h8 : 8 * ε / Pi ≤ 1 := by
    refine le_trans ?_ hδ'
    have : 0 ≤ 8 * ε / Pi := by positivity
    calc 8 * ε / Pi = 8 * ε / Pi * 1 * 1 := by ring
      _ ≤ 8 * ε / Pi * K * (5 / 2) ^ F.card := by gcongr
      _ = 8 * ε * K / Pi * (5 / 2) ^ F.card := by ring
  have hδ : 2 * ε * K / Pi ≤ 1 / 2 := by
    have : 8 * ε * K / Pi ≤ 1 := by
      refine le_trans ?_ hδ'
      have : 0 ≤ 8 * ε * K / Pi := by have := hε0; positivity
      exact le_mul_of_one_le_right this hpow1
    have : 2 * ε * K / Pi = (8 * ε * K / Pi) / 4 := by ring
    linarith
  have hW0 : 0 ≤ 1 / (dampedDensity x (j' + 1) * (γ * Real.log x)) := by positivity
  have hfree := freeFactorSum_le R hc₁ hc₁' (fun g hgF => hg g (hFC hgF)) hFS
    ((pairwiseDisjoint_candidateGroups hlogx).subset hFC) hγ hb1 hW0 (by linarith) hwf hδ hδ'
  refine hfree.trans (add_le_add ?_ le_rfl)
  -- the main term
  have hWP : 1 / (dampedDensity x (j' + 1) * (γ * Real.log x)) * (Pi + 2 * ε) ≤
      2 * κ / (γ * Real.log x) := by
    rw [dampedDensity_eq]
    have hε' : Pi + 2 * ε ≤ 2 * Pi := by
      have : ε ≤ Pi / 8 := by rw [div_le_iff₀ hPi0] at h8; linarith
      linarith
    calc 1 / (Pi / κ * (γ * Real.log x)) * (Pi + 2 * ε)
        ≤ 1 / (Pi / κ * (γ * Real.log x)) * (2 * Pi) := by gcongr
      _ = 2 * κ / (γ * Real.log x) := by field_simp
  have hSd := sum_loneFactor_div_le hlogx hg hFC hPX hc₁ hc₁'
    (δ := 8 * ε * K / Pi * (5 / 2) ^ F.card) (by positivity)
  have hSd0 : 0 ≤ ∑ d ∈ (Icc 1 X).filter (· ∈ Nat.factoredNumbers (candidatePrimes x)),
      (loneFactor c₁ F d + 8 * ε * K / Pi * (5 / 2) ^ F.card) / d :=
    sum_nonneg fun d _ => div_nonneg (add_nonneg (loneFactor_mem hc₁ hc₁' F d).1 (by positivity))
      (Nat.cast_nonneg _)
  have hSb := sum_coreFactor_div_le hx hγL hj X
  have hSb0 : 0 ≤ ∑ a ∈ Icc 1 X, coreFactor x γ (j' + 1) a / a :=
    sum_nonneg fun a _ => div_nonneg (coreFactor_nonneg hj hγ a) (Nat.cast_nonneg _)
  have h := main_combine (Xr := (X : ℝ)) j' (Nat.cast_nonneg X) (by positivity) hWP hSd0 hSd hSb0
    hSb hκ0.le hγL
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · ring
  · ring

end

end Erdos408
