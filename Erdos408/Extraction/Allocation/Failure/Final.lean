import Erdos408.Extraction.Allocation.Failure.Params

/-!
# E6 at one scale

The free-factor sum of a family, given the numerical facts at the scale `x`:
`κ_j^j ∏_{p ∈ P} (1 - 1/p)⁻¹ ≤ 2`, `(1 - θ/300)^{|F|} ≤ e^{-aT}`, `δ ≤ e^{-T}`,
`(2/(γ L)) H^{j-1} ≤ e^{aT/4}/L`, and a rounding term at most `X e^{-T}/L`.
-/

namespace Erdos408

open Finset Filter Real

noncomputable section

/-- The weight facts at one scale. -/
lemma weightFacts_at {x γ : ℝ} (hx : 1 < x) (hγ0 : 0 < γ) (hγ : 1 ≤ x ^ γ) {j : ℕ}
    (hj : 1 ≤ j) (X : ℕ) :
    WeightFacts x γ j X (1 / (dampedDensity x j * (γ * Real.log x)))
      (Real.log X / (γ * Real.log x)) := by
  have hD := dampedDensity_pos x hj
  have hL : 0 < Real.log x := Real.log_pos hx
  have hγL : 0 < γ * Real.log x := mul_pos hγ0 hL
  have hA1 : 1 ≤ ⌊x ^ γ⌋₊ := Nat.le_floor (by simpa using hγ)
  have hx0 : 0 < x := by linarith
  -- above `A = ⌊x^γ⌋`, `log e > γ L`
  have hlog : ∀ e : ℕ, ⌊x ^ γ⌋₊ < e → γ * Real.log x < Real.log e := by
    intro e he
    have h1 : x ^ γ < e := (Nat.floor_lt (by positivity)).1 he
    rw [← Real.log_rpow hx0]
    exact Real.log_lt_log (rpow_pos_of_pos hx0 γ) h1
  refine ⟨fun e => ?_, fun e he => ?_, fun e he => ?_, fun e he heX => ?_⟩
  · unfold roughWeight
    have : 0 ≤ Real.log (e : ℝ) := Real.log_natCast_nonneg e
    positivity
  · unfold roughWeight
    have h1 := hlog e he
    have h2 : Real.log (e : ℝ) ≤ Real.log ((e + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by have := lt_trans hγL h1; exact_mod_cast (show 0 < e by omega))
        (by push_cast; linarith)
    exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
  · unfold roughWeight
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hlog e he])
  · unfold roughWeight
    have h1 := hlog (⌊x ^ γ⌋₊ + 1) (by omega)
    have h2 := hlog e he
    have h3 : Real.log (e : ℝ) ≤ Real.log X :=
      Real.log_le_log (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast heX)
    have hle : 0 < Real.log (e : ℝ) := lt_trans hγL h2
    calc 1 / (dampedDensity x j * Real.log ((⌊x ^ γ⌋₊ + 1 : ℕ) : ℝ))
        ≤ 1 / (dampedDensity x j * (γ * Real.log x)) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = Real.log (e : ℝ) / (γ * Real.log x) * (1 / (dampedDensity x j * Real.log (e : ℝ))) := by
          field_simp
      _ ≤ Real.log X / (γ * Real.log x) * (1 / (dampedDensity x j * Real.log (e : ℝ))) := by
          gcongr

/-- Every core factor is at most `1/(D_j γ L)`. -/
lemma coreFactor_le_of {x γ : ℝ} (hx : 1 < x) {j : ℕ} (hj : 1 ≤ j) (e : ℕ) :
    coreFactor x γ j e ≤ 1 / (dampedDensity x j * (γ * Real.log x)) ∨ γ ≤ 0 := by
  by_cases hγ0 : γ ≤ 0
  · exact Or.inr hγ0
  left
  push Not at hγ0
  have hD := dampedDensity_pos x hj
  have hL : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  unfold coreFactor
  split_ifs with h
  · have hlog : γ * Real.log x < Real.log e := by
      rw [← Real.log_rpow hx0]
      exact Real.log_lt_log (rpow_pos_of_pos hx0 γ) h.1
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  · positivity

/-- Real arithmetic for the last step. -/
lemma final_combine {X L κE Q δ G Err W e1 e2 e3 : ℝ} (hX : 0 ≤ X) (hL : 0 < L)
    (hκE : κE ≤ 2) (hQ0 : 0 ≤ Q) (hQ : Q ≤ e1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ e2) (hG0 : 0 ≤ G)
    (hG : G ≤ e3 / L) (hW : W ≤ 1) (hErr0 : 0 ≤ Err) (hErr : Err ≤ X * e2 / L) :
    X * κE * (Q + δ) * G + W * Err ≤ X / L * (2 * e3 * (e1 + e2) + e2) := by
  have h1 : X * κE * (Q + δ) * G ≤ X * 2 * (e1 + e2) * (e3 / L) := by
    have a1 : X * κE ≤ X * 2 := mul_le_mul_of_nonneg_left hκE hX
    have a2 : Q + δ ≤ e1 + e2 := add_le_add hQ hδ
    have a3 : X * κE * (Q + δ) ≤ X * 2 * (e1 + e2) :=
      mul_le_mul a1 a2 (by linarith) (by positivity)
    exact mul_le_mul a3 hG hG0 (mul_nonneg (by positivity) (by linarith))
  have h2 : W * Err ≤ X * e2 / L := (mul_le_of_le_one_left hErr0 hW).trans hErr
  have h3 : X * 2 * (e1 + e2) * (e3 / L) + X * e2 / L = X / L * (2 * e3 * (e1 + e2) + e2) := by
    field_simp
  linarith

/-- The free-factor sum of one family at one scale, given the numerical facts. -/
theorem freeFactorSum_le_of_facts {x γ : ℝ} {j' X : ℕ} (R : ℕ) {F : Finset (Finset ℕ)} (a : ℝ)
    (hx : 1 < x) (hlogx : 1 ≤ Real.log x) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hg : ∀ g ∈ candidateGroups x, SideGroup g) (hFC : F ⊆ candidateGroups x)
    (hFS : ∀ g ∈ F, g ⊆ primesIcc 2 (proxyCutoff x)) (hxX : x ≤ X)
    (hPX : ∀ p ∈ candidatePrimes x, p ≤ X)
    (hDγL : 1 ≤ dampedDensity x (j' + 1) * (γ * Real.log x))
    (hκE : candKappa x (j' + 1) ^ (j' + 1) * ∏ p ∈ candidatePrimes x, (1 - (1 : ℝ) / p)⁻¹ ≤ 2)
    (hdecay : (1 - chernoffTheta * (1 / 4) / 75) ^ F.card ≤ Real.exp (-(a * logLog x)))
    (hδ : 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
      ∏ p ∈ u, (1 : ℝ) / p) * (Real.log X / (γ * Real.log x)) /
        (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card ≤
      Real.exp (-logLog x))
    (hH : 2 / (γ * Real.log x) *
      (1 / ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)) *
        ∑ a ∈ (Icc 1 X).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a) ^ j' ≤
      Real.exp (a * logLog x / 4) / Real.log x)
    (herr : (((primesIcc 2 (proxyCutoff x)).powerset.filter (·.card ≤ R + 1)).card : ℝ) *
        (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) *
        ((X : ℝ) / (⌊x ^ γ⌋₊ + 1) * (1 + Real.log X) ^ (j' + 1)) ≤
      X * Real.exp (-logLog x) / Real.log x) :
    freeFactorSum x γ (1 / 4) j' X F ≤
      X / Real.log x * (2 * Real.exp (a * logLog x / 4) *
        (Real.exp (-(a * logLog x)) + Real.exp (-logLog x)) + Real.exp (-logLog x)) := by
  have hj : 1 ≤ j' + 1 := by omega
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := by linarith
  have hγL : 0 < γ * Real.log x := mul_pos hγ0 hL
  have hγx : 1 ≤ x ^ γ := one_le_rpow hx.le hγ0.le
  have hW1 : 1 / (dampedDensity x (j' + 1) * (γ * Real.log x)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hDγL
  have hb1 : ∀ e, coreFactor x γ (j' + 1) e ≤ 1 := fun e =>
    ((coreFactor_le_of hx hj e).resolve_right (not_le.2 hγ0)).trans hW1
  have hK1 : 1 ≤ Real.log X / (γ * Real.log x) := by
    rw [le_div_iff₀ hγL, one_mul]
    have h1 : Real.log x ≤ Real.log X := Real.log_le_log hx0 hxX
    nlinarith
  have hwf := weightFacts_at hx hγ0 hγx hj X
  have hδ1 : 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
      ∏ p ∈ u, (1 : ℝ) / p) * (Real.log X / (γ * Real.log x)) /
        (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card ≤ 1 :=
    hδ.trans (by rw [exp_le_one_iff]; linarith [Real.log_nonneg hlogx, show 0 ≤ logLog x from
      Real.log_nonneg hlogx])
  have hmain := freeFactorSum_le_at (c₁ := 1 / 4) R hx0 hlogx hγL (by norm_num) (by norm_num) hg hFC
    hFS hPX
    hγx hb1 hK1 hwf hδ1
  refine hmain.trans ?_
  have hPi0 : 0 < ∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIcc.1 hp).1.two_le
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hQ0 : 0 ≤ (1 - chernoffTheta * (1 / 4) / 75) ^ F.card := pow_nonneg (by
    have := chernoffTheta_le_one
    linarith) _
  have hδ0 : 0 ≤ 8 * (∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1),
      ∏ p ∈ u, (1 : ℝ) / p) * (Real.log X / (γ * Real.log x)) /
        (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card := by
    have : 0 ≤ ∑ u ∈ (primesIcc 2 (proxyCutoff x)).powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p :=
      sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
    have : 0 ≤ Real.log X / (γ * Real.log x) := by linarith
    positivity
  have hG0 : 0 ≤ 2 / (γ * Real.log x) *
      (1 / ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)) *
        ∑ a ∈ (Icc 1 X).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a) ^ j' := by
    have : 0 ≤ ∑ a ∈ (Icc 1 X).filter (IsYRough (proxyCutoff x)), (1 : ℝ) / a :=
      sum_nonneg fun a _ => by positivity
    positivity
  have hErr0 : 0 ≤ (((primesIcc 2 (proxyCutoff x)).powerset.filter (·.card ≤ R + 1)).card : ℝ) *
      (2 + 4 * ∏ g ∈ F, ((lowSubsets g).card : ℝ)) *
      ((X : ℝ) / (⌊x ^ γ⌋₊ + 1) * (1 + Real.log X) ^ (j' + 1)) := by
    have : 0 ≤ ∏ g ∈ F, ((lowSubsets g).card : ℝ) := prod_nonneg fun _ _ => by positivity
    have : 0 ≤ 1 + Real.log X := by linarith [Real.log_natCast_nonneg X]
    positivity
  have h := final_combine (X := (X : ℝ)) (Nat.cast_nonneg X) hL hκE hQ0 hdecay hδ0 hδ hG0 hH
    hW1 hErr0 herr
  refine le_trans (le_of_eq ?_) h
  ring

end

end Erdos408
