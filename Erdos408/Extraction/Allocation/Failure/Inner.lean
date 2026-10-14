import Erdos408.Extraction.Allocation.Failure.Reduction

/-!
# The free-factor sum at fixed `d` and `r`

For the candidate part `d` and the product `r = e₂ ⋯ e_j` of rough factors, the
sum over the free rough factor `e₁ ∈ (A, B]` of `w(e₁) Ψ_{F,d}(e₁ r d - 1)` is
at most `S_∅ (Φ_F(d) + δ (5/2)^{|F|}) + 4 N w(A + 1) ∏_g #K_g`, where
`Φ_F(d) = ∏_{g ∈ F} (1 - θ c₁ / 5 [ω_g(d) = 1])` and `δ = 8 ε K / Π`: the
relative residue estimate (`Allocation/Failure/Sieve`) feeds the `u`-side
comparison (`Allocation/Failure/USide`), and the model of each group is bounded
on the `v`-side (`Allocation/Failure/VSide`). Since `r` is rough, a group prime
divides `r d` exactly when it divides `d`.

Also `S_∅ ≤ W (B (Π + 2ε) + N)` when `w ≤ W` on `(A, B]`, by the sifted count
with `U = ∅`; above `x^γ` one may take `W = 1/(D_j γ L)`.
-/

namespace Erdos408

open Finset Real

noncomputable section

/-- The `v`-side factor `Φ_F(d) = ∏_{g ∈ F} (1 - θ c₁ / 5 [ω_g(d) = 1])`. -/
def loneFactor (c₁ : ℝ) (F : Finset (Finset ℕ)) (d : ℕ) : ℝ :=
  ∏ g ∈ F, (1 - chernoffTheta * c₁ / 5 * (if primeCount g d = 1 then 1 else 0))

/-- The model product is at most `Φ_F(d)` when `p ∣ c ↔ p ∣ d` on the groups. -/
lemma prod_model_le_loneFactor {F : Finset (Finset ℕ)} (hF : ∀ g ∈ F, SideGroup g) {c₁ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) {c d : ℕ} (hcd : ∀ g ∈ F, ∀ p ∈ g, p ∣ c ↔ p ∣ d) :
    ∏ g ∈ F, (1 - sideAlpha c₁ g d * (∑ p ∈ g, modelWeight c p -
      ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, modelWeight c p)) ≤ loneFactor c₁ F d :=
  prod_le_prod₀ (fun g hg => ((hF g hg).one_sub_sideAlpha_mul_le hc₁ hc₁' (hcd g hg)).1)
    fun g hg => ((hF g hg).one_sub_sideAlpha_mul_le hc₁ hc₁' (hcd g hg)).2

/-- The absolute model product is at most `(5/2)^{|F|}`. -/
lemma prod_model_abs_le {F : Finset (Finset ℕ)} (hF : ∀ g ∈ F, SideGroup g) {c₁ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₁' : c₁ ≤ 1 / 4) (d c : ℕ) :
    ∏ g ∈ F, (1 + |sideAlpha c₁ g d| * (∑ p ∈ g, modelWeight c p +
      ∑ K ∈ g.powersetCard 2, ∏ p ∈ K, modelWeight c p)) ≤ (5 / 2) ^ F.card := by
  rw [← prod_const]
  refine prod_le_prod₀ (fun g hg => ?_) fun g hg => ?_
  · have h0 : 0 ≤ sideModelAbs g c := add_nonneg (sum_nonneg ((hF g hg).modelWeight_nonneg _))
      (sum_nonneg fun K hK => prod_nonneg fun p hp =>
        (hF g hg).modelWeight_nonneg _ p ((mem_powersetCard.1 hK).1 hp))
    have := mul_nonneg (abs_nonneg (sideAlpha c₁ g d)) h0
    unfold sideModelAbs at this
    linarith
  · obtain ⟨h1, h2⟩ := (hF g hg).sideAlpha_mem hc₁ hc₁' d
    have h3 : 0 ≤ sideModelAbs g c := add_nonneg (sum_nonneg ((hF g hg).modelWeight_nonneg _))
      (sum_nonneg fun K hK => prod_nonneg fun p hp =>
        (hF g hg).modelWeight_nonneg _ p ((mem_powersetCard.1 hK).1 hp))
    have h5 := mul_le_mul h2 ((hF g hg).sideModelAbs_le c) h3 (by norm_num)
    unfold sideModelAbs at h5
    rw [abs_of_nonneg h1]
    linarith

/-- The free-factor sum at fixed `d` and `r`. -/
theorem sum_free_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {F : Finset (Finset ℕ)}
    (hF : ∀ g ∈ F, SideGroup g) (hFS : ∀ g ∈ F, g ⊆ S)
    (hdisj : (F : Set (Finset ℕ)).PairwiseDisjoint id) {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₁' : c₁ ≤ 1 / 4) {d r : ℕ} (hd : 1 ≤ d) (hr : 1 ≤ r) (hrS : ∀ p ∈ S, ¬ p ∣ r) (R : ℕ)
    {A B : ℕ} (hA : 1 ≤ A) {w : ℕ → ℝ} (hw0 : ∀ e, 0 ≤ w e)
    (hw : ∀ e, A < e → w (e + 1) ≤ w e) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ e ∈ Ioc A B, w (A + 1) ≤ K * w e)
    (hδ : 2 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) * K /
      ∏ p ∈ S, (1 - (1 : ℝ) / p) ≤ 1 / 2) :
    ∑ a ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ a then w a else 0) * sideProd c₁ F d (a * (r * d) - 1) ≤
      (∑ a ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ a then w a else 0)) *
          (loneFactor c₁ F d + 8 * (∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) * K /
            (∏ p ∈ S, (1 - (1 : ℝ) / p)) * (5 / 2) ^ F.card) +
        4 * ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ) * w (A + 1) *
          ∏ g ∈ F, ((lowSubsets g).card : ℝ) := by
  set ε := ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p
  set Pi := ∏ p ∈ S, (1 - (1 : ℝ) / p)
  set N := ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ)
  set S0 := ∑ a ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ a then w a else 0)
  have hε0 : 0 ≤ ε := sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  have hPi0 : 0 < Pi := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hS00 : 0 ≤ S0 := sum_nonneg fun a _ => by split_ifs <;> simp [hw0 a]
  have hcard0 : 0 ≤ ∏ g ∈ F, ((lowSubsets g).card : ℝ) := prod_nonneg fun _ _ => by positivity
  have hE0 : 0 ≤ 4 * N * w (A + 1) := mul_nonneg (by positivity) (hw0 _)
  have hδ0 : 0 ≤ 8 * ε * K / Pi := by positivity
  have hloneF0 : 0 ≤ loneFactor c₁ F d := prod_nonneg fun g _ => by
    have := chernoffTheta_le_one
    have := chernoffTheta_pos
    split_ifs <;> nlinarith
  by_cases hAB : A ≤ B
  swap
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity
  have hrd : 1 ≤ r * d := one_le_mul hr hd
  -- the relative residue estimate for every admissible `U`
  have hstar : ∀ U ⊆ S, (∀ p ∈ U, ¬ p ∣ r * d) →
      |∑ e ∈ Ioc A B, (if (∀ p ∈ S, ¬ p ∣ e) ∧ ∀ p ∈ U, e * (r * d) ≡ 1 [MOD p] then w e else 0) -
          S0 / ∏ p ∈ U, ((p : ℝ) - 1)| ≤
        8 * ε * K / Pi * (S0 / ∏ p ∈ U, ((p : ℝ) - 1)) + 4 * N * w (A + 1) := fun U hU hc =>
    abs_weighted_cong_sub_le S U hS hU hc R hAB (fun e _ => hw0 e) hw hK0 hK hδ
  have hF' := sum_rough_mul_prod_le S hS F hFS hdisj (fun g => sideAlpha c₁ g d)
    (fun g hg => by
      obtain ⟨h1, h2⟩ := (hF g hg).sideAlpha_mem hc₁ hc₁' d
      rw [abs_le]
      constructor <;> linarith) hrd hA hw0 hE0 hstar
  simp only [sideProd]
  beta_reduce at hF'
  refine hF'.trans ?_
  -- the model of each group, and the absolute model
  have hcd : ∀ g ∈ F, ∀ p ∈ g, p ∣ r * d ↔ p ∣ d := by
    intro g hg p hp
    refine ⟨fun h => ?_, fun h => dvd_mul_of_dvd_right h r⟩
    rcases (Nat.Prime.dvd_mul (hS p (hFS g hg hp))).1 h with h | h
    · exact absurd h (hrS p (hFS g hg hp))
    · exact h
  have hmodel := prod_model_le_loneFactor hF hc₁ hc₁' hcd
  have habs := prod_model_abs_le hF hc₁ hc₁' d (r * d)
  have h1 := mul_le_mul_of_nonneg_left hmodel hS00
  have h2 := mul_le_mul_of_nonneg_left habs (mul_nonneg hδ0 hS00)
  refine (add_le_add (add_le_add h1 h2) le_rfl).trans (le_of_eq ?_)
  ring

/-- The total free weight: `S_∅ ≤ W (B (Π + 2ε) + N)` when `w ≤ W` on `(A, B]`. -/
lemma sum_rough_weight_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℕ) {A B : ℕ}
    {w : ℕ → ℝ} {W : ℝ} (hwW : ∀ e ∈ Ioc A B, w e ≤ W) (hW : 0 ≤ W) :
    ∑ a ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ a then w a else 0) ≤
      W * ((B : ℝ) * (∏ p ∈ S, (1 - (1 : ℝ) / p) +
          2 * ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p) +
        ((S.powerset.filter (·.card ≤ R + 1)).card : ℝ)) := by
  by_cases hAB : A ≤ B
  swap
  · rw [Ioc_eq_empty (by omega), sum_empty]
    have : 0 ≤ ∏ p ∈ S, (1 - (1 : ℝ) / p) := prod_nonneg fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
      have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have : 0 ≤ ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p :=
      sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
    positivity
  have h := abs_card_rough_cong_sub_le S ∅ hS (empty_subset S) (c := 1) (by simp) R hAB
  simp only [prod_empty, div_one, notMem_empty, IsEmpty.forall_iff, implies_true, and_true] at h
  have hcount := (abs_le.1 h).2
  have hle : ∑ a ∈ Ioc A B, (if ∀ p ∈ S, ¬ p ∣ a then w a else 0) ≤
      W * (((Ioc A B).filter fun e => ∀ p ∈ S, ¬ p ∣ e).card : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, mul_sum, sum_filter]
    refine sum_le_sum fun a ha => ?_
    split_ifs
    · rw [mul_one]
      exact hwW a ha
    · exact le_rfl
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ hW)
  have hB : (B : ℝ) - A ≤ B := by linarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hBA : 0 ≤ (B : ℝ) - A := by
    rw [sub_nonneg]
    exact_mod_cast hAB
  have hPi : 0 ≤ ∏ p ∈ S, (1 - (1 : ℝ) / p) := prod_nonneg fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hε : 0 ≤ ∑ u ∈ S.powersetCard (R + 1), ∏ p ∈ u, (1 : ℝ) / p :=
    sum_nonneg fun u _ => prod_nonneg fun p _ => by positivity
  have := mul_le_mul_of_nonneg_right hB (add_nonneg hPi (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε))
  nlinarith

end

end Erdos408
