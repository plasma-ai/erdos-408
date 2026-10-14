module

public import Erdos408.Extraction.Allocation.Analytic
public import Erdos408.Extraction.Allocation.Budget
public import Erdos408.Extraction.Allocation.Decomposition
public import Erdos408.Extraction.Allocation.MainTerm
public import Erdos408.Extraction.Allocation.Regroup

/-!
# Assembly of E6–E8 at one scale

At a large `x`, given the two-sided estimate, the facts about the groups and
bands, the budgets, and the two analytic inputs (`exists_failure_mass_le`,
`exists_sum_proxyCore_sq_le`) at that `x`, the four pieces of the
decomposition are each `O((x/L) L^{-c'})`:

* the signed expansion: at most `L^4` terms, each `x C* L^{-5-c'}`;
* the clipping error: `L^{c'} · x L^{C₅} / L^{C₅ + 1 + 2c'}`;
* the candidate squares: `L^{c'} √(x L^{-2-4c'-C₅} · x L^{C₅})`;
* the failed patterns: `L^{c'} · C₃ (x/L) L^{-2c'}`.
-/

@[expose] public section

namespace Erdos408

open Finset Real

/-- The endpoint bound at one scale: `|Φ(w/x) P(w) (f_𝔟 - C_𝔟)(w)| ≤ B_d`. -/
lemma abs_endpoint_le_at {q cw : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hcw : 0 < cw)
    (hcw₁ : cw ≤ (1 - q) ^ 2 / 3) {K : ℕ} {CN c κ CΦ : ℝ} {M : ℕ → ℝ} (hκ : 1 < κ)
    (hc : 0 < c) {x : ℝ} {k : ℕ} (hbands : BandFacts K CN x)
    (hmassband : ∀ a : ℝ, 11 / 100 ≤ a → 1 / 2 ≤ harmonicMass (band x a))
    (hH : ∑ p ∈ primesIoc (x ^ (c / logLog x ^ 20)) x, (1 : ℝ) / p ≤ logLog x)
    (hx : 1 < x) (hxκ : κ ≤ x) (hT : 1 ≤ logLog x) (hk : k ≤ 2) {u v : Fin (k + 1) → ℝ}
    {B : (Fin k → ℕ) → ℝ} {Φ : ℝ → ℝ} (hadm : AdmissibleSlots c x u v)
    (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1) (hΦ : IsCutoff κ CΦ M x Φ) :
    ∀ w ∈ Icc 1 ⌊κ * x⌋₊, |Φ (w / x) * endpoint q cw K CN x u v B w| ≤
      |M 0| * ((2 * logLog x ^ 20 / c + 1) ^ 3 + logLog x ^ 3) := by
  set T := logLog x
  have hκ0 : 0 < κ := by linarith
  intro w hw
  obtain ⟨hw1, hwN⟩ := mem_Icc.1 hw
  have hwx : (w : ℝ) ≤ κ * x := (Nat.le_floor_iff (by positivity)).1 hwN
  have hΦ0 : |Φ (w / x)| ≤ |M 0| := by
    have := hΦ.2.2.2 0 (w / x)
    simp only [iteratedDeriv_zero, Nat.cast_zero, mul_zero, rpow_zero, mul_one] at this
    exact this.trans (le_abs_self _)
  have hε : 0 < c / T ^ 20 := by positivity
  have hslot := abs_slotCount_sub_slotMean_le hx
    (Real.log_le_log hκ0 hxκ) hκ0 hε hH hT hk hadm.1
    (by
      have : 0 < c / T ^ 20 := hε
      linarith [hadm.2]) hB hw1 hwx
  have h2ε : 2 / (c / T ^ 20) = 2 * T ^ 20 / c := by
    field_simp
  rw [h2ε] at hslot
  have hP := inertPoly_mem hq hq₁ hcw.le hcw₁ (K := K) (CN := CN) (x := x)
    (fun c hc i hi => hmassband _ (hbands.1 (c, i) (mem_product.2 ⟨hc, hi⟩)).1) w
  rw [endpoint, abs_mul, abs_mul, abs_of_nonneg hP.1]
  calc |Φ (w / x)| * (inertPoly q cw K CN x w * |slotCount x u v B w - slotMean x u v B|)
      ≤ |M 0| * (1 * ((2 * T ^ 20 / c + 1) ^ 3 + T ^ 3)) :=
        mul_le_mul hΦ0 (mul_le_mul hP.2 hslot (abs_nonneg _) zero_le_one)
          (mul_nonneg hP.1 (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

/-- The number of terms of the signed expansion at one scale. -/
lemma card_mul_card_le_at {c₂ x : ℝ} {K : ℕ} {CN : ℝ} (hgroups : GroupFacts x)
    (hbands : BandFacts K CN x)
    (hterms : (4 : ℝ) ^ (2 * logLog x) *
        (2 ^ K * (2 : ℝ) ^ ((K : ℝ) + max CN 0 * logLogLog x)) ≤ Real.log x ^ (4 : ℝ)) :
    ((patternIndex c₂ x).card : ℝ) * (monomialIndex K CN x).card ≤ Real.log x ^ (4 : ℝ) := by
  set T := logLog x
  obtain ⟨-, -, -, -, hcs, hcb, -⟩ := hgroups
  have hC : ((candidateGroups x).card : ℝ) ≤ 2 * T := by
    have : ((candidateGroups x).card : ℝ) ≤ (smallGroups x).card + (bigGroups x).card := by
      exact_mod_cast card_union_le (smallGroups x) (bigGroups x)
    linarith
  have h1 : ((patternIndex c₂ x).card : ℝ) ≤ (4 : ℝ) ^ (2 * T) := by
    calc ((patternIndex c₂ x).card : ℝ) ≤ ((4 ^ (candidateGroups x).card : ℕ) : ℝ) := by
          exact_mod_cast card_patternIndex_le c₂ x
      _ = (4 : ℝ) ^ ((candidateGroups x).card : ℝ) := by push_cast; rw [rpow_natCast]
      _ ≤ _ := rpow_le_rpow_of_exponent_le (by norm_num) hC
  have h2 : ((monomialIndex K CN x).card : ℝ) ≤
      2 ^ K * (2 : ℝ) ^ ((K : ℝ) + max CN 0 * logLogLog x) := by
    calc ((monomialIndex K CN x).card : ℝ)
        ≤ ((2 ^ K * 2 ^ (K * inertPerCluster K CN x) : ℕ) : ℝ) := by
          exact_mod_cast card_monomialIndex_le K CN x
      _ = 2 ^ K * (2 : ℝ) ^ ((K * inertPerCluster K CN x : ℕ) : ℝ) := by
          rw [rpow_natCast]
          push_cast
          ring
      _ ≤ _ := by
          gcongr
          · norm_num
          · exact hbands.2.2
  calc ((patternIndex c₂ x).card : ℝ) * (monomialIndex K CN x).card
      ≤ (4 : ℝ) ^ (2 * T) * (2 ^ K * (2 : ℝ) ^ ((K : ℝ) + max CN 0 * logLogLog x)) := by
        gcongr
    _ ≤ _ := hterms

/-- The signed expansion at one scale: `L^4` terms of size `x C* L^{-5-c'}`. -/
lemma abs_expansion_le_at {q cw : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hcw : 0 < cw)
    (hcw₁ : cw ≤ (1 - q) ^ 2 / 3) {K : ℕ} {CN c κ CΦ γ : ℝ} {M : ℕ → ℝ} (hκ : 1 < κ)
    {c₁ c₂ c' C₅ Cs : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 4) {x : ℝ} {k j : ℕ}
    (hbody : TwoSidedBody q (1 / 2) c₂ 1 (1 / 2) 3 (11 / 100) (39 / 200) K (max CN 0) c k
      (C₅ + 1 + 2 * c') κ (max CΦ 0) (fun r => κ * M r + r * M (r - 1)) (5 + c') Cs x)
    (hgroups : GroupFacts x) (hbands : BandFacts K CN x) (hx : 1 < x) (hT : 1 ≤ logLog x)
    (hγ : 1 ≤ x ^ γ) (hj1 : 1 ≤ j)
    (hterms : (4 : ℝ) ^ (2 * logLog x) *
        (2 ^ K * (2 : ℝ) ^ ((K : ℝ) + max CN 0 * logLogLog x)) ≤ Real.log x ^ (4 : ℝ))
    {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ} {Φ : ℝ → ℝ}
    (hadm : AdmissibleSlots c x u v) (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1)
    (hΦ : IsCutoff κ CΦ M x Φ) :
    |∑ w ∈ Icc 1 ⌊κ * x⌋₊, Φ (w / x) * endpoint q cw K CN x u v B w *
        min (proxyCore x γ j (w + 1)) (Real.log x ^ (C₅ + 1 + 2 * c')) * successProb c₁ c₂ x w| ≤
      |Cs| * (x / Real.log x * Real.log x ^ (-c')) := by
  set L := Real.log x with hLdef
  set Λ := L ^ (C₅ + 1 + 2 * c')
  have hx0 : 0 < x := by linarith
  have hL : 0 < L := Real.log_pos hx
  have hmain := sum_mul_successProb_eq q cw hq.ne' K CN hx0 κ Φ u v B
    (fun n => min (proxyCore x γ j n) Λ) c₁ c₂
  have hexp := abs_sum_expansion_le (c₂ := c₂) (K := K) (CN := CN) hc₁.le (by linarith) hcw.le
    (by nlinarith) hx0.le (R := Cs * L ^ (-(5 + c')))
    (F := fun i m => twoSidedSum q K x κ Φ m.2 u v B (fun n => min (proxyCore x γ j n) Λ)
      (i.1 ∪ i.2))
    (fun i hi m hm => by
      obtain ⟨hP, hQ⟩ := mem_sigma.1 hi
      obtain ⟨hP, hmany⟩ := mem_filter.1 hP
      obtain ⟨hU, hS⟩ := mem_sigma.1 hm
      have hPQ : i.1 ∪ i.2 ⊆ candidateGroups x :=
        union_subset (mem_powerset.1 hP) ((mem_powerset.1 hQ).trans sdiff_subset)
      refine abs_twoSidedSum_le hbody hgroups hbands hx hT hγ hj1 hκ hadm hB hΦ hPQ ?_ ?_ ?_
      · refine hmany.1.trans ?_
        exact_mod_cast card_le_card (inter_subset_inter_right subset_union_left)
      · refine hmany.2.trans ?_
        exact_mod_cast card_le_card (inter_subset_inter_right subset_union_left)
      · exact (mem_powerset.1 hS).trans
          (product_subset_product_left (by simpa using mem_powerset.1 hU)))
  set X := x / L * L ^ (-c') with hX
  have hrp : ∀ a b : ℝ, L ^ a * L ^ b = L ^ (a + b) := fun a b => (rpow_add hL a b).symm
  have hXe : ∀ a : ℝ, a = -c' - 1 → x * L ^ a = X := by
    intro a ha
    rw [ha, rpow_sub_one hL.ne', hX]
    ring
  have hcard := card_mul_card_le_at (c₂ := c₂) hgroups hbands hterms
  rw [hmain]
  refine hexp.trans ?_
  have hR : Cs * L ^ (-(5 + c')) ≤ |Cs| * L ^ (-(5 + c')) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (rpow_pos_of_pos hL _).le
  have hIJ : (0 : ℝ) ≤ ((patternIndex c₂ x).card : ℝ) * (monomialIndex K CN x).card := by
    positivity
  have hR' : 0 ≤ x * (|Cs| * L ^ (-(5 + c'))) :=
    mul_nonneg hx0.le (mul_nonneg (abs_nonneg _) (rpow_pos_of_pos hL _).le)
  calc ((patternIndex c₂ x).card : ℝ) * (monomialIndex K CN x).card *
        (x * (Cs * L ^ (-(5 + c'))))
      ≤ ((patternIndex c₂ x).card : ℝ) * (monomialIndex K CN x).card *
        (x * (|Cs| * L ^ (-(5 + c')))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR hx0.le) hIJ
    _ ≤ L ^ (4 : ℝ) * (x * (|Cs| * L ^ (-(5 + c')))) := mul_le_mul_of_nonneg_right hcard hR'
    _ = |Cs| * (x * L ^ ((4 : ℝ) + -(5 + c'))) := by rw [← hrp]; ring
    _ = |Cs| * X := by rw [hXe _ (by ring)]

/-- The candidate-square multiples up to `κ x + 1` at one scale. -/
lemma card_squares_le_at {x κ c' C₅ : ℝ} (hgroups : GroupFacts x) (hx : 1 < x) (hκ0 : 0 < κ)
    (hL1 : 1 ≤ Real.log x)
    (hsq : (κ * x + 1) * Real.exp (-(Real.log x ^ (28 / 100 : ℝ))) * (6 * logLog x) ≤
      x * Real.log x ^ (-(2 + 4 * c' + C₅))) :
    ((((Icc 1 ⌊κ * x⌋₊).filter fun w => ∃ p ∈ candidatePrimes x, p * p ∣ w + 1).card : ℕ) :
      ℝ) ≤ x * Real.log x ^ (-(2 + 4 * c' + C₅)) := by
  set L := Real.log x
  set T := logLog x
  set N := ⌊κ * x⌋₊
  have hx0 : 0 < x := by linarith
  have h1 := card_filter_sq_dvd_le (candidatePrimes x) N
  have hN : (N : ℝ) + 1 ≤ κ * x + 1 := by
    have := Nat.floor_le (show 0 ≤ κ * x by positivity)
    linarith
  have hsum := sum_one_div_candidatePrimes_le hL1 hgroups
  set e := Real.exp (-(L ^ (28 / 100 : ℝ))) with he
  have he0 : 0 ≤ e := (exp_pos _).le
  have hp : ∀ p ∈ candidatePrimes x,
      ((N : ℝ) + 1) / (p * p) ≤ (κ * x + 1) * e * (1 / p) := by
    intro p hp
    have hp1 : Real.exp (L ^ (28 / 100 : ℝ)) ≤ p := hgroups.2.2.2.2.2.2 p hp
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (exp_pos _) hp1
    have hinv : 1 / (p : ℝ) ≤ e := by
      rw [one_div, he, exp_neg]
      exact inv_anti₀ (exp_pos _) hp1
    have h1p : 0 ≤ 1 / (p : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
    have heq : ((N : ℝ) + 1) / (p * p) = ((N : ℝ) + 1) * (1 / p) * (1 / p) := by
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hN hinv h1p (by linarith [mul_pos hκ0 hx0])) h1p
  calc _ ≤ _ := h1
    _ ≤ ∑ p ∈ candidatePrimes x, (κ * x + 1) * e * (1 / p) := sum_le_sum hp
    _ = (κ * x + 1) * e * ∑ p ∈ candidatePrimes x, (1 : ℝ) / p := by rw [mul_sum]
    _ ≤ (κ * x + 1) * e * (6 * T) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ _ := hsq

/-- E6–E8 at one large `x`. -/
theorem abs_proxySum_le_at {q cw : ℝ} (hq : 0 < q) (hq₁ : q < 1) (hcw : 0 < cw)
    (hcw₁ : cw ≤ (1 - q) ^ 2 / 3) {K : ℕ} {CN c Ch κ CΦ : ℝ} {M : ℕ → ℝ} (hκ : 1 < κ)
    (hc : 0 < c) {c₁ c₂ c' C₃ C₅ Cs : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 4) {x : ℝ} {k j : ℕ}
    (hbody : TwoSidedBody q (1 / 2) c₂ 1 (1 / 2) 3 (11 / 100) (39 / 200) K (max CN 0) c k
      (C₅ + 1 + 2 * c') κ (max CΦ 0) (fun r => κ * M r + r * M (r - 1)) (5 + c') Cs x)
    (hgroups : GroupFacts x) (hbands : BandFacts K CN x)
    (hmassband : ∀ a : ℝ, 11 / 100 ≤ a → 1 / 2 ≤ harmonicMass (band x a))
    (hH : ∑ p ∈ primesIoc (x ^ (c / logLog x ^ 20)) x, (1 : ℝ) / p ≤ logLog x)
    (hx : 1 < x) (hxκ : κ ≤ x) (hT : 1 ≤ logLog x)
    (hBd : |M 0| * ((2 * logLog x ^ 20 / c + 1) ^ 3 + logLog x ^ 3) ≤ Real.log x ^ c')
    (hterms : (4 : ℝ) ^ (2 * logLog x) *
        (2 ^ K * (2 : ℝ) ^ ((K : ℝ) + max CN 0 * logLogLog x)) ≤ Real.log x ^ (4 : ℝ))
    (hsq : (κ * x + 1) * Real.exp (-(Real.log x ^ (28 / 100 : ℝ))) * (6 * logLog x) ≤
      x * Real.log x ^ (-(2 + 4 * c' + C₅)))
    (hfail : ∑ w ∈ Icc 1 ⌊κ * x⌋₊ with x / κ ≤ ((w : ℕ) : ℝ),
        proxyCoeff x (presieveExponent c Ch x) j (w + 1) * failureProb c₁ c₂ x w ≤
      C₃ * (x / Real.log x) * Real.log x ^ (-(2 * c')))
    (hcore : ∑ w ∈ Icc 1 ⌊κ * x⌋₊, proxyCore x (presieveExponent c Ch x) j (w + 1) ^ 2 ≤
      x * Real.log x ^ C₅)
    (hk : k ≤ 2) {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ} {Φ : ℝ → ℝ}
    (hadm : AdmissibleSlots c x u v) (hB : ∀ Q, 0 ≤ B Q ∧ B Q ≤ 1)
    (hΦ : IsCutoff κ CΦ M x Φ) (hj : 2 ≤ j) :
    |proxySum q cw K CN x (presieveExponent c Ch x) κ j Φ u v B| ≤
      (|Cs| + |C₃| + 2) * (x / Real.log x) * Real.log x ^ (-c') := by
  set L := Real.log x with hLdef
  set T := logLog x with hTdef
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x⌋₊
  set Λ := L ^ (C₅ + 1 + 2 * c')
  set Bd := |M 0| * ((2 * T ^ 20 / c + 1) ^ 3 + T ^ 3)
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hL : 0 < L := Real.log_pos hx
  have hL1 : 1 ≤ L := by
    have := Real.log_le_sub_one_of_pos hL
    rw [hTdef, logLog] at hT
    linarith
  have hγ0 : 0 ≤ γ := by
    simp only [γ, presieveExponent]
    positivity
  have hγ : 1 ≤ x ^ γ := one_le_rpow hx.le hγ0
  have hj1 : 1 ≤ j := by omega
  have hΛ : 0 < Λ := rpow_pos_of_pos hL _
  have hBd0 : 0 ≤ Bd := by positivity
  have hBdL : Bd ≤ L ^ c' := hBd
  have hE := abs_endpoint_le_at hq hq₁ hcw hcw₁ hκ hc hbands hmassband hH hx hxκ hT hk hadm hB hΦ
  -- the cutoff vanishes below `x/κ`
  have hFz : ∀ w ∈ Icc 1 N, ¬ x / κ ≤ (w : ℝ) →
      Φ (w / x) * endpoint q cw K CN x u v B w = 0 := by
    intro w _ hw
    by_contra h
    have h1 := (hΦ.2.2.1 _ (left_ne_zero_of_mul h)).1
    rw [inv_eq_one_div, div_le_div_iff₀ hκ0 hx0, one_mul] at h1
    exact hw (by rw [div_le_iff₀ hκ0]; linarith)
  -- the allocation identity
  have hA : ∀ w ∈ Icc 1 N, 0 ≤ proxyCoeff x γ j (w + 1) ∧
      proxyCoeff x γ j (w + 1) ≤ proxyCore x γ j (w + 1) := by
    intro w _
    rw [proxyCoeff_eq x γ j (by omega)]
    have h1 := proxyCore_nonneg hj1 hγ (w + 1)
    have h2 := allocationFactor_nonneg x j (w + 1)
    have h3 := allocationFactor_le_one x hj1 (w + 1)
    exact ⟨mul_nonneg h1 h2, mul_le_of_le_one_right h1 h3⟩
  have hAeq : ∀ w ∈ Icc 1 N, ¬ (∃ p ∈ candidatePrimes x, p * p ∣ w + 1) →
      proxyCoeff x γ j (w + 1) = proxyCore x γ j (w + 1) := by
    intro w _ hw
    rw [proxyCoeff_eq x γ j (by omega), allocationFactor_eq_one x hj1, mul_one]
    by_contra h
    exact hw (exists_sq_dvd_of_not_squarefree x (by omega) h)
  -- the coins lie in `[0, 1]`
  have hcoin : ∀ w : ℕ, ∀ g ∈ candidateGroups x,
      0 ≤ successCoin c₁ g w ∧ successCoin c₁ g w ≤ 1 :=
    fun w g hg => successCoin_mem hc₁.le hc₁' (hgroups.1 g hg).1 w
  -- the decomposition
  rw [proxySum_eq_sum q cw K CN γ j u v B hx0 hκ0 hΦ.2.2.1]
  have hdec := abs_sum_le_of_decomp (W := Icc 1 N)
    (F := fun w => Φ (w / x) * endpoint q cw K CN x u v B w)
    (Aw := fun w => proxyCoeff x γ j (w + 1)) (Gt := fun w => proxyCore x γ j (w + 1))
    (S := successProb c₁ c₂ x) (Fl := failureProb c₁ c₂ x) (Λ := Λ)
    (fun w => ∃ p ∈ candidatePrimes x, p * p ∣ w + 1) (fun w => x / κ ≤ (w : ℝ)) hBd0 hΛ
    hE hFz hA hAeq (fun w _ => successProb_mem_Icc (hcoin w))
    (fun w _ => successProb_add_failureProb c₁ c₂ x w) (fun w _ => failureProb_nonneg (hcoin w))
  -- the signed expansion
  have hmainb := abs_expansion_le_at hq hq₁ hcw hcw₁ hκ hc₁ hc₁' hbody hgroups hbands hx hT hγ
    hj1 hterms hadm hB hΦ (j := j)
  set X := x / L * L ^ (-c') with hX
  have hX0 : 0 ≤ X := by positivity
  have hrp : ∀ a b : ℝ, L ^ a * L ^ b = L ^ (a + b) := fun a b => (rpow_add hL a b).symm
  have hXe : ∀ a : ℝ, a = -c' - 1 → x * L ^ a = X := by
    intro a ha
    rw [ha, rpow_sub_one hL.ne', hX]
    ring
  have hbadc := card_squares_le_at hgroups hx hκ0 hL1 hsq
  -- the clipping error
  have hclip : Bd * (∑ w ∈ Icc 1 N, proxyCore x γ j (w + 1) ^ 2) / Λ ≤ X := by
    rw [div_le_iff₀ hΛ]
    calc Bd * ∑ w ∈ Icc 1 N, proxyCore x γ j (w + 1) ^ 2 ≤ L ^ c' * (x * L ^ C₅) :=
          mul_le_mul hBdL hcore (sum_nonneg fun w _ => sq_nonneg _) (rpow_pos_of_pos hL _).le
      _ = x * (L ^ (-c' - 1) * L ^ (C₅ + 1 + 2 * c')) := by
          rw [mul_left_comm, hrp, hrp]
          ring_nf
      _ = X * Λ := by rw [← mul_assoc, hXe (-c' - 1) rfl]
  have hsqb : Bd * ∑ w ∈ Icc 1 N with (∃ p ∈ candidatePrimes x, p * p ∣ w + 1),
      proxyCore x γ j (w + 1) ≤ X := by
    have hcs := sum_filter_le_sqrt (s := Icc 1 N) (f := fun w => proxyCore x γ j (w + 1))
      (fun w => ∃ p ∈ candidatePrimes x, p * p ∣ w + 1)
    set Y := x * L ^ (-1 - 2 * c') with hYdef
    have hY : 0 ≤ Y := by positivity
    have hcore0 : 0 ≤ ∑ w ∈ Icc 1 N, proxyCore x γ j (w + 1) ^ 2 :=
      sum_nonneg fun w _ => sq_nonneg _
    have hprod : (((Icc 1 N).filter fun w => ∃ p ∈ candidatePrimes x, p * p ∣ w + 1).card : ℝ) *
        ∑ w ∈ Icc 1 N, proxyCore x γ j (w + 1) ^ 2 ≤ Y ^ 2 := by
      have h1 := mul_le_mul hbadc hcore hcore0 (by positivity)
      refine h1.trans (le_of_eq ?_)
      rw [show Y ^ 2 = x * x * (L ^ (-1 - 2 * c') * L ^ (-1 - 2 * c')) by rw [hYdef]; ring,
        show x * L ^ (-(2 + 4 * c' + C₅)) * (x * L ^ C₅) =
          x * x * (L ^ (-(2 + 4 * c' + C₅)) * L ^ C₅) by ring, hrp, hrp]
      ring_nf
    have hsq' : ∑ w ∈ Icc 1 N with (∃ p ∈ candidatePrimes x, p * p ∣ w + 1),
        proxyCore x γ j (w + 1) ≤ Y :=
      hcs.trans ((Real.sqrt_le_sqrt hprod).trans (by rw [Real.sqrt_sq hY]))
    have hnn : 0 ≤ ∑ w ∈ Icc 1 N with (∃ p ∈ candidatePrimes x, p * p ∣ w + 1),
        proxyCore x γ j (w + 1) := sum_nonneg fun w _ => proxyCore_nonneg hj1 hγ _
    calc Bd * _ ≤ L ^ c' * Y := mul_le_mul hBdL hsq' hnn (by positivity)
      _ = x * L ^ (-c' - 1) := by
          rw [hYdef, mul_left_comm, hrp]
          ring_nf
      _ = X := hXe (-c' - 1) rfl
  -- the failed patterns
  have hfailb : Bd * ∑ w ∈ Icc 1 N with x / κ ≤ ((w : ℕ) : ℝ),
      proxyCoeff x γ j (w + 1) * failureProb c₁ c₂ x w ≤ |C₃| * X := by
    have hnn : 0 ≤ ∑ w ∈ Icc 1 N with x / κ ≤ ((w : ℕ) : ℝ),
        proxyCoeff x γ j (w + 1) * failureProb c₁ c₂ x w :=
      sum_nonneg fun w hw => mul_nonneg (hA w (mem_filter.1 hw).1).1
        (failureProb_nonneg (hcoin w))
    have hxL : 0 ≤ x / L := div_nonneg hx0.le hL.le
    have h1 : C₃ * (x / L) * L ^ (-(2 * c')) ≤ |C₃| * (x / L) * L ^ (-(2 * c')) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hxL)
        (rpow_pos_of_pos hL _).le
    calc Bd * _ ≤ L ^ c' * (|C₃| * (x / L) * L ^ (-(2 * c'))) :=
          mul_le_mul hBdL (hfail.trans h1) hnn (rpow_pos_of_pos hL _).le
      _ = |C₃| * (x / L * (L ^ c' * L ^ (-(2 * c')))) := by ring
      _ = |C₃| * X := by rw [hrp, hX]; ring_nf
  -- combine
  calc _ ≤ |Cs| * X + X + X + |C₃| * X := by linarith
    _ = (|Cs| + |C₃| + 2) * (x / L) * L ^ (-c') := by rw [hX]; ring


end Erdos408
