module

public import Erdos408.TwoSided.Graph.BoundsLists

/-!
# The absolute bound of a pattern pairing

The generic bound behind Lemma G2a of `blueprint/two_sided_correlation.md` §4.2: bounding every
factor of `patternPairing` absolutely, keeping each damping with its list sum.

* `sup_z z^M q₀^{z/2} < ∞`, so `#lists(n) q₀^{(ω(n) - Ms)₊/2} ≤ c^s` with `c = c(M, q₀)`.
* The auxiliary labels have mass exactly `1` (`sum_labelMass`, `Setup.lean`).
* Hence `‖patternPairing‖ ≤ |S| κ_K sup|g| (β^{2M} c²)^s` with `β = max 1 v₋⁻¹`.
-/

@[expose] public section

namespace Erdos408.TwoSided

namespace GraphBounds

open Finset

/-- `z^M q₀^{z/2} ≤ c q₀^{M/2}` for all `z`, for some `c ≥ 1`. -/
theorem exists_pow_mul_sqrt_pow_le {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (M : ℕ) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ z : ℕ, (z : ℝ) ^ M * Real.sqrt q₀ ^ z ≤ c * Real.sqrt q₀ ^ M := by
  have hs0 : 0 < Real.sqrt q₀ := Real.sqrt_pos.2 hq₀
  have hs1 : Real.sqrt q₀ < 1 := (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hq₀₁)
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one M
    (show |Real.sqrt q₀| < 1 by rw [abs_of_pos hs0]; exact hs1)
  obtain ⟨K, hK⟩ := ht.bddAbove_range
  have hpos : 0 < Real.sqrt q₀ ^ M := pow_pos hs0 M
  refine ⟨max 1 (K / Real.sqrt q₀ ^ M), le_max_left _ _, fun z => ?_⟩
  calc (z : ℝ) ^ M * Real.sqrt q₀ ^ z ≤ K := hK ⟨z, rfl⟩
    _ = K / Real.sqrt q₀ ^ M * Real.sqrt q₀ ^ M := by field_simp
    _ ≤ max 1 (K / Real.sqrt q₀ ^ M) * Real.sqrt q₀ ^ M :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A list sum with its damping.** If `z^M q₀^{z/2} ≤ c q₀^{M/2}` for all `z`, then
`#lists(n) q₀^{(ω(n) - Ms)₊/2} ≤ c^s`: `#lists(n) ≤ ∏_g ω_g(n)^M`. -/
theorem card_physicalLists_mul_damping_le (P : ι → Finset ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hq₀₁ : q₀ < 1) {M : ℕ} {c : ℝ}
    (hc : ∀ z : ℕ, (z : ℝ) ^ M * Real.sqrt q₀ ^ z ≤ c * Real.sqrt q₀ ^ M) (n : ℕ) :
    (#(physicalLists P M n) : ℝ) *
        Real.sqrt q₀ ^ (groupPrimeCount P n - M * Fintype.card ι) ≤
      c ^ Fintype.card ι := by
  set r := Real.sqrt q₀
  have hr0 : 0 < r := Real.sqrt_pos.2 hq₀
  have hr1 : r ≤ 1 := ((Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hq₀₁)).le
  have hpos : 0 < ∏ _g : ι, r ^ M := prod_pos fun _ _ => pow_pos hr0 M
  -- `q₀^{(ω - Ms)₊/2} q₀^{Ms/2} ≤ q₀^{ω/2} = ∏_g q₀^{ω_g/2}`
  have hdamp : r ^ (groupPrimeCount P n - M * Fintype.card ι) * ∏ _g : ι, r ^ M ≤
      ∏ g, r ^ primeCount (P g) n := by
    rw [prod_const, card_univ, ← pow_mul, ← pow_add, prod_pow_eq_pow_sum]
    exact pow_le_pow_of_le_one hr0.le hr1 (by unfold groupPrimeCount; omega)
  have hcard : (#(physicalLists P M n) : ℝ) ≤ ∏ g, (primeCount (P g) n : ℝ) ^ M := by
    exact_mod_cast card_physicalLists_le P M n
  have h₁ : (#(physicalLists P M n) : ℝ) *
      r ^ (groupPrimeCount P n - M * Fintype.card ι) * ∏ _g : ι, r ^ M ≤
      c ^ Fintype.card ι * ∏ _g : ι, r ^ M := by
    calc (#(physicalLists P M n) : ℝ) *
          r ^ (groupPrimeCount P n - M * Fintype.card ι) * ∏ _g : ι, r ^ M
        ≤ (∏ g, (primeCount (P g) n : ℝ) ^ M) * ∏ g, r ^ primeCount (P g) n := by
          rw [mul_assoc]
          exact mul_le_mul hcard hdamp (by positivity)
            (prod_nonneg fun _ _ => by positivity)
      _ = ∏ g, (primeCount (P g) n : ℝ) ^ M * r ^ primeCount (P g) n :=
          prod_mul_distrib.symm
      _ ≤ ∏ _g : ι, c * r ^ M :=
          prod_le_prod₀ (fun _ _ => by positivity) fun g _ => hc _
      _ = c ^ Fintype.card ι * ∏ _g : ι, r ^ M := by
          rw [prod_mul_distrib, prod_const, card_univ]
  exact le_of_mul_le_mul_right h₁ hpos

/-- `‖D^{iζ}‖ ≤ 1` for a natural number `D`. -/
theorem norm_natCast_cpow_mul_I_le (D : ℕ) (ζ : ℝ) :
    ‖(D : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    by_cases hζ : (ζ : ℂ) * Complex.I = 0
    · rw [hζ, Complex.cpow_zero, norm_one]
    · rw [Nat.cast_zero, Complex.zero_cpow hζ, norm_zero]
      exact zero_le_one
  · rw [Complex.norm_natCast_cpow_of_pos hD]
    simp

/-- **The absolute pattern bound.** With `‖f‖ ≤ 1`, `‖g‖ ≤ L_g`, `‖K‖ ≤ κ_K`, `V_g ≥ v₋` and
`z^M q₀^{z/2} ≤ c q₀^{M/2}` (`M = J + 1`),
`‖patternPairing P q₀ C K ζ S f g‖ ≤ |S| κ_K L_g (β^{2M} c²)^s` with `β = max 1 v₋⁻¹`. The
target lists are bounded by all physical lists at `n + D`. -/
theorem norm_patternPairing_le (P : ι → Finset ℕ) {vlo : ℝ} (hvlo : 0 < vlo)
    (hV : ∀ g, vlo ≤ harmonicMass (P g)) {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) {J : ℕ}
    {c : ℝ} (hc : ∀ z : ℕ, (z : ℝ) ^ (J + 1) * Real.sqrt q₀ ^ z ≤ c * Real.sqrt q₀ ^ (J + 1))
    (hc1 : 1 ≤ c) (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ) {κK : ℝ}
    (hK : ∀ p p' a, ‖K p p' a‖ ≤ κK) (ζ : ℝ) (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, ‖f n‖ ≤ 1) {g : ℕ → ℂ} {Lg : ℝ} (hg : ∀ n, ‖g n‖ ≤ Lg) :
    ‖patternPairing P q₀ C K ζ S f g‖ ≤
      #S * κK * Lg * ((max 1 vlo⁻¹) ^ (2 * (J + 1)) * c ^ 2) ^ Fintype.card ι := by
  set β := max 1 vlo⁻¹
  set s := Fintype.card ι
  set Λ : ℕ → ℝ := fun n => Real.sqrt q₀ ^ (groupPrimeCount P n - (J + 1) * s)
  set aux : (ι → Fin J → ℕ) → ℝ := fun a => ∏ h, ∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹
  set B := (β ^ (2 * (J + 1))) ^ s with hB
  have hVpos : ∀ h, 0 < harmonicMass (P h) := fun h => hvlo.trans_le (hV h)
  have hκ : 0 ≤ κK := (norm_nonneg _).trans (hK 0 0 0)
  have hLg : 0 ≤ Lg := (norm_nonneg _).trans (hg 0)
  have hc0 : 0 ≤ c := by linarith
  have hβ : 1 ≤ β := le_max_left _ _
  have hBnn : 0 ≤ B := pow_nonneg (pow_nonneg (by linarith) _) _
  have hΛ : ∀ n, 0 ≤ Λ n := fun n => pow_nonneg (Real.sqrt_nonneg _) _
  have haux : ∀ a, 0 ≤ aux a := fun a => prod_nonneg fun h _ => prod_nonneg fun i _ =>
    inv_nonneg.2 (mul_nonneg (hVpos h).le (Nat.cast_nonneg _))
  have hlist : ∀ n, (#(physicalLists P (J + 1) n) : ℝ) * Λ n ≤ c ^ s := fun n =>
    card_physicalLists_mul_damping_le P hq₀ hq₀₁ hc n
  -- the mass of one edge
  have hmass : ∀ a, 0 ≤ ∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
      (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) * (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) ∧
      ∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
      (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) * (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) ≤
      B * aux a := by
    intro a
    have hinv : ∀ h, 0 ≤ (harmonicMass (P h))⁻¹ := fun h => inv_nonneg.2 (hVpos h).le
    have hβh : ∀ h, (harmonicMass (P h))⁻¹ ≤ β := fun h =>
      (inv_anti₀ hvlo (hV h)).trans (le_max_right _ _)
    have heq : ∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
        (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) * (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) =
        (∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) * (harmonicMass (P h))⁻¹ ^ ((C h).card + 1)) *
          aux a := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun h _ => by ring
    rw [heq]
    have hβ0 : 0 ≤ β := by linarith
    refine ⟨mul_nonneg (prod_nonneg fun h _ =>
        mul_nonneg (pow_nonneg (hinv h) _) (pow_nonneg (hinv h) _)) (haux a),
      mul_le_mul_of_nonneg_right ?_ (haux a)⟩
    rw [hB, show (β ^ (2 * (J + 1))) ^ s = ∏ _h : ι, β ^ (2 * (J + 1)) by
      rw [prod_const, card_univ]]
    refine prod_le_prod₀ (fun h _ => mul_nonneg (pow_nonneg (hinv h) _)
      (pow_nonneg (hinv h) _)) fun h _ => ?_
    have hCh : (C h).card + 1 ≤ J + 1 := by
      have := card_le_univ (C h)
      rw [Fintype.card_fin] at this
      omega
    calc (harmonicMass (P h))⁻¹ ^ (J + 1) * (harmonicMass (P h))⁻¹ ^ ((C h).card + 1)
        ≤ β ^ (J + 1) * β ^ (J + 1) := mul_le_mul (pow_le_pow_left₀ (hinv h) (hβh h) _)
          ((pow_le_pow_left₀ (hinv h) (hβh h) _).trans (pow_le_pow_right₀ hβ hCh))
          (pow_nonneg (hinv h) _) (pow_nonneg hβ0 _)
      _ = β ^ (2 * (J + 1)) := by ring
  -- one term
  have hterm : ∀ n p a p', ‖((∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
          (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) *
          (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) : ℝ) : ℂ) *
        starRingEnd ℂ (f n) * K p p' a *
        ((edgeProduct C p a : ℂ) ^ ((ζ : ℂ) * Complex.I)) *
        ((Λ n * Λ (n + edgeProduct C p a) : ℝ) : ℂ) * g (n + edgeProduct C p a)‖ ≤
      B * aux a * κK * Lg * (Λ n * Λ (n + edgeProduct C p a)) := by
    intro n p a p'
    obtain ⟨hm0, hm⟩ := hmass a
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_conj, Real.norm_of_nonneg hm0, Real.norm_of_nonneg (mul_nonneg (hΛ n) (hΛ _))]
    have h₁ := norm_natCast_cpow_mul_I_le (edgeProduct C p a) ζ
    have hBw : 0 ≤ B * aux a := mul_nonneg hBnn (haux a)
    have hΛ2 := mul_nonneg (hΛ n) (hΛ (n + edgeProduct C p a))
    calc _ ≤ B * aux a * 1 * κK * 1 * (Λ n * Λ (n + edgeProduct C p a)) * Lg :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul
            (mul_le_mul hm (hf n) (norm_nonneg _) hBw) (hK p p' a) (norm_nonneg _)
            (by rw [mul_one]; exact hBw)) h₁ (norm_nonneg _)
            (by rw [mul_one]; exact mul_nonneg hBw hκ)) hΛ2) (hg _) (norm_nonneg _)
            (by rw [mul_one, mul_one]; exact mul_nonneg (mul_nonneg hBw hκ) hΛ2)
      _ = B * aux a * κK * Lg * (Λ n * Λ (n + edgeProduct C p a)) := by ring
  -- the target lists, by all physical lists at `n + D`
  have hinner : ∀ n p a (T : Finset (ι → Fin (J + 1) → ℕ)),
      T ⊆ physicalLists P (J + 1) (n + edgeProduct C p a) →
      ∑ _p' ∈ T, B * aux a * κK * Lg * (Λ n * Λ (n + edgeProduct C p a)) ≤
        κK * Lg * B * c ^ s * Λ n * aux a := by
    intro n p a T hT
    rw [sum_const, nsmul_eq_mul]
    have hcard : (#T : ℝ) ≤ #(physicalLists P (J + 1) (n + edgeProduct C p a)) := by
      exact_mod_cast card_le_card hT
    have hl := hlist (n + edgeProduct C p a)
    have h0 : 0 ≤ B * aux a * κK * Lg * Λ n :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hBnn (haux a)) hκ) hLg) (hΛ n)
    have hΛ' := hΛ (n + edgeProduct C p a)
    calc (#T : ℝ) * (B * aux a * κK * Lg * (Λ n * Λ (n + edgeProduct C p a)))
        = (#T : ℝ) * Λ (n + edgeProduct C p a) * (B * aux a * κK * Lg * Λ n) := by ring
      _ ≤ (#(physicalLists P (J + 1) (n + edgeProduct C p a)) : ℝ) * Λ (n + edgeProduct C p a) *
          (B * aux a * κK * Lg * Λ n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hΛ') h0
      _ ≤ c ^ s * (B * aux a * κK * Lg * Λ n) :=
          mul_le_mul_of_nonneg_right hl h0
      _ = κK * Lg * B * c ^ s * Λ n * aux a := by ring
  have hB0 : 0 ≤ κK * Lg * B * c ^ s :=
    mul_nonneg (mul_nonneg (mul_nonneg hκ hLg) hBnn) (pow_nonneg hc0 _)
  unfold patternPairing
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_sum fun n _ => (norm_sum_le _ _).trans (sum_le_sum fun p _ =>
    (norm_sum_le _ _).trans (sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (sum_le_sum fun p' _ => hterm n p a p')))).trans ?_
  refine (sum_le_sum fun n _ => sum_le_sum fun p _ => sum_le_sum fun a _ =>
    hinner n p a _ (filter_subset _ _)).trans ?_
  have haux1 : ∑ a ∈ auxLabels P C, aux a = 1 := sum_labelMass (fun h => (hVpos h).ne') C
  simp_rw [← mul_sum, haux1]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  calc _
      ≤ ∑ _n ∈ S, c ^ s * (κK * Lg * B * c ^ s) := by
        refine sum_le_sum fun n _ => ?_
        calc _
            = (#(physicalLists P (J + 1) n) : ℝ) * Λ n * (κK * Lg * B * c ^ s) := by ring
          _ ≤ c ^ s * (κK * Lg * B * c ^ s) :=
              mul_le_mul_of_nonneg_right (hlist n) hB0
    _ = #S * κK * Lg * (β ^ (2 * (J + 1)) * c ^ 2) ^ s := by
        rw [sum_const, nsmul_eq_mul, hB, mul_pow, ← pow_mul, ← pow_mul]
        ring

end GraphBounds

end Erdos408.TwoSided
