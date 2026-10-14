import Erdos408.Extraction.TypeII.Box
import Erdos408.Extraction.TypeII.ProxySums
import Erdos408.Extraction.TypeII.Tuples

/-!
# The companion coefficient and its moments

For a family `v_k` of prime or proxy weights, the companion is
`β(n) = ∑_{m_1 ⋯ m_r = n} ∏ v_k(m_k)`. Since `v_k ≤ g_j` and `g_j` is completely
multiplicative, `β(n) ≤ g_j(n) r^{Ω(n)}`, and for every completely multiplicative `G ≥ 0`

  `∑_n β(n) G(n) ≤ ∏_k ∑_m v_k(m) G(m)`.

With `G(n) = 1/n` and `G(n) = g_j(n) r^{Ω(n)}/n` this gives the log density and, since
`β² ≤ β g_j r^Ω`, the mean square of the companion. The single-factor sums are bounded by
the Euler products of `Erdos408.Extraction.TypeII.ProxySums`, using `∏_{p ≤ Y}(1 - 1/p) γ L ≥ 1`
to absorb the proxy normalization.
-/

namespace Erdos408.TypeII

open Finset Real

/-- The companion `β(n) = ∑_{m_1 ⋯ m_r = n} ∏ v_k(m_k)` over `m ∈ S^r`. -/
noncomputable def tupleWeight (S : Finset ℕ) {r : ℕ} (v : Fin r → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Fintype.piFinset (fun _ : Fin r => S) with ∏ k, m k = n, ∏ k, v k (m k)

theorem tupleWeight_nonneg (S : Finset ℕ) {r : ℕ} {v : Fin r → ℕ → ℝ}
    (hv : ∀ k m, 0 ≤ v k m) (n : ℕ) : 0 ≤ tupleWeight S v n :=
  sum_nonneg fun _ _ => prod_nonneg fun _ _ => hv _ _

/-- `∑_{n ∈ T} β(n) G(n) ≤ ∏_k ∑_{m ∈ S} v_k(m) G(m)` for `G = cmul l ≥ 0`. -/
theorem sum_tupleWeight_mul_le (S : Finset ℕ) {r : ℕ} {v : Fin r → ℕ → ℝ}
    (hv : ∀ k m, 0 ≤ v k m) {l : ℕ → ℝ} (hl : ∀ p, p.Prime → 0 ≤ l p) (T : Finset ℕ) :
    ∑ n ∈ T, tupleWeight S v n * cmul l n ≤ ∏ k, ∑ m ∈ S, v k m * cmul l m := by
  rw [prod_univ_sum]
  unfold tupleWeight
  simp only [sum_mul]
  have h : ∑ n ∈ T, ∑ m ∈ Fintype.piFinset (fun _ : Fin r => S) with ∏ k, m k = n,
      (∏ k, v k (m k)) * cmul l n =
      ∑ m ∈ (Fintype.piFinset (fun _ : Fin r => S)).filter (fun m => ∏ k, m k ∈ T),
        ∏ k, v k (m k) * cmul l (m k) := by
    rw [← sum_fiberwise_of_maps_to (s := (Fintype.piFinset (fun _ : Fin r => S)).filter
      (fun m => ∏ k, m k ∈ T)) (t := T) (g := fun m => ∏ k, m k)
      (fun m hm => (mem_filter.1 hm).2)]
    refine sum_congr rfl fun n hn => ?_
    rw [filter_filter]
    refine (sum_congr ?_ fun m hm => ?_)
    · ext m; simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ hn, h2⟩
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rw [(mem_filter.1 hm).2.2.symm, map_prod, prod_mul_distrib]
  rw [h]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m _ _ =>
    prod_nonneg fun k _ => mul_nonneg (hv _ _) (cmul_nonneg hl _)

/-- `β(n) ≤ g_j(n) r^{Ω(n)}` when every `v_k ≤ g_j` on positive integers. -/
theorem tupleWeight_le {x : ℝ} {j : ℕ} {S : Finset ℕ} (hS : ∀ m ∈ S, 1 ≤ m) {r : ℕ}
    {v : Fin r → ℕ → ℝ} (hv : ∀ k m, 0 ≤ v k m) (hvg : ∀ k m, 1 ≤ m → v k m ≤ dampedWeight x j m)
    {n : ℕ} (hn : n ≠ 0) :
    tupleWeight S v n ≤ dampedWeight x j n * cmul (fun _ => (r : ℝ)) n := by
  unfold tupleWeight
  have hsub : (Fintype.piFinset (fun _ : Fin r => S)).filter (fun m => ∏ k, m k = n) ⊆
      factorizationTuples r n := by
    intro m hm
    obtain ⟨hmS, hprod⟩ := mem_filter.1 hm
    refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun k => Nat.mem_divisors.2
      ⟨hprod ▸ Finset.dvd_prod_of_mem _ (mem_univ k), hn⟩, hprod⟩
  have hterm : ∀ m ∈ (Fintype.piFinset (fun _ : Fin r => S)).filter (fun m => ∏ k, m k = n),
      ∏ k, v k (m k) ≤ dampedWeight x j n := by
    intro m hm
    obtain ⟨hmS, hprod⟩ := mem_filter.1 hm
    have hpos : ∀ k, 1 ≤ m k := fun k => hS _ (Fintype.mem_piFinset.1 hmS k)
    calc ∏ k, v k (m k) ≤ ∏ k, dampedWeight x j (m k) :=
          prod_le_prod₀ (fun k _ => hv _ _) fun k _ => hvg k _ (hpos k)
      _ = dampedWeight x j n := by
          rw [← hprod, dampedWeight_eq_cmul x j (prod_ne_zero_iff.2 fun k _ => by
            have := hpos k; omega), map_prod]
          exact prod_congr rfl fun k _ => dampedWeight_eq_cmul x j (n := m k) (by
            have := hpos k; omega)
  calc ∑ m ∈ (Fintype.piFinset (fun _ : Fin r => S)).filter (fun m => ∏ k, m k = n),
        ∏ k, v k (m k)
      ≤ ∑ _m ∈ (Fintype.piFinset (fun _ : Fin r => S)).filter (fun m => ∏ k, m k = n),
          dampedWeight x j n := sum_le_sum hterm
    _ = dampedWeight x j n *
          ((Fintype.piFinset (fun _ : Fin r => S)).filter (fun m => ∏ k, m k = n)).card := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ dampedWeight x j n * (factorizationTuples r n).card := by
        have := dampedWeight_nonneg x j n
        gcongr
    _ ≤ dampedWeight x j n * cmul (fun _ => (r : ℝ)) n :=
        mul_le_mul_of_nonneg_left (card_factorizationTuples_le r hn)
          (dampedWeight_nonneg x j n)

/-- The companion vanishes unless `n` is a product of points where the weights are nonzero. -/
theorem exists_of_tupleWeight_ne_zero (S : Finset ℕ) {r : ℕ} {v : Fin r → ℕ → ℝ} {n : ℕ}
    (h : tupleWeight S v n ≠ 0) :
    ∃ m : Fin r → ℕ, (∀ k, m k ∈ S) ∧ ∏ k, m k = n ∧ ∀ k, v k (m k) ≠ 0 := by
  unfold tupleWeight at h
  obtain ⟨m, hm, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hmS, hprod⟩ := mem_filter.1 hm
  exact ⟨m, Fintype.mem_piFinset.1 hmS, hprod, fun k hk => hne (prod_eq_zero (mem_univ k) hk)⟩

/-! ### Single-factor sums -/

/-- The prime weight `[m prime, m > x^γ]`. -/
noncomputable def primeWeight (x γ : ℝ) (m : ℕ) : ℝ :=
  if m.Prime ∧ x ^ γ < m then 1 else 0

theorem primeWeight_nonneg (x γ : ℝ) (m : ℕ) : 0 ≤ primeWeight x γ m := by
  unfold primeWeight; split_ifs <;> norm_num

theorem primeWeight_le_one (x γ : ℝ) (m : ℕ) : primeWeight x γ m ≤ 1 := by
  unfold primeWeight; split_ifs <;> norm_num

section Factor

variable {x γ : ℝ} {j : ℕ}

/-- The prime weight is at most `g_j` once `Y ≤ x^γ`. -/
theorem primeWeight_le_dampedWeight (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x)
    (hYγ : proxyCutoff x ≤ x ^ γ) (m : ℕ) : primeWeight x γ m ≤ dampedWeight x j m := by
  unfold primeWeight
  split_ifs with h
  · rw [dampedWeight_prime hL hYP h.1 (lt_of_le_of_lt hYγ h.2)]
  · exact dampedWeight_nonneg x j m

/-- The unstripped proxy is at most `g_j` once `∏_{p ≤ Y} (1 - 1/p) γ L ≥ 1`. -/
theorem unstrippedProxy_le_dampedWeight (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ)
    (hj : 1 ≤ j)
    (hY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))
    (m : ℕ) : unstrippedProxy x γ j m ≤ dampedWeight x j m := by
  obtain ⟨-, h1⟩ := unstrippedProxy_le hx hL hγ hj m
  refine h1.trans ?_
  obtain ⟨-, hPiD⟩ := prod_le_dampedDensity hL hj
  have hγL : 0 < γ * Real.log x := by positivity
  have hg := dampedWeight_nonneg x j m
  have hD1 : 1 ≤ dampedDensity x j * (γ * Real.log x) :=
    hY.trans (mul_le_mul_of_nonneg_right hPiD hγL.le)
  have hite : (if x ^ γ < m then dampedWeight x j m else 0) ≤ dampedWeight x j m := by
    split_ifs <;> linarith
  calc (if x ^ γ < m then dampedWeight x j m else 0) / (dampedDensity x j * (γ * Real.log x))
      ≤ (if x ^ γ < m then dampedWeight x j m else 0) :=
        div_le_self (by split_ifs <;> linarith) hD1
    _ ≤ _ := hite

/-- `∑_{m ≤ N} [m prime, m > x^γ] ρ/m = ρ ∑_{x^γ < p ≤ N} 1/p`. -/
theorem sum_primeWeight_le (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x)
    (hYγ : proxyCutoff x ≤ x ^ γ) (N : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ m ∈ Icc 1 N, primeWeight x γ m * cmul (fun p => proxyLoc x j p * ρ / p) m ≤
      ρ * ∑ p ∈ primesIoc (x ^ γ) N, (1 : ℝ) / p := by
  rw [mul_sum]
  have hsub : (Icc 1 N).filter (fun m : ℕ => m.Prime ∧ x ^ γ < m) ⊆ primesIoc (x ^ γ) N := by
    intro m hm
    obtain ⟨hmI, hp, hlt⟩ := mem_filter.1 hm
    exact mem_primesIoc.2 ⟨hp, hlt, by exact_mod_cast (mem_Icc.1 hmI).2⟩
  calc ∑ m ∈ Icc 1 N, primeWeight x γ m * cmul (fun p => proxyLoc x j p * ρ / p) m
      = ∑ m ∈ (Icc 1 N).filter (fun m : ℕ => m.Prime ∧ x ^ γ < m), ρ * ((1 : ℝ) / m) := by
        rw [sum_filter]
        refine sum_congr rfl fun m _ => ?_
        unfold primeWeight
        split_ifs with h
        · rw [one_mul, cmul_prime _ h.1,
            proxyLoc_of_gt hL hYP (lt_of_le_of_lt hYγ h.2)]
          ring
        · rw [zero_mul]
    _ ≤ ∑ p ∈ primesIoc (x ^ γ) N, ρ * ((1 : ℝ) / p) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

/-- `∑_{m ≤ N} [m prime, m > x^γ] / m = ∑_{x^γ < p ≤ N} 1/p`. -/
theorem sum_primeWeight_div_le (N : ℕ) :
    ∑ m ∈ Icc 1 N, primeWeight x γ m * cmul (fun p => (p : ℝ)⁻¹) m ≤
      ∑ p ∈ primesIoc (x ^ γ) N, (1 : ℝ) / p := by
  have hsub : (Icc 1 N).filter (fun m : ℕ => m.Prime ∧ x ^ γ < m) ⊆ primesIoc (x ^ γ) N := by
    intro m hm
    obtain ⟨hmI, hp, hlt⟩ := mem_filter.1 hm
    exact mem_primesIoc.2 ⟨hp, hlt, by exact_mod_cast (mem_Icc.1 hmI).2⟩
  calc ∑ m ∈ Icc 1 N, primeWeight x γ m * cmul (fun p => (p : ℝ)⁻¹) m
      = ∑ m ∈ (Icc 1 N).filter (fun m : ℕ => m.Prime ∧ x ^ γ < m), (1 : ℝ) / m := by
        rw [sum_filter]
        refine sum_congr rfl fun m _ => ?_
        unfold primeWeight
        split_ifs with h
        · rw [one_mul, cmul_prime _ h.1, one_div]
        · rw [zero_mul]
    _ ≤ ∑ p ∈ primesIoc (x ^ γ) N, (1 : ℝ) / p :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

/-- `∑_{m ≤ N} a_j^0(m)/m ≤ ∏_{Y < p ≤ N} (1 - 1/p)⁻¹`. -/
theorem sum_unstrippedProxy_div_le (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ)
    (hj : 1 ≤ j)
    (hY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {N : ℕ}
    (hYN : proxyCutoff x ≤ N) :
    ∑ m ∈ Icc 1 N, unstrippedProxy x γ j m * cmul (fun p => (p : ℝ)⁻¹) m ≤
      ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ := by
  obtain ⟨hPi, hPiD⟩ := prod_le_dampedDensity hL hj
  have hD := dampedDensity_pos hL hj
  have hγL : 0 < γ * Real.log x := by positivity
  set ν := (dampedDensity x j * (γ * Real.log x))⁻¹ with hν
  have hterm : ∀ m ∈ Icc 1 N, unstrippedProxy x γ j m * cmul (fun p => (p : ℝ)⁻¹) m ≤
      ν * (dampedWeight x j m / m) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    rw [cmul_inv hm0]
    obtain ⟨h0, h1⟩ := unstrippedProxy_le hx hL hγ hj m
    have hite : (if x ^ γ < m then dampedWeight x j m else 0) ≤ dampedWeight x j m := by
      have := dampedWeight_nonneg x j m; split_ifs <;> linarith
    calc unstrippedProxy x γ j m * (m : ℝ)⁻¹
        ≤ dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) * (m : ℝ)⁻¹ := by
          gcongr
          exact h1.trans (div_le_div_of_nonneg_right hite (by positivity))
      _ = ν * (dampedWeight x j m / m) := by rw [hν]; ring
  have hsum := sum_dampedWeight_div_le hL hYP hYN hj
  have hPP : 0 ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ :=
    prod_nonneg fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesIoc.1 hp).1.two_le
      rw [inv_nonneg, sub_nonneg, div_le_one (by linarith)]; linarith
  calc ∑ m ∈ Icc 1 N, unstrippedProxy x γ j m * cmul (fun p => (p : ℝ)⁻¹) m
      ≤ ∑ m ∈ Icc 1 N, ν * (dampedWeight x j m / m) := sum_le_sum hterm
    _ = ν * ∑ m ∈ Icc 1 N, dampedWeight x j m / m := (mul_sum _ _ _).symm
    _ ≤ ν * ((∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹) *
          ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹) /
          ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)) := by
        have hPc : 0 < ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
          have := hD; unfold dampedDensity at this
          exact pos_of_mul_pos_right this hPi.le
        have key : ∀ a b c d : ℝ, b ≠ 0 → (a * b * c)⁻¹ * (b * d) = d / (a * c) := by
          intro a b c d hb
          rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
          field_simp
        rw [hν, dampedDensity]
        exact key _ _ _ _ hPc.ne'
    _ ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - (1 : ℝ) / p)⁻¹ := div_le_self hPP hY

/-- `∑_{m ≤ N} a_j^0(m) g_j(m) r^{Ω(m)}/m ≤ ∏_{Y < p ≤ N} (1 - r/p)⁻¹` for `r ≤ j`. -/
theorem sum_unstrippedProxy_sq_le (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ)
    (hj : 1 ≤ j)
    (hY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x) {N : ℕ}
    (hYN : proxyCutoff x ≤ N) {r : ℝ} (hr : 0 ≤ r) (hrj : r ≤ j) (hrY : r < proxyCutoff x) :
    ∑ m ∈ Icc 1 N, unstrippedProxy x γ j m * cmul (fun p => proxyLoc x j p * r / p) m ≤
      ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - r / p)⁻¹ := by
  obtain ⟨hPi, hPiD⟩ := prod_le_dampedDensity hL hj
  have hD := dampedDensity_pos hL hj
  have hγL : 0 < γ * Real.log x := by positivity
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set ν := (dampedDensity x j * (γ * Real.log x))⁻¹ with hν
  have hterm : ∀ m ∈ Icc 1 N, unstrippedProxy x γ j m * cmul (fun p => proxyLoc x j p * r / p) m ≤
      ν * (dampedWeight x j m ^ 2 * cmul (fun _ => r) m / m) := by
    intro m hm
    have hm0 : m ≠ 0 := by have := (mem_Icc.1 hm).1; omega
    have hc : cmul (fun p => proxyLoc x j p * r / p) m =
        dampedWeight x j m * cmul (fun _ => r) m / m := by
      rw [← cmul_div hm0, cmul_mul_loc, dampedWeight_eq_cmul x j hm0]
    rw [hc]
    obtain ⟨h0, h1⟩ := unstrippedProxy_le hx hL hγ hj m
    have hite : (if x ^ γ < m then dampedWeight x j m else 0) ≤ dampedWeight x j m := by
      have := dampedWeight_nonneg x j m; split_ifs <;> linarith
    have hnn : 0 ≤ dampedWeight x j m * cmul (fun _ => r) m / m :=
      div_nonneg (mul_nonneg (dampedWeight_nonneg x j m) (cmul_nonneg (fun _ _ => hr) m))
        (Nat.cast_nonneg m)
    calc unstrippedProxy x γ j m * (dampedWeight x j m * cmul (fun _ => r) m / m)
        ≤ dampedWeight x j m / (dampedDensity x j * (γ * Real.log x)) *
            (dampedWeight x j m * cmul (fun _ => r) m / m) := by
          gcongr
          exact h1.trans (div_le_div_of_nonneg_right hite (by positivity))
      _ = ν * (dampedWeight x j m ^ 2 * cmul (fun _ => r) m / m) := by rw [hν]; ring
  have hsum := sum_dampedWeight_sq_div_le hL hYP hYN hj hr hrj hrY
  have hPP : 0 ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - r / p)⁻¹ :=
    prod_nonneg fun p hp => by
      have := (mem_primesIoc.1 hp).2.1
      rw [inv_nonneg, sub_nonneg, div_le_one (by linarith)]; linarith
  -- `Π_P(r t²) ≤ Π_P(t)`
  have hPc : ∏ p ∈ candidatePrimes x, (1 - r * ((j : ℝ)⁻¹) ^ 2 / p)⁻¹ ≤
      ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
    refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_candidatePrimes hL hp).1.two_le
      have : r * ((j : ℝ)⁻¹) ^ 2 ≤ 1 := by
        rw [sq, ← mul_assoc]
        have : r * (j : ℝ)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one (by linarith)]; exact hrj
        have := inv_le_one_of_one_le₀ hj'
        nlinarith [inv_nonneg.2 (show (0 : ℝ) ≤ j by linarith)]
      rw [inv_nonneg, sub_nonneg, div_le_one (by linarith)]; linarith
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_candidatePrimes hL hp).1.two_le
      have ht : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj'
      have ht0 : 0 ≤ (j : ℝ)⁻¹ := by positivity
      have hrt : r * ((j : ℝ)⁻¹) ^ 2 ≤ (j : ℝ)⁻¹ := by
        rw [sq, ← mul_assoc]
        have : r * (j : ℝ)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one (by linarith)]; exact hrj
        nlinarith
      have h1 : 0 < 1 - (j : ℝ)⁻¹ / p := by
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      apply inv_anti₀ h1
      have : r * ((j : ℝ)⁻¹) ^ 2 / p ≤ (j : ℝ)⁻¹ / p :=
        div_le_div_of_nonneg_right hrt (by linarith)
      linarith
  have hPcpos : 0 < ∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹ := by
    have := hD; unfold dampedDensity at this
    exact pos_of_mul_pos_right this hPi.le
  have hν0 : 0 ≤ ν := by positivity
  calc ∑ m ∈ Icc 1 N, unstrippedProxy x γ j m * cmul (fun p => proxyLoc x j p * r / p) m
      ≤ ∑ m ∈ Icc 1 N, ν * (dampedWeight x j m ^ 2 * cmul (fun _ => r) m / m) :=
        sum_le_sum hterm
    _ = ν * ∑ m ∈ Icc 1 N, dampedWeight x j m ^ 2 * cmul (fun _ => r) m / m :=
        (mul_sum _ _ _).symm
    _ ≤ ν * ((∏ p ∈ candidatePrimes x, (1 - r * ((j : ℝ)⁻¹) ^ 2 / p)⁻¹) *
          ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - r / p)⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hν0
    _ ≤ ν * ((∏ p ∈ candidatePrimes x, (1 - (j : ℝ)⁻¹ / p)⁻¹) *
          ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - r / p)⁻¹) := by gcongr
    _ = (∏ p ∈ primesIoc (proxyCutoff x) N, (1 - r / p)⁻¹) /
          ((∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x)) := by
        have key : ∀ a b c d : ℝ, b ≠ 0 → (a * b * c)⁻¹ * (b * d) = d / (a * c) := by
          intro a b c d hb
          rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
          field_simp
        rw [hν, dampedDensity]
        exact key _ _ _ _ hPcpos.ne'
    _ ≤ ∏ p ∈ primesIoc (proxyCutoff x) N, (1 - r / p)⁻¹ := div_le_self hPP hY

end Factor

end Erdos408.TypeII
