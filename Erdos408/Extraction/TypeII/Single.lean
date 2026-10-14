module

public import Erdos408.Extraction.TypeII.Taylor

/-!
# One telescoping step of E4

The step replaces one prime factor `m` by the proxy, with the other `r = j - 1` factors (each
a prime above `x^γ` or a proxy) aggregated into the companion `β`:

  `∑_{m, n ≤ M} Ψ(m n) α(m) β(n)`,  `Ψ(h) = Φ((h - 1)/x) P(h - 1)(f_𝔟 - C_𝔟)(h - 1)`,

with `α = [prime, > x^γ] - a_j^0`. Clip `β` at `L³` (the tail is controlled by the mean
square `∑ β²/n`), cut `(m, n)` into the cells of the grid `λ_a = x^γ (1 + δ)^a`, freeze the
cutoff on each box, and bound each box by the Type II estimate.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset Real

section Weights

variable {x γ : ℝ} {j : ℕ}

/-- The facts used about one factor weight `v ∈ {a_j^0, [prime, > x^γ]}`. -/
structure FactorWeight (x γ : ℝ) (j : ℕ) (w : ℕ → ℝ) : Prop where
  nonneg : ∀ m, 0 ≤ w m
  le_one : ∀ m, w m ≤ 1
  le_damped : ∀ m, 1 ≤ m → w m ≤ dampedWeight x j m
  support : ∀ m, w m ≠ 0 →
    x ^ γ < m ∧ ∀ p ∈ m.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p

/-- The prime weight is a factor weight. -/
theorem factorWeight_prime (hL : 1 ≤ Real.log x)
    (hYP : Real.exp (Real.log x ^ (45 / 100 : ℝ)) < proxyCutoff x)
    (hYγ : proxyCutoff x ≤ x ^ γ)
    (hexpγ : Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ x ^ γ) :
    FactorWeight x γ j (primeWeight x γ) where
  nonneg := primeWeight_nonneg x γ
  le_one := primeWeight_le_one x γ
  le_damped m _ := primeWeight_le_dampedWeight hL hYP hYγ m
  support m h := by
    unfold primeWeight at h
    split_ifs at h with hm
    · refine ⟨hm.2, fun p hp => ?_⟩
      rw [Nat.Prime.primeFactors hm.1, mem_singleton] at hp
      subst hp
      exact hexpγ.trans hm.2.le
    · exact absurd rfl h

/-- The unstripped proxy is a factor weight. -/
theorem factorWeight_unstripped (hx : 1 < x) (hL : 1 ≤ Real.log x) (hγ : 0 < γ) (hj : 1 ≤ j)
    (hY : 1 ≤ (∏ p ∈ primesIcc 2 (proxyCutoff x), (1 - (1 : ℝ) / p)) * (γ * Real.log x))
    (hexpY : Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ proxyCutoff x) :
    FactorWeight x γ j (unstrippedProxy x γ j) where
  nonneg m := (unstrippedProxy_le_one hx hL hγ hj hY m).1
  le_one m := (unstrippedProxy_le_one hx hL hγ hj hY m).2
  le_damped m _ := unstrippedProxy_le_dampedWeight hx hL hγ hj hY m
  support m h := by
    unfold unstrippedProxy at h
    split_ifs at h with hxm
    · refine ⟨hxm, fun p hp => ?_⟩
      have hg : dampedWeight x j m ≠ 0 := fun h0 => h (by rw [h0, zero_div])
      by_cases hpP : p ∈ candidatePrimes x
      · exact (mem_candidatePrimes hL hpP).2.1
      · unfold dampedWeight at hg
        split_ifs at hg with hrough
        · have hpm : p ∈ (candidateStrip x m).primeFactors := by
            rw [candidateStrip, primeFactors_stripPrimes, mem_filter]
            exact ⟨hp, hpP⟩
          exact hexpY.trans (hrough p hpm).le
        · exact absurd rfl hg
    · exact absurd rfl h

/-- Facts about the companion of factor weights. -/
theorem tupleWeight_support {r : ℕ} (hr : 1 ≤ r) {V : Fin r → ℕ → ℝ}
    (hV : ∀ k, FactorWeight x γ j (V k)) {N n : ℕ}
    (h : tupleWeight (Icc 1 N) V n ≠ 0) :
    x ^ γ < n ∧ ∀ p ∈ n.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p := by
  obtain ⟨m, hmS, hprod, hne⟩ := exists_of_tupleWeight_ne_zero _ h
  have hpos : ∀ k, 1 ≤ m k := fun k => (mem_Icc.1 (hmS k)).1
  have hk := (hV ⟨0, hr⟩).support _ (hne ⟨0, hr⟩)
  refine ⟨?_, fun p hp => ?_⟩
  · rw [← hprod]
    calc x ^ γ < m ⟨0, hr⟩ := hk.1
      _ ≤ ((∏ k, m k : ℕ) : ℝ) := by
          exact_mod_cast Finset.single_le_prod (fun k _ => hpos k) (mem_univ _)
  · rw [← hprod] at hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.1 hp
    obtain ⟨k, -, hpk⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hpd
    have hk0 : m k ≠ 0 := by have := hpos k; omega
    exact ((hV k).support _ (hne k)).2 p (Nat.mem_primeFactors.2 ⟨hpp, hpk, hk0⟩)

end Weights

/-! ### The summand `Ψ` -/

/-- The summand `Ψ(h) = Φ((h - 1)/x) E(h - 1)`. -/
noncomputable def cutPsi (Φ : ℝ → ℝ) (E : ℕ → ℝ) (x : ℝ) (h : ℕ) : ℝ :=
  Φ (((h : ℝ) - 1) / x) * E (h - 1)

section Psi

variable {κ CΦ x : ℝ} {M : ℕ → ℝ} {Φ : ℝ → ℝ} {E : ℕ → ℝ}

theorem cutPsi_eq_zero (hΦ : IsCutoff κ CΦ M x Φ) (hx : 0 < x) (hκ : 0 < κ) {h : ℕ}
    (hh : ⌊κ * x + 1⌋₊ < h) : cutPsi Φ E x h = 0 := by
  unfold cutPsi
  by_contra hne
  have hΦ0 : Φ (((h : ℝ) - 1) / x) ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  have h1 := (hΦ.2.2.1 _ hΦ0).2
  rw [div_le_iff₀ hx] at h1
  have h2 : κ * x + 1 < h := (Nat.floor_lt (by positivity)).1 hh
  linarith

/-- `|Ψ(h)| ≤ M₀ S_E` when `|E| ≤ S_E` on `[1, x²]`, `κ x ≤ x²` and `κ ≤ x`. -/
theorem abs_cutPsi_le (hΦ : IsCutoff κ CΦ M x Φ) (hx : 0 < x) (hκ : 0 < κ)
    (hκx : κ * x ≤ x ^ 2) (hxκ : κ ≤ x) {SE : ℝ} (hSE0 : 0 ≤ SE)
    (hSE : ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ x ^ 2 → |E h| ≤ SE) (h : ℕ) :
    |cutPsi Φ E x h| ≤ M 0 * SE := by
  unfold cutPsi
  have hM0 : ∀ y, |Φ y| ≤ M 0 := fun y => by
    have := hΦ.2.2.2 0 y
    simpa using this
  have hM00 : 0 ≤ M 0 := (abs_nonneg _).trans (hM0 0)
  by_cases hΦ0 : Φ (((h : ℝ) - 1) / x) = 0
  · rw [hΦ0, zero_mul, abs_zero]
    positivity
  obtain ⟨h1, h2⟩ := hΦ.2.2.1 _ hΦ0
  rw [le_div_iff₀ hx] at h1
  rw [div_le_iff₀ hx] at h2
  have hx1 : 1 ≤ κ⁻¹ * x := by
    rw [← div_eq_inv_mul, le_div_iff₀ hκ]; linarith
  have hh1 : (1 : ℝ) ≤ (h : ℝ) - 1 := by linarith
  have hh : 2 ≤ h := by
    have : (2 : ℝ) ≤ h := by linarith
    exact_mod_cast this
  have hcast : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [abs_mul]
  refine mul_le_mul (hM0 _) (hSE _ (by omega) ?_) (abs_nonneg _) hM00
  rw [hcast]
  linarith

end Psi



/-! ### One box -/

/-- One box: the frozen main term plus the cutoff variation. -/
theorem abs_box_term_le {q cw : ℝ} {K : ℕ} {CN c Ch Cj κ CΦ C₂ x 𝒩 SE : ℝ} {M : ℕ → ℝ}
    {Φ : ℝ → ℝ} {k : ℕ} {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B 𝒩) (hbox : BoxBound q K c Ch Cj κ C₂ x)
    (hC₂ : 0 ≤ C₂) (hΦ : IsCutoff κ CΦ M x Φ) (hκ : 1 < κ) (hx : 1 < x)
    (hxγ : 1 ≤ x ^ presieveExponent c Ch x) (hsq : 4 * (κ * x + 1) ≤ x ^ 2)
    (hSE0 : 0 ≤ SE)
    (hSE : ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ x ^ 2 → |endpoint q cw K CN x u v B h| ≤ SE)
    {lam mu δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlam : x ^ presieveExponent c Ch x ≤ lam)
    (hmu : x ^ presieveExponent c Ch x ≤ mu) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : (j : ℝ) ≤ Cj * logLogLog x + 1)
    (hα : ∀ m, |primeProxyDiff x (presieveExponent c Ch x) j m| ≤ 1) (β βc : ℕ → ℝ)
    (hβc : ∀ n, βc n ≠ 0 → (∀ p ∈ n.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p) ∧
      0 ≤ βc n ∧ βc n ≤ Real.log x ^ (3 : ℝ))
    (hββ : ∀ n, 0 ≤ βc n ∧ βc n ≤ β n) :
    |∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
        cutPsi Φ (endpoint q cw K CN x u v B) x (m * n) *
          primeProxyDiff x (presieveExponent c Ch x) j m * βc n| ≤
      M 0 * ((clusterSets K (inertPerCluster K CN x)).card * 𝒩 *
        (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ))) +
      ∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
        (if (m * n : ℝ) ≤ 4 * (κ * x + 1) then
          M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) else 0) * SE * β n := by
  set γ := presieveExponent c Ch x
  set E := endpoint q cw K CN x u v B
  set α := primeProxyDiff x γ j
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hlam1 : 1 ≤ lam := hxγ.trans hlam
  have hmu1 : 1 ≤ mu := hxγ.trans hmu
  have hM0 : ∀ y, |Φ y| ≤ M 0 := fun y => by simpa using hΦ.2.2.2 0 y
  have hM00 : 0 ≤ M 0 := (abs_nonneg _).trans (hM0 0)
  have hLr : 0 ≤ Real.log x ^ (-12 : ℝ) := Real.rpow_nonneg (Real.log_pos hx).le _
  -- split off the frozen cutoff
  have hsplit : ∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
      cutPsi Φ E x (m * n) * α m * βc n =
      Φ (lam * mu / x) * ∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
        E (m * n - 1) * α m * βc n +
      ∑ m ∈ Ioc ⌊lam⌋₊ ⌊lam * (1 + δ)⌋₊, ∑ n ∈ Ioc ⌊mu⌋₊ ⌊mu * (1 + δ)⌋₊,
        (Φ ((((m * n : ℕ) : ℝ) - 1) / x) - Φ (lam * mu / x)) * E (m * n - 1) * α m * βc n := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    unfold cutPsi
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the frozen main term
    rw [abs_mul]
    by_cases hz : Φ (lam * mu / x) = 0
    · rw [hz, abs_zero, zero_mul]
      have : (0 : ℝ) ≤ (clusterSets K (inertPerCluster K CN x)).card * 𝒩 *
          (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ)) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hE.norm_pos.le)
          (mul_nonneg (mul_nonneg hC₂ (by positivity)) hLr)
      exact mul_nonneg hM00 this
    obtain ⟨h1, h2⟩ := hΦ.2.2.1 _ hz
    rw [le_div_iff₀ hx0] at h1
    rw [div_le_iff₀ hx0] at h2
    have h1' : x / κ ≤ lam * mu := by
      have : x / κ = κ⁻¹ * x := by ring
      rw [this]; exact h1
    have hsq' : 4 * (lam * mu) ≤ x ^ 2 := by linarith
    have hmain := abs_box_main_le hE hbox hδ0 hδ1 hlam hmu hxγ h1' h2 hsq' hj1 hj2 βc hβc
    refine mul_le_mul (hM0 _) (hmain.trans ?_) (abs_nonneg _) hM00
    have := hE.norm_pos
    gcongr
  · -- the cutoff variation
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    obtain ⟨hm1, hm2⟩ := mem_Ioc.1 hm
    obtain ⟨hn1, hn2⟩ := mem_Ioc.1 hn
    have hlm : lam < m := (Nat.floor_lt (by linarith)).1 hm1
    have hmn : mu < n := (Nat.floor_lt (by linarith)).1 hn1
    have hm2' : (m : ℝ) ≤ lam * (1 + δ) := (Nat.le_floor_iff' (by
      have : (0 : ℝ) < m := by linarith
      exact_mod_cast this.ne')).1 hm2
    have hn2' : (n : ℝ) ≤ mu * (1 + δ) := (Nat.le_floor_iff' (by
      have : (0 : ℝ) < n := by linarith
      exact_mod_cast this.ne')).1 hn2
    have hfr := abs_cutoff_freeze_le hΦ hx0 hκ (by linarith) (by linarith) hδ0 hδ1 hlm hm2' hmn
      hn2'
    have hβ0 := (hββ n).1
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hβ0]
    split_ifs at hfr ⊢ with hX
    · -- the box point has `mn - 1 ∈ [1, x²]`
      have hm2 : 2 ≤ m := by
        have : (1 : ℝ) < m := by linarith
        exact_mod_cast this
      have hn2 : 2 ≤ n := by
        have : (1 : ℝ) < n := by linarith
        exact_mod_cast this
      have hmn4 : 4 ≤ m * n := Nat.mul_le_mul hm2 hn2
      have hEb : |E (m * n - 1)| ≤ SE := by
        refine hSE _ (by omega) ?_
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith
      have hτ : 0 ≤ M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) :=
        (abs_nonneg _).trans hfr
      calc |Φ ((((m * n : ℕ) : ℝ) - 1) / x) - Φ (lam * mu / x)| * |E (m * n - 1)| * |α m| *
            βc n ≤ (M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x)) * SE * 1 *
              β n := by
            gcongr
            · exact hα m
            · exact (hββ n).2
        _ = _ := by ring
    · have : |Φ ((((m * n : ℕ) : ℝ) - 1) / x) - Φ (lam * mu / x)| = 0 :=
        le_antisymm hfr (abs_nonneg _)
      rw [this]
      simp

/-! ### Summing over the boxes -/

/-- The cutoff variations of all boxes, regrouped: at most `τ S_E X ∑_n β(n)/n`. -/
theorem sum_cells_variation_le (A : ℕ) (lam : ℕ → ℝ) (hmono : ∀ a, lam a ≤ lam (a + 1))
    {τ SE X : ℝ} (hτ : 0 ≤ τ) (hSE : 0 ≤ SE) (hX : 0 ≤ X) (β : ℕ → ℝ)
    (hβ : ∀ n, 0 ≤ β n) :
    ∑ a ∈ range A, ∑ b ∈ range A, ∑ m ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊,
        ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊, (if (m * n : ℝ) ≤ X then τ else 0) * SE * β n ≤
      τ * SE * X * ∑ n ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊, β n / n := by
  have hswap : ∑ a ∈ range A, ∑ b ∈ range A, ∑ m ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊,
        ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊, (if (m * n : ℝ) ≤ X then τ else 0) * SE * β n =
      ∑ m ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊, ∑ n ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊,
        (if (m * n : ℝ) ≤ X then τ else 0) * SE * β n := by
    rw [← sum_cells_eq _ lam hmono A]
    refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun m _ => ?_
    exact sum_cells_eq _ lam hmono A
  rw [hswap, sum_comm, mul_sum]
  refine sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := by have := (mem_Ioc.1 hn).1; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hcount : ∑ m ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊, (if (m * n : ℝ) ≤ X then (1 : ℝ) else 0) ≤ X / n := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
    have hsub : (Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊).filter (fun m : ℕ => (m * n : ℝ) ≤ X) ⊆
        Icc 1 ⌊X / n⌋₊ := by
      intro m hm
      obtain ⟨hmI, hmX⟩ := mem_filter.1 hm
      have hm1 : 1 ≤ m := by have := (mem_Ioc.1 hmI).1; omega
      refine mem_Icc.2 ⟨hm1, Nat.le_floor ?_⟩
      rw [le_div_iff₀ hn0]; exact hmX
    calc (((Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊).filter (fun m : ℕ => (m * n : ℝ) ≤ X)).card : ℝ)
        ≤ (Icc 1 ⌊X / n⌋₊).card := by exact_mod_cast card_le_card hsub
      _ = ⌊X / n⌋₊ := by simp
      _ ≤ X / n := Nat.floor_le (by positivity)
  calc ∑ m ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊, (if (m * n : ℝ) ≤ X then τ else 0) * SE * β n
      = τ * SE * β n * ∑ m ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊, (if (m * n : ℝ) ≤ X then (1 : ℝ) else 0) := by
        rw [mul_sum]
        exact sum_congr rfl fun m _ => by split_ifs <;> ring
    _ ≤ τ * SE * β n * (X / n) := mul_le_mul_of_nonneg_left hcount (by
        have := hβ n; positivity)
    _ = τ * SE * X * (β n / n) := by ring

/-- The grid `λ_a = x^γ (1 + δ)^a`. -/
noncomputable def gridPt (x γ δ : ℝ) (a : ℕ) : ℝ := x ^ γ * (1 + δ) ^ a

theorem gridPt_succ (x γ δ : ℝ) (a : ℕ) : gridPt x γ δ (a + 1) = gridPt x γ δ a * (1 + δ) := by
  unfold gridPt; ring

theorem gridPt_mono {x γ δ : ℝ} (hx : 0 ≤ x ^ γ) (hδ : 0 ≤ δ) (a : ℕ) :
    gridPt x γ δ a ≤ gridPt x γ δ (a + 1) := by
  rw [gridPt_succ]
  have : 0 ≤ gridPt x γ δ a := by unfold gridPt; positivity
  nlinarith

/-- The clipped part of a telescoping step: the boxes of the grid. -/
theorem abs_clipped_le {q cw : ℝ} {K : ℕ} {CN c Ch Cj κ CΦ C₂ x 𝒩 SE δ : ℝ}
    {M : ℕ → ℝ} {Φ : ℝ → ℝ} {k : ℕ} {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B 𝒩) (hbox : BoxBound q K c Ch Cj κ C₂ x)
    (hC₂ : 0 ≤ C₂) (hΦ : IsCutoff κ CΦ M x Φ) (hκ : 1 < κ) (hx : 1 < x)
    (hxγ : 1 ≤ x ^ presieveExponent c Ch x) (hsq : 4 * (κ * x + 1) ≤ x ^ 2)
    (hSE0 : 0 ≤ SE)
    (hSE : ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ x ^ 2 → |endpoint q cw K CN x u v B h| ≤ SE)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {A : ℕ}
    (hA : (⌊κ * x + 1⌋₊ : ℝ) ≤ gridPt x (presieveExponent c Ch x) δ A) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : (j : ℝ) ≤ Cj * logLogLog x + 1)
    (hα : ∀ m, |primeProxyDiff x (presieveExponent c Ch x) j m| ≤ 1)
    (hαs : ∀ m : ℕ, (m : ℝ) ≤ x ^ presieveExponent c Ch x →
      primeProxyDiff x (presieveExponent c Ch x) j m = 0)
    (β βc : ℕ → ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβc : ∀ n, βc n ≠ 0 → (∀ p ∈ n.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p) ∧
      0 ≤ βc n ∧ βc n ≤ Real.log x ^ (3 : ℝ))
    (hββ : ∀ n, 0 ≤ βc n ∧ βc n ≤ β n)
    (hβs : ∀ n : ℕ, (n : ℝ) ≤ x ^ presieveExponent c Ch x → βc n = 0) :
    |∑ m₀ ∈ Icc 1 ⌊κ * x + 1⌋₊, ∑ n ∈ Icc 1 ⌊κ * x + 1⌋₊,
        cutPsi Φ (endpoint q cw K CN x u v B) x (m₀ * n) *
          primeProxyDiff x (presieveExponent c Ch x) j m₀ * βc n| ≤
      (A : ℝ) ^ 2 * (M 0 * ((clusterSets K (inertPerCluster K CN x)).card * 𝒩 *
          (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ)))) +
        M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) * SE *
          (4 * (κ * x + 1)) *
          ∑ n ∈ Ioc ⌊gridPt x (presieveExponent c Ch x) δ 0⌋₊
            ⌊gridPt x (presieveExponent c Ch x) δ A⌋₊, β n / n := by
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  set E := endpoint q cw K CN x u v B
  set α := primeProxyDiff x γ j
  set lam := gridPt x γ δ
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hΨ0 : ∀ h, N < h → cutPsi Φ E x h = 0 := fun h hh => cutPsi_eq_zero hΦ hx0 hκ0 hh
  have hmono : ∀ a, lam a ≤ lam (a + 1) := gridPt_mono (by linarith) hδ0
  have hlam0 : 0 ≤ lam 0 := by simp only [lam, gridPt]; positivity
  have hlam00 : lam 0 = x ^ γ := by simp [lam, gridPt]
  have hlamγ : ∀ a, x ^ γ ≤ lam a := fun a => by
    simp only [lam, gridPt]
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith))
  -- cut `m₀` and `n` into the cells of the grid
  have hgrid : ∑ m₀ ∈ Icc 1 N, ∑ n ∈ Icc 1 N, cutPsi Φ E x (m₀ * n) * α m₀ * βc n =
      ∑ a ∈ range A, ∑ b ∈ range A, ∑ m₀ ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊,
        ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊, cutPsi Φ E x (m₀ * n) * α m₀ * βc n := by
    rw [sum_Icc_eq_sum_cells _ lam hmono hlam0 hA (fun m hm1 hm => ?_) (fun m hm => ?_)]
    · refine sum_congr rfl fun a _ => ?_
      have hinner : ∀ m₀ ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊,
          ∑ n ∈ Icc 1 N, cutPsi Φ E x (m₀ * n) * α m₀ * βc n =
          ∑ b ∈ range A, ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊,
            cutPsi Φ E x (m₀ * n) * α m₀ * βc n := by
        intro m₀ hm₀
        have hm₀1 : 1 ≤ m₀ := by have := (mem_Ioc.1 hm₀).1; omega
        exact sum_Icc_eq_sum_cells _ lam hmono hlam0 hA
          (fun n _ hn => by rw [hβs n (hlam00 ▸ hn), mul_zero])
          (fun n hn => by rw [hΨ0 _ (lt_of_lt_of_le hn (Nat.le_mul_of_pos_left n hm₀1)),
            zero_mul, zero_mul])
      rw [sum_congr rfl hinner]
      exact sum_comm
    · rw [hlam00] at hm
      exact sum_eq_zero fun n _ => by rw [hαs m hm, mul_zero, zero_mul]
    · exact sum_eq_zero fun n hn => by
        have := (mem_Icc.1 hn).1
        rw [hΨ0 _ (lt_of_lt_of_le hm (Nat.le_mul_of_pos_right m this)), zero_mul, zero_mul]
  rw [hgrid]
  -- bound each box
  have hbox_le : ∀ a b, |∑ m₀ ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊, ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊,
      cutPsi Φ E x (m₀ * n) * α m₀ * βc n| ≤
      M 0 * ((clusterSets K (inertPerCluster K CN x)).card * 𝒩 *
        (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ))) +
      ∑ m ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊, ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊,
        (if (m * n : ℝ) ≤ 4 * (κ * x + 1) then
          M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) else 0) * SE * β n := by
    intro a b
    have h := abs_box_term_le hE hbox hC₂ hΦ hκ hx hxγ hsq hSE0 hSE hδ0 hδ1 (hlamγ a) (hlamγ b)
      hj1 hj2 hα β βc hβc hββ
    simp only [lam, gridPt_succ] at h ⊢
    exact h
  have hτ : 0 ≤ M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) :=
    mul_nonneg (by
      have := cutoff_deriv_bound_nonneg hΦ 1; push_cast at this; exact this) (by positivity)
  have hvar := sum_cells_variation_le (X := 4 * (κ * x + 1)) A lam hmono hτ hSE0
    (by positivity) β hβ0
  calc _ ≤ ∑ a ∈ range A, ∑ b ∈ range A, |∑ m₀ ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊,
        ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊, cutPsi Φ E x (m₀ * n) * α m₀ * βc n| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ range A, ∑ b ∈ range A, (M 0 * ((clusterSets K (inertPerCluster K CN x)).card *
          𝒩 * (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ))) +
        ∑ m ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊, ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊,
          (if (m * n : ℝ) ≤ 4 * (κ * x + 1) then
            M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) else 0) * SE * β n) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hbox_le a b
    _ = (A : ℝ) ^ 2 * (M 0 * ((clusterSets K (inertPerCluster K CN x)).card * 𝒩 *
          (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ)))) +
        ∑ a ∈ range A, ∑ b ∈ range A, ∑ m ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊,
          ∑ n ∈ Ioc ⌊lam b⌋₊ ⌊lam (b + 1)⌋₊,
          (if (m * n : ℝ) ≤ 4 * (κ * x + 1) then
            M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) else 0) * SE * β n := by
        simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
        ring
    _ ≤ _ := by
        rw [hlam00] at hvar ⊢
        exact add_le_add le_rfl hvar

/-- One telescoping step of E4. -/
theorem abs_single_step_le {q cw : ℝ} {K : ℕ} {CN c Ch Cj κ CΦ C₂ x 𝒩 SE δ : ℝ}
    {M : ℕ → ℝ} {Φ : ℝ → ℝ} {k : ℕ} {u v : Fin (k + 1) → ℝ} {B : (Fin k → ℕ) → ℝ}
    (hE : EndpointData q cw K CN x u v B 𝒩) (hbox : BoxBound q K c Ch Cj κ C₂ x)
    (hC₂ : 0 ≤ C₂) (hΦ : IsCutoff κ CΦ M x Φ) (hκ : 1 < κ) (hx : 1 < x) (hxκ : κ ≤ x)
    (hxγ : 1 ≤ x ^ presieveExponent c Ch x) (hsq : 4 * (κ * x + 1) ≤ x ^ 2)
    (hSE0 : 0 ≤ SE)
    (hSE : ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ x ^ 2 → |endpoint q cw K CN x u v B h| ≤ SE)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {A : ℕ}
    (hA : (⌊κ * x + 1⌋₊ : ℝ) ≤ gridPt x (presieveExponent c Ch x) δ A) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : (j : ℝ) ≤ Cj * logLogLog x + 1)
    (hα : ∀ m, |primeProxyDiff x (presieveExponent c Ch x) j m| ≤ 1)
    (hαs : ∀ m : ℕ, (m : ℝ) ≤ x ^ presieveExponent c Ch x →
      primeProxyDiff x (presieveExponent c Ch x) j m = 0)
    {r : ℕ} (hr : 1 ≤ r) (V : Fin r → ℕ → ℝ)
    (hV : ∀ i, FactorWeight x (presieveExponent c Ch x) j (V i)) :
    |∑ m₀ ∈ Icc 1 ⌊κ * x + 1⌋₊, ∑ m' ∈ Fintype.piFinset (fun _ : Fin r => Icc 1 ⌊κ * x + 1⌋₊),
        cutPsi Φ (endpoint q cw K CN x u v B) x (m₀ * ∏ i, m' i) *
          primeProxyDiff x (presieveExponent c Ch x) j m₀ * ∏ i, V i (m' i)| ≤
      M 0 * SE * (⌊κ * x + 1⌋₊ / Real.log x ^ (3 : ℝ)) *
          ∏ i, ∑ m ∈ Icc 1 ⌊κ * x + 1⌋₊, V i m * cmul (fun p => proxyLoc x j p * r / p) m +
        (A : ℝ) ^ 2 * (M 0 * ((clusterSets K (inertPerCluster K CN x)).card * 𝒩 *
          (C₂ * (κ * x) * Real.log x ^ (-12 : ℝ)))) +
        M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) * SE *
          (4 * (κ * x + 1)) *
          ∏ i, ∑ m ∈ Icc 1 ⌊κ * x + 1⌋₊, V i m * cmul (fun p => (p : ℝ)⁻¹) m := by
  set γ := presieveExponent c Ch x
  set N := ⌊κ * x + 1⌋₊
  set E := endpoint q cw K CN x u v B
  set α := primeProxyDiff x γ j
  set L := Real.log x
  have hx0 : 0 < x := by linarith
  have hκ0 : 0 < κ := by linarith
  have hL0 : 0 < L := Real.log_pos hx
  have hL3 : 0 < L ^ (3 : ℝ) := by positivity
  have hκx : κ * x ≤ x ^ 2 := by nlinarith
  have hΨ0 : ∀ h, N < h → cutPsi Φ E x h = 0 := fun h hh => cutPsi_eq_zero hΦ hx0 hκ0 hh
  have hΨ := abs_cutPsi_le (E := E) hΦ hx0 hκ0 hκx hxκ hSE0 hSE
  have hV0 : ∀ i m, 0 ≤ V i m := fun i => (hV i).nonneg
  set β := tupleWeight (Icc 1 N) V with hβdef
  have hβ0 : ∀ n, 0 ≤ β n := tupleWeight_nonneg _ hV0
  set βc : ℕ → ℝ := fun n => if β n ≤ L ^ (3 : ℝ) then β n else 0 with hβcdef
  set βt : ℕ → ℝ := fun n => β n - βc n with hβtdef
  -- regroup and split off the clipped tail
  rw [sum_tuple_eq_sum_fiber hr _ hΨ0]
  have hsplit : ∑ m₀ ∈ Icc 1 N, ∑ n ∈ Icc 1 N, cutPsi Φ E x (m₀ * n) * α m₀ * β n =
      ∑ m₀ ∈ Icc 1 N, ∑ n ∈ Icc 1 N, cutPsi Φ E x (m₀ * n) * α m₀ * βc n +
        ∑ m₀ ∈ Icc 1 N, ∑ n ∈ Icc 1 N, cutPsi Φ E x (m₀ * n) * α m₀ * βt n := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m₀ _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [hβtdef]
    ring
  rw [hsplit, add_comm, add_assoc]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the clipped tail, by the mean square of the companion
    have hβle : ∀ n, n ≠ 0 → β n ≤ dampedWeight x j n * cmul (fun _ => (r : ℝ)) n :=
      fun n hn => tupleWeight_le (fun m hm => (mem_Icc.1 hm).1) hV0
        (fun i m hm => (hV i).le_damped m hm) hn
    have hβz : β 0 = 0 := by
      simp only [hβdef, tupleWeight]
      refine sum_eq_zero fun m hm => ?_
      exfalso
      obtain ⟨hmS, hprod⟩ := mem_filter.1 hm
      have hne : ∏ i, m i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => by
        have := (mem_Icc.1 (Fintype.mem_piFinset.1 hmS i)).1; omega
      exact hne hprod
    have hβt : ∀ n, 0 ≤ βt n ∧ βt n ≤ β n * (dampedWeight x j n * cmul (fun _ => (r : ℝ)) n) /
        L ^ (3 : ℝ) := by
      intro n
      have hh0 : 0 ≤ dampedWeight x j n * cmul (fun _ => (r : ℝ)) n :=
        mul_nonneg (dampedWeight_nonneg x j n) (cmul_nonneg (fun _ _ => Nat.cast_nonneg r) n)
      simp only [hβtdef, hβcdef]
      split_ifs with h
      · rw [sub_self]
        exact ⟨le_rfl, div_nonneg (mul_nonneg (hβ0 n) hh0) hL3.le⟩
      · push Not at h
        rw [sub_zero]
        have hn : n ≠ 0 := by
          intro hn; rw [hn, hβz] at h; linarith
        have hle := hβle n hn
        refine ⟨hβ0 n, ?_⟩
        rw [le_div_iff₀ hL3]
        nlinarith [hβ0 n]
    have htail := abs_sum_tail_le (M := N) (cutPsi Φ E x) α βt β
      (fun n => dampedWeight x j n * cmul (fun _ => (r : ℝ)) n) hL3 hΨ0 hΨ hα hβt
    refine htail.trans ?_
    have hconv : ∑ n ∈ Icc 1 N, β n * (dampedWeight x j n * cmul (fun _ => (r : ℝ)) n) / n =
        ∑ n ∈ Icc 1 N, β n * cmul (fun p => proxyLoc x j p * r / p) n := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (mem_Icc.1 hn).1; omega
      rw [dampedWeight_eq_cmul x j hn0, ← cmul_mul_loc, mul_div_assoc, cmul_div hn0]
    rw [hconv]
    have hprod := sum_tupleWeight_mul_le (Icc 1 N) hV0
      (l := fun p => proxyLoc x j p * r / p) (fun p _ => by
        have := proxyLoc_nonneg x j p; positivity) (Icc 1 N)
    have hS : 0 ≤ M 0 * SE * (N / L ^ (3 : ℝ)) := by
      have := (abs_nonneg _).trans (hΨ 0)
      positivity
    exact mul_le_mul_of_nonneg_left hprod hS
  · -- the clipped part, box by box
    have hββ : ∀ n, 0 ≤ βc n ∧ βc n ≤ β n := fun n => by
      simp only [hβcdef]; split_ifs <;> simp [hβ0 n]
    have hβc : ∀ n, βc n ≠ 0 →
        (∀ p ∈ n.primeFactors, Real.exp (Real.log x ^ (28 / 100 : ℝ)) ≤ p) ∧
        0 ≤ βc n ∧ βc n ≤ Real.log x ^ (3 : ℝ) := by
      intro n hn
      simp only [hβcdef] at hn ⊢
      split_ifs at hn ⊢ with h
      · exact ⟨(tupleWeight_support hr hV hn).2, hβ0 n, h⟩
      · exact absurd rfl hn
    have hβs : ∀ n : ℕ, (n : ℝ) ≤ x ^ γ → βc n = 0 := by
      intro n hn
      have : β n = 0 := by
        by_contra h
        have := (tupleWeight_support hr hV h).1
        linarith
      simp only [hβcdef, this]; split_ifs <;> rfl
    refine (abs_clipped_le hE hbox hC₂ hΦ hκ hx hxγ hsq hSE0 hSE hδ0 hδ1 hA hj1 hj2 hα hαs β βc
      hβ0 hβc hββ hβs).trans (add_le_add le_rfl ?_)
    have hτ : 0 ≤ M 1 * logLog x ^ (CΦ * 1) * ((3 * δ * (κ * x + 1) + 1) / x) * SE *
        (4 * (κ * x + 1)) := by
      have := cutoff_deriv_bound_nonneg hΦ 1
      push_cast at this
      positivity
    refine mul_le_mul_of_nonneg_left ?_ hτ
    have hconv : ∑ n ∈ Ioc ⌊gridPt x γ δ 0⌋₊ ⌊gridPt x γ δ A⌋₊, β n / n =
        ∑ n ∈ Ioc ⌊gridPt x γ δ 0⌋₊ ⌊gridPt x γ δ A⌋₊, β n * cmul (fun p => (p : ℝ)⁻¹) n := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (mem_Ioc.1 hn).1; omega
      rw [cmul_inv hn0, div_eq_mul_inv]
    rw [hconv]
    exact sum_tupleWeight_mul_le (Icc 1 N) hV0 (l := fun p => (p : ℝ)⁻¹)
      (fun p _ => by positivity) _

end Erdos408.TypeII
