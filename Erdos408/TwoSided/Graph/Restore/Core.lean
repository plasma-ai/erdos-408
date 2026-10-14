module

public import Erdos408.Extraction.Allocation.Groups
public import Erdos408.TwoSided.Setup

/-!
# The centered core and the clipped core at the active primes

The pointwise facts about `F = 𝒲 (f_B - C_B)` and the clipped core `G` that Lemma G5 uses
(`blueprint/two_sided_correlation.md` §2), besides the crude U7 `|F(n)| ≤ L` of `Setup.lean`:

* the consequences of (6.1) used by G5;
* U8: eventually `F(p n) = F(n)` for every active prime `p`, which lies above the bands and
  below the slots;
* `G(p n) = G(n)` for every active prime `p`, since `G = G ∘ stripPrimes`.
-/

@[expose] public section

namespace Erdos408.TwoSided

namespace Restore

open Filter Finset

/-! ### The groups -/

/-- The consequences of (6.1) used by Lemma G5: disjoint groups of primes in
`[exp(L^{0.27}), exp(L^{0.46})]`, masses `V_g ≥ v₋`, and `s_P ≤ 2 C₀ T`. -/
lemma groupAdmissible_facts {c₀ C₀ vlo vhi x : ℝ} {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Finset ℕ} {big : Finset ι} (hL : 1 ≤ Real.log x)
    (h : GroupAdmissible c₀ C₀ vlo vhi x P big) :
    (∀ g h, g ≠ h → Disjoint (P g) (P h)) ∧
      (∀ g, ∀ p ∈ P g, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
        (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ))) ∧
      (∀ g, vlo ≤ harmonicMass (P g)) ∧
      (Fintype.card ι : ℝ) ≤ 2 * C₀ * Real.log (Real.log x) := by
  obtain ⟨hdisj, -, hs₂, -, hb₂, hV, hSm, hBg, -⟩ := h
  have hexp : ∀ {a b : ℝ}, a ≤ b → Real.exp (Real.log x ^ a) ≤ Real.exp (Real.log x ^ b) :=
    fun hab => Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL hab)
  refine ⟨hdisj, fun g p hp => ?_, fun g => (hV g).1, ?_⟩
  · by_cases hg : g ∈ big
    · obtain ⟨hpr, h₁, h₂⟩ := mem_primesIcc.1 (hBg g hg hp)
      exact ⟨hpr, (hexp (by norm_num)).trans h₁, h₂⟩
    · obtain ⟨hpr, h₁, h₂⟩ := mem_primesIcc.1 (hSm g hg hp)
      exact ⟨hpr, h₁, h₂.trans (hexp (by norm_num))⟩
  · have hcard : ((univ \ big).card : ℝ) + big.card = Fintype.card ι := by
      rw [← card_univ]
      exact_mod_cast card_sdiff_add_card_eq_card (subset_univ big)
    linarith

/-! ### U8 and the invariance of the clipped core -/

/-- Eventually `2 L^{1/5} < L^{0.27}` and `exp(L^{0.46}) ≤ x^{c/T^{20}}`. -/
lemma eventually_band_lt_and_le_slot {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧
      2 * Real.log x ^ (1 / 5 : ℝ) < Real.log x ^ (0.27 : ℝ) ∧
      Real.exp (Real.log x ^ (0.46 : ℝ)) ≤ x ^ (c / Real.log (Real.log x) ^ 20) := by
  have h₁ := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.07)).comp Real.tendsto_log_atTop
  have h₂ := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.14)).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 3, h₁.eventually_gt_atTop 2,
    h₂.eventually_ge_atTop ((50 : ℝ) ^ 20 / c), eventually_gt_atTop 0] with x hL h₁ h₂ hx0
  simp only [Function.comp_apply] at h₁ h₂
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  refine ⟨by linarith, ?_, ?_⟩
  · calc 2 * L ^ (1 / 5 : ℝ) < L ^ (0.07 : ℝ) * L ^ (1 / 5 : ℝ) :=
          mul_lt_mul_of_pos_right h₁ (by positivity)
      _ = L ^ (0.27 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num
  · set T := Real.log L
    have hT0' : 0 < T := Real.log_pos (by linarith)
    -- `T ≤ 50 L^{0.02}`, so `T²⁰ L^{0.46} ≤ 50²⁰ L^{0.86} ≤ c L`
    have hT : T ≤ 50 * L ^ (0.02 : ℝ) := by
      have := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 0.02)
      calc T ≤ L ^ (0.02 : ℝ) / 0.02 := this
        _ = 50 * L ^ (0.02 : ℝ) := by norm_num [div_eq_mul_inv, mul_comm]
    have hT20 : T ^ 20 ≤ 50 ^ 20 * L ^ (0.4 : ℝ) := by
      calc T ^ 20 ≤ (50 * L ^ (0.02 : ℝ)) ^ 20 := pow_le_pow_left₀ hT0'.le hT 20
        _ = 50 ^ 20 * L ^ (0.4 : ℝ) := by
          rw [mul_pow, ← Real.rpow_mul_natCast hL0.le]
          norm_num
    have key : T ^ 20 * L ^ (0.46 : ℝ) ≤ c * L := by
      have hc' : (50 : ℝ) ^ 20 ≤ c * L ^ (0.14 : ℝ) := by
        rw [div_le_iff₀ hc] at h₂
        linarith
      calc T ^ 20 * L ^ (0.46 : ℝ) ≤ 50 ^ 20 * L ^ (0.4 : ℝ) * L ^ (0.46 : ℝ) :=
            mul_le_mul_of_nonneg_right hT20 (by positivity)
        _ ≤ c * L ^ (0.14 : ℝ) * L ^ (0.4 : ℝ) * L ^ (0.46 : ℝ) := by gcongr
        _ = c * L := by
            rw [mul_assoc, mul_assoc, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
            norm_num
    rw [Real.rpow_def_of_pos hx0, Real.exp_le_exp, mul_div_assoc', le_div_iff₀ (pow_pos hT0' 20)]
    linarith

/-- **U8.** Eventually, for an active prime `p` and every `n`, `F(p n) = F(n)`: active
primes lie above the bands and below the slots. -/
theorem eventually_centeredCore_mul_prime (q c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ)
    (d : ℕ) (hahi : ahi < 1 / 5) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
          ∀ p ∈ Finset.univ.biUnion P, ∀ n : ℕ,
            centeredCore x q a u v Bc (p * n) = centeredCore x q a u v Bc n := by
  filter_upwards [eventually_band_lt_and_le_slot hc, eventually_gt_atTop 1]
    with x ⟨hL, hband, hslot⟩ hx1 ι _ _ P big hadm r a u v Bc ha hu p hp n
  obtain ⟨-, hP, -, -⟩ := groupAdmissible_facts hL hadm
  obtain ⟨g, -, hpg⟩ := mem_biUnion.1 hp
  obtain ⟨hpr, hp₁, hp₂⟩ := hP g p hpg
  -- `p` is no band prime
  have hnb : ∀ i, p ∉ band x (a i) := by
    intro i hpb
    unfold band at hpb
    obtain ⟨hpb, -⟩ := mem_filter.1 hpb
    have h₂ : (p : ℝ) ≤ Real.exp (2 * Real.log x ^ a i) :=
      (Nat.le_floor_iff (Real.exp_pos _).le).1 (mem_Icc.1 hpb).2
    have hai : Real.log x ^ a i ≤ Real.log x ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith [(ha.2.1 i).2])
    have : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ Real.exp (2 * Real.log x ^ a i) := hp₁.trans h₂
    rw [Real.exp_le_exp] at this
    linarith
  -- `p` lies below every slot
  have hpu : ∀ i, (p : ℝ) ≤ x ^ u i := fun i =>
    hp₂.trans (hslot.trans (Real.rpow_le_rpow_of_exponent_le hx1.le (hu.1 i)))
  unfold centeredCore markedWeight
  rw [TypeII.slotCount_prime_mul u v Bc hpr hpu]
  simp_rw [TypeII.primeCount_prime_mul (fun q hq => TypeII.band_prime hq) hpr (hnb _)]

/-- The clipped core is invariant under the active primes. -/
lemma coreAdmissible_mul_prime {B₀ x : ℝ} {ι : Type} [Fintype ι] {P : ι → Finset ℕ}
    {G : ℕ → ℝ} (hG : CoreAdmissible B₀ x P G) (hprime : ∀ g, ∀ p ∈ P g, p.Prime) :
    ∀ p ∈ Finset.univ.biUnion P, ∀ n, G (p * n) = G n := by
  intro p hp n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [mul_zero]
  obtain ⟨g, -, hpg⟩ := mem_biUnion.1 hp
  have hpr := hprime g p hpg
  rw [hG.1 (p * n), hG.1 n]
  congr 1
  refine Nat.eq_of_factorization_eq (stripPrimes_ne_zero _ _) (stripPrimes_ne_zero _ _)
    fun r => ?_
  rw [factorization_stripPrimes, factorization_stripPrimes, Finsupp.filter_apply,
    Finsupp.filter_apply, Nat.factorization_mul hpr.ne_zero hn.ne']
  by_cases hr : r ∈ Finset.univ.biUnion P
  · simp [hr]
  · have hrp : r ≠ p := fun h => hr (h ▸ hp)
    simp [hr, Nat.Prime.factorization hpr, hrp.symm]

end Restore

end Erdos408.TwoSided
