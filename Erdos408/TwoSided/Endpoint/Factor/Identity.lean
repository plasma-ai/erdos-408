import Erdos408.Extraction.Allocation.Groups
import Erdos408.OneSided.Bands
import Erdos408.TwoSided.Setup

/-!
# Small-prime removal: the exact identities

Helpers for `Erdos408/TwoSided/Endpoint/Factor.lean`, E3 of
`blueprint/two_sided_correlation.md` §6.3 (PD (6.30); WD (5.12)).

* The invariance of `slotLists` when the primes that matter divide both positions or neither
  (for `markedWeight` and `markedListWeight`, see `Setup.lean`).
* The separation of the scales (`eventually_scales`, `scales_of_admissible`): the bands lie
  below the small groups, and every group lies below the slots.
* E3 (`markedListWeight_eq_removal`): if a group `g_s` has the single slot `j` and `b` ignores
  `g_s`, then `W_S^b(w) = V_{g_s}⁻¹ ∑_{p_s ∈ P_{g_s}, p_s ∣ w} W_{S'}^b(w / p_s)`, with
  `S' g_s = ∅`, as long as no `p² ∣ w` with `p ∈ P_{g_s}`.
-/

namespace Erdos408.TwoSided

namespace FactorAux

open Filter Finset

/-! ### The scales -/

/-- Eventually `1 < L`, `0 < T`, `2 L^{a_hi} < L^{0.27}` and `L^{0.46} < c L / T²⁰`. -/
theorem eventually_scales {ahi c : ℝ} (hahi : ahi < 1 / 5) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 1 < Real.log x ∧ 0 < Real.log (Real.log x) ∧
      2 * Real.log x ^ ahi < Real.log x ^ (0.27 : ℝ) ∧
      Real.log x ^ (0.46 : ℝ) < c * Real.log x / Real.log (Real.log x) ^ 20 := by
  have hgap : (0 : ℝ) < 0.27 - ahi := by linarith
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1,
    ((tendsto_rpow_atTop hgap).comp Real.tendsto_log_atTop).eventually_gt_atTop 2,
    ((isLittleO_log_rpow_rpow_atTop 20 (by norm_num : (0 : ℝ) < 0.54)).comp_tendsto
      Real.tendsto_log_atTop).bound (half_pos hc)] with x hL h₁ h₂
  simp only [Function.comp_apply] at h₁ h₂
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hT : 0 < Real.log L := Real.log_pos hL
  refine ⟨hL, hT, ?_, ?_⟩
  · have : L ^ (0.27 : ℝ) = L ^ (0.27 - ahi) * L ^ ahi := by
      rw [← Real.rpow_add hL0]; ring_nf
    rw [this]
    exact mul_lt_mul_of_pos_right h₁ (Real.rpow_pos_of_pos hL0 _)
  · have h20 : Real.log L ^ (20 : ℝ) = Real.log L ^ 20 := by
      rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hT.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _), h20] at h₂
    have hT20 : 0 < Real.log L ^ 20 := by positivity
    rw [lt_div_iff₀ hT20]
    have hsplit : L ^ (0.46 : ℝ) * L ^ (0.54 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    have h46 : 0 < L ^ (0.46 : ℝ) := Real.rpow_pos_of_pos hL0 _
    calc L ^ (0.46 : ℝ) * Real.log L ^ 20 ≤ L ^ (0.46 : ℝ) * (c / 2 * L ^ (0.54 : ℝ)) :=
          mul_le_mul_of_nonneg_left h₂ h46.le
      _ = c / 2 * (L ^ (0.46 : ℝ) * L ^ (0.54 : ℝ)) := by ring
      _ = c / 2 * L := by rw [hsplit]
      _ < c * L := by nlinarith [mul_pos hc hL0]

/-- The separation of the scales at an `x` where `eventually_scales` holds: every group prime
is a prime `≤ exp(L^{0.46})`, the small-group primes are `≥ exp(L^{0.27})`, the band primes
are `< exp(L^{0.27})` and the slots start above `exp(L^{0.46})`. -/
theorem scales_of_admissible {c₀ C₀ vlo vhi alo ahi c x : ℝ} {K₀ : ℕ} {CN : ℝ}
    (hx : 0 < x) (hL : 1 < Real.log x) (hband : 2 * Real.log x ^ ahi < Real.log x ^ (0.27 : ℝ))
    (hslot : Real.log x ^ (0.46 : ℝ) < c * Real.log x / Real.log (Real.log x) ^ 20)
    {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ} {big : Finset ι}
    (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big) {r : ℕ} {a : Fin r → ℝ}
    (hin : InertAdmissible K₀ CN alo ahi x a) {d : ℕ} {u v : Fin (d + 1) → ℝ}
    (hsl : AdmissibleSlots c x u v) :
    (∀ g, ∀ p ∈ P g, p.Prime ∧ (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ))) ∧
      (∀ g ∉ big, ∀ p ∈ P g, Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p) ∧
      (∀ i, ∀ p ∈ band x (a i), (p : ℝ) < Real.exp (Real.log x ^ (0.27 : ℝ))) ∧
      ∀ i, Real.exp (Real.log x ^ (0.46 : ℝ)) < x ^ u i := by
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  refine ⟨fun g p hp => ?_, fun g hg p hp => ?_, fun i p hp => ?_, fun i => ?_⟩
  · by_cases hg : g ∈ big
    · obtain ⟨h₁, -, h₂⟩ := mem_primesIcc.1 (hadm.2.2.2.2.2.2.2.1 g hg hp)
      exact ⟨h₁, h₂⟩
    · obtain ⟨h₁, -, h₂⟩ := mem_primesIcc.1 (hadm.2.2.2.2.2.2.1 g hg hp)
      refine ⟨h₁, h₂.trans (Real.exp_le_exp.2 ?_)⟩
      exact Real.rpow_le_rpow_of_exponent_le hL.le (by norm_num)
  · exact (mem_primesIcc.1 (hadm.2.2.2.2.2.2.1 g hg hp)).2.1
  · refine (OneSided.mem_band_bounds hp).2.trans_lt (Real.exp_lt_exp.2 ?_)
    calc 2 * L ^ a i ≤ 2 * L ^ ahi := by
          gcongr
          exacts [hL.le, (hin.2.1 i).2]
      _ < L ^ (0.27 : ℝ) := hband
  · rw [Real.rpow_def_of_pos hx, Real.exp_lt_exp]
    refine hslot.trans_le ?_
    have := hsl.1 i
    unfold logLog at this
    calc c * L / Real.log L ^ 20 = L * (c / Real.log L ^ 20) := by ring
      _ ≤ L * u i := mul_le_mul_of_nonneg_left this hL0.le

/-- For `k ∣ n` and `m` coprime to `k`, `m ∣ n / k ↔ m ∣ n`. -/
theorem dvd_div_iff_of_coprime {m k n : ℕ} (hk : k ∣ n) (hmk : Nat.Coprime m k) :
    m ∣ n / k ↔ m ∣ n := by
  obtain ⟨j, rfl⟩ := hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · rw [Nat.mul_div_cancel_left j hk0, hmk.dvd_mul_left]

/-- Distinct primes are coprime, in the form used with `dvd_div_iff_of_coprime`. -/
theorem coprime_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.Coprime p q :=
  (Nat.coprime_primes hp hq).2 hpq

/-- Membership in the represented lists. -/
theorem mem_slotLists {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ} {M : ℕ}
    {S : ι → Finset (Fin M)} {n : ℕ} {p : ι → Fin M → ℕ} :
    p ∈ slotLists P S n ↔ (∀ g i, p g i ∈ if i ∈ S g then P g else {1}) ∧
      ∀ g, Set.InjOn (p g) (S g) ∧ ∀ i ∈ S g, p g i ∣ n := by
  simp only [slotLists, mem_filter, Fintype.mem_piFinset]

/-- The represented lists agree at `m` and `n` when each prime of a group with a slot
divides both or neither. -/
theorem slotLists_congr {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ} {M : ℕ}
    {S : ι → Finset (Fin M)} {m n : ℕ} (h : ∀ g, ∀ i ∈ S g, ∀ p ∈ P g, p ∣ m ↔ p ∣ n) :
    slotLists P S m = slotLists P S n := by
  unfold slotLists
  refine filter_congr fun p hp => ?_
  rw [Fintype.mem_piFinset] at hp
  refine forall_congr' fun g => and_congr_right fun _ => forall₂_congr fun i hi => ?_
  have hpi := Fintype.mem_piFinset.1 (hp g) i
  rw [ite_eq_left hi] at hpi
  exact h g i hi _ hpi

/-- **E3 (small-prime removal).** If the group `g_s` has the single slot `j`, `b` ignores the
labels of `g_s` and no `p ∈ P_{g_s}` has `p² ∣ w`, then
`W_S^b(w) = V_{g_s}⁻¹ ∑_{p_s ∈ P_{g_s}, p_s ∣ w} W_{S'}^b(w / p_s)` with `S' g_s = ∅`. -/
theorem markedListWeight_eq_removal {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : ι → Finset ℕ} (hpr : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) (q₀ : ℝ) {M : ℕ}
    (S : ι → Finset (Fin M)) (b : (ι → Fin M → ℕ) → ℂ) (gs : ι) (j : Fin M)
    (hS : S gs = {j}) (hb : ∀ p p', (∀ g, g ≠ gs → p g = p' g) → b p = b p') {w : ℕ}
    (hsq : ∀ p ∈ P gs, ¬ p ^ 2 ∣ w) :
    markedListWeight P q₀ S b w = (((harmonicMass (P gs))⁻¹ : ℝ) : ℂ) *
      ∑ ps ∈ (P gs).filter (· ∣ w),
        markedListWeight P q₀ (Function.update S gs ∅) b (w / ps) := by
  set S' := Function.update S gs ∅ with hS'
  set F := (P gs).filter (· ∣ w) with hF
  have hS'gs : S' gs = ∅ := Function.update_self _ _ _
  have hS'ne : ∀ g, g ≠ gs → S' g = S g := fun g hg => Function.update_of_ne hg _ _
  have hjS : j ∈ S gs := by rw [hS]; exact mem_singleton_self j
  have hnS : ∀ i, i ≠ j → i ∉ S gs := fun i hij h => hij (mem_singleton.1 (hS ▸ h))
  -- a prime of another group does not see `p_s`
  have hother : ∀ ps ∈ F, ∀ g, g ≠ gs → ∀ p ∈ P g, p ∣ w / ps ↔ p ∣ w := by
    intro ps hps g hg p hp
    obtain ⟨hps, hdvd⟩ := mem_filter.1 hps
    refine dvd_div_iff_of_coprime hdvd (coprime_of_prime_ne (hpr g p hp) (hpr gs ps hps) ?_)
    rintro rfl
    exact Finset.disjoint_left.1 (hdisj g gs hg) hp hps
  -- `ω(w / p_s) + 1 = ω(w)`
  have hω : ∀ ps ∈ F, groupPrimeCount P (w / ps) + 1 = groupPrimeCount P w := by
    intro ps hps
    obtain ⟨hpsP, hdvd⟩ := mem_filter.1 hps
    have hgs : (P gs).filter (· ∣ w / ps) = ((P gs).filter (· ∣ w)).erase ps := by
      ext p
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨hp, hpd⟩
        have hne : p ≠ ps := by
          rintro rfl
          exact hsq p hp (by rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hdvd hpd)
        exact ⟨hne, hp, hpd.trans (Nat.div_dvd_of_dvd hdvd)⟩
      · rintro ⟨hne, hp, hpd⟩
        exact ⟨hp, (dvd_div_iff_of_coprime hdvd
          (coprime_of_prime_ne (hpr gs p hp) (hpr gs ps hpsP) hne)).2 hpd⟩
    unfold groupPrimeCount
    rw [← add_sum_erase _ _ (mem_univ gs), ← add_sum_erase _ _ (mem_univ gs),
      sum_congr rfl fun g hg => Sieve.primeCount_congr (hother ps hps g (ne_of_mem_erase hg))]
    have hcard : primeCount (P gs) (w / ps) + 1 = primeCount (P gs) w := by
      unfold primeCount
      rw [hgs, card_erase_add_one (mem_filter.2 ⟨hpsP, hdvd⟩)]
    omega
  -- the represented lists of `S'` do not see `p_s`
  have hlists : ∀ ps ∈ F, slotLists P S' (w / ps) = slotLists P S' w := by
    intro ps hps
    refine slotLists_congr fun g i hi p hp => ?_
    rcases eq_or_ne g gs with rfl | hg
    · rw [hS'gs] at hi
      exact absurd hi (notMem_empty i)
    · exact hother ps hps g hg p hp
  -- the slot counts and the normalizations
  have hcard : ∑ g, (S' g).card + 1 = ∑ g, (S g).card := by
    rw [← add_sum_erase _ _ (mem_univ gs), ← add_sum_erase _ _ (mem_univ gs), hS'gs, hS,
      sum_congr rfl fun g hg => by rw [hS'ne g (ne_of_mem_erase hg)], card_empty,
      card_singleton]
    omega
  have hprod : ∏ g, (harmonicMass (P g))⁻¹ ^ (S g).card =
      (harmonicMass (P gs))⁻¹ * ∏ g, (harmonicMass (P g))⁻¹ ^ (S' g).card := by
    have he : ∏ g ∈ univ.erase gs, (harmonicMass (P g))⁻¹ ^ (S' g).card =
        ∏ g ∈ univ.erase gs, (harmonicMass (P g))⁻¹ ^ (S g).card :=
      prod_congr rfl fun g hg => by rw [hS'ne g (ne_of_mem_erase hg)]
    rw [← mul_prod_erase _ _ (mem_univ gs), ← mul_prod_erase _ _ (mem_univ gs), hS'gs, hS, he,
      card_empty, card_singleton, pow_zero, pow_one, one_mul]
  -- the lists of `S` are a mark of `g_s` times a list of `S'`
  have hsum : ∑ p ∈ slotLists P S w, b p = ∑ ps ∈ F, ∑ p ∈ slotLists P S' w, b p := by
    rw [← sum_product']
    refine sum_nbij' (fun p => (p gs j, Function.update p gs fun _ => 1))
      (fun x => Function.update x.2 gs (Function.update (fun _ => 1) j x.1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_slotLists] at hp
      rw [mem_product]
      refine ⟨mem_filter.2 ⟨?_, (hp.2 gs).2 j hjS⟩, ?_⟩
      · have := hp.1 gs j
        rwa [ite_eq_left hjS] at this
      · dsimp only
        rw [mem_slotLists]
        refine ⟨fun g i => ?_, fun g => ?_⟩
        · rcases eq_or_ne g gs with rfl | hg
          · rw [Function.update_self, hS'gs, ite_eq_right (notMem_empty i)]
            exact mem_singleton_self 1
          · rw [Function.update_of_ne hg, hS'ne g hg]
            exact hp.1 g i
        · rcases eq_or_ne g gs with rfl | hg
          · rw [hS'gs, coe_empty]
            exact ⟨Set.injOn_empty _, fun i hi => absurd hi (notMem_empty i)⟩
          · rw [Function.update_of_ne hg, hS'ne g hg]
            exact hp.2 g
    · rintro ⟨ps, p'⟩ hx
      rw [mem_product] at hx
      obtain ⟨hps, hp'⟩ := hx
      obtain ⟨hpsP, hdvd⟩ := mem_filter.1 hps
      rw [mem_slotLists] at hp'
      dsimp only
      rw [mem_slotLists]
      refine ⟨fun g i => ?_, fun g => ?_⟩
      · rcases eq_or_ne g gs with rfl | hg
        · rw [Function.update_self]
          rcases eq_or_ne i j with rfl | hij
          · rw [Function.update_self, ite_eq_left hjS]
            exact hpsP
          · rw [Function.update_of_ne hij, ite_eq_right (hnS i hij)]
            exact mem_singleton_self 1
        · rw [Function.update_of_ne hg, ← hS'ne g hg]
          exact hp'.1 g i
      · rcases eq_or_ne g gs with rfl | hg
        · rw [Function.update_self, hS, coe_singleton]
          refine ⟨Set.injOn_singleton _ _, fun i hi => ?_⟩
          rw [mem_singleton.1 hi, Function.update_self]
          exact hdvd
        · rw [Function.update_of_ne hg, ← hS'ne g hg]
          exact hp'.2 g
    · intro p hp
      rw [mem_slotLists] at hp
      simp only [Function.update_idem]
      funext g
      rcases eq_or_ne g gs with rfl | hg
      · rw [Function.update_self]
        funext i
        rcases eq_or_ne i j with rfl | hij
        · rw [Function.update_self]
        · rw [Function.update_of_ne hij]
          have := hp.1 g i
          rw [ite_eq_right (hnS i hij)] at this
          exact (mem_singleton.1 this).symm
      · rw [Function.update_of_ne hg]
    · rintro ⟨ps, p'⟩ hx
      rw [mem_product] at hx
      obtain ⟨-, hp'⟩ := hx
      rw [mem_slotLists] at hp'
      simp only [Function.update_self, Function.update_idem, Prod.mk.injEq, true_and]
      rw [Function.update_eq_self_iff]
      funext i
      have := hp'.1 gs i
      rw [hS'gs, ite_eq_right (notMem_empty i)] at this
      exact (mem_singleton.1 this).symm
    · intro p _
      exact hb _ _ fun g hg => (Function.update_of_ne hg _ _).symm
  -- assemble
  have hexp : ∀ ps ∈ F, ((groupPrimeCount P (w / ps) : ℤ) - ∑ g, ((S' g).card : ℤ)) =
      (groupPrimeCount P w : ℤ) - ∑ g, ((S g).card : ℤ) := by
    intro ps hps
    have h₁ := hω ps hps
    rw [← Nat.cast_sum, ← Nat.cast_sum]
    omega
  have hterm : ∀ ps ∈ F, markedListWeight P q₀ S' b (w / ps) =
      ((q₀ ^ ((groupPrimeCount P w : ℤ) - ∑ g, ((S g).card : ℤ)) *
        ∏ g, (harmonicMass (P g))⁻¹ ^ (S' g).card : ℝ) : ℂ) * ∑ p ∈ slotLists P S' w, b p := by
    intro ps hps
    unfold markedListWeight
    rw [hexp ps hps, hlists ps hps]
  rw [sum_congr rfl hterm]
  unfold markedListWeight
  rw [hsum, sum_const, sum_const, hprod]
  push_cast
  ring

end FactorAux

end Erdos408.TwoSided
