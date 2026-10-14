import Erdos408.OneSided.Analysis.Divisor
import Erdos408.TwoSided.Graph.Restore.Core
import Erdos408.TwoSided.Graph.Restore.General

/-!
# Lemma G5 at scale `x`

The size of the constants of `norm_physSum_sub_stripSum_le` for groups as in (6.1)
(`blueprint/two_sided_correlation.md` §4.4, U1, U9–U11): with `s_P ≤ 2 C₀ T`,

* `Λ(n) ≤ (q₀^{-M} c_q)^{s_P} ≤ L^{O(1)}`, from `q₀^z z^t ≤ t!/log(1/q₀)^t` (U9);
* `T = ∏_g V_g^{-t_g} ≤ max(1, 1/v₋)^{(m₀+1) s_P} ≤ L^{O(1)}`;
* `ω(n) ≤ log₂ n` (U11), `μ_g(p) ≤ e^{-L^{0.27}}/v₋` (U1), `D_R D_C ≤ e^{J s_P L^{0.46}}`
  (U10), and `∑_{w ≤ x²} 1/w ≤ 1 + 2L`.

The result (`exists_eventually_norm_physSum_sub_stripSum_le`) is G5 for every pattern with
`|C g| ≤ m₀`: the error is `κ_K L^{C_r} e^{-L^{0.27}}`.
-/

namespace Erdos408.TwoSided

namespace Restore

open Finset Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ}

/-! ### The list weights -/

/-- The unshared parts with labels dividing `n` number at most `∏_g ω_g(n)^{t_g}`. -/
lemma listCount_le_prod (P : ι → Finset ℕ) (C : ι → Finset (Fin J)) (n : ℕ) :
    listCount P C n ≤ ∏ g, primeCount (P g) n ^ (unsharedSlots C g).card := by
  unfold listCount
  calc _ ≤ (Fintype.piFinset fun g => Fintype.piFinset fun j =>
        if j ∈ unsharedSlots C g then (P g).filter (· ∣ n) else {1}).card := by
        refine card_le_card fun l hl => ?_
        obtain ⟨hl, hdvd⟩ := mem_filter.1 hl
        refine Fintype.mem_piFinset.2 fun g => Fintype.mem_piFinset.2 fun j => ?_
        by_cases hj : j ∈ unsharedSlots C g
        · rw [ite_eq_left hj]
          exact mem_filter.2 ⟨mem_of_mem_unsharedLists hl hj, hdvd g j hj⟩
        · rw [ite_eq_right hj, eq_one_of_mem_unsharedLists hl hj]
          exact mem_singleton_self 1
    _ = _ := by
        rw [Fintype.card_piFinset]
        refine prod_congr rfl fun g _ => ?_
        rw [Fintype.card_piFinset]
        have : ∀ j, ((if j ∈ unsharedSlots C g then (P g).filter (· ∣ n) else {1}).card) =
            if j ∈ unsharedSlots C g then primeCount (P g) n else 1 := fun j => by
          split_ifs <;> simp [primeCount]
        simp_rw [this]
        rw [Fintype.prod_ite_mem, prod_const]

/-- `q₀^z z^t ≤ t! / log(1/q₀)^t`. -/
private lemma pow_mul_pow_le {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (z t : ℕ) :
    q₀ ^ z * (z : ℝ) ^ t ≤ t.factorial / Real.log q₀⁻¹ ^ t := by
  set θ := Real.log q₀⁻¹
  have hθ : 0 < θ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hq₀, hq₀₁⟩)
  have hq : q₀ ^ z = Real.exp (-(θ * z)) := by
    rw [← Real.exp_log (pow_pos hq₀ z), Real.log_pow]
    simp only [θ, Real.log_inv]
    ring_nf
  have h := Real.pow_div_factorial_le_exp _ (mul_nonneg hθ.le (Nat.cast_nonneg z)) t
  rw [hq, le_div_iff₀ (pow_pos hθ t)]
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  have he := Real.exp_pos (θ * z)
  calc Real.exp (-(θ * z)) * (z : ℝ) ^ t * θ ^ t
      = Real.exp (-(θ * z)) * (θ ^ t * (z : ℝ) ^ t) := by ring
    _ ≤ Real.exp (-(θ * z)) * (Real.exp (θ * z) * t.factorial) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = t.factorial := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- The per-group constant `c_q = (m₀ + 1)! max(1, 1/log(1/q₀))^{m₀+1}` of U9. -/
noncomputable def listConst (q₀ : ℝ) (m₀ : ℕ) : ℝ :=
  (m₀ + 1).factorial * max 1 (Real.log q₀⁻¹)⁻¹ ^ (m₀ + 1)

/-- `c_q ≥ 1`. -/
lemma one_le_listConst (q₀ : ℝ) (m₀ : ℕ) : 1 ≤ listConst q₀ m₀ := by
  unfold listConst
  have h₁ : (1 : ℝ) ≤ (m₀ + 1).factorial := Nat.one_le_cast.2 (Nat.factorial_pos _)
  have h₂ : (1 : ℝ) ≤ max 1 (Real.log q₀⁻¹)⁻¹ ^ (m₀ + 1) := one_le_pow₀ (le_max_left _ _)
  nlinarith

/-- **U9 for the list weights.** `Λ(n) ≤ (q₀^{-M} c_q)^{s_P}`. -/
lemma listWeight_le {P : ι → Finset ℕ} {q₀ : ℝ} (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    {C : ι → Finset (Fin J)} {m₀ : ℕ} (hC : ∀ g, (C g).card ≤ m₀) (n : ℕ) :
    listWeight P q₀ C n ≤ (q₀⁻¹ ^ (J + 1) * listConst q₀ m₀) ^ Fintype.card ι := by
  set θ := Real.log q₀⁻¹
  have hθ : 0 < θ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hq₀, hq₀₁⟩)
  have hgroup : ∀ g, q₀ ^ primeCount (P g) n *
      ((primeCount (P g) n : ℝ) ^ (unsharedSlots C g).card) ≤ listConst q₀ m₀ := by
    intro g
    have ht : (unsharedSlots C g).card ≤ m₀ + 1 := by rw [card_unsharedSlots]; linarith [hC g]
    refine (pow_mul_pow_le hq₀ hq₀₁ _ _).trans ?_
    unfold listConst
    rw [div_eq_mul_inv, ← inv_pow]
    refine mul_le_mul (by exact_mod_cast Nat.factorial_le ht) ?_ (by positivity)
      (by positivity)
    calc θ⁻¹ ^ (unsharedSlots C g).card ≤ max 1 θ⁻¹ ^ (unsharedSlots C g).card :=
          pow_le_pow_left₀ (inv_nonneg.2 hθ.le) (le_max_right _ _) _
      _ ≤ max 1 θ⁻¹ ^ (m₀ + 1) := pow_le_pow_right₀ (le_max_left _ _) ht
  have hq : q₀ ^ ((groupPrimeCount P n : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) =
      (∏ g, q₀ ^ primeCount (P g) n) * (q₀⁻¹ ^ (J + 1)) ^ Fintype.card ι := by
    rw [zpow_sub₀ hq₀.ne', zpow_natCast, zpow_natCast, div_eq_mul_inv, pow_mul, ← inv_pow,
      ← inv_pow, groupPrimeCount, prod_pow_eq_pow_sum]
  unfold listWeight
  rw [hq]
  calc (∏ g, q₀ ^ primeCount (P g) n) * (q₀⁻¹ ^ (J + 1)) ^ Fintype.card ι *
        (listCount P C n : ℝ)
      ≤ (∏ g, q₀ ^ primeCount (P g) n) * (q₀⁻¹ ^ (J + 1)) ^ Fintype.card ι *
          ∏ g, (primeCount (P g) n : ℝ) ^ (unsharedSlots C g).card := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast listCount_le_prod P C n
    _ = ∏ g, (q₀⁻¹ ^ (J + 1) * (q₀ ^ primeCount (P g) n *
          (primeCount (P g) n : ℝ) ^ (unsharedSlots C g).card)) := by
        rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ]
        ring
    _ ≤ ∏ _g : ι, q₀⁻¹ ^ (J + 1) * listConst q₀ m₀ :=
        Finset.prod_le_prod₀ (fun g _ => by positivity) fun g _ =>
          mul_le_mul_of_nonneg_left (hgroup g) (by positivity)
    _ = _ := by rw [prod_const, card_univ]

omit [DecidableEq ι] in
/-- `T = ∏_g V_g^{-t_g} ≤ max(1, 1/v₋)^{(m₀+1) s_P}`. -/
lemma targetMass_le {P : ι → Finset ℕ} {vlo : ℝ} (hvlo : 0 < vlo)
    (hV : ∀ g, vlo ≤ harmonicMass (P g)) {C : ι → Finset (Fin J)} {m₀ : ℕ}
    (hC : ∀ g, (C g).card ≤ m₀) :
    targetMass P C ≤ (max 1 vlo⁻¹ ^ (m₀ + 1)) ^ Fintype.card ι := by
  unfold targetMass
  rw [← card_univ, ← prod_const]
  refine Finset.prod_le_prod₀ (fun g _ => pow_nonneg (inv_nonneg.2 (hvlo.trans_le (hV g)).le) _)
    fun g _ => ?_
  have ht : (unsharedSlots C g).card ≤ m₀ + 1 := by rw [card_unsharedSlots]; linarith [hC g]
  calc (harmonicMass (P g))⁻¹ ^ (unsharedSlots C g).card
      ≤ max 1 vlo⁻¹ ^ (unsharedSlots C g).card := by
        refine pow_le_pow_left₀ (inv_nonneg.2 (hvlo.trans_le (hV g)).le) ?_ _
        exact (inv_anti₀ hvlo (hV g)).trans (le_max_right _ _)
    _ ≤ max 1 vlo⁻¹ ^ (m₀ + 1) := pow_le_pow_right₀ (le_max_left _ _) ht

/-! ### Prime factors, masses and edges -/

omit [DecidableEq ι] in
/-- **U11.** `ω(n) log 2 ≤ log n` for `n ≥ 1`. -/
lemma groupPrimeCount_mul_log_two_le {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {n : ℕ} (hn : 1 ≤ n) :
    (groupPrimeCount P n : ℝ) * Real.log 2 ≤ Real.log n := by
  set S := (univ.biUnion P).filter (· ∣ n)
  have hcard : groupPrimeCount P n = S.card := by
    unfold groupPrimeCount primeCount
    rw [show S = univ.biUnion fun g => (P g).filter (· ∣ n) from filter_biUnion _ _ _,
      card_biUnion]
    intro g _ h _ hgh
    exact disjoint_filter_filter (hdisj g h hgh)
  have hprime' : ∀ p ∈ S, p.Prime := fun p hp => by
    obtain ⟨g, -, hpg⟩ := mem_biUnion.1 (mem_filter.1 hp).1
    exact hprime g p hpg
  have hdvd : ∏ p ∈ S, p ∣ n :=
    prod_primes_dvd n (fun p hp => (hprime' p hp).prime) fun p hp => (mem_filter.1 hp).2
  have hle : 2 ^ S.card ≤ n := by
    calc 2 ^ S.card ≤ ∏ p ∈ S, p :=
          pow_card_le_prod S (fun p => p) 2 fun p hp => (hprime' p hp).two_le
      _ ≤ n := Nat.le_of_dvd (by omega) hdvd
  have hle' : ((2 : ℕ) : ℝ) ^ S.card ≤ n := by exact_mod_cast hle
  rw [hcard, ← Real.log_pow]
  exact Real.log_le_log (by positivity) (by exact_mod_cast hle')

/-- **U10.** The edge product `D_R D_C` is at most `E^{J s_P}` when every group prime is at most
`E`. -/
lemma sharedProduct_mul_slotProduct_le {P : ι → Finset ℕ} {E : ℝ} (hE : 1 ≤ E)
    (hP : ∀ g, ∀ p ∈ P g, (p : ℝ) ≤ E) {C : ι → Finset (Fin J)} {s a : ι → Fin J → ℕ}
    (hs : s ∈ auxLabels P (sharedSlots C)) (ha : a ∈ auxLabels P C) :
    (sharedProduct C s : ℝ) * slotProduct C a ≤ E ^ (J * Fintype.card ι) := by
  have ha' : ∀ g, ∀ i ∈ C g, a g i ∈ P g := fun g i hi => by
    have := mem_auxLabels.1 ha g i
    rwa [ite_eq_left hi] at this
  unfold sharedProduct slotProduct
  push_cast
  rw [← prod_mul_distrib, pow_mul, ← card_univ, ← prod_const]
  refine Finset.prod_le_prod₀ (fun g _ => by positivity) fun g _ => ?_
  have hJ : (sharedSlots C g).card + (C g).card = J := by
    rw [sharedSlots, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have : (C g).card ≤ J := by simpa using card_le_univ (C g)
    omega
  rw [show E ^ J = E ^ (sharedSlots C g).card * E ^ (C g).card by rw [← pow_add, hJ],
    ← prod_const, ← prod_const]
  exact mul_le_mul (Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi =>
      hP g _ (mem_of_mem_sharedLabels hs (by simpa [sharedSlots] using hi)))
    (Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => hP g _ (ha' g i hi))
    (by positivity) (prod_nonneg fun _ _ => by positivity)

/-! ### Lemma G5 at scale `x` -/

/-- The eventual conditions on `x`: `L ≥ 10`, `A T ≤ L`, `log κ + J A T L^{0.46} ≤ L` and
`K₁ ≤ L`. -/
lemma eventually_restore_scale (A κ K₁ : ℝ) (J : ℕ) :
    ∀ᶠ x : ℝ in atTop, 10 ≤ Real.log x ∧ A * Real.log (Real.log x) ≤ Real.log x ∧
      Real.log κ + J * A * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤ Real.log x ∧
      K₁ ≤ Real.log x := by
  set c := |J * A| * 25 + |Real.log κ| + |A| * 25 + 1
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 10,
    Real.tendsto_log_atTop.eventually_ge_atTop (c ^ 2),
    Real.tendsto_log_atTop.eventually_ge_atTop K₁] with x h₁ h₂ h₃
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hc1 : 1 ≤ c := by
    have := abs_nonneg (J * A); have := abs_nonneg (Real.log κ); have := abs_nonneg A
    simp only [c]; linarith
  -- `T ≤ 25 L^{0.04}` and `L^{1/2} ≥ c`
  have hT : Real.log L ≤ 25 * L ^ (0.04 : ℝ) := by
    have := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 0.04)
    calc Real.log L ≤ L ^ (0.04 : ℝ) / 0.04 := this
      _ = 25 * L ^ (0.04 : ℝ) := by norm_num [div_eq_mul_inv, mul_comm]
  have hT0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hsq : c ≤ L ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by linarith) hL0.le]
    exact h₂
  have hhalf : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
    rw [← Real.rpow_add hL0]; norm_num
  have h04 : L ^ (0.04 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h50 : L ^ (0.04 : ℝ) * L ^ (0.46 : ℝ) = L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hhalf1 : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  refine ⟨h₁, ?_, ?_, h₃⟩
  · calc A * Real.log L ≤ |A| * Real.log L := mul_le_mul_of_nonneg_right (le_abs_self A) hT0
      _ ≤ |A| * (25 * L ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hT.trans (by linarith)) (abs_nonneg A)
      _ ≤ c * L ^ (1 / 2 : ℝ) := by
          have : |A| * 25 ≤ c := by
            have := abs_nonneg (J * A); have := abs_nonneg (Real.log κ); simp only [c]; linarith
          nlinarith [Real.rpow_nonneg hL0.le (1 / 2 : ℝ)]
      _ ≤ L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hL0.le _)
      _ = L := hhalf
  · have hJA : J * A * Real.log L * L ^ (0.46 : ℝ) ≤ |J * A| * 25 * L ^ (1 / 2 : ℝ) := by
      calc J * A * Real.log L * L ^ (0.46 : ℝ)
          ≤ |J * A| * Real.log L * L ^ (0.46 : ℝ) := by
            gcongr
            exact le_abs_self _
        _ ≤ |J * A| * (25 * L ^ (0.04 : ℝ)) * L ^ (0.46 : ℝ) := by gcongr
        _ = |J * A| * 25 * L ^ (1 / 2 : ℝ) := by rw [← h50]; ring
    have hκ' : Real.log κ ≤ |Real.log κ| * L ^ (1 / 2 : ℝ) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hhalf1)
    calc Real.log κ + J * A * Real.log L * L ^ (0.46 : ℝ)
        ≤ (|J * A| * 25 + |Real.log κ|) * L ^ (1 / 2 : ℝ) := by nlinarith
      _ ≤ c * L ^ (1 / 2 : ℝ) := by
          gcongr
          have := abs_nonneg A
          simp only [c]; linarith
      _ ≤ L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hL0.le _)
      _ = L := hhalf

/-- **U10 at scale `x`.** `D_R D_C ≤ x/κ` once `log κ + J A T L^{0.46} ≤ L` and
`s_P ≤ A T`. -/
lemma sharedProduct_mul_slotProduct_le_of_scale {x κ A : ℝ} (hx0 : 0 < x) (hκ : 1 < κ)
    {P : ι → Finset ℕ} (hP : ∀ g, ∀ p ∈ P g, (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)))
    (hs : (Fintype.card ι : ℝ) ≤ A * Real.log (Real.log x))
    (hκT : Real.log κ + J * A * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤
      Real.log x)
    {C : ι → Finset (Fin J)} {s a : ι → Fin J → ℕ} (hs' : s ∈ auxLabels P (sharedSlots C))
    (ha : a ∈ auxLabels P C) :
    (sharedProduct C s : ℝ) * slotProduct C a ≤ x / κ := by
  set L := Real.log x
  set E := Real.exp (L ^ (0.46 : ℝ))
  have hL46 : 0 ≤ L ^ (0.46 : ℝ) := by
    rcases le_or_gt 0 L with hL | hL
    · exact Real.rpow_nonneg hL _
    · rw [Real.rpow_def_of_neg hL]
      exact mul_nonneg (Real.exp_pos _).le (by
        have := Real.cos_nonneg_of_mem_Icc (x := 0.46 * Real.pi) ⟨by nlinarith [Real.pi_pos],
          by nlinarith [Real.pi_pos]⟩
        exact this)
  have hE1 : 1 ≤ E := Real.one_le_exp hL46
  have hEJ : κ * E ^ (J * Fintype.card ι) ≤ x := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < κ), ← Real.exp_nat_mul, ← Real.exp_add,
      ← Real.exp_log hx0, Real.exp_le_exp]
    have : ((J * Fintype.card ι : ℕ) : ℝ) * L ^ (0.46 : ℝ) ≤
        J * A * Real.log L * L ^ (0.46 : ℝ) := by
      push_cast
      rw [mul_assoc (J : ℝ) A]
      gcongr
    linarith
  rw [le_div_iff₀ (by linarith)]
  have := sharedProduct_mul_slotProduct_le hE1 hP hs' ha
  nlinarith

omit [DecidableEq ι] in
/-- **U11 at scale `x`.** `ω(m) ≤ 3L` for `1 ≤ m ≤ 2x²`, once `L ≥ 10`. -/
lemma groupPrimeCount_le_of_scale {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {x : ℝ} (hx0 : 0 < x)
    (hL10 : 10 ≤ Real.log x) {m : ℕ} (hm1 : 1 ≤ m) (hm : (m : ℝ) ≤ 2 * x ^ 2) :
    (groupPrimeCount P m : ℝ) ≤ 3 * Real.log x := by
  have h := groupPrimeCount_mul_log_two_le hprime hdisj hm1
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlm : Real.log m ≤ Real.log 2 + 2 * Real.log x := by
    calc Real.log m ≤ Real.log (2 * x ^ 2) := Real.log_le_log (by exact_mod_cast hm1) hm
      _ = Real.log 2 + 2 * Real.log x := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
  have h0 := Nat.cast_nonneg (α := ℝ) (groupPrimeCount P m)
  nlinarith

/-- The final arithmetic of G5:
`2 (T² κ_K M₀ L L^{B₀} Λ²) H (e^{-L^{0.27}}/v₋ · Z) ≤ κ_K L^{2c_T + 2c_Λ + B₀ + 4} e^{-L^{0.27}}`
for `T ≤ L^{c_T}`, `Λ ≤ L^{c_Λ}`, `H ≤ 3L`, `Z ≤ Q L` and `6 |M₀| Q / v₋ ≤ L`. -/
lemma restore_final_le {L κK M₀ B₀ cT cΛ vlo Q Tm Λ H Z Y : ℝ} (hL : 1 ≤ L) (hκK : 0 ≤ κK)
    (hM₀ : 0 ≤ M₀) (hvlo : 0 < vlo) (hY : 0 < Y) (hTm0 : 0 ≤ Tm) (hTm : Tm ≤ L ^ cT)
    (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L ^ cΛ) (hH0 : 0 ≤ H) (hH : H ≤ 3 * L) (hZ0 : 0 ≤ Z)
    (hZ : Z ≤ Q * L) (hQ0 : 0 ≤ Q) (hK₁ : 6 * |M₀| * Q / vlo ≤ L) :
    2 * (Tm ^ 2 * κK * M₀ * L * L ^ B₀ * Λ ^ 2) * H * (Y / vlo * Z) ≤
      κK * L ^ (2 * cT + 2 * cΛ + B₀ + 4) * Y := by
  have hL0 : 0 < L := by linarith
  have hQ : 0 ≤ Q * L := hZ0.trans hZ
  have hX : Tm ^ 2 * κK * M₀ * L * L ^ B₀ * Λ ^ 2 ≤
      (L ^ cT) ^ 2 * κK * M₀ * L * L ^ B₀ * (L ^ cΛ) ^ 2 := by
    gcongr
  have hX'0 : 0 ≤ (L ^ cT) ^ 2 * κK * M₀ * L * L ^ B₀ * (L ^ cΛ) ^ 2 := by positivity
  have hpow : ∀ c : ℝ, L ^ (2 * cT + 2 * cΛ + B₀ + c) =
      L ^ cT * L ^ cT * (L ^ cΛ * L ^ cΛ) * L ^ B₀ * L ^ c := fun c => by
    rw [show 2 * cT + 2 * cΛ + B₀ + c = cT + cT + (cΛ + cΛ) + B₀ + c by ring]
    simp only [Real.rpow_add hL0]
  calc _ ≤ 2 * ((L ^ cT) ^ 2 * κK * M₀ * L * L ^ B₀ * (L ^ cΛ) ^ 2) * (3 * L) *
        (Y / vlo * (Q * L)) := by
        gcongr
    _ = κK * Y * (L ^ (2 * cT + 2 * cΛ + B₀ + 3) * (6 * M₀ * Q / vlo)) := by
        rw [hpow, show (3 : ℝ) = 1 + 1 + 1 by norm_num]
        simp only [Real.rpow_add hL0, Real.rpow_one]
        field_simp
        ring
    _ ≤ κK * Y * (L ^ (2 * cT + 2 * cΛ + B₀ + 3) * L) := by
        gcongr
        refine le_trans ?_ hK₁
        have := le_abs_self M₀
        gcongr
    _ = κK * L ^ (2 * cT + 2 * cΛ + B₀ + 4) * Y := by
        rw [hpow, hpow, show (4 : ℝ) = 3 + 1 by norm_num, Real.rpow_add hL0 3 1,
          Real.rpow_one]
        ring

/-- The groups of (6.1) are nonempty, so shared labels exist. -/
lemma sharedLabels_nonempty {P : ι → Finset ℕ} (hV : ∀ g, 0 < harmonicMass (P g))
    (C : ι → Finset (Fin J)) : (auxLabels P (sharedSlots C)).Nonempty := by
  have hne : ∀ g, (P g).Nonempty := fun g => by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hV g
    rw [h, harmonicMass, sum_empty] at this
    exact lt_irrefl 0 this
  refine ⟨fun g i => if i ∈ C g then 1 else (hne g).choose, mem_auxLabels.2 fun g i => ?_⟩
  by_cases hi : i ∈ C g
  · rw [ite_eq_right (by simp [sharedSlots, hi]), ite_eq_left hi]
    exact mem_singleton_self 1
  · rw [ite_eq_left (by simp [sharedSlots, hi]), ite_eq_right hi]
    exact (hne g).choose_spec

/-- The support condition of G5 from `D_R D_C ≤ x/κ`. -/
lemma sharedProduct_mul_le_floor {x κ : ℝ} (hx0 : 0 < x) (hκ : 1 < κ) {Ψ : ℝ → ℝ}
    (hsupp : ∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) {DR DC w : ℕ}
    (hD : (DR : ℝ) * DC ≤ x / κ) (hψ : Ψ (w / (x * DC)) ≠ 0) : DR * w ≤ ⌊x ^ 2⌋₊ := by
  have hDC0 : (0 : ℝ) < DC := by
    by_contra h
    have : (DC : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, mul_zero, div_zero] at hψ
    have := (hsupp 0 hψ).1
    have : (0 : ℝ) < κ⁻¹ := by positivity
    linarith
  have hw := (hsupp _ hψ).2
  rw [div_le_iff₀ (by positivity)] at hw
  refine Nat.le_floor ?_
  push_cast
  calc (DR : ℝ) * w ≤ DR * (κ * (x * DC)) := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
    _ = κ * x * ((DR : ℝ) * DC) := by ring
    _ ≤ κ * x * (x / κ) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = x ^ 2 := by field_simp

/-- **Lemma G5 at a large scale `x`.** The explicit bound of `norm_physSum_sub_stripSum_le`,
evaluated: the error is `κ_K L^{2c_T + 2c_Λ + B₀ + 4} e^{-L^{0.27}}`. -/
theorem norm_physSum_sub_stripSum_le_of_scale {q₀ c₀ C₀ vlo vhi B₀ κ M₀ x : ℝ} (hq₀ : 0 < q₀)
    (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo) (hκ : 1 < κ) {m₀ : ℕ} (hx0 : 0 < x)
    (hL10 : 10 ≤ Real.log x)
    (hAT : 2 * |C₀| * Real.log (Real.log x) ≤ Real.log x)
    (hκT : Real.log κ + J * (2 * |C₀|) * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤
      Real.log x)
    (hK₁ : 6 * |M₀| * (J ^ 2 + 6 * J + J * m₀ + 3 * m₀) / vlo ≤ Real.log x)
    {P : ι → Finset ℕ} {big : Finset ι} (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big)
    {C : ι → Finset (Fin J)} (hC : ∀ g, (C g).card ≤ m₀)
    {K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ} {κK : ℝ}
    (hK : ∀ p p' a, ‖K p p' a‖ ≤ κK) (hKpad : ∀ p p' a, K p p' a = K (pad C p) (pad C p') a)
    {F G : ℕ → ℝ} {Ψ : ℝ → ℝ} (hF : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ 3 → |F n| ≤ Real.log x)
    (hFinv : ∀ p ∈ Finset.univ.biUnion P, ∀ n, F (p * n) = F n)
    (hG : CoreAdmissible B₀ x P G) (hΨ : ∀ y, |Ψ y| ≤ M₀)
    (hsupp : ∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) :
    ‖physSum x q₀ P C K F G Ψ - stripSum x q₀ P C K F G Ψ‖ ≤
      κK * Real.log x ^ (2 * (2 * |C₀| * Real.log (max 1 vlo⁻¹ ^ (m₀ + 1))) +
        2 * (2 * |C₀| * Real.log (q₀⁻¹ ^ (J + 1) * listConst q₀ m₀)) + B₀ + 4) *
        Real.exp (-Real.log x ^ (0.27 : ℝ)) := by
  have hL1 : 1 ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hx1 : 1 ≤ x := by
    by_contra h
    have : Real.log x ≤ 0 := Real.log_nonpos hx0.le (by linarith)
    linarith
  obtain ⟨hdisj, hP, hV, hs⟩ := groupAdmissible_facts hL1 hadm
  have hprime : ∀ g, ∀ p ∈ P g, p.Prime := fun g p hp => (hP g p hp).1
  have hV0 : ∀ g, 0 < harmonicMass (P g) := fun g => hvlo.trans_le (hV g)
  have hT0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hs' : (Fintype.card ι : ℝ) ≤ 2 * |C₀| * Real.log (Real.log x) := by
    refine hs.trans (mul_le_mul_of_nonneg_right ?_ hT0)
    linarith [le_abs_self C₀]
  have hsL : (Fintype.card ι : ℝ) ≤ Real.log x := hs'.trans hAT
  have hedge : ∀ s' ∈ auxLabels P (sharedSlots C), ∀ a ∈ auxLabels P C,
      (sharedProduct C s' : ℝ) * slotProduct C a ≤ x / κ := fun s' hs₁ a ha =>
    sharedProduct_mul_slotProduct_le_of_scale hx0 hκ (fun g p hp => (hP g p hp).2.2) hs' hκT
      hs₁ ha
  have hDC : ∀ a ∈ auxLabels P C, (slotProduct C a : ℝ) ≤ x / κ := by
    intro a ha
    obtain ⟨s₀, hs₀⟩ := sharedLabels_nonempty hV0 C
    have h1 : (1 : ℝ) ≤ sharedProduct C s₀ := by
      exact_mod_cast sharedProduct_pos hprime hs₀
    have := hedge s₀ hs₀ a ha
    have h0 : (0 : ℝ) ≤ slotProduct C a := Nat.cast_nonneg _
    nlinarith
  have hxκ : x / κ ≤ x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hF' : ∀ n, 1 ≤ n → n ≤ ⌊x ^ 2⌋₊ → |F n| ≤ Real.log x := fun n hn hnN => by
    refine hF n hn ?_
    have : (n : ℝ) ≤ x ^ 2 := (Nat.le_floor_iff (by positivity)).1 hnN
    nlinarith
  have hG' : ∀ n, |G n| ≤ Real.log x ^ B₀ := fun n => by
    rw [abs_of_nonneg (hG.2 n).1]
    exact (hG.2 n).2
  have hμ : ∀ g, ∀ p ∈ P g, (harmonicMass (P g) * p)⁻¹ ≤
      Real.exp (-Real.log x ^ (0.27 : ℝ)) / vlo := by
    intro g p hp
    have hp₁ := (hP g p hp).2.1
    rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) (mul_le_mul (hV g) hp₁ (Real.exp_pos _).le (hV0 g).le)
      |>.trans_eq (by ring)
  have hΩ₁ : ∀ w ∈ Icc 1 ⌊x ^ 2⌋₊, (groupPrimeCount P w : ℝ) ≤ 3 * Real.log x := by
    intro w hw
    obtain ⟨hw₁, hwN⟩ := mem_Icc.1 hw
    have hw' : (w : ℝ) ≤ x ^ 2 := (Nat.le_floor_iff (by positivity)).1 hwN
    exact groupPrimeCount_le_of_scale hprime hdisj hx0 hL10 hw₁ (by nlinarith)
  have hΩ₂ : ∀ a ∈ auxLabels P C, ∀ w ∈ Icc 1 ⌊x ^ 2⌋₊,
      (groupPrimeCount P (w + slotProduct C a) : ℝ) ≤ 3 * Real.log x := by
    intro a ha w hw
    obtain ⟨hw₁, hwN⟩ := mem_Icc.1 hw
    have hw' : (w : ℝ) ≤ x ^ 2 := (Nat.le_floor_iff (by positivity)).1 hwN
    refine groupPrimeCount_le_of_scale hprime hdisj hx0 hL10 (by omega) ?_
    push_cast
    linarith [hDC a ha]
  have hsupp' : ∀ a ∈ auxLabels P C, ∀ s' ∈ auxLabels P (sharedSlots C), ∀ w : ℕ,
      Ψ (w / (x * slotProduct C a)) ≠ 0 → sharedProduct C s' * w ≤ ⌊x ^ 2⌋₊ :=
    fun a ha s' hs₁ w hψ => sharedProduct_mul_le_floor hx0 hκ hsupp (hedge s' hs₁ a ha) hψ
  have hmain := norm_physSum_sub_stripSum_le hprime hdisj hV0 hq₀ hq₀₁.le hC hK hKpad hΨ
    hL0.le hF' hFinv hG' (coreAdmissible_mul_prime hG hprime)
    (by positivity : (0 : ℝ) ≤ Real.exp (-Real.log x ^ (0.27 : ℝ)) / vlo) hμ
    (listWeight_le hq₀ hq₀₁ hC) hΩ₁ hΩ₂ hsupp'
  refine hmain.trans ?_
  have hbΛ : 1 ≤ q₀⁻¹ ^ (J + 1) * listConst q₀ m₀ := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (one_le_inv_iff₀.2 ⟨hq₀, hq₀₁.le⟩)) (one_le_listConst q₀ m₀)
  have hbT : 1 ≤ max 1 vlo⁻¹ ^ (m₀ + 1) := one_le_pow₀ (le_max_left _ _)
  have hκK : 0 ≤ κK := (norm_nonneg _).trans (hK (fun _ _ => 0) (fun _ _ => 0) fun _ _ => 0)
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (hΨ 0)
  have hharm : ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊, (1 : ℝ) / w ≤ 3 * Real.log x := by
    have h := OneSided.sum_Icc_inv_le ⌊x ^ 2⌋₊
    simp only [one_div]
    have hN : Real.log ⌊x ^ 2⌋₊ ≤ 2 * Real.log x := by
      rcases Nat.eq_zero_or_pos ⌊x ^ 2⌋₊ with hN | hN
      · rw [hN, Nat.cast_zero, Real.log_zero]; linarith
      · calc Real.log ⌊x ^ 2⌋₊ ≤ Real.log (x ^ 2) :=
            Real.log_le_log (by exact_mod_cast hN) (Nat.floor_le (by positivity))
          _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
    linarith
  have hcount : (Fintype.card ι : ℝ) * J ^ 2 +
      J * (2 * (3 * Real.log x) + m₀ * Fintype.card ι) + m₀ * (3 * Real.log x) ≤
      (J ^ 2 + 6 * J + J * m₀ + 3 * m₀) * Real.log x := by
    have h0 : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hsL (sq_nonneg (J : ℝ)),
      mul_le_mul_of_nonneg_left hsL (mul_nonneg hJ hm)]
  exact restore_final_le hL1 hκK hM₀ hvlo (Real.exp_pos _) (targetMass_nonneg hV0 C)
    ((targetMass_le hvlo hV hC).trans (pow_le_rpow_mul_log hbT hL0 hs'))
    (pow_nonneg (by linarith) _) (pow_le_rpow_mul_log hbΛ hL0 hs')
    (sum_nonneg fun w _ => by positivity) hharm (by positivity) hcount (by positivity) hK₁

/-- **Lemma G5 at scale `x`.** For every `m₀, J` there is `C_r` such that, eventually, for
groups as in (6.1), every pattern `C` with `|C g| ≤ m₀`, every kernel `|K| ≤ κ_K` depending
only on the unshared parts, every `F` with `|F| ≤ L` on `[1, x³]` invariant under the active
primes, every clipped core and every `Ψ` with `|Ψ| ≤ M₀` supported in `[κ⁻¹, κ]`, the cutoff
pairing is the stripped correlation up to `κ_K L^{C_r} e^{-L^{0.27}}`. -/
theorem exists_eventually_norm_physSum_sub_stripSum_le (q₀ c₀ C₀ vlo vhi B₀ κ M₀ : ℝ)
    (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo) (hκ : 1 < κ) (m₀ J : ℕ) :
    ∃ Cr : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (C : ι → Finset (Fin J)), (∀ g, (C g).card ≤ m₀) →
        ∀ (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
          (κK : ℝ), (∀ p p' a, ‖K p p' a‖ ≤ κK) →
          (∀ p p' a, K p p' a = K (pad C p) (pad C p') a) →
        ∀ (F G : ℕ → ℝ) (Ψ : ℝ → ℝ),
          (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x ^ 3 → |F n| ≤ Real.log x) →
          (∀ p ∈ Finset.univ.biUnion P, ∀ n, F (p * n) = F n) →
          CoreAdmissible B₀ x P G → (∀ y, |Ψ y| ≤ M₀) → (∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) →
          ‖physSum x q₀ P C K F G Ψ - stripSum x q₀ P C K F G Ψ‖ ≤
            κK * Real.log x ^ Cr * Real.exp (-Real.log x ^ (0.27 : ℝ)) := by
  refine ⟨2 * (2 * |C₀| * Real.log (max 1 vlo⁻¹ ^ (m₀ + 1))) +
    2 * (2 * |C₀| * Real.log (q₀⁻¹ ^ (J + 1) * listConst q₀ m₀)) + B₀ + 4, ?_⟩
  filter_upwards [eventually_restore_scale (2 * |C₀|) κ
      (6 * |M₀| * (J ^ 2 + 6 * J + J * m₀ + 3 * m₀) / vlo) J, eventually_gt_atTop 0]
    with x ⟨hL10, hAT, hκT, hK₁⟩ hx0 ι _ _ P big hadm C hC K κK hK hKpad F G Ψ hF hFinv hG
      hΨ hsupp
  exact norm_physSum_sub_stripSum_le_of_scale hq₀ hq₀₁ hvlo hκ hx0 hL10 hAT hκT hK₁ hadm hC
    hK hKpad hF hFinv hG hΨ hsupp

end Restore

end Erdos408.TwoSided
