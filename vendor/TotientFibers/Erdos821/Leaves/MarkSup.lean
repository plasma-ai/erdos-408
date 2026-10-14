import Mathlib
import Erdos821.Blueprint.Analytic

open scoped BigOperators
open Filter Topology

attribute [local instance] Classical.propDecidable

namespace Erdos821.GraphLemmas

theorem tendsto_pow_mul_geometric2 (k : ℕ) (r : ℝ) (hr : ‖r‖ < 1) :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ k * r ^ n)) atTop (𝓝 0) := by
  have hsumm : Summable (fun n : ℕ => ((n : ℝ) ^ k * r ^ n)) :=
    summable_pow_mul_geometric_of_norm_lt_one k hr
  have hco : Tendsto (fun n : ℕ => ((n : ℝ) ^ k * r ^ n)) Filter.cofinite (𝓝 0) :=
    hsumm.tendsto_cofinite_zero
  rwa [Nat.cofinite_eq_atTop] at hco

theorem bounded_pow_mul_geometric2 (k : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C, ∀ n : ℕ, ((n : ℝ) ^ k * r ^ n) ≤ C := by
  have hr_norm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have htend := tendsto_pow_mul_geometric2 k r hr_norm
  have hbdd : Bornology.IsBounded (Set.range (fun n : ℕ => ((n : ℝ) ^ k * r ^ n))) :=
    Metric.isBounded_range_of_tendsto _ htend
  rw [Metric.isBounded_range_iff] at hbdd
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨C + (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ)), ?_⟩
  intro n
  have hdist := hC n 0
  have hle : ((n : ℝ) ^ k * r ^ n) - (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ)) ≤ C := by
    calc ((n : ℝ) ^ k * r ^ n) - (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ))
        ≤ |((n : ℝ) ^ k * r ^ n) - (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ))| := le_abs_self _
      _ = dist (((n : ℝ) ^ k * r ^ n)) (((0 : ℕ) : ℝ) ^ k * r ^ (0 : ℕ)) := by
          rw [Real.dist_eq]
      _ ≤ C := hdist
  linarith

-- Per-group uniform bound
theorem per_group_bound (q vmin : ℝ) (hq : 0 < q) (hq1 : q < 1) (hv : 0 < vmin)
    (tMax : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ (t w : ℕ) (mass : ℝ), t ≤ tMax → vmin ≤ mass →
      q ^ (((w : ℕ) : ℤ) - (t : ℤ)) * mass⁻¹ ^ t * ((w : ℕ) : ℝ) ^ t ≤ K := by
  have hq0 : 0 ≤ q := le_of_lt hq
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have hr0 : (0:ℝ) ≤ q := le_of_lt hq
  -- C_t for w^t * q^w bounds
  choose C hC using fun k => bounded_pow_mul_geometric2 k q hr0 hq1
  -- B_max for q^{-t} * mass⁻¹^t bounds (uniform in t,mass)
  -- q^{-t} = (1/q)^t ≤ (1/q)^tMax since 1/q ≥ 1 and t ≤ tMax
  have hqinv_ge : (1:ℝ) ≤ 1 / q := by
    rw [le_div_iff₀ hq, one_mul]
    exact hq1.le
  -- B_max uniform bound for (q^t)⁻¹ * mass⁻¹^t
  have hBmax_exists : ∃ Bmax, 0 ≤ Bmax ∧ ∀ (t : ℕ) (mass : ℝ),
      t ≤ tMax → vmin ≤ mass → (q ^ t)⁻¹ * mass⁻¹ ^ t ≤ Bmax := by
    refine ⟨(1 / q) ^ tMax * max 1 ((vmin⁻¹) ^ tMax),
      mul_nonneg (pow_nonneg (by positivity) _) (le_trans zero_le_one (le_max_left _ _)), ?_⟩
    intro t mass ht hmass
    have hmass_pos : 0 < mass := lt_of_lt_of_le hv hmass
    have hq_pow_pos : 0 < q ^ t := pow_pos hq t
    -- (q^t)⁻¹ = (1/q)^t ≤ (1/q)^tMax
    have hqinv_eq : ((q ^ t)⁻¹) = (1 / q) ^ t := by
      rw [one_div, inv_pow]
    have hqinv_le : ((q ^ t)⁻¹) ≤ (1 / q) ^ tMax := by
      rw [hqinv_eq]
      exact pow_le_pow_right₀ hqinv_ge ht
    -- mass⁻¹^t ≤ max 1 (vmin⁻¹)^tMax
    have hmass_inv_le : mass⁻¹ ^ t ≤ max 1 ((vmin⁻¹) ^ tMax) := by
      have hmass_inv_le_vmin : mass⁻¹ ≤ vmin⁻¹ := by
        rw [inv_le_inv₀ hmass_pos hv]
        exact hmass
      by_cases hge : 1 ≤ mass⁻¹
      · have hle1 : mass⁻¹ ^ t ≤ vmin⁻¹ ^ t :=
          pow_le_pow_left₀ (le_of_lt (inv_pos.mpr hmass_pos)) hmass_inv_le_vmin t
        have hle2 : vmin⁻¹ ^ t ≤ vmin⁻¹ ^ tMax := by
          have h1le : 1 ≤ vmin⁻¹ := le_trans hge hmass_inv_le_vmin
          exact pow_le_pow_right₀ h1le ht
        calc mass⁻¹ ^ t ≤ vmin⁻¹ ^ t := hle1
          _ ≤ vmin⁻¹ ^ tMax := hle2
          _ ≤ max 1 (vmin⁻¹ ^ tMax) := le_max_right _ _
      · have hlt : mass⁻¹ < 1 := lt_of_not_ge hge
        have h0le : 0 ≤ mass⁻¹ := le_of_lt (inv_pos.mpr hmass_pos)
        have hle1 : mass⁻¹ ^ t ≤ 1 := pow_le_one₀ h0le (le_of_lt hlt)
        calc mass⁻¹ ^ t ≤ 1 := hle1
          _ ≤ max 1 (vmin⁻¹ ^ tMax) := le_max_left _ _
    have hmass_nonneg : 0 ≤ mass⁻¹ ^ t :=
      pow_nonneg (le_of_lt (inv_pos.mpr hmass_pos)) t
    have hqmax_nonneg : 0 ≤ (1 / q) ^ tMax :=
      pow_nonneg (by positivity) tMax
    calc ((q ^ t)⁻¹) * mass⁻¹ ^ t
        ≤ ((1 / q) ^ tMax) * (max 1 ((vmin⁻¹) ^ tMax)) := by
          exact mul_le_mul hqinv_le hmass_inv_le hmass_nonneg hqmax_nonneg
      _ = (1 / q) ^ tMax * max 1 ((vmin⁻¹) ^ tMax) := rfl
  obtain ⟨Bmax, hBmax_nonneg, hBmax⟩ := hBmax_exists
  -- C_t nonnegativity and sup via sum
  have hC_nonneg : ∀ k, 0 ≤ C k := by
    intro k
    have h0 := hC k 0
    have hterm_nonneg : 0 ≤ (((0 : ℕ) : ℝ) ^ k * q ^ (0 : ℕ)) := by
      positivity
    linarith
  have hBmax_mul_nonneg : ∀ k, 0 ≤ C k * Bmax :=
    fun k => mul_nonneg (hC_nonneg k) hBmax_nonneg
  refine ⟨∑ s ∈ Finset.range (tMax + 1), C s * Bmax,
    Finset.sum_nonneg (fun s _ => hBmax_mul_nonneg s), ?_⟩
  intro t w mass ht hmass
  have hmass_pos : 0 < mass := lt_of_lt_of_le hv hmass
  -- split q^(w-t)
  have hq_zpow : q ^ (((w : ℕ) : ℤ) - (t : ℤ)) = (q ^ w) * ((q ^ t)⁻¹) := by
    rw [zpow_sub₀ hq_ne, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have hA_le : (((w : ℕ) : ℝ) ^ t * q ^ w) ≤ C t := hC t w
  have hA_nonneg : 0 ≤ (((w : ℕ) : ℝ) ^ t * q ^ w) := by
    positivity
  have hB_le : (q ^ t)⁻¹ * mass⁻¹ ^ t ≤ Bmax := hBmax t mass ht hmass
  have hB_nonneg : 0 ≤ (q ^ t)⁻¹ * mass⁻¹ ^ t := by
    positivity
  have hC_nonneg_t : 0 ≤ C t := hC_nonneg t
  have hF_eq : q ^ (((w : ℕ) : ℤ) - (t : ℤ)) * mass⁻¹ ^ t * ((w : ℕ) : ℝ) ^ t
      = ((((w : ℕ) : ℝ) ^ t * q ^ w)) * (((q ^ t)⁻¹ * mass⁻¹ ^ t)) := by
    rw [hq_zpow]
    ring
  have hF_le : q ^ (((w : ℕ) : ℤ) - (t : ℤ)) * mass⁻¹ ^ t * ((w : ℕ) : ℝ) ^ t
      ≤ C t * Bmax := by
    rw [hF_eq]
    exact mul_le_mul hA_le hB_le hB_nonneg hC_nonneg_t
  have hmem : t ∈ Finset.range (tMax + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ht)
  have hterm_nonneg : ∀ s ∈ Finset.range (tMax + 1), 0 ≤ C s * Bmax :=
    fun s _ => hBmax_mul_nonneg s
  calc q ^ (((w : ℕ) : ℤ) - (t : ℤ)) * mass⁻¹ ^ t * ((w : ℕ) : ℝ) ^ t
      ≤ C t * Bmax := hF_le
    _ ≤ ∑ s ∈ Finset.range (tMax + 1), C s * Bmax :=
        Finset.single_le_sum hterm_nonneg hmem

variable (G : Erdos821.Blueprint.Analytic.PrimeGroups) (t : Fin G.size → ℕ) (n : ℕ)

-- Per-group dividing subtype card
theorem card_div_label2 (g : Fin G.size) :
    Fintype.card {p : Erdos821.Blueprint.Analytic.Label G g // p.val ∣ n}
    = Erdos821.Blueprint.Analytic.omegaGroup G g n := by
  have hequiv : {p : Erdos821.Blueprint.Analytic.Label G g // p.val ∣ n}
      ≃ ↥((G.primes g).filter (fun p => p ∣ n)) := {
    toFun := fun p => ⟨p.val.val, Finset.mem_filter.mpr ⟨p.val.property, p.property⟩⟩
    invFun := fun p => ⟨⟨p.val, (Finset.mem_filter.mp p.property).1⟩,
      (Finset.mem_filter.mp p.property).2⟩
    left_inv := fun p => by
      obtain ⟨⟨pv, hmem⟩, hdvd⟩ := p
      rfl
    right_inv := fun p => by
      obtain ⟨pv, hmem⟩ := p
      rfl
  }
  rw [Fintype.card_congr hequiv, Fintype.card_coe]
  rfl

-- All-dividing Pi type
abbrev AllDiv := ∀ g : Fin G.size, ∀ _ : Fin (t g),
  {p : Erdos821.Blueprint.Analytic.Label G g // p.val ∣ n}

-- Its card is ∏ w^t
theorem card_allDiv :
    Fintype.card (AllDiv G t n) = ∏ g, (Erdos821.Blueprint.Analytic.omegaGroup G g n) ^ (t g) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro g _
  rw [Fintype.card_pi]
  simp [Finset.prod_const, Finset.card_univ, card_div_label2]

end Erdos821.GraphLemmas

namespace Erdos821.Blueprint.Analytic

theorem mark_sup (P : Geometry) (tmax : ℕ) :
    ∃ C : ℝ, ∀ᶠ x in Filter.atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ (t : Fin G.size → ℕ) (b : Tuple G t → ℂ) (B : ℝ),
      (∀ g, t g ≤ tmax) → 0 ≤ B → (∀ z, ‖b z‖ ≤ B) →
      ∀ n : ℕ, ‖weightedMarks G P.q t b n‖ ≤ B * L x ^ C := by
  -- per-group K
  obtain ⟨K, hK_nonneg, hK⟩ := Erdos821.GraphLemmas.per_group_bound
    P.q P.vmin P.damping.1 P.damping.2 P.positive.2.2.1 tmax
  -- K' = max 1 K, C = 2*C₀*log K'
  set Kp : ℝ := max 1 K with hKp_def
  have hKp_ge1 : 1 ≤ Kp := le_max_left _ _
  have hKp_pos : 0 < Kp := lt_of_lt_of_le one_pos hKp_ge1
  have hC0_pos : 0 < P.C₀ := P.positive.2.1
  set C : ℝ := 2 * P.C₀ * Real.log Kp with hC_def
  refine ⟨C, ?_⟩
  -- eventually 1 < L x
  have hEv : ∀ᶠ x in Filter.atTop, 1 < L x := by
    have htend : Filter.Tendsto L Filter.atTop Filter.atTop := Real.tendsto_log_atTop
    have hev : ∀ᶠ y in Filter.atTop, (1:ℝ) < y :=
      Filter.eventually_gt_atTop 1
    exact htend.eventually hev
  apply hEv.mono
  intro x hx
  intro G hAdm t b B htB hB0 hbB n
  have hLpos : 0 < L x := lt_trans zero_lt_one hx
  have hTpos : 0 < T x := by
    have h1 : Real.log 1 < Real.log (L x) :=
      Real.log_lt_log zero_lt_one hx
    simpa [T, Real.log_one] using h1
  have hmass_lo : ∀ g, P.vmin ≤ mass G g := by
    obtain ⟨_, _, h_mass, _, _⟩ := hAdm
    intro g
    exact (h_mass g).1
  have hcard_small_le : (G.small.card : ℝ) ≤ P.C₀ * T x := by
    obtain ⟨⟨_, h_small_le⟩, _, _, _, _⟩ := hAdm
    exact h_small_le
  have hcard_big_le : (G.big.card : ℝ) ≤ P.C₀ * T x := by
    obtain ⟨_, ⟨_, h_big_le⟩, _, _, _⟩ := hAdm
    exact h_big_le
  have hsize_le : (G.size : ℝ) ≤ 2 * P.C₀ * T x := by
    have hsub : G.small ⊆ Finset.univ := Finset.subset_univ _
    have hbig_eq : G.big = Finset.univ \ G.small := rfl
    have hcard_univ : (Finset.univ : Finset (Fin G.size)).card = G.size := by
      rw [Finset.card_univ, Fintype.card_fin]
    have hcard_add : G.big.card + G.small.card = G.size := by
      have h1 : ((Finset.univ \ G.small).card + G.small.card
          = (Finset.univ : Finset (Fin G.size)).card) :=
        Finset.card_sdiff_add_card_eq_card hsub
      rw [← hbig_eq, hcard_univ] at h1
      omega
    have hsize_eq : G.size = G.small.card + G.big.card := by omega
    have hcast : ((G.size : ℕ) : ℝ) = (G.small.card : ℝ) + (G.big.card : ℝ) := by
      exact_mod_cast congrArg Nat.cast hsize_eq
    rw [hcast]
    calc (G.small.card : ℝ) + (G.big.card : ℝ)
        ≤ P.C₀ * T x + P.C₀ * T x := add_le_add hcard_small_le hcard_big_le
      _ = 2 * P.C₀ * T x := by ring
  have hsum_le : ‖∑ z : Tuple G t, (if admissibleMarks G t n z then b z else 0)‖
      ≤ (∏ g, ((omegaGroup G g n : ℕ) : ℝ) ^ (t g)) * B := by
    -- S = admissible set
    set S : Finset (Tuple G t) := Finset.univ.filter (fun z => admissibleMarks G t n z) with hS_def
    have hsum_eq : (∑ z : Tuple G t, (if admissibleMarks G t n z then b z else 0))
        = ∑ z ∈ S, b z := by
      rw [hS_def, Finset.sum_filter]
    rw [hsum_eq]
    -- norm ≤ card * B
    have hnorm_le : ‖∑ z ∈ S, b z‖ ≤ (S.card : ℝ) * B := by
      calc ‖∑ z ∈ S, b z‖ ≤ ∑ z ∈ S, ‖b z‖ := norm_sum_le S b
        _ ≤ S.card • B := Finset.sum_le_card_nsmul S _ B (fun z _ => hbB z)
        _ = (S.card : ℝ) * B := by rw [nsmul_eq_mul]
    -- card S ≤ ∏ w^t
    have hcard_le : (S.card : ℝ) ≤ (∏ g, ((omegaGroup G g n : ℕ) : ℝ) ^ (t g)) := by
      -- injection from ↥S to AllDiv
      have hinj : Function.Injective
          ((fun (p : ↥S) (g : Fin G.size) (j : Fin (t g)) =>
            ⟨p.val g j, ((((Finset.mem_filter.mp p.property).2) g).2 j)⟩) :
            ↥S → Erdos821.GraphLemmas.AllDiv G t n) := by
        intro a b hab
        -- hab : ∀ g j, ⟨a...⟩ = ⟨b...⟩ as DivSub; hence a.val = b.val as Tuple
        have hval : a.val = b.val := by
          funext g j
          have hji := congrFun (congrFun hab g) j
          exact congrArg Subtype.val hji
        exact Subtype.ext hval
      have hcard_nat : S.card ≤ ∏ g, (omegaGroup G g n) ^ (t g) := by
        have hle : Fintype.card ↥S ≤ Fintype.card (Erdos821.GraphLemmas.AllDiv G t n) :=
          Fintype.card_le_of_injective _ hinj
        rw [Fintype.card_coe, Erdos821.GraphLemmas.card_allDiv] at hle
        exact hle
      exact_mod_cast hcard_nat
    calc ‖∑ z ∈ S, b z‖ ≤ (S.card : ℝ) * B := hnorm_le
      _ ≤ (∏ g, ((omegaGroup G g n : ℕ) : ℝ) ^ (t g)) * B := by
          apply mul_le_mul_of_nonneg_right hcard_le hB0
  -- Kp power bound by L^C
  have hKp_pow_le : (Kp ^ G.size : ℝ) ≤ L x ^ C := by
    have hKp_nonneg : 0 ≤ Kp := le_of_lt hKp_pos
    have hlogKp_nonneg : 0 ≤ Real.log Kp := Real.log_nonneg hKp_ge1
    have hsize_nonneg : 0 ≤ ((G.size : ℕ) : ℝ) := Nat.cast_nonneg _
    -- convert pow to exp, rpow to exp
    have hpow_eq : (Kp ^ G.size : ℝ) = Real.exp (((G.size : ℕ) : ℝ) * Real.log Kp) := by
      rw [← Real.rpow_natCast Kp G.size, Real.rpow_def_of_pos hKp_pos]
      ring
    have hrpow_eq : L x ^ C = Real.exp (Real.log (L x) * C) := by
      rw [Real.rpow_def_of_pos hLpos]
    rw [hpow_eq, hrpow_eq]
    apply Real.exp_le_exp.mpr
    -- need (size)*log Kp ≤ log L * C
    have hlogL_eq : Real.log (L x) = T x := rfl
    rw [hlogL_eq]
    rw [hC_def]
    -- size*logKp ≤ (2*C₀*T)*logKp = T*(2*C₀*logKp)
    have hsize_mul : ((G.size : ℕ) : ℝ) * Real.log Kp ≤ (2 * P.C₀ * T x) * Real.log Kp :=
      mul_le_mul_of_nonneg_right hsize_le hlogKp_nonneg
    calc ((G.size : ℕ) : ℝ) * Real.log Kp
        ≤ (2 * P.C₀ * T x) * Real.log Kp := hsize_mul
      _ = T x * (2 * P.C₀ * Real.log Kp) := by ring
  -- final combination: real factor * sum bound * per-group product * L^C
  have hreal_q_pos : 0 < P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) := by
    exact zpow_pos P.damping.1 _
  -- mass positivity from admissibility lower bound
  have hmass_pos : ∀ g, 0 < mass G g := by
    intro g
    exact lt_of_lt_of_le P.positive.2.2.1 (hmass_lo g)
  -- real factor unfolding + norm + per-group + L^C
  have hreal_factor_pos : 0 < (P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) * ∏ g, (mass G g)⁻¹ ^ (t g) : ℝ) := by
    apply mul_pos hreal_q_pos
    apply Finset.prod_pos
    intro g _
    exact pow_pos (inv_pos.mpr (hmass_pos g)) _
  -- norm unfolding
  have hnorm_eq : ‖weightedMarks G P.q t b n‖
      = (P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) * ∏ g, (mass G g)⁻¹ ^ (t g) : ℝ) *
        ‖∑ z : Tuple G t, (if admissibleMarks G t n z then b z else 0)‖ := by
    unfold weightedMarks
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hreal_factor_pos)]
  -- per-group product bound: B * ∏F ≤ B * Kp^size
  have hprod_le : B * (∏ g, (P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ) * (mass G g)⁻¹ ^ (t g) * (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g) : ℝ))
      ≤ B * (Kp ^ G.size : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hB0
    -- ∏F ≤ Kp^size via per-group F ≤ Kp
    have hF_le_Kp : ∀ g ∈ (Finset.univ : Finset (Fin G.size)),
        (P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ) * (mass G g)⁻¹ ^ (t g) * (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g) : ℝ) ≤ Kp := by
      intro g _
      have ht := htB g
      have hmass_ge := hmass_lo g
      have hFg_le_K := hK (t g) (omegaGroup G g n) (mass G g) ht hmass_ge
      -- hFg_le_K : q^((w:ℤ)-(t:ℤ)) * mass⁻¹^t * (w:ℝ)^t ≤ K
      -- Need F_g (with same form) ≤ K? Actually hK gives exactly F_g ≤ K (same expression? Check: hK's conclusion is q^((w:ℤ)-(t:ℤ))*mass⁻¹^t*(w:ℝ)^t ≤ K with w=omegaGroup, t=t g, mass=mass. Good, matches F_g (up to casts? Need to check casts match exactly: hK's w is ℕ, (w:ℕ):ℤ? Actually hK takes (t w : ℕ) with (w:ℕ):ℤ? Yes, ((w:ℕ):ℤ) - (t:ℤ)? With w=omegaGroup (ℕ), t=t g (ℕ). Good. And ((w:ℕ):ℝ)^t? Good. So hFg_le_K : F_g ≤ K. Good.)
      calc (P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ) * (mass G g)⁻¹ ^ (t g) * (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g) : ℝ)
          ≤ K := hFg_le_K
        _ ≤ Kp := le_max_right _ _
    have hF_nonneg : ∀ g ∈ (Finset.univ : Finset (Fin G.size)),
        0 ≤ (P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ) * (mass G g)⁻¹ ^ (t g) * (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g) : ℝ) := by
      intro g _
      apply mul_nonneg
      · apply mul_nonneg
        · exact le_of_lt (zpow_pos P.damping.1 _)
        · exact pow_nonneg (le_of_lt (inv_pos.mpr (hmass_pos g))) _
      · exact pow_nonneg (Nat.cast_nonneg _) _
    calc (∏ g, (P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ) * (mass G g)⁻¹ ^ (t g) * (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g) : ℝ))
        ≤ ∏ _g ∈ (Finset.univ : Finset (Fin G.size)), Kp := Finset.prod_le_prod₀ hF_nonneg hF_le_Kp
      _ = Kp ^ G.size := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- q splitting: ∏ q^(w-t) = q^(omega-∑t)
  have hq_split : (∏ g : Fin G.size, P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ))
      = P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) := by
    have hq_ne : P.q ≠ 0 := ne_of_gt P.damping.1
    -- ∏ q^e = q^∑e via induction
    have hprod : ∀ s : Finset (Fin G.size), (∏ g ∈ s, P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ))
        = P.q ^ (∑ g ∈ s, ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ)) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert a s has ih =>
        rw [Finset.prod_insert has, Finset.sum_insert has, zpow_add₀ hq_ne, ih]
    rw [hprod]
    congr 1
    -- ∑(w-t) = omega-∑t
    rw [Finset.sum_sub_distrib]
    congr 1
    -- ∑w (as ℤ) = (omega:ℤ)
    have homega_eq : omega G n = ∑ g, omegaGroup G g n := rfl
    rw [homega_eq, Nat.cast_sum]
  -- real_factor * ∏w = ∏F
  have hreal_prod_eq :
      (P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) * ∏ g, (mass G g)⁻¹ ^ (t g) : ℝ) *
        (∏ g, (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g))
      = ∏ g, (P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ) * (mass G g)⁻¹ ^ (t g) * (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g) : ℝ) := by
    rw [← hq_split, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  calc ‖weightedMarks G P.q t b n‖
      = (P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) * ∏ g, (mass G g)⁻¹ ^ (t g) : ℝ) *
        ‖∑ z : Tuple G t, (if admissibleMarks G t n z then b z else 0)‖ := hnorm_eq
    _ ≤ (P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) * ∏ g, (mass G g)⁻¹ ^ (t g) : ℝ) *
        ((∏ g, (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g)) * B) :=
        mul_le_mul_of_nonneg_left hsum_le (le_of_lt hreal_factor_pos)
    _ = B * ((P.q ^ (((omega G n : ℕ) : ℤ) - ∑ g, ((t g : ℕ) : ℤ)) * ∏ g, (mass G g)⁻¹ ^ (t g) : ℝ) *
        (∏ g, (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g))) := by ring
    _ = B * (∏ g, (P.q ^ ((((omegaGroup G g n : ℕ)) - (t g : ℤ)) : ℤ) * (mass G g)⁻¹ ^ (t g) * (((omegaGroup G g n : ℕ)) : ℝ) ^ (t g) : ℝ)) := by
        rw [hreal_prod_eq]
    _ ≤ B * (Kp ^ G.size : ℝ) := hprod_le
    _ ≤ B * (L x ^ C) :=
        mul_le_mul_of_nonneg_left hKp_pow_le hB0

example : @Erdos821.Blueprint.Analytic.mark_sup =
    @Erdos821.Blueprint.Analytic.mark_sup := rfl

end Erdos821.Blueprint.Analytic

