module

public import Erdos408.TwoSided.Setup
public import Erdos821.P5Minor.MinorArcTask
public import Erdos821.S34.OwnedLeafProofs

/-!
# The bilinear multiplier and the minor arcs

S6–S7 of `blueprint/two_sided_correlation.md` §5.2 (PD (6.20)–(6.21), WD §5.3). The
multiplier `𝔪(θ) = 𝔼_a b₁(D_A) b₂(D_B) e(θ D_A D_B)` is bilinear in independent free products,
`𝔪(θ) = ∑_{n, v} α_n β_v e(θ n v)`.

* Lemma C1 (`eventually_sum_auxLabels_eq_le`): the atoms `|α_n| ≤ ρ_A(n) ≤ L^{C₇}/n`.
* Lemma C2 (`exists_minorArc_bound`): off the arcs of denominator `≤ L^{C_arc}`, each dyadic
  box of `𝔪` is `≤ K L^{-A_m}` (WD's `MinorArcTask`), replacing PD (6.20)–(6.21).
-/

@[expose] public section

namespace Erdos408.TwoSided

open Filter

open scoped Classical in
/-- **Lemma C1 (atoms).** For `m₀` there is `C₇` (`2 m₀ C₀ log γ`, with
`γ = max(1, m₀) max(1, v₋⁻¹)`) such that, eventually, for groups as in (6.1) and free slots
`A g` with `|A g| ≤ m₀`, the law of the free product `D_A` satisfies
`ρ_A(n) = ∑_{a : D_A = n} ∏ μ(a) ≤ L^{C₇}/n`. Each slot holds one of the at most `|A g|` prime
factors of `n` in its group (each prime lies in one group), so there are at most
`max(1, m₀)^k` labels with product `n`, `k = m₀ |ι|`, each of mass at most
`max(1, v₋⁻¹)^k / n`; and `|ι| ≤ 2 C₀ T`. -/
theorem eventually_sum_auxLabels_eq_le (c₀ C₀ vlo vhi : ℝ) (hvlo : 0 < vlo) (m₀ : ℕ) :
    ∃ C₇ : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (J : ℕ) (A : ι → Finset (Fin J)), (∀ g, (A g).card ≤ m₀) →
        ∀ n : ℕ, 1 ≤ n →
          ∑ l ∈ (auxLabels P A).filter (fun l => slotProduct A l = n),
              ∏ g, ∏ i ∈ A g, (harmonicMass (P g) * l g i)⁻¹ ≤
            Real.log x ^ C₇ / n := by
  set β : ℝ := max 1 vlo⁻¹ with hβ
  set γ : ℝ := max 1 (m₀ : ℝ) * β with hγ
  have hβ1 : 1 ≤ β := le_max_left _ _
  have hγ1 : 1 ≤ γ := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hβ1
  refine ⟨2 * m₀ * C₀ * Real.log γ, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hL
  intro ι _ _ P big hadm J A hA n hn
  set S := (auxLabels P A).filter (fun l => slotProduct A l = n) with hSdef
  set k : ℕ := m₀ * Fintype.card ι with hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the group elements are primes
  have hprime : ∀ g, ∀ p ∈ P g, p.Prime := by
    intro g p hp
    by_cases hg : g ∈ big
    · exact (Finset.mem_filter.1 (hadm.2.2.2.2.2.2.2.1 g hg hp)).2
    · exact (Finset.mem_filter.1 (hadm.2.2.2.2.2.2.1 g hg hp)).2
  -- each term is `∏_g V_g^{-|A g|} / n ≤ β^k / n`
  have hterm : ∀ l ∈ S, ∏ g, ∏ i ∈ A g, (harmonicMass (P g) * l g i)⁻¹ ≤ β ^ k / n := by
    intro l hl
    have hln := (Finset.mem_filter.1 hl).2
    have hcast : (n : ℝ) = ∏ g, ∏ i ∈ A g, (l g i : ℝ) := by
      rw [← hln, slotProduct]
      push_cast
      rfl
    have hsplit : ∏ g, ∏ i ∈ A g, (harmonicMass (P g) * l g i)⁻¹ =
        (∏ g, ∏ _i ∈ A g, (harmonicMass (P g))⁻¹) / n := by
      rw [hcast, div_eq_mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => mul_inv _ _
    rw [hsplit]
    refine div_le_div_of_nonneg_right ?_ hn0.le
    calc ∏ g, ∏ _i ∈ A g, (harmonicMass (P g))⁻¹ ≤ ∏ _g : ι, β ^ m₀ := by
          refine Finset.prod_le_prod₀ (fun g _ => Finset.prod_nonneg fun i _ =>
            inv_nonneg.2 (hvlo.le.trans (hadm.2.2.2.2.2.1 g).1)) fun g _ => ?_
          rw [Finset.prod_const]
          have hV := hadm.2.2.2.2.2.1 g
          have hVβ : (harmonicMass (P g))⁻¹ ≤ β :=
            (inv_anti₀ hvlo hV.1).trans (le_max_right _ _)
          exact (pow_le_pow_left₀ (inv_nonneg.2 (hvlo.le.trans hV.1)) hVβ _).trans
            (pow_le_pow_right₀ hβ1 (hA g))
      _ = β ^ k := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  -- the fibre has at most `max(1, m₀)^k` labels: each slot holds a prime factor of `n` in
  -- its group, and these number at most `|A g|`
  have hcard : (S.card : ℝ) ≤ max 1 (m₀ : ℝ) ^ k := by
    rcases S.eq_empty_or_nonempty with hS | ⟨l₀, hl₀⟩
    · rw [hS, Finset.card_empty, Nat.cast_zero]
      positivity
    have hl₀n := (Finset.mem_filter.1 hl₀).2
    have hl₀a := Finset.mem_filter.1 hl₀ |>.1
    simp only [auxLabels, Fintype.mem_piFinset] at hl₀a
    have hc : ∀ g, ((P g).filter (· ∣ n)).card ≤ (A g).card := by
      intro g
      refine (Finset.card_le_card fun p hp => ?_).trans (Finset.card_image_le (s := A g)
        (f := l₀ g))
      obtain ⟨hpP, hpn⟩ := Finset.mem_filter.1 hp
      have hpp := (hprime g p hpP).prime
      rw [← hl₀n, slotProduct] at hpn
      obtain ⟨g', -, hg'⟩ := (Prime.dvd_finsetProd_iff hpp _).1 hpn
      obtain ⟨i, hi, hgi⟩ := (Prime.dvd_finsetProd_iff hpp _).1 hg'
      have hmem : l₀ g' i ∈ P g' := by simpa [hi] using hl₀a g' i
      have heq : p = l₀ g' i := (Nat.prime_dvd_prime_iff_eq (hprime g p hpP)
        (hprime g' _ hmem)).1 hgi
      have hgg : g' = g := by
        by_contra hne
        exact Finset.disjoint_left.1 (hadm.1 g g' (Ne.symm hne)) hpP (heq ▸ hmem)
      subst hgg
      exact Finset.mem_image.2 ⟨i, hi, heq.symm⟩
    have hsub : S ⊆ Fintype.piFinset fun g =>
        Fintype.piFinset fun i => if i ∈ A g then (P g).filter (· ∣ n) else {1} := by
      intro l hl
      obtain ⟨hla, hln⟩ := Finset.mem_filter.1 hl
      simp only [auxLabels, Fintype.mem_piFinset] at hla
      simp only [Fintype.mem_piFinset]
      intro g i
      have := hla g i
      split_ifs with hi
      · rw [ite_eq_left hi] at this
        refine Finset.mem_filter.2 ⟨this, ?_⟩
        rw [← hln, slotProduct]
        exact (Finset.dvd_prod_of_mem _ hi).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ g))
      · rwa [ite_eq_right hi] at this
    have hpi : (Fintype.piFinset fun g =>
        Fintype.piFinset fun i => if i ∈ A g then (P g).filter (· ∣ n) else {1}).card ≤
          (max 1 m₀) ^ k := by
      rw [Fintype.card_piFinset]
      calc ∏ g, (Fintype.piFinset fun i =>
            if i ∈ A g then (P g).filter (· ∣ n) else {1}).card
          = ∏ g, ((P g).filter (· ∣ n)).card ^ (A g).card := by
            refine Finset.prod_congr rfl fun g _ => ?_
            rw [Fintype.card_piFinset]
            simp only [apply_ite Finset.card, Finset.card_singleton]
            rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
        _ ≤ ∏ _g : ι, (max 1 m₀) ^ m₀ := by
            refine Finset.prod_le_prod fun g _ => ?_
            exact (Nat.pow_le_pow_left ((hc g).trans ((hA g).trans (le_max_right _ _))) _).trans
              (Nat.pow_le_pow_right (lt_of_lt_of_le Nat.one_pos (le_max_left 1 m₀)) (hA g))
        _ = (max 1 m₀) ^ k := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
    have := (Finset.card_le_card hsub).trans hpi
    calc (S.card : ℝ) ≤ ((max 1 m₀ ^ k : ℕ) : ℝ) := by exact_mod_cast this
      _ = max 1 (m₀ : ℝ) ^ k := by push_cast; rfl
  -- `γ^k ≤ L^{C₇}`, as `|ι| ≤ 2 C₀ T`
  have hι : (Fintype.card ι : ℝ) ≤ 2 * C₀ * Real.log (Real.log x) := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ big)
    rw [Finset.card_univ] at h
    rw [← h]
    push_cast
    linarith [hadm.2.2.1, hadm.2.2.2.2.1]
  have hγk : γ ^ k ≤ Real.log x ^ (2 * m₀ * C₀ * Real.log γ) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hL,
      Real.exp_le_exp, hk]
    push_cast
    have h₀ : (0 : ℝ) ≤ m₀ * Real.log γ := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hγ1)
    nlinarith [mul_le_mul_of_nonneg_left hι h₀]
  calc ∑ l ∈ S, ∏ g, ∏ i ∈ A g, (harmonicMass (P g) * l g i)⁻¹ ≤ S.card • (β ^ k / n) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = S.card * β ^ k / n := by rw [nsmul_eq_mul, mul_div_assoc]
    _ ≤ max 1 (m₀ : ℝ) ^ k * β ^ k / n := by gcongr
    _ = γ ^ k / n := by rw [hγ, mul_pow]
    _ ≤ Real.log x ^ (2 * m₀ * C₀ * Real.log γ) / n := by gcongr

/-- **Lemma C2 (minor arcs).** WD's `MinorArcTask`: for `C, δ, A > 0` there are
`C_arc, K > 0` such that, eventually, for `exp(L^δ) ≤ U, V` with `UV ≤ x²`, `0 < |k| ≤ L^C`,
integer coefficients on `[U, 2U]` and `[V, 2V]` with `∑ |a_n|² ≤ L^C/U`, `∑ |b_v|² ≤ L^C/V`,
and `θ` at distance `> L^{C_arc}/(UV)` from every `u/r` with `r ≤ L^{C_arc}`,
`|∑_{n, v} a_n b_v e(-kθnv)| ≤ K L^{-A}`. Applied with `C = max(C₇, 1)`, `δ = 0.38` and
`k = 1` to the coefficients of C1 on the dyadic boxes of the cells `[U, eU]`. -/
theorem exists_minorArc_bound (C δ A : ℝ) (hC : 0 < C) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ Carc K : ℝ, 0 < Carc ∧ 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (U V θ : ℝ) (k : ℤ) (s t : Finset ℤ) (a b : ℤ → ℂ),
        Real.exp (Real.log x ^ δ) ≤ U → Real.exp (Real.log x ^ δ) ≤ V → U * V ≤ x ^ 2 →
        k ≠ 0 → |(k : ℝ)| ≤ Real.log x ^ C →
        (∀ n ∈ s, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U) → (∀ n ∈ t, V ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * V) →
        ∑ n ∈ s, ‖a n‖ ^ 2 ≤ Real.log x ^ C / U → ∑ n ∈ t, ‖b n‖ ^ 2 ≤ Real.log x ^ C / V →
        (∀ (r : ℕ) (u : ℤ), 1 ≤ r → (r : ℝ) ≤ Real.log x ^ Carc →
          Real.log x ^ Carc / (U * V) < |θ - u / r|) →
        ‖∑ n ∈ s, ∑ v ∈ t, a n * b v *
            Complex.exp (2 * Real.pi * (-(k : ℝ) * θ * n * v : ℝ) * Complex.I)‖ ≤
          K * Real.log x ^ (-A) :=
  Erdos821.P5Core.minorArcTask_proof Erdos821.Blueprint.Analytic.integer_bilinear_proof C δ A
    hC hδ hA

end Erdos408.TwoSided
