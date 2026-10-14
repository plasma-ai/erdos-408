module

public import Erdos408.TwoSided.Graph.Endpoint

/-!
# The Mellin and dyad insertion identity

The ingredients of Lemma G2 of `blueprint/two_sided_correlation.md` §4.2 (PD §6.2, (6.13)):

* `cutoffTerm`: the terms of `cutoffPairing` at one position `n`;
* the exchange of finite sums with the `ξ`-integral against an integrable density, and Mellin
  inversion at `y = n/(xD)` (`integrable_and_integral_mul_patternPairing`), using
  `(n/x)^{2πiξ} D^{-2πiξ} = (n/(xD))^{2πiξ}` and that every target `n + D` of a nonzero term
  lies in `S'_X`;
* the dyad partition of the support (`sum_Icc_cutoffTerm_eq_sum_dyads`): every nonzero term
  has `n ∈ [x/κ, x²]`, since `1 ≤ D ≤ x/κ` (U10).
-/

@[expose] public section

namespace Erdos408.TwoSided.InsertionIdentity

open Filter MeasureTheory

/-- The terms of `cutoffPairing` at the position `n`. -/
noncomputable def cutoffTerm (x q₀ : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) {J : ℕ} (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) (n : ℕ) : ℂ :=
  ∑ p ∈ physicalLists P (J + 1) n, ∑ a ∈ auxLabels P C,
    ∑ p' ∈ (physicalLists P (J + 1) (n + edgeProduct C p a)).filter (fun p' =>
        ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
          ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j),
      ((∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
          (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) *
          (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) : ℝ) : ℂ) * K p p' a *
        ((Ψ (n / (x * edgeProduct C p a)) / n * F n * G (n + edgeProduct C p a) *
          q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
          q₀ ^ (groupPrimeCount P (n + edgeProduct C p a) - (J + 1) * Fintype.card ι) : ℝ) :
          ℂ)

/-! ### Integrals against the density -/

/-- Integrability and the integral against `a` of a finite sum, termwise. -/
private theorem integrable_and_integral_mul_sum {α : Type*} {a : ℝ → ℂ} (s : Finset α)
    {φ : α → ℝ → ℂ} {v : α → ℂ}
    (h : ∀ i ∈ s, Integrable (fun ξ => a ξ * φ i ξ) ∧ ∫ ξ, a ξ * φ i ξ = v i) :
    Integrable (fun ξ => a ξ * ∑ i ∈ s, φ i ξ) ∧ ∫ ξ, a ξ * ∑ i ∈ s, φ i ξ = ∑ i ∈ s, v i := by
  simp_rw [Finset.mul_sum]
  refine ⟨integrable_finsetSum _ fun i hi => (h i hi).1, ?_⟩
  rw [integral_finsetSum _ fun i hi => (h i hi).1]
  exact Finset.sum_congr rfl fun i hi => (h i hi).2

/-- Integrability and the integral against `a` of a sum of two functions. -/
private theorem integrable_and_integral_mul_add {a φ₁ φ₂ : ℝ → ℂ} {v₁ v₂ : ℂ}
    (h₁ : Integrable (fun ξ => a ξ * φ₁ ξ) ∧ ∫ ξ, a ξ * φ₁ ξ = v₁)
    (h₂ : Integrable (fun ξ => a ξ * φ₂ ξ) ∧ ∫ ξ, a ξ * φ₂ ξ = v₂) :
    Integrable (fun ξ => a ξ * (φ₁ ξ + φ₂ ξ)) ∧ ∫ ξ, a ξ * (φ₁ ξ + φ₂ ξ) = v₁ + v₂ := by
  simp_rw [mul_add]
  exact ⟨h₁.1.add h₂.1, by rw [integral_add h₁.1 h₂.1, h₁.2, h₂.2]⟩

/-- `u^{it} D^{-it} = (u/D)^{it}` for `u > 0` and `D ≥ 1`. -/
private theorem cpow_mul_natCast_cpow {u : ℝ} (hu : 0 < u) {D : ℕ} (hD : 0 < D) (t : ℝ) :
    (u : ℂ) ^ ((t : ℂ) * Complex.I) * (D : ℂ) ^ (((-t : ℝ) : ℂ) * Complex.I) =
      ((u / D : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hu.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hD.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (div_pos hu hD').ne'), ← Complex.exp_add,
    ← Complex.ofReal_log hu.le, ← Complex.ofReal_natCast, ← Complex.ofReal_log hD'.le,
    ← Complex.ofReal_log (div_pos hu hD').le, Real.log_div hu.ne' hD'.ne']
  push_cast
  ring_nf

/-- **One term.** For `n ∈ S_X` and an edge `D ≥ 1` whose target lies in `S'_X` whenever
`Ψ(n/(xD)) ≠ 0`, the term of `⟨f_{X,ξ}, 𝒜 g_X⟩` at `ζ = -2πξ`, integrated against `a`, is
`L⁻¹ X` times the term of the cutoff pairing. -/
theorem integrable_and_integral_mul_term {x q₀ : ℝ} (hx : 0 < x) (hq₀ : 0 ≤ q₀) {ι : Type}
    [Fintype ι] (P : ι → Finset ℕ) (J : ℕ) (F G : ℕ → ℝ) {Ψ : ℝ → ℝ} {a : ℝ → ℂ}
    (ha : Integrable a)
    (hrep : ∀ y : ℝ, 0 < y →
      (Ψ y : ℂ) = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))
    {X : ℝ} {n D : ℕ} (hn : n ∈ dyadSource X) (hX : 0 < X) (hD : 0 < D)
    (htgt : Ψ (n / (x * D)) ≠ 0 → n + D ∈ dyadTarget X) (w k : ℂ) :
    Integrable (fun ξ => a ξ * (w * starRingEnd ℂ (sourceEndpoint x q₀ P J F X ξ n) * k *
        ((D : ℂ) ^ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I)) *
        ((Real.sqrt q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
          Real.sqrt q₀ ^ (groupPrimeCount P (n + D) - (J + 1) * Fintype.card ι) : ℝ) : ℂ) *
        targetEndpoint q₀ P J G X (n + D))) ∧
    ∫ ξ, a ξ * (w * starRingEnd ℂ (sourceEndpoint x q₀ P J F X ξ n) * k *
        ((D : ℂ) ^ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I)) *
        ((Real.sqrt q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
          Real.sqrt q₀ ^ (groupPrimeCount P (n + D) - (J + 1) * Fintype.card ι) : ℝ) : ℂ) *
        targetEndpoint q₀ P J G X (n + D)) =
      (((Real.log x)⁻¹ * X : ℝ) : ℂ) * (w * k *
        ((Ψ (n / (x * D)) / n * F n * G (n + D) *
          q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
          q₀ ^ (groupPrimeCount P (n + D) - (J + 1) * Fintype.card ι) : ℝ) : ℂ)) := by
  obtain ⟨hn₁, -⟩ := mem_dyadSource hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  set y : ℝ := n / (x * D) with hy
  have hy0 : 0 < y := by positivity
  set e₁ := groupPrimeCount P n - (J + 1) * Fintype.card ι
  set e₂ := groupPrimeCount P (n + D) - (J + 1) * Fintype.card ι
  set r : ℝ := (Real.log x)⁻¹ * F n * (X / n) * physicalDamping q₀ P (J + 1) n
  set s : ℝ := Real.sqrt q₀ ^ e₁ * Real.sqrt q₀ ^ e₂
  set g := targetEndpoint q₀ P J G X (n + D)
  -- the phase of the source endpoint combines with `D^{-2πiξ}`
  have hfun : (fun ξ => a ξ * (w * starRingEnd ℂ (sourceEndpoint x q₀ P J F X ξ n) * k *
        ((D : ℂ) ^ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I)) * (s : ℂ) * g)) =
      fun ξ => (w * r * k * s * g) *
        (a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) := by
    funext ξ
    rw [sourceEndpoint, ite_eq_left hn, Complex.conj_conj, hy, ← div_div,
      ← cpow_mul_natCast_cpow (div_pos hn0 hx) hD]
    ring
  rw [hfun]
  refine ⟨(integrable_mul_cpow ha hy0).const_mul _, ?_⟩
  rw [integral_const_mul, ← hrep y hy0]
  by_cases hΨ : Ψ y = 0
  · simp [hΨ]
  have hg : g = ((G (n + D) * physicalDamping q₀ P (J + 1) (n + D) : ℝ) : ℂ) := by
    simp only [g, targetEndpoint, ite_eq_left (htgt hΨ)]
  have hs₁ : Real.sqrt q₀ ^ e₁ * Real.sqrt q₀ ^ e₁ = q₀ ^ e₁ := by
    rw [← mul_pow, Real.mul_self_sqrt hq₀]
  have hs₂ : Real.sqrt q₀ ^ e₂ * Real.sqrt q₀ ^ e₂ = q₀ ^ e₂ := by
    rw [← mul_pow, Real.mul_self_sqrt hq₀]
  have key : r * s * (G (n + D) * physicalDamping q₀ P (J + 1) (n + D)) * Ψ y =
      (Real.log x)⁻¹ * X * (Ψ y / n * F n * G (n + D) * q₀ ^ e₁ * q₀ ^ e₂) := by
    have hd₁ : physicalDamping q₀ P (J + 1) n = Real.sqrt q₀ ^ e₁ := rfl
    have hd₂ : physicalDamping q₀ P (J + 1) (n + D) = Real.sqrt q₀ ^ e₂ := rfl
    simp only [r, s]
    rw [hd₁, hd₂, ← hs₁, ← hs₂]
    field_simp
  rw [hg]
  have key' := congrArg (fun z : ℝ => (z : ℂ)) key
  push_cast at key' ⊢
  linear_combination (w * k) * key'

/-- The labels of a physical list lie in their groups. -/
theorem mem_of_mem_physicalLists {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ}
    {M n : ℕ} {p : ι → Fin M → ℕ} (hp : p ∈ physicalLists P M n) (g : ι) (i : Fin M) :
    p g i ∈ P g :=
  Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (Finset.mem_filter.1 hp).1 g) i

/-- The auxiliary labels in the free slots lie in their groups. -/
theorem mem_of_mem_auxLabels {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ}
    {J : ℕ} {C : ι → Finset (Fin J)} {a : ι → Fin J → ℕ} (ha : a ∈ auxLabels P C) (g : ι)
    {i : Fin J} (hi : i ∈ C g) : a g i ∈ P g := by
  have h := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 ha g) i
  rwa [ite_eq_left hi] at h

/-- The edge product is positive and at most `B^{s J}` when every group label is positive and
at most `B`. -/
theorem edgeProduct_pos_and_le {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ}
    {B : ℝ} (hP : ∀ g, ∀ p ∈ P g, 0 < p ∧ (p : ℝ) ≤ B) {J : ℕ} {C : ι → Finset (Fin J)}
    {n : ℕ} {p : ι → Fin (J + 1) → ℕ} (hp : p ∈ physicalLists P (J + 1) n)
    {a : ι → Fin J → ℕ} (ha : a ∈ auxLabels P C) :
    0 < edgeProduct C p a ∧ (edgeProduct C p a : ℝ) ≤ B ^ (Fintype.card ι * J) := by
  have hmem : ∀ g i, (if i ∈ C g then a g i else p g i.castSucc) ∈ P g := by
    intro g i
    split_ifs with hi
    · exact mem_of_mem_auxLabels ha g hi
    · exact mem_of_mem_physicalLists hp g i.castSucc
  refine ⟨Finset.prod_pos fun g _ => Finset.prod_pos fun i _ => (hP g _ (hmem g i)).1, ?_⟩
  calc (edgeProduct C p a : ℝ) =
        ∏ g, ∏ i, ((if i ∈ C g then a g i else p g i.castSucc : ℕ) : ℝ) := by
        simp only [edgeProduct, Nat.cast_prod]
    _ ≤ ∏ _g : ι, ∏ _i : Fin J, B :=
        Finset.prod_le_prod₀ (fun g _ => Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
          fun g _ => Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
            fun i _ => (hP g _ (hmem g i)).2
    _ = B ^ (Fintype.card ι * J) := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, ← pow_mul, mul_comm]

/-! ### The dyads -/

/-- Membership in `S_{2^m}`. -/
theorem mem_dyadSource_two_pow {m n : ℕ} :
    n ∈ dyadSource ((2 : ℝ) ^ m) ↔ 2 ^ m ≤ n ∧ n < 2 ^ (m + 1) := by
  have h₁ : ⌈(2 : ℝ) ^ m⌉₊ = 2 ^ m := by exact_mod_cast Nat.ceil_natCast (2 ^ m)
  have h₂ : ⌈2 * (2 : ℝ) ^ m⌉₊ = 2 ^ (m + 1) := by
    rw [pow_succ, mul_comm]
    exact_mod_cast Nat.ceil_natCast (2 ^ m * 2)
  rw [dyadSource, Finset.mem_Ico, h₁, h₂]

/-- The sources `S_{2^m}` are pairwise disjoint. -/
theorem pairwiseDisjoint_dyadSource (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint fun m => dyadSource ((2 : ℝ) ^ m) := by
  intro m _ m' _ hmm'
  refine Finset.disjoint_left.2 fun n hn hn' => hmm' ?_
  obtain ⟨h₁, h₂⟩ := mem_dyadSource_two_pow.1 hn
  obtain ⟨h₁', h₂'⟩ := mem_dyadSource_two_pow.1 hn'
  rw [← Nat.log_eq_of_pow_le_of_lt_pow h₁ h₂, ← Nat.log_eq_of_pow_le_of_lt_pow h₁' h₂']

/-- A position `n ∈ [2√x, x²]` lies in the source of the dyad `2^{⌊log₂ n⌋}`. -/
theorem exists_mem_dyads {x : ℝ} (hx : 0 < x) {n : ℕ} (hn₁ : 2 * √x ≤ n) (hn₂ : (n : ℝ) ≤ x ^ 2)
    (hn₀ : 0 < n) : ∃ m ∈ dyads x, n ∈ dyadSource ((2 : ℝ) ^ m) := by
  set m := Nat.log 2 n
  have h₁ : 2 ^ m ≤ n := Nat.pow_log_le_self 2 hn₀.ne'
  have h₂ : n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h₁' : (2 : ℝ) ^ m ≤ n := by exact_mod_cast h₁
  have h₂' : (n : ℝ) < 2 * 2 ^ m := by
    rw [← pow_succ']
    exact_mod_cast h₂
  refine ⟨m, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor ?_)),
    by linarith, h₁'.trans hn₂⟩, mem_dyadSource_two_pow.2 ⟨h₁, h₂⟩⟩
  have hm : (m : ℝ) ≤ Real.logb 2 (x ^ 2) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    exact h₁'.trans hn₂
  rwa [Real.logb_pow, Nat.cast_ofNat] at hm

/-- A term of the cutoff pairing at `n` vanishes unless `x/κ ≤ n ≤ x²`, when every edge
satisfies `1 ≤ D ≤ x/κ`. -/
theorem cutoffTerm_eq_zero {x q₀ κ : ℝ} (hx : 0 < x) (hκ : 0 < κ) {ι : Type} [Fintype ι]
    [DecidableEq ι] {P : ι → Finset ℕ} {J : ℕ} (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) {Ψ : ℝ → ℝ} (hΨ : ∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) {n : ℕ}
    (hD : ∀ p ∈ physicalLists P (J + 1) n, ∀ a ∈ auxLabels P C,
      0 < edgeProduct C p a ∧ (edgeProduct C p a : ℝ) ≤ x / κ)
    (hn : ¬ (x / κ ≤ n ∧ (n : ℝ) ≤ x ^ 2)) : cutoffTerm x q₀ P C K F G Ψ n = 0 := by
  refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun b hb =>
    Finset.sum_eq_zero fun p' _ => ?_
  obtain ⟨hD₀, hD₁⟩ := hD p hp b hb
  have hD₀' : (1 : ℝ) ≤ edgeProduct C p b := by exact_mod_cast hD₀
  suffices h : Ψ (n / (x * edgeProduct C p b)) = 0 by simp [h]
  by_contra hne
  obtain ⟨h₁, h₂⟩ := hΨ _ hne
  have hxD : 0 < x * edgeProduct C p b := by positivity
  rw [le_div_iff₀ hxD] at h₁
  rw [div_le_iff₀ hxD] at h₂
  refine hn ⟨?_, ?_⟩
  · rw [div_le_iff₀ hκ]
    have := mul_le_mul_of_nonneg_left h₁ hκ.le
    rw [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at this
    nlinarith
  · calc (n : ℝ) ≤ κ * (x * edgeProduct C p b) := h₂
      _ ≤ κ * (x * (x / κ)) := by gcongr
      _ = x ^ 2 := by field_simp

/-- **The dyad partition.** When every edge satisfies `1 ≤ D ≤ x/κ` and `2√x ≤ x/κ`, the
cutoff pairing over `n ≤ x²` is the sum over the dyads `X` of the terms on `S_X`. -/
theorem sum_Icc_cutoffTerm_eq_sum_dyads {x q₀ κ : ℝ} (hx : 0 < x) (hκ : 0 < κ)
    (hxκ : 2 * √x ≤ x / κ) {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ} {J : ℕ}
    (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) {Ψ : ℝ → ℝ} (hΨ : ∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ)
    (hD : ∀ n, ∀ p ∈ physicalLists P (J + 1) n, ∀ a ∈ auxLabels P C,
      0 < edgeProduct C p a ∧ (edgeProduct C p a : ℝ) ≤ x / κ) :
    ∑ n ∈ Finset.Icc 1 ⌊x ^ 2⌋₊, cutoffTerm x q₀ P C K F G Ψ n =
      ∑ m ∈ dyads x, ∑ n ∈ dyadSource ((2 : ℝ) ^ m), cutoffTerm x q₀ P C K F G Ψ n := by
  rw [← Finset.sum_biUnion (pairwiseDisjoint_dyadSource _)]
  have hpos : 0 < x / κ := by positivity
  -- a nonzero term has `x/κ ≤ n ≤ x²`
  have hsupp : ∀ n, cutoffTerm x q₀ P C K F G Ψ n ≠ 0 → x / κ ≤ n ∧ (n : ℝ) ≤ x ^ 2 :=
    fun n hn => by_contra fun h => hn (cutoffTerm_eq_zero hx hκ C K F G hΨ (hD n) h)
  have h₁ := Finset.sum_subset (f := cutoffTerm x q₀ P C K F G Ψ)
    (Finset.inter_subset_left (s₁ := Finset.Icc 1 ⌊x ^ 2⌋₊)
      (s₂ := (dyads x).biUnion fun m => dyadSource ((2 : ℝ) ^ m))) ?_
  · have h₂ := Finset.sum_subset (f := cutoffTerm x q₀ P C K F G Ψ)
      (Finset.inter_subset_right (s₁ := Finset.Icc 1 ⌊x ^ 2⌋₊)
        (s₂ := (dyads x).biUnion fun m => dyadSource ((2 : ℝ) ^ m))) ?_
    · rw [← h₁, h₂]
    intro n hn hn'
    by_contra hne
    obtain ⟨h₁, h₂⟩ := hsupp n hne
    have hn0 : (0 : ℝ) < n := hpos.trans_le h₁
    refine hn' (Finset.mem_inter.2 ⟨Finset.mem_Icc.2 ⟨by exact_mod_cast hn0, ?_⟩, hn⟩)
    exact Nat.le_floor h₂
  · intro n hn hn'
    by_contra hne
    obtain ⟨h₁, h₂⟩ := hsupp n hne
    have hn0 : (0 : ℝ) < n := hpos.trans_le h₁
    obtain ⟨m, hm, hnm⟩ := exists_mem_dyads hx (hxκ.trans h₁) h₂ (by exact_mod_cast hn0)
    exact hn' (Finset.mem_inter.2 ⟨hn, Finset.mem_biUnion.2 ⟨m, hm, hnm⟩⟩)

/-! ### One pattern at one dyad -/

/-- **One pattern at one dyad.** For every edge positive, `2κ ≤ x` and `Ψ` supported in
`[κ⁻¹, κ]` with Mellin density `a`, the pairing `⟨f_{X,ξ}, 𝒜 g_X⟩` at `ζ = -2πξ`, integrated
against `a`, is `L⁻¹ X` times the cutoff pairing on `S_X`. Every target `n + D` of a nonzero
term lies in `S'_X`, since `D ≤ κ n / x < 2κX/x ≤ X`. -/
theorem integrable_and_integral_mul_patternPairing {x q₀ κ : ℝ} (hx : 0 < x) (hxκ : 2 * κ ≤ x)
    (hκ : 0 < κ) (hq₀ : 0 ≤ q₀) {ι : Type} [Fintype ι] [DecidableEq ι] {P : ι → Finset ℕ}
    {B : ℝ} (hP : ∀ g, ∀ p ∈ P g, 0 < p ∧ (p : ℝ) ≤ B) {J : ℕ} (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) {Ψ : ℝ → ℝ} (hΨ : ∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) {a : ℝ → ℂ}
    (ha : Integrable a)
    (hrep : ∀ y : ℝ, 0 < y →
      (Ψ y : ℂ) = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))
    {X : ℝ} (hX : 0 < X) :
    Integrable (fun ξ => a ξ * patternPairing P q₀ C K (-(2 * Real.pi * ξ)) (dyadSource X)
        (sourceEndpoint x q₀ P J F X ξ) (targetEndpoint q₀ P J G X)) ∧
      ∫ ξ, a ξ * patternPairing P q₀ C K (-(2 * Real.pi * ξ)) (dyadSource X)
          (sourceEndpoint x q₀ P J F X ξ) (targetEndpoint q₀ P J G X) =
        (((Real.log x)⁻¹ * X : ℝ) : ℂ) * ∑ n ∈ dyadSource X, cutoffTerm x q₀ P C K F G Ψ n := by
  conv_rhs => simp only [cutoffTerm, Finset.mul_sum]
  unfold patternPairing
  refine integrable_and_integral_mul_sum _ fun n hn => integrable_and_integral_mul_sum _
    fun p hp => integrable_and_integral_mul_sum _ fun b hb =>
      integrable_and_integral_mul_sum _ fun p' _ => ?_
  have hD := (edgeProduct_pos_and_le hP hp hb).1
  refine integrable_and_integral_mul_term hx hq₀ P J F G ha hrep hn hX hD (fun hne => ?_) _ _
  -- the target `n + D` lies in `S'_X`
  obtain ⟨h₁, -⟩ := hΨ _ hne
  obtain ⟨-, hn₂⟩ := mem_dyadSource hn
  have hD' : (0 : ℝ) < edgeProduct C p b := by exact_mod_cast hD
  have hxD : 0 < x * edgeProduct C p b := by positivity
  rw [le_div_iff₀ hxD] at h₁
  have h₃ : x * edgeProduct C p b ≤ κ * n := by
    have := mul_le_mul_of_nonneg_left h₁ hκ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hκ.ne', one_mul] at this
  have h₄ : (edgeProduct C p b : ℝ) < X := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  rw [dyadTarget, Finset.mem_Ico]
  refine ⟨(Finset.mem_Ico.1 hn).1.trans (Nat.le_add_right _ _), Nat.lt_ceil.2 ?_⟩
  push_cast
  linarith

/-! ### The identity -/

/-- Eventually `x > 0`, `2κ ≤ x`, `2√x ≤ x/κ`, `L ≥ 1`, `T ≥ 0` and
`2 J |C₀| T L^{0.46} + log κ ≤ L`, the last for the edge sizes (U10). -/
theorem eventually_insertion_conditions (C₀ κ : ℝ) (hκ : 1 < κ) (J : ℕ) :
    ∀ᶠ x : ℝ in atTop, 0 < x ∧ 2 * κ ≤ x ∧ 2 * √x ≤ x / κ ∧ 1 ≤ Real.log x ∧
      0 ≤ Real.log (Real.log x) ∧
      2 * J * |C₀| * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) + Real.log κ ≤
        Real.log x := by
  have hκ0 : 0 < κ := by linarith
  set c : ℝ := 2 * J * |C₀|
  have hc0 : 0 ≤ c := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0 : ℝ) < 0.54)).bound
    (by positivity : (0 : ℝ) < 1 / (2 * (c + 1)))
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop (2 * κ),
    eventually_ge_atTop (4 * κ ^ 2), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * |Real.log κ|),
    Real.tendsto_log_atTop.eventually ho] with x hx h2κ h4κ hL1 hLκ hlo
  set L := Real.log x
  have hT0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  refine ⟨hx, h2κ, ?_, hL1, hT0, ?_⟩
  · have hs : 2 * κ ≤ √x := Real.le_sqrt_of_sq_le (by nlinarith)
    rw [le_div_iff₀ hκ0]
    nlinarith [Real.mul_self_sqrt hx.le, Real.sqrt_nonneg x]
  · rw [Real.rpow_one, Real.norm_of_nonneg hT0,
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hlo
    have hL : L ^ (0.54 : ℝ) * L ^ (0.46 : ℝ) = L := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    have hp : 0 ≤ L ^ (0.46 : ℝ) := Real.rpow_nonneg (by linarith) _
    have h₁ : c * Real.log L * L ^ (0.46 : ℝ) ≤ c * (1 / (2 * (c + 1)) * L) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hc0
      calc Real.log L * L ^ (0.46 : ℝ) ≤ 1 / (2 * (c + 1)) * L ^ (0.54 : ℝ) * L ^ (0.46 : ℝ) :=
            mul_le_mul_of_nonneg_right hlo hp
        _ = 1 / (2 * (c + 1)) * L := by rw [mul_assoc, hL]
    have h₂ : c * (1 / (2 * (c + 1)) * L) ≤ L / 2 := by
      rw [← mul_assoc, mul_one_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
        (by norm_num)]
      nlinarith
    linarith [le_abs_self (Real.log κ)]

/-- **Lemma G2**, with `cutoffPairing` written as the sum of `cutoffTerm` over `n ≤ x²`. -/
theorem eventually_sum_cutoffTerm_eq (q₀ c₀ C₀ vlo vhi κ : ℝ) (hq₀ : 0 < q₀) (hκ : 1 < κ)
    (J : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (N : ℕ) (C : Fin N → ι → Finset (Fin J))
          (K : Fin N → (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
          (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) (a : ℝ → ℂ),
          (∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) → Integrable a →
          (∀ y : ℝ, 0 < y →
            (Ψ y : ℂ) = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)) →
          ∑ n ∈ Finset.Icc 1 ⌊x ^ 2⌋₊,
              cutoffTerm x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ n +
              ∑ ν, ∑ n ∈ Finset.Icc 1 ⌊x ^ 2⌋₊, cutoffTerm x q₀ P (C ν) (K ν) F G Ψ n =
            (Real.log x : ℂ) * ∑ m ∈ dyads x, (((2 : ℝ) ^ m : ℝ) : ℂ)⁻¹ *
              ∫ ξ, a ξ *
                (patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
                    (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
                    (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m)) +
                  ∑ ν, patternPairing P q₀ (C ν) (K ν) (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
                    (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m))) := by
  have hκ0 : 0 < κ := by linarith
  filter_upwards [eventually_insertion_conditions C₀ κ hκ J] with x hcond
  obtain ⟨hx, h2κ, hsq, hL1, hT0, hedge⟩ := hcond
  intro ι _ _ P big hadm N C K F G Ψ a hΨ ha hrep
  obtain ⟨-, -, hs₂, -, hb₂, -, hSm, hBg, -⟩ := hadm
  set L := Real.log x with hLdef
  set T := Real.log L
  set B : ℝ := Real.exp (L ^ (0.46 : ℝ))
  -- every group label is a prime at most `B`
  have hP : ∀ g, ∀ p ∈ P g, 0 < p ∧ (p : ℝ) ≤ B := by
    intro g p hp
    have hmem : ∀ y z : ℝ, z ≤ B → p ∈ primesIcc y z → 0 < p ∧ (p : ℝ) ≤ B := by
      intro y z hz hpz
      obtain ⟨hpI, hpp⟩ := Finset.mem_filter.1 hpz
      refine ⟨hpp.pos, le_trans ?_ hz⟩
      exact (Nat.le_floor_iff' hpp.ne_zero).1 (Finset.mem_Icc.1 hpI).2
    by_cases hg : g ∈ big
    · exact hmem _ _ le_rfl (hBg g hg hp)
    · refine hmem _ _ (Real.exp_le_exp.2 ?_) (hSm g hg hp)
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  -- `s ≤ 2 C₀ T`, so `B^{s J} ≤ x/κ`
  have hcard : (Fintype.card ι : ℝ) ≤ 2 * C₀ * T := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ big)
    rw [Finset.card_univ] at h
    rw [← h]
    push_cast
    linarith
  have hB : B ^ (Fintype.card ι * J) ≤ x / κ := by
    rw [← Real.exp_nat_mul, ← Real.exp_log hx, ← Real.exp_log hκ0, ← Real.exp_sub]
    refine Real.exp_le_exp.2 ?_
    have hp : 0 ≤ L ^ (0.46 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have h₁ : (Fintype.card ι : ℝ) * J * L ^ (0.46 : ℝ) ≤
        2 * C₀ * T * J * L ^ (0.46 : ℝ) := by gcongr
    have h₂ : 2 * C₀ * T * J * L ^ (0.46 : ℝ) ≤ 2 * J * |C₀| * T * L ^ (0.46 : ℝ) := by
      have : C₀ * (T * J * L ^ (0.46 : ℝ)) ≤ |C₀| * (T * J * L ^ (0.46 : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₀) (by positivity)
      linarith
    push_cast
    linarith
  have hD : ∀ (C : ι → Finset (Fin J)) n, ∀ p ∈ physicalLists P (J + 1) n,
      ∀ b ∈ auxLabels P C, 0 < edgeProduct C p b ∧ (edgeProduct C p b : ℝ) ≤ x / κ :=
    fun C n p hp b hb => ⟨(edgeProduct_pos_and_le hP hp hb).1,
      (edgeProduct_pos_and_le hP hp hb).2.trans hB⟩
  have hdec := fun C K => sum_Icc_cutoffTerm_eq_sum_dyads (q₀ := q₀) hx hκ0 hsq C K F G hΨ (hD C)
  rw [hdec, Finset.sum_congr rfl fun ν _ => hdec (C ν) (K ν)]
  -- each dyad
  have hm : ∀ m : ℕ, ∫ ξ, a ξ *
      (patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1)
          (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
          (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m)) +
        ∑ ν, patternPairing P q₀ (C ν) (K ν) (-(2 * Real.pi * ξ)) (dyadSource (2 ^ m))
          (sourceEndpoint x q₀ P J F (2 ^ m) ξ) (targetEndpoint q₀ P J G (2 ^ m))) =
      ((L⁻¹ * 2 ^ m : ℝ) : ℂ) *
        (∑ n ∈ dyadSource ((2 : ℝ) ^ m),
            cutoffTerm x q₀ P (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G Ψ n +
          ∑ ν, ∑ n ∈ dyadSource ((2 : ℝ) ^ m), cutoffTerm x q₀ P (C ν) (K ν) F G Ψ n) := by
    intro m
    have hX : (0 : ℝ) < 2 ^ m := by positivity
    have h := integrable_and_integral_mul_add
      (integrable_and_integral_mul_patternPairing hx h2κ hκ0 hq₀.le hP
        (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) F G hΨ ha hrep hX)
      (integrable_and_integral_mul_sum Finset.univ fun ν _ =>
        integrable_and_integral_mul_patternPairing hx h2κ hκ0 hq₀.le hP (C ν) (K ν) F G hΨ ha
          hrep hX)
    rw [h.2, mul_add, ← Finset.mul_sum]
  simp only [hm]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by linarith)
  have hcancel : ∀ (m : ℕ) (z : ℂ),
      (L : ℂ) * ((((2 : ℝ) ^ m : ℝ) : ℂ)⁻¹ * (((L⁻¹ * 2 ^ m : ℝ) : ℂ) * z)) = z := by
    intro m z
    have h2 : ((2 : ℂ) ^ m) ≠ 0 := pow_ne_zero _ two_ne_zero
    push_cast
    field_simp
  rw [Finset.mul_sum]
  simp only [hcancel]
  rw [Finset.sum_add_distrib, Finset.sum_comm]

end Erdos408.TwoSided.InsertionIdentity
