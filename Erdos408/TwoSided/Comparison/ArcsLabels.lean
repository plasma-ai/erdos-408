import Erdos408.TwoSided.Setup

/-!
# Free labels of a comparison pattern

The label combinatorics behind S6–S7 of `blueprint/two_sided_correlation.md` §5.2: the free
labels of `C = A ∪ B` (disjoint slots) are pairs of free labels of `A` and of `B`, and the free
products `D_A, D_B` live at the scales (6.17). The law `labelMass = ∏ μ_g` and its mass `1` are
in `Setup.lean`.

* `sum_auxLabels_union`: the sum over labels of `A ∪ B` is the double sum over labels of `A`
  and of `B`, with `D_A`, `D_B` and the weights splitting.
* `le_slotProduct`, `eventually_slotProduct_le`: `exp(L^{0.39}) ≤ D_C ≤ exp(L^{0.465})`.
* `norm_sum_bilinear_le`: a bilinear multiplier of two independent free products is at most
  four box sums `∑_{n, v} α_n β_v e(-θnv)` (`bilinearPhase`), grouping the labels by their
  products and splitting `[U, 4U]` into `[U, 2U]` and `(2U, 4U]`.
-/

namespace Erdos408.TwoSided.Arcs

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The free labels of `A ∪ B` are pairs.** For disjoint slots, the sum of
`μ(a) Φ(D_A, D_B)` over the labels of `A ∪ B` is the double sum over the labels of `A` and of
`B`, with `μ = μ_A μ_B`. -/
theorem sum_auxLabels_union (P : ι → Finset ℕ) {J : ℕ} {A B : ι → Finset (Fin J)}
    (hAB : ∀ g, Disjoint (A g) (B g)) (Φ : ℕ → ℕ → ℂ) :
    ∑ l ∈ auxLabels P (fun g => A g ∪ B g),
        (labelMass P (fun g => A g ∪ B g) l : ℂ) * Φ (slotProduct A l) (slotProduct B l) =
      ∑ l₁ ∈ auxLabels P A, ∑ l₂ ∈ auxLabels P B,
        (labelMass P A l₁ : ℂ) * (labelMass P B l₂ : ℂ) *
          Φ (slotProduct A l₁) (slotProduct B l₂) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun p g i => if i ∈ A g then p.1 g i else p.2 g i)
    (fun l => (fun g i => if i ∈ A g then l g i else 1, fun g i => if i ∈ B g then l g i else 1))
    ?_ ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    rw [mem_auxLabels] at h₁ h₂ ⊢
    intro g i
    by_cases hA : i ∈ A g
    · simpa [hA] using h₁ g i
    · simpa [hA] using h₂ g i
  · intro l hl
    rw [mem_auxLabels] at hl
    refine Finset.mem_product.2 ⟨mem_auxLabels.2 fun g i => ?_, mem_auxLabels.2 fun g i => ?_⟩
    · by_cases hA : i ∈ A g
      · simpa [hA] using hl g i
      · simp [hA]
    · by_cases hB : i ∈ B g
      · simpa [hB] using hl g i
      · simp [hB]
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    rw [mem_auxLabels] at h₁ h₂
    refine Prod.ext (funext fun g => funext fun i => ?_) (funext fun g => funext fun i => ?_)
    · by_cases hA : i ∈ A g
      · simp [hA]
      · have h := h₁ g i
        rw [ite_eq_right hA, Finset.mem_singleton] at h
        simp [hA, h]
    · by_cases hB : i ∈ B g
      · have hA : i ∉ A g := Finset.disjoint_right.1 (hAB g) hB
        simp [hA, hB]
      · have h := h₂ g i
        rw [ite_eq_right hB, Finset.mem_singleton] at h
        simp [hB, h]
  · intro l hl
    rw [mem_auxLabels] at hl
    refine funext fun g => funext fun i => ?_
    by_cases hA : i ∈ A g
    · simp [hA]
    · by_cases hB : i ∈ B g
      · simp [hA, hB]
      · have h := hl g i
        rw [ite_eq_right (by simp [hA, hB] : i ∉ A g ∪ B g), Finset.mem_singleton] at h
        simp [hA, hB, h]
  · intro p _
    have hA : slotProduct A (fun g i => if i ∈ A g then p.1 g i else p.2 g i) =
        slotProduct A p.1 :=
      Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i hi => by simp [hi]
    have hB : slotProduct B (fun g i => if i ∈ A g then p.1 g i else p.2 g i) =
        slotProduct B p.2 :=
      Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i hi => by
        simp [Finset.disjoint_right.1 (hAB g) hi]
    have hw : labelMass P (fun g => A g ∪ B g)
        (fun g i => if i ∈ A g then p.1 g i else p.2 g i) =
          labelMass P A p.1 * labelMass P B p.2 := by
      simp only [labelMass, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [Finset.prod_union (hAB g)]
      congr 1
      · exact Finset.prod_congr rfl fun i hi => by simp [hi]
      · exact Finset.prod_congr rfl fun i hi => by simp [Finset.disjoint_right.1 (hAB g) hi]
    rw [hA, hB, hw]
    push_cast
    ring

/-- Grouping a weighted sum by an integer key. -/
private theorem sum_mul_eq_sum_image {Λ : Type*} (S : Finset Λ) (w : Λ → ℂ) (key : Λ → ℤ)
    (Ψ : ℤ → ℂ) :
    ∑ l ∈ S, w l * Ψ (key l) =
      ∑ z ∈ S.image key, (∑ l ∈ S.filter (fun l => key l = z), w l) * Ψ z := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := S.image key)
    fun l hl => Finset.mem_image_of_mem key hl]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [(Finset.mem_filter.1 hl).2]

/-- **Two boxes.** A sum over integers whose nonzero terms lie in `[U, 4U]` is the sum over
`[U, 2U]` plus the sum over `(2U, 4U]`. -/
private theorem sum_eq_add_filter_of_support (s : Finset ℤ) (f : ℤ → ℂ) (U : ℝ)
    (hf : ∀ z ∈ s, f z ≠ 0 → U ≤ (z : ℝ) ∧ (z : ℝ) ≤ 4 * U) :
    ∑ z ∈ s, f z = ∑ z ∈ s.filter (fun z : ℤ => U ≤ (z : ℝ) ∧ (z : ℝ) ≤ 2 * U), f z +
      ∑ z ∈ s.filter (fun z : ℤ => 2 * U < (z : ℝ) ∧ (z : ℝ) ≤ 4 * U), f z := by
  rw [← Finset.sum_filter_of_ne (p := fun z : ℤ => U ≤ (z : ℝ) ∧ (z : ℝ) ≤ 4 * U) hf,
    ← Finset.sum_filter_add_sum_filter_not _ (fun z : ℤ => (z : ℝ) ≤ 2 * U), Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  · refine Finset.sum_congr (Finset.filter_congr fun z _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨⟨h₁, -⟩, h₂⟩
      exact ⟨h₁, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨h₁, by linarith⟩, h₂⟩
  · refine Finset.sum_congr (Finset.filter_congr fun z _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨⟨-, h₁⟩, h₂⟩
      exact ⟨lt_of_not_ge h₂, h₁⟩
    · rintro ⟨h₁, h₂⟩
      have : 0 ≤ U := by linarith
      exact ⟨⟨by linarith, h₂⟩, not_le.2 h₁⟩

/-- **Lower scale.** For a free label of `C` and slots `S ⊆ C` with a slot in a big group,
`D_S ≥ exp(L^{0.39})`. -/
theorem le_slotProduct {c₀ C₀ vlo vhi x : ℝ} {P : ι → Finset ℕ} {big : Finset ι}
    (hadm : GroupAdmissible c₀ C₀ vlo vhi x P big) {J : ℕ} {C S : ι → Finset (Fin J)}
    (hC : ∀ g ∉ big, C g = ∅) (hS : ∀ g, S g ⊆ C g) {l : ι → Fin J → ℕ}
    (hl : l ∈ auxLabels P C) {g : ι} {i : Fin J} (hi : i ∈ S g) :
    Real.exp (Real.log x ^ (0.39 : ℝ)) ≤ slotProduct S l := by
  have hiC := hS g hi
  have hg : g ∈ big := by
    by_contra hg
    rw [hC g hg] at hiC
    exact Finset.notMem_empty i hiC
  have hl' := mem_auxLabels.1 hl
  have hmem : l g i ∈ P g := by simpa [hiC] using hl' g i
  have hp := hadm.2.2.2.2.2.2.2.1 g hg hmem
  simp only [primesIcc, Finset.mem_filter, Finset.mem_Icc] at hp
  have hdvd : l g i ∣ slotProduct S l :=
    (Finset.dvd_prod_of_mem _ hi).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ g))
  have hle : l g i ≤ slotProduct S l := Nat.le_of_dvd (slotProduct_pos hadm hl S) hdvd
  calc Real.exp (Real.log x ^ (0.39 : ℝ)) ≤ ⌈Real.exp (Real.log x ^ (0.39 : ℝ))⌉₊ :=
        Nat.le_ceil _
    _ ≤ l g i := by exact_mod_cast hp.1.1
    _ ≤ slotProduct S l := by exact_mod_cast hle

/-- **Upper scale.** Eventually, for a free label of `C` and slots `S ⊆ C`, at most `m₀` in
each big group and none in the small groups, `D_S ≤ exp(L^{0.465})`:
`D_S ≤ exp(m₀ C₀ T L^{0.46})`. -/
theorem eventually_slotProduct_le (c₀ C₀ vlo vhi : ℝ) (m₀ : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (J : ℕ) (C S : ι → Finset (Fin J)), (∀ g ∉ big, S g = ∅) →
        (∀ g, (S g).card ≤ m₀) → (∀ g, S g ⊆ C g) → ∀ l ∈ auxLabels P C,
          (slotProduct S l : ℝ) ≤ Real.exp (Real.log x ^ (0.465 : ℝ)) := by
  have hT := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 0.005 by norm_num)).bound
    (show (0 : ℝ) < 1 / (m₀ * |C₀| + 1) by positivity)
  filter_upwards [Real.tendsto_log_atTop.eventually hT,
    Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hx hL
  intro ι _ _ P big hadm J C S hC hCm hSC l hl
  set L := Real.log x
  have hL0 : 0 < L := by linarith
  have hl' := mem_auxLabels.1 hl
  -- each slot holds a prime `≤ exp(L^{0.46})`
  have hslot : ∀ g, ∀ i ∈ S g, (l g i : ℝ) ≤ Real.exp (L ^ (0.46 : ℝ)) := by
    intro g i hi
    have hg : g ∈ big := by
      by_contra hg
      rw [hC g hg] at hi
      exact Finset.notMem_empty i hi
    have hmem : l g i ∈ P g := by simpa [hSC g hi] using hl' g i
    have hp := hadm.2.2.2.2.2.2.2.1 g hg hmem
    simp only [primesIcc, Finset.mem_filter, Finset.mem_Icc] at hp
    exact (Nat.le_floor_iff (Real.exp_pos _).le).1 hp.1.2
  have hprod : (slotProduct S l : ℝ) ≤ ∏ g, Real.exp (L ^ (0.46 : ℝ)) ^ (S g).card := by
    rw [slotProduct]
    push_cast
    refine Finset.prod_le_prod₀ (fun g _ => Finset.prod_nonneg fun i _ => by positivity)
      fun g _ => ?_
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => hslot g i hi
  -- `∑_g |S g| ≤ m₀ |big| ≤ m₀ C₀ T`
  have hsum : ((∑ g, (S g).card : ℕ) : ℝ) ≤ m₀ * |C₀| * Real.log L := by
    have h₁ : ∑ g, (S g).card = ∑ g ∈ big, (S g).card := by
      refine (Finset.sum_subset (Finset.subset_univ big) fun g _ hg => ?_).symm
      rw [hC g hg, Finset.card_empty]
    have h₂ : ∑ g, (S g).card ≤ big.card * m₀ := by
      rw [h₁]
      simpa [smul_eq_mul] using Finset.sum_le_card_nsmul big (fun g => (S g).card) m₀
        fun g _ => hCm g
    have h₃ : (big.card : ℝ) ≤ |C₀| * Real.log L :=
      hadm.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
        (Real.log_nonneg hL.le))
    have h₄ : ((∑ g, (S g).card : ℕ) : ℝ) ≤ big.card * m₀ := by exact_mod_cast h₂
    nlinarith [Nat.cast_nonneg (α := ℝ) m₀]
  rw [Real.norm_of_nonneg (Real.log_nonneg hL.le),
    Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _)] at hx
  refine hprod.trans ?_
  rw [Finset.prod_pow_eq_pow_sum, ← Real.exp_nat_mul, Real.exp_le_exp]
  have hm : 0 ≤ (m₀ : ℝ) * |C₀| := by positivity
  have hlog : (m₀ * |C₀|) * Real.log L ≤ L ^ (0.005 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ m₀ * |C₀| + 1 by positivity)
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at h
    nlinarith [Real.log_nonneg hL.le]
  calc ((∑ g, (S g).card : ℕ) : ℝ) * L ^ (0.46 : ℝ)
        ≤ (m₀ * |C₀| * Real.log L) * L ^ (0.46 : ℝ) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ ≤ L ^ (0.005 : ℝ) * L ^ (0.46 : ℝ) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = L ^ (0.465 : ℝ) := by rw [← Real.rpow_add hL0]; norm_num

/-- The phase `e(-θ n v)` of the bilinear multiplier, in the form of `exists_minorArc_bound`
with `k = 1`. -/
noncomputable def bilinearPhase (θ : ℝ) (n v : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * (-((1 : ℤ) : ℝ) * θ * n * v : ℝ) * Complex.I)

/-- **The bilinear multiplier on four boxes (S6–S7).** Let two independent free products have
laws `μ₁, μ₂` of mass `1` with atoms `ρ_i(n) ≤ W/n`, and tests `|b_i| ≤ 1` supported in
`[U, 4U]` and `[V, 4V]`. If every box sum `∑_{n, v} a_n b_v e(-θnv)` over `[U₀, 2U₀]` and
`[V₀, 2V₀]` (`U₀ ∈ {U, 2U}`, `V₀ ∈ {V, 2V}`) with `∑ |a|² ≤ W/U₀`, `∑ |b|² ≤ W/V₀` is at most
`K`, then the multiplier `∑_{a₁, a₂} μ₁ μ₂ b₁(D₁) b₂(D₂) e(-θ D₁ D₂)` is at most `4K`. The
proof collapses it to integer coefficients `α_n = ∑_{D₁ = n} μ₁ b₁(n)`, with `|α_n| ≤ ρ₁(n)`
and `∑_{box} |α_n|² ≤ (W/U₀) ∑ |α_n| ≤ W/U₀`. -/
theorem norm_sum_bilinear_le {Λ₁ Λ₂ : Type} (S₁ : Finset Λ₁) (S₂ : Finset Λ₂)
    (μ₁ : Λ₁ → ℝ) (μ₂ : Λ₂ → ℝ) (key₁ : Λ₁ → ℕ) (key₂ : Λ₂ → ℕ) (b₁ b₂ : ℕ → ℂ)
    (U V W K θ : ℝ) (hU : 0 < U) (hV : 0 < V) (hW : 0 ≤ W)
    (hμ₁ : ∀ l ∈ S₁, 0 ≤ μ₁ l) (hμ₂ : ∀ l ∈ S₂, 0 ≤ μ₂ l)
    (hm₁ : ∑ l ∈ S₁, μ₁ l = 1) (hm₂ : ∑ l ∈ S₂, μ₂ l = 1)
    (hb₁ : ∀ n, ‖b₁ n‖ ≤ 1) (hb₂ : ∀ n, ‖b₂ n‖ ≤ 1)
    (hs₁ : ∀ n, b₁ n ≠ 0 → U ≤ n ∧ (n : ℝ) ≤ 4 * U)
    (hs₂ : ∀ n, b₂ n ≠ 0 → V ≤ n ∧ (n : ℝ) ≤ 4 * V)
    (hρ₁ : ∀ n : ℕ, 1 ≤ n → ∑ l ∈ S₁.filter (fun l => key₁ l = n), μ₁ l ≤ W / n)
    (hρ₂ : ∀ n : ℕ, 1 ≤ n → ∑ l ∈ S₂.filter (fun l => key₂ l = n), μ₂ l ≤ W / n)
    (hbox : ∀ (U₀ V₀ : ℝ) (s t : Finset ℤ) (a b : ℤ → ℂ), (U₀ = U ∨ U₀ = 2 * U) →
      (V₀ = V ∨ V₀ = 2 * V) → (∀ n ∈ s, U₀ ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U₀) →
      (∀ n ∈ t, V₀ ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * V₀) →
      ∑ n ∈ s, ‖a n‖ ^ 2 ≤ W / U₀ → ∑ n ∈ t, ‖b n‖ ^ 2 ≤ W / V₀ →
      ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * bilinearPhase θ n v‖ ≤ K) :
    ‖∑ l₁ ∈ S₁, ∑ l₂ ∈ S₂, (μ₁ l₁ : ℂ) * (μ₂ l₂ : ℂ) *
        (b₁ (key₁ l₁) * b₂ (key₂ l₂) * bilinearPhase θ (key₁ l₁) (key₂ l₂))‖ ≤ 4 * K := by
  -- the collapsed integer coefficients of one side
  have side : ∀ {Λ : Type} (S : Finset Λ) (μ : Λ → ℝ) (key : Λ → ℕ) (b : ℕ → ℂ) (U : ℝ),
      0 < U → (∀ l ∈ S, 0 ≤ μ l) → ∑ l ∈ S, μ l = 1 → (∀ n, ‖b n‖ ≤ 1) →
      (∀ n, b n ≠ 0 → U ≤ n ∧ (n : ℝ) ≤ 4 * U) →
      (∀ n : ℕ, 1 ≤ n → ∑ l ∈ S.filter (fun l => key l = n), μ l ≤ W / n) →
      let α : ℤ → ℂ := fun z => ∑ l ∈ S.filter (fun l => ((key l : ℕ) : ℤ) = z),
        (μ l : ℂ) * b (key l)
      (∀ z ∈ S.image (fun l => ((key l : ℕ) : ℤ)), α z ≠ 0 → U ≤ (z : ℝ) ∧ (z : ℝ) ≤ 4 * U) ∧
      ∀ U₀ : ℝ, (U₀ = U ∨ U₀ = 2 * U) → ∀ s ⊆ S.image (fun l => ((key l : ℕ) : ℤ)),
        (∀ z ∈ s, U₀ ≤ (z : ℝ)) → ∑ z ∈ s, ‖α z‖ ^ 2 ≤ W / U₀ := by
    intro Λ S μ key b U hU hμ hm hb hs hρ α
    have hα : ∀ z, ‖α z‖ ≤ ∑ l ∈ S.filter (fun l => ((key l : ℕ) : ℤ) = z), μ l := by
      intro z
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ l (Finset.mem_filter.1 hl).1)]
      exact mul_le_of_le_one_right (hμ l (Finset.mem_filter.1 hl).1) (hb _)
    refine ⟨fun z hz hαz => ?_, fun U₀ hU₀ s hs₀ hsU => ?_⟩
    · obtain ⟨l, hl, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hαz
      have hbl : b (key l) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hz : ((key l : ℕ) : ℤ) = z := (Finset.mem_filter.1 hl).2
      rw [← hz]
      exact_mod_cast hs _ hbl
    have hU₀ : 0 < U₀ := by rcases hU₀ with h | h <;> rw [h] <;> positivity
    -- `|α_z| ≤ W/U₀` on the box, and `∑ |α_z| ≤ 1`
    have hpt : ∀ z ∈ s, ‖α z‖ ≤ W / U₀ := by
      intro z hz
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 (hs₀ hz)
      have hn : U₀ ≤ (key l : ℝ) := by exact_mod_cast hsU _ hz
      have hn1 : 1 ≤ key l := by
        have : (0 : ℝ) < key l := lt_of_lt_of_le hU₀ hn
        exact_mod_cast this
      refine (hα _).trans ?_
      have hf : S.filter (fun l' => ((key l' : ℕ) : ℤ) = ((key l : ℕ) : ℤ)) =
          S.filter (fun l' => key l' = key l) :=
        Finset.filter_congr fun l' _ => Nat.cast_inj
      rw [hf]
      exact (hρ _ hn1).trans (div_le_div_of_nonneg_left hW hU₀ hn)
    have hsum : ∑ z ∈ s, ‖α z‖ ≤ 1 := by
      calc ∑ z ∈ s, ‖α z‖ ≤ ∑ z ∈ S.image (fun l => ((key l : ℕ) : ℤ)), ‖α z‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hs₀ fun _ _ _ => norm_nonneg _
        _ ≤ ∑ z ∈ S.image (fun l => ((key l : ℕ) : ℤ)),
              ∑ l ∈ S.filter (fun l => ((key l : ℕ) : ℤ) = z), μ l :=
            Finset.sum_le_sum fun z _ => hα z
        _ = 1 := by
            rw [Finset.sum_fiberwise_of_maps_to fun l hl => Finset.mem_image_of_mem _ hl, hm]
    calc ∑ z ∈ s, ‖α z‖ ^ 2 ≤ ∑ z ∈ s, W / U₀ * ‖α z‖ :=
          Finset.sum_le_sum fun z hz => by
            rw [sq]
            exact mul_le_mul_of_nonneg_right (hpt z hz) (norm_nonneg _)
      _ = W / U₀ * ∑ z ∈ s, ‖α z‖ := by rw [Finset.mul_sum]
      _ ≤ W / U₀ * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = W / U₀ := mul_one _
  obtain ⟨hsupp₁, hbox₁⟩ := side S₁ μ₁ key₁ b₁ U hU hμ₁ hm₁ hb₁ hs₁ hρ₁
  obtain ⟨hsupp₂, hbox₂⟩ := side S₂ μ₂ key₂ b₂ V hV hμ₂ hm₂ hb₂ hs₂ hρ₂
  set α : ℤ → ℂ := fun z => ∑ l ∈ S₁.filter (fun l => ((key₁ l : ℕ) : ℤ) = z),
    (μ₁ l : ℂ) * b₁ (key₁ l) with hα
  set β : ℤ → ℂ := fun z => ∑ l ∈ S₂.filter (fun l => ((key₂ l : ℕ) : ℤ) = z),
    (μ₂ l : ℂ) * b₂ (key₂ l) with hβ
  set s₁ := S₁.image (fun l => ((key₁ l : ℕ) : ℤ)) with hs₁def
  set s₂ := S₂.image (fun l => ((key₂ l : ℕ) : ℤ)) with hs₂def
  -- collapse to `∑_{n, v} α_n β_v e(-θnv)`
  have hcol : ∑ l₁ ∈ S₁, ∑ l₂ ∈ S₂, (μ₁ l₁ : ℂ) * (μ₂ l₂ : ℂ) *
      (b₁ (key₁ l₁) * b₂ (key₂ l₂) * bilinearPhase θ (key₁ l₁) (key₂ l₂)) =
      ∑ z ∈ s₁, ∑ y ∈ s₂, α z * β y * bilinearPhase θ z y := by
    have h₁ : ∀ l₁ ∈ S₁, ∑ l₂ ∈ S₂, (μ₁ l₁ : ℂ) * (μ₂ l₂ : ℂ) *
        (b₁ (key₁ l₁) * b₂ (key₂ l₂) * bilinearPhase θ (key₁ l₁) (key₂ l₂)) =
        ((μ₁ l₁ : ℂ) * b₁ (key₁ l₁)) *
          ∑ y ∈ s₂, β y * bilinearPhase θ (key₁ l₁) y := by
      intro l₁ _
      rw [hs₂def, hβ, ← sum_mul_eq_sum_image S₂ (fun l₂ => (μ₂ l₂ : ℂ) * b₂ (key₂ l₂))
        (fun l₂ => ((key₂ l₂ : ℕ) : ℤ)) (bilinearPhase θ (key₁ l₁)), Finset.mul_sum]
      exact Finset.sum_congr rfl fun l₂ _ => by ring
    rw [Finset.sum_congr rfl h₁, hs₁def, hα, sum_mul_eq_sum_image S₁
      (fun l₁ => (μ₁ l₁ : ℂ) * b₁ (key₁ l₁)) (fun l₁ => ((key₁ l₁ : ℕ) : ℤ))
      (fun z => ∑ y ∈ s₂, β y * bilinearPhase θ z y)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  -- the four boxes
  set B₁ := s₁.filter (fun z : ℤ => U ≤ (z : ℝ) ∧ (z : ℝ) ≤ 2 * U)
  set B₂ := s₁.filter (fun z : ℤ => 2 * U < (z : ℝ) ∧ (z : ℝ) ≤ 4 * U)
  set C₁ := s₂.filter (fun z : ℤ => V ≤ (z : ℝ) ∧ (z : ℝ) ≤ 2 * V)
  set C₂ := s₂.filter (fun z : ℤ => 2 * V < (z : ℝ) ∧ (z : ℝ) ≤ 4 * V)
  have hinner : ∀ z, ∑ y ∈ s₂, α z * β y * bilinearPhase θ z y =
      ∑ y ∈ C₁, α z * β y * bilinearPhase θ z y + ∑ y ∈ C₂, α z * β y * bilinearPhase θ z y :=
    fun z => sum_eq_add_filter_of_support s₂ _ V fun y hy hne =>
      hsupp₂ y hy fun h => hne (by rw [h, mul_zero, zero_mul])
  have houter : ∑ z ∈ s₁, ∑ y ∈ s₂, α z * β y * bilinearPhase θ z y =
      ∑ z ∈ B₁, ∑ y ∈ s₂, α z * β y * bilinearPhase θ z y +
        ∑ z ∈ B₂, ∑ y ∈ s₂, α z * β y * bilinearPhase θ z y :=
    sum_eq_add_filter_of_support s₁ _ U fun z hz hne =>
      hsupp₁ z hz fun h => hne (Finset.sum_eq_zero fun y _ => by rw [h, zero_mul, zero_mul])
  rw [hcol, houter]
  simp_rw [hinner, Finset.sum_add_distrib]
  have hb : ∀ (U₀ V₀ : ℝ) (B : Finset ℤ) (C : Finset ℤ), (U₀ = U ∨ U₀ = 2 * U) →
      (V₀ = V ∨ V₀ = 2 * V) → B ⊆ s₁ → C ⊆ s₂ → (∀ n ∈ B, U₀ ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U₀) →
      (∀ n ∈ C, V₀ ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * V₀) →
      ‖∑ z ∈ B, ∑ y ∈ C, α z * β y * bilinearPhase θ z y‖ ≤ K :=
    fun U₀ V₀ B C hU₀ hV₀ hB hC hBs hCs => hbox U₀ V₀ B C α β hU₀ hV₀ hBs hCs
      (hbox₁ U₀ hU₀ B hB fun n hn => (hBs n hn).1) (hbox₂ V₀ hV₀ C hC fun n hn => (hCs n hn).1)
  have hB₁ : ∀ n ∈ B₁, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U := fun n hn => (Finset.mem_filter.1 hn).2
  have hB₂ : ∀ n ∈ B₂, 2 * U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (2 * U) := fun n hn => by
    obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.1 hn).2
    exact ⟨h₁.le, by linarith⟩
  have hC₁ : ∀ n ∈ C₁, V ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * V := fun n hn => (Finset.mem_filter.1 hn).2
  have hC₂ : ∀ n ∈ C₂, 2 * V ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (2 * V) := fun n hn => by
    obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.1 hn).2
    exact ⟨h₁.le, by linarith⟩
  have e₁ := hb U V B₁ C₁ (Or.inl rfl) (Or.inl rfl) (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) hB₁ hC₁
  have e₂ := hb U (2 * V) B₁ C₂ (Or.inl rfl) (Or.inr rfl) (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) hB₁ hC₂
  have e₃ := hb (2 * U) V B₂ C₁ (Or.inr rfl) (Or.inl rfl) (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) hB₂ hC₁
  have e₄ := hb (2 * U) (2 * V) B₂ C₂ (Or.inr rfl) (Or.inr rfl) (Finset.filter_subset _ _)
    (Finset.filter_subset _ _) hB₂ hC₂
  calc _ ≤ ‖∑ z ∈ B₁, ∑ y ∈ C₁, α z * β y * bilinearPhase θ z y‖ +
        ‖∑ z ∈ B₁, ∑ y ∈ C₂, α z * β y * bilinearPhase θ z y‖ +
        (‖∑ z ∈ B₂, ∑ y ∈ C₁, α z * β y * bilinearPhase θ z y‖ +
          ‖∑ z ∈ B₂, ∑ y ∈ C₂, α z * β y * bilinearPhase θ z y‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    _ ≤ K + K + (K + K) := add_le_add (add_le_add e₁ e₂) (add_le_add e₃ e₄)
    _ = 4 * K := by ring

end Erdos408.TwoSided.Arcs
