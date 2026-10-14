import Erdos408.OneSided.Goodness.BadCount
import Erdos408.OneSided.Goodness.Targets
import Erdos408.OneSided.Decomposition.Eventually
import Erdos408.OneSided.Pairing

/-!
# The bad mass

The proof of `eventually_badMass_le` (`blueprint/one_sided_type_ii.md` §14, PD §4.9): the
absolute row mass of `𝒯` on pairs with a bad source or a bad target is at most
`C₀ UV L^{3A₀} exp(-L^{a₋}/8)`. By `norm_rowOp_le`, an entry of `𝒯` is at most
`∏ V_i^{-1} ([t = b - a] + 4 L^{3A₀}/Y)` on its support.

* **Comparison part.** A source has at most `17 (10Y + 1)` target positions and at most
  `(log₂ 16U)^K` target lists at each (`card_det_le`, `card_lists_dvd_le`), so the factor
  `4 L^{3A₀}/Y` leaves `O(L^{3A₀} (log U)^K)` per source. The bad sources are counted at
  fixed lists by `eventually_card_not_isGood_le`, with the interval bound of
  `exists_card_cong_le` at `S = G`, the list product: at most `90 UV/G · e^{-L^{a₋}/4}`
  up to errors. The lists carry `∏ V_i^{-M} ∑ 1/G ≤ 1`.
* **Raw part.** At fixed lists the pairs `(P, Q)` with `det(P, Q) = D (b - a)` are counted
  jointly (`card_pairs_le`) with `S = G a`: at most `17 · 90 UV/(G a) · e^{-L^{a₋}/4}` up to
  errors. The new labels add `∏ V_i^{-1} ∑ 1/a ≤ 1` (PD `mem:one-edge-label-mass`).
* **Bad targets.** The same counts with source and target exchanged.
* The errors are `exp(O(L^{1/2})) UV min(U, V)^{-1/5}`, negligible since
  `min(U, V) ≥ x^γ ≥ exp(L^{0.99})`.
-/

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### Lists -/

/-- The list part of `RowEdge`. -/
def ListEdge (Y d₀ : ℝ) {J : ℕ} (p p' : Lists K J) : Prop :=
  (∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc) ∧
    (∀ i i' h', p' i (Fin.last J) ≠ p i' h') ∧
    d₀ ≤ (padProd p : ℝ) ∧ (padProd p : ℝ) < 2 * d₀ ∧
    Y < (lastProd p : ℝ) ∧ (lastProd p : ℝ) < 4 * Y ∧
    Y < (lastProd p' : ℝ) ∧ (lastProd p' : ℝ) < 4 * Y

/-- The list part of an edge. -/
theorem RowEdge.listEdge {Y d₀ : ℝ} {J : ℕ} {P Q : ℕ × ℕ} {p p' : Lists K J}
    (h : RowEdge Y d₀ P p Q p') : ListEdge Y d₀ p p' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2⟩

/-- Copied pads have the same product. -/
theorem padProd_eq_of_pads {J : ℕ} {p p' : Lists K J}
    (h : ∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc) : padProd p' = padProd p := by
  unfold padProd
  exact prod_congr rfl fun i _ => prod_congr rfl fun h' _ => h i h'

/-- `det(Q, P) = -det(P, Q)`. -/
theorem det_swap (P Q : ℕ × ℕ) : det Q P = -det P Q := by
  unfold det
  ring

/-- The list product of a list in `lists` is squarefree, for disjoint bands. -/
theorem squarefree_listProd {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {J : ℕ}
    {p : Lists K J} (hp : p ∈ lists x d J) : Squarefree (listProd p) := by
  have h := squarefree_prod_of_injective
    (label_injective hdisj (fun i h => lists_slot_mem_band hp i h) (lists_group_injective hp))
    fun ih => (mem_filter.1 (lists_slot_mem_band hp ih.1 ih.2)).2
  rwa [Fintype.prod_prod_type] at h

/-- `∑_{a ∈ labels} 1/a = ∏_i V_i`. -/
theorem sum_labels_inv_prod (x : ℝ) (d : Data K) :
    ∑ t ∈ d.labels x, ((∏ i, t i : ℕ) : ℝ)⁻¹ = d.bandMass x := by
  unfold Data.labels Data.bandMass harmonicMass
  simp_rw [one_div]
  rw [prod_univ_sum (fun i => band x (d.a i)) fun _ q => ((q : ℕ) : ℝ)⁻¹]
  refine sum_congr rfl fun t _ => ?_
  push_cast
  rw [prod_inv_distrib]

open scoped Classical in
/-- With the pads of `p` fixed, the lists `p'` have `∑ 1/a ≤ ∏_i V_i`, where `a` is the
product of the last slots: `p'` is fixed by its last slots. -/
theorem sum_inv_lastProd_le {x : ℝ} {d : Data K} {J : ℕ} (p : Lists K J) :
    ∑ p' ∈ (lists x d J).filter (fun p' => ∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc),
      ((lastProd p' : ℕ) : ℝ)⁻¹ ≤ d.bandMass x := by
  set f : Lists K J → Fin K → ℕ := fun p' i => p' i (Fin.last J)
  have hinj : Set.InjOn f
      ((lists x d J).filter fun p' => ∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc) := by
    intro p₁ hp₁ p₂ hp₂ hf
    have h₁ := (mem_filter.1 (mem_coe.1 hp₁)).2
    have h₂ := (mem_filter.1 (mem_coe.1 hp₂)).2
    funext i h
    refine Fin.lastCases ?_ (fun h => ?_) h
    · exact congrFun hf i
    · rw [h₁, h₂]
  have hsub : ((lists x d J).filter fun p' => ∀ i (h : Fin J),
      p' i h.castSucc = p i h.castSucc).image f ⊆ d.labels x := by
    intro t ht
    obtain ⟨p', hp', rfl⟩ := mem_image.1 ht
    exact Fintype.mem_piFinset.2 fun i => lists_slot_mem_band (mem_filter.1 hp').1 i _
  calc ∑ p' ∈ (lists x d J).filter (fun p' => ∀ i (h : Fin J), p' i h.castSucc = p i h.castSucc),
        ((lastProd p' : ℕ) : ℝ)⁻¹
      = ∑ t ∈ ((lists x d J).filter fun p' => ∀ i (h : Fin J),
          p' i h.castSucc = p i h.castSucc).image f, ((∏ i, t i : ℕ) : ℝ)⁻¹ :=
        (sum_image (f := fun t : Fin K → ℕ => ((∏ i, t i : ℕ) : ℝ)⁻¹) hinj).symm
    _ ≤ ∑ t ∈ d.labels x, ((∏ i, t i : ℕ) : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = d.bandMass x := sum_labels_inv_prod x d

open scoped Classical in
/-- PD `mem:one-edge-label-mass`: `∏ V_i^{-(M + 1)} ∑ 1/(G a) ≤ 1` over the list pairs with
copied pads, `G` the list product of the source and `a` the last product of the target. -/
theorem mass_mul_sum_inv_le {x : ℝ} {d : Data K} (hV : 0 < d.bandMass x) (Y d₀ : ℝ) :
    stateMass x d * (d.bandMass x)⁻¹ *
      ∑ pp ∈ (lists x d (padCount x) ×ˢ lists x d (padCount x)).filter
        (fun pp => ListEdge Y d₀ pp.1 pp.2),
        (((listProd pp.1 : ℕ) : ℝ) * (lastProd pp.2 : ℕ))⁻¹ ≤ 1 := by
  set J := padCount x
  have hsum : ∑ pp ∈ (lists x d J ×ˢ lists x d J).filter (fun pp => ListEdge Y d₀ pp.1 pp.2),
      (((listProd pp.1 : ℕ) : ℝ) * (lastProd pp.2 : ℕ))⁻¹ ≤
        ∑ p ∈ lists x d J, ((listProd p : ℕ) : ℝ)⁻¹ * d.bandMass x := by
    rw [sum_filter, sum_product]
    refine sum_le_sum fun p _ => ?_
    calc ∑ p' ∈ lists x d J, (if ListEdge Y d₀ p p' then
          (((listProd p : ℕ) : ℝ) * (lastProd p' : ℕ))⁻¹ else 0)
        ≤ ∑ p' ∈ (lists x d J).filter (fun p' => ∀ i (h : Fin J),
            p' i h.castSucc = p i h.castSucc),
            ((listProd p : ℕ) : ℝ)⁻¹ * ((lastProd p' : ℕ) : ℝ)⁻¹ := by
          rw [sum_filter]
          refine sum_le_sum fun p' _ => ?_
          by_cases h : ListEdge Y d₀ p p'
          · rw [ite_eq_left h, ite_eq_left h.1, mul_inv]
          · rw [ite_eq_right h]
            split_ifs <;> positivity
      _ ≤ ((listProd p : ℕ) : ℝ)⁻¹ * d.bandMass x := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_inv_lastProd_le p) (by positivity)
  calc stateMass x d * (d.bandMass x)⁻¹ *
        ∑ pp ∈ (lists x d J ×ˢ lists x d J).filter (fun pp => ListEdge Y d₀ pp.1 pp.2),
          (((listProd pp.1 : ℕ) : ℝ) * (lastProd pp.2 : ℕ))⁻¹
      ≤ stateMass x d * (d.bandMass x)⁻¹ *
          ∑ p ∈ lists x d J, ((listProd p : ℕ) : ℝ)⁻¹ * d.bandMass x := by
        gcongr
        exact mul_nonneg (stateMass_nonneg x d) (inv_nonneg.2 hV.le)
    _ = stateMass x d * ∑ p ∈ lists x d J, ((listProd p : ℕ) : ℝ)⁻¹ := by
        rw [← sum_mul]
        field_simp
    _ ≤ 1 := stateMass_mul_sum_inv_listProd_le x d

open scoped Classical in
/-- The mirror of `mass_mul_sum_inv_le`, with `G` the list product of the target and `b` the
last product of the source. -/
theorem mass_mul_sum_inv_le' {x : ℝ} {d : Data K} (hV : 0 < d.bandMass x) (Y d₀ : ℝ) :
    stateMass x d * (d.bandMass x)⁻¹ *
      ∑ pp ∈ (lists x d (padCount x) ×ˢ lists x d (padCount x)).filter
        (fun pp => ListEdge Y d₀ pp.1 pp.2),
        (((listProd pp.2 : ℕ) : ℝ) * (lastProd pp.1 : ℕ))⁻¹ ≤ 1 := by
  set J := padCount x
  have hsum : ∑ pp ∈ (lists x d J ×ˢ lists x d J).filter (fun pp => ListEdge Y d₀ pp.1 pp.2),
      (((listProd pp.2 : ℕ) : ℝ) * (lastProd pp.1 : ℕ))⁻¹ ≤
        ∑ p' ∈ lists x d J, ((listProd p' : ℕ) : ℝ)⁻¹ * d.bandMass x := by
    rw [sum_filter, sum_product, sum_comm]
    refine sum_le_sum fun p' _ => ?_
    calc ∑ p ∈ lists x d J, (if ListEdge Y d₀ p p' then
          (((listProd p' : ℕ) : ℝ) * (lastProd p : ℕ))⁻¹ else 0)
        ≤ ∑ p ∈ (lists x d J).filter (fun p => ∀ i (h : Fin J),
            p i h.castSucc = p' i h.castSucc),
            ((listProd p' : ℕ) : ℝ)⁻¹ * ((lastProd p : ℕ) : ℝ)⁻¹ := by
          rw [sum_filter]
          refine sum_le_sum fun p _ => ?_
          by_cases h : ListEdge Y d₀ p p'
          · rw [ite_eq_left h, ite_eq_left fun i h' => (h.1 i h').symm, mul_inv]
          · rw [ite_eq_right h]
            split_ifs <;> positivity
      _ ≤ ((listProd p' : ℕ) : ℝ)⁻¹ * d.bandMass x := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (sum_inv_lastProd_le p') (by positivity)
  calc stateMass x d * (d.bandMass x)⁻¹ *
        ∑ pp ∈ (lists x d J ×ˢ lists x d J).filter (fun pp => ListEdge Y d₀ pp.1 pp.2),
          (((listProd pp.2 : ℕ) : ℝ) * (lastProd pp.1 : ℕ))⁻¹
      ≤ stateMass x d * (d.bandMass x)⁻¹ *
          ∑ p' ∈ lists x d J, ((listProd p' : ℕ) : ℝ)⁻¹ * d.bandMass x := by
        gcongr
        exact mul_nonneg (stateMass_nonneg x d) (inv_nonneg.2 hV.le)
    _ = stateMass x d * ∑ p ∈ lists x d J, ((listProd p : ℕ) : ℝ)⁻¹ := by
        rw [← sum_mul]
        field_simp
    _ ≤ 1 := stateMass_mul_sum_inv_listProd_le x d

/-! ### Edges -/

/-- The defining properties of a state, on the underlying pair. -/
theorem mem_states_iff {x : ℝ} {d : Data K} {Y d₀ : ℝ} {y : (ℕ × ℕ) × Lists K (padCount x)} :
    y ∈ states x d Y d₀ ↔ y.1 ∈ positions d Y d₀ ∧ y.2 ∈ lists x d (padCount x) ∧
      ∀ i h, y.2 i h ∣ y.1.1 := by
  unfold states
  rw [mem_filter, mem_product, and_assoc]

open scoped Classical in
/-- Comparison part: a source has at most `17 (10Y + 1) (log₂ 16U)^K` targets. -/
theorem card_targets_le {x : ℝ} {d : Data K} {Y d₀ : ℝ} (hY : 0 ≤ Y) (hU : 0 < d₀ * Y * d.Hm)
    (hV : 0 ≤ d.Hn) {y₁ : (ℕ × ℕ) × Lists K (padCount x)} (hy₁ : y₁ ∈ states x d Y d₀) :
    (#{y₂ ∈ states x d Y d₀ | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} : ℝ) ≤
      17 * (10 * Y + 1) * (Nat.log 2 ⌊16 * (d₀ * Y * d.Hm)⌋₊ ^ K : ℕ) := by
  set U := d₀ * Y * d.Hm
  set D := padProd y₁.2
  set F := {Q ∈ positions d Y d₀ | (D : ℤ) ∣ det y₁.1 Q ∧ |((det y₁.1 Q / D : ℤ) : ℝ)| < 5 * Y}
  set LF : ℕ × ℕ → Finset (Lists K (padCount x)) := fun Q =>
    {p' ∈ lists x d (padCount x) | (∀ i (h : Fin (padCount x)),
      p' i h.castSucc = y₁.2 i h.castSucc) ∧ ∀ i, p' i (Fin.last _) ∣ Q.1}
  have hsub : {y₂ ∈ states x d Y d₀ | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} ⊆
      F.biUnion fun Q => (LF Q).image fun p' => (Q, p') := by
    intro y₂ hy₂
    obtain ⟨hst, he⟩ := mem_filter.1 hy₂
    obtain ⟨hpos, hl, hdvd⟩ := mem_states_iff.1 hst
    refine mem_biUnion.2 ⟨y₂.1, mem_filter.2 ⟨hpos, he.2.2.2.2.1, he.2.2.2.2.2.1⟩,
      mem_image.2 ⟨y₂.2, mem_filter.2 ⟨hl, he.1, fun i => hdvd i _⟩, rfl⟩⟩
  obtain ⟨hP, -, -⟩ := mem_states_iff.1 hy₁
  rw [positions_eq_rootBox] at hP
  obtain ⟨hP1, -, -, -, hcop⟩ := mem_rootBox_bounds hU.le hV hP
  have hP0 : 0 < y₁.1.1 := by exact_mod_cast hU.trans_le hP1
  have hF := card_det_le hU.le hV hP1 hP0 hcop D hY
  rw [← positions_eq_rootBox] at hF
  have hLF : ∀ Q ∈ F, (LF Q).card ≤ Nat.log 2 ⌊16 * U⌋₊ ^ K := by
    intro Q hQ
    have hQ' := (mem_filter.1 hQ).1
    rw [positions_eq_rootBox] at hQ'
    obtain ⟨hQ1, hQ16, -, -, -⟩ := mem_rootBox_bounds hU.le hV hQ'
    have hQ0 : Q.1 ≠ 0 := by
      have : (0 : ℝ) < Q.1 := hU.trans_le hQ1
      exact_mod_cast this.ne'
    refine (card_lists_dvd_le y₁.2 hQ0).trans (Nat.pow_le_pow_left (Nat.log_mono_right ?_) K)
    exact Nat.le_floor hQ16
  calc (#{y₂ ∈ states x d Y d₀ | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} : ℝ)
      ≤ ∑ Q ∈ F, ((LF Q).card : ℝ) := by
        refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
        push_cast
        exact sum_le_sum fun Q _ => by exact_mod_cast card_image_le
    _ ≤ ∑ _Q ∈ F, ((Nat.log 2 ⌊16 * U⌋₊ ^ K : ℕ) : ℝ) :=
        sum_le_sum fun Q hQ => by exact_mod_cast hLF Q hQ
    _ = F.card * ((Nat.log 2 ⌊16 * U⌋₊ ^ K : ℕ) : ℝ) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 17 * (10 * Y + 1) * ((Nat.log 2 ⌊16 * U⌋₊ ^ K : ℕ) : ℝ) := by gcongr

open scoped Classical in
/-- Comparison part, reversed: a target has at most `17 (10Y + 1) (log₂ 16U)^K` sources. -/
theorem card_sources_le {x : ℝ} {d : Data K} {Y d₀ : ℝ} (hY : 0 ≤ Y) (hU : 0 < d₀ * Y * d.Hm)
    (hV : 0 ≤ d.Hn) {y₂ : (ℕ × ℕ) × Lists K (padCount x)} (hy₂ : y₂ ∈ states x d Y d₀) :
    (#{y₁ ∈ states x d Y d₀ | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} : ℝ) ≤
      17 * (10 * Y + 1) * (Nat.log 2 ⌊16 * (d₀ * Y * d.Hm)⌋₊ ^ K : ℕ) := by
  set U := d₀ * Y * d.Hm
  set D := padProd y₂.2
  set F := {P ∈ positions d Y d₀ | (D : ℤ) ∣ det y₂.1 P ∧ |((det y₂.1 P / D : ℤ) : ℝ)| < 5 * Y}
  set LF : ℕ × ℕ → Finset (Lists K (padCount x)) := fun P =>
    {p ∈ lists x d (padCount x) | (∀ i (h : Fin (padCount x)),
      p i h.castSucc = y₂.2 i h.castSucc) ∧ ∀ i, p i (Fin.last _) ∣ P.1}
  have hsub : {y₁ ∈ states x d Y d₀ | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} ⊆
      F.biUnion fun P => (LF P).image fun p => (P, p) := by
    intro y₁ hy₁
    obtain ⟨hst, he⟩ := mem_filter.1 hy₁
    obtain ⟨hpos, hl, hdvd⟩ := mem_states_iff.1 hst
    have hD : padProd y₁.2 = D := (padProd_eq_of_pads he.1).symm
    have hdvd' : (D : ℤ) ∣ det y₂.1 y₁.1 := by
      rw [det_swap, ← hD]
      exact dvd_neg.2 he.2.2.2.2.1
    have ht : |((det y₂.1 y₁.1 / D : ℤ) : ℝ)| < 5 * Y := by
      rw [det_swap, Int.neg_ediv_of_dvd (hD ▸ he.2.2.2.2.1), Int.cast_neg, abs_neg, ← hD]
      exact he.2.2.2.2.2.1
    refine mem_biUnion.2 ⟨y₁.1, mem_filter.2 ⟨hpos, hdvd', ht⟩,
      mem_image.2 ⟨y₁.2, mem_filter.2 ⟨hl, fun i h => (he.1 i h).symm, fun i => hdvd i _⟩, rfl⟩⟩
  obtain ⟨hQ, -, -⟩ := mem_states_iff.1 hy₂
  rw [positions_eq_rootBox] at hQ
  obtain ⟨hQ1, -, -, -, hcop⟩ := mem_rootBox_bounds hU.le hV hQ
  have hQ0 : 0 < y₂.1.1 := by exact_mod_cast hU.trans_le hQ1
  have hF := card_det_le hU.le hV hQ1 hQ0 hcop D hY
  rw [← positions_eq_rootBox] at hF
  have hLF : ∀ P ∈ F, (LF P).card ≤ Nat.log 2 ⌊16 * U⌋₊ ^ K := by
    intro P hP
    have hP' := (mem_filter.1 hP).1
    rw [positions_eq_rootBox] at hP'
    obtain ⟨hP1, hP16, -, -, -⟩ := mem_rootBox_bounds hU.le hV hP'
    have hP0 : P.1 ≠ 0 := by
      have : (0 : ℝ) < P.1 := hU.trans_le hP1
      exact_mod_cast this.ne'
    refine (card_lists_dvd_le y₂.2 hP0).trans (Nat.pow_le_pow_left (Nat.log_mono_right ?_) K)
    exact Nat.le_floor hP16
  calc (#{y₁ ∈ states x d Y d₀ | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} : ℝ)
      ≤ ∑ P ∈ F, ((LF P).card : ℝ) := by
        refine (Nat.cast_le.2 ((card_le_card hsub).trans card_biUnion_le)).trans ?_
        push_cast
        exact sum_le_sum fun P _ => by exact_mod_cast card_image_le
    _ ≤ ∑ _P ∈ F, ((Nat.log 2 ⌊16 * U⌋₊ ^ K : ℕ) : ℝ) :=
        sum_le_sum fun P hP => by exact_mod_cast hLF P hP
    _ = F.card * ((Nat.log 2 ⌊16 * U⌋₊ ^ K : ℕ) : ℝ) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 17 * (10 * Y + 1) * ((Nat.log 2 ⌊16 * U⌋₊ ^ K : ℕ) : ℝ) := by gcongr

/-- On a raw edge, `det(P, Q) = D (b - a)`. -/
theorem det_eq_of_rawEdge {Y d₀ : ℝ} {J : ℕ} {P Q : ℕ × ℕ} {p p' : Lists K J}
    (he : RowEdge Y d₀ P p Q p') (hr : RawEdge P p Q p') :
    det P Q = padProd p * ((lastProd p : ℤ) - lastProd p') := by
  rw [← Int.mul_ediv_cancel' he.2.2.2.2.1]
  unfold RawEdge at hr
  rw [hr]

/-- With disjoint bands, the last product of a state divides its first coordinate. -/
theorem lastProd_dvd {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {J : ℕ}
    {p : Lists K J} (hp : p ∈ lists x d J) {n : ℕ} (hdvd : ∀ i h, p i h ∣ n) :
    lastProd p ∣ n := by
  have h := listProd_dvd_of_dvd hdisj (fun i h => lists_slot_mem_band hp i h)
    (lists_group_injective hp) hdvd
  rw [listProd_eq_padProd_mul_lastProd] at h
  exact (Dvd.intro_left _ rfl).trans h

open scoped Classical in
/-- Raw part, bad source: the raw edges from bad sources inject, list pair by list pair, into
the pairs `(P, Q)` with `G ∣ P₁`, `a ∣ Q₁`, `det(P, Q) = D (b - a)` and `P` bad. -/
theorem card_raw_le {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (Y d₀ : ℝ) :
    #{yy ∈ states x d Y d₀ ×ˢ states x d Y d₀ | ¬ IsGood x d Y d₀ yy.1.1 yy.1.2 ∧
        RowEdge Y d₀ yy.1.1 yy.1.2 yy.2.1 yy.2.2 ∧ RawEdge yy.1.1 yy.1.2 yy.2.1 yy.2.2} ≤
      ∑ pp ∈ (lists x d (padCount x) ×ˢ lists x d (padCount x)).filter
          (fun pp => ListEdge Y d₀ pp.1 pp.2),
        #{PQ ∈ positions d Y d₀ ×ˢ positions d Y d₀ | (listProd pp.1 : ℤ) ∣ PQ.1.1 ∧
          (lastProd pp.2 : ℤ) ∣ PQ.2.1 ∧
          det PQ.1 PQ.2 = padProd pp.1 * ((lastProd pp.1 : ℤ) - lastProd pp.2) ∧
          ¬ IsGood x d Y d₀ PQ.1 pp.1} := by
  rw [card_eq_sum_card_fiberwise (f := fun yy => (yy.1.2, yy.2.2)) (t :=
    (lists x d (padCount x) ×ˢ lists x d (padCount x)).filter
      (fun pp => ListEdge Y d₀ pp.1 pp.2))]
  · refine sum_le_sum fun pp _ => card_le_card_of_injOn (fun yy => (yy.1.1, yy.2.1)) ?_ ?_
    · intro yy hyy
      rw [mem_coe, filter_filter, mem_filter] at hyy
      obtain ⟨hmem, ⟨hbad, he, hr⟩, hpp⟩ := hyy
      obtain ⟨h₁, h₂⟩ := mem_product.1 hmem
      obtain ⟨hpos₁, hl₁, hdvd₁⟩ := mem_states_iff.1 h₁
      obtain ⟨hpos₂, hl₂, hdvd₂⟩ := mem_states_iff.1 h₂
      rw [← hpp]
      refine mem_coe.2 (mem_filter.2 ⟨mem_product.2 ⟨hpos₁, hpos₂⟩, ?_, ?_,
        det_eq_of_rawEdge he hr, hbad⟩)
      · exact_mod_cast listProd_dvd_of_dvd hdisj (fun i h => lists_slot_mem_band hl₁ i h)
          (lists_group_injective hl₁) hdvd₁
      · exact_mod_cast lastProd_dvd hdisj hl₂ hdvd₂
    · intro yy hyy yy' hyy' heq
      have hpp := (mem_filter.1 (mem_coe.1 hyy)).2
      have hpp' := (mem_filter.1 (mem_coe.1 hyy')).2
      have h₁ : yy.1.1 = yy'.1.1 := (Prod.ext_iff.1 heq).1
      have h₂ : yy.2.1 = yy'.2.1 := (Prod.ext_iff.1 heq).2
      rw [← hpp'] at hpp
      exact Prod.ext (Prod.ext h₁ (Prod.ext_iff.1 hpp).1) (Prod.ext h₂ (Prod.ext_iff.1 hpp).2)
  · intro yy hyy
    obtain ⟨hmem, -, he, -⟩ := mem_filter.1 hyy
    obtain ⟨h₁, h₂⟩ := mem_product.1 hmem
    exact mem_filter.2 ⟨mem_product.2 ⟨(mem_states_iff.1 h₁).2.1, (mem_states_iff.1 h₂).2.1⟩,
      he.listEdge⟩

open scoped Classical in
/-- Raw part, bad target: the same injection with source and target exchanged, into the
pairs `(Q, P)` with `G' ∣ Q₁`, `b ∣ P₁`, `det(Q, P) = D (a - b)` and `Q` bad. -/
theorem card_raw_le' {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (Y d₀ : ℝ) :
    #{yy ∈ states x d Y d₀ ×ˢ states x d Y d₀ | ¬ IsGood x d Y d₀ yy.2.1 yy.2.2 ∧
        RowEdge Y d₀ yy.1.1 yy.1.2 yy.2.1 yy.2.2 ∧ RawEdge yy.1.1 yy.1.2 yy.2.1 yy.2.2} ≤
      ∑ pp ∈ (lists x d (padCount x) ×ˢ lists x d (padCount x)).filter
          (fun pp => ListEdge Y d₀ pp.1 pp.2),
        #{QP ∈ positions d Y d₀ ×ˢ positions d Y d₀ | (listProd pp.2 : ℤ) ∣ QP.1.1 ∧
          (lastProd pp.1 : ℤ) ∣ QP.2.1 ∧
          det QP.1 QP.2 = padProd pp.1 * ((lastProd pp.2 : ℤ) - lastProd pp.1) ∧
          ¬ IsGood x d Y d₀ QP.1 pp.2} := by
  rw [card_eq_sum_card_fiberwise (f := fun yy => (yy.1.2, yy.2.2)) (t :=
    (lists x d (padCount x) ×ˢ lists x d (padCount x)).filter
      (fun pp => ListEdge Y d₀ pp.1 pp.2))]
  · refine sum_le_sum fun pp _ => card_le_card_of_injOn (fun yy => (yy.2.1, yy.1.1)) ?_ ?_
    · intro yy hyy
      rw [mem_coe, filter_filter, mem_filter] at hyy
      obtain ⟨hmem, ⟨hbad, he, hr⟩, hpp⟩ := hyy
      obtain ⟨h₁, h₂⟩ := mem_product.1 hmem
      obtain ⟨hpos₁, hl₁, hdvd₁⟩ := mem_states_iff.1 h₁
      obtain ⟨hpos₂, hl₂, hdvd₂⟩ := mem_states_iff.1 h₂
      rw [← hpp]
      refine mem_coe.2 (mem_filter.2 ⟨mem_product.2 ⟨hpos₂, hpos₁⟩, ?_, ?_, ?_, hbad⟩)
      · exact_mod_cast listProd_dvd_of_dvd hdisj (fun i h => lists_slot_mem_band hl₂ i h)
          (lists_group_injective hl₂) hdvd₂
      · exact_mod_cast lastProd_dvd hdisj hl₁ hdvd₁
      · rw [det_swap, det_eq_of_rawEdge he hr]
        ring
    · intro yy hyy yy' hyy' heq
      have hpp := (mem_filter.1 (mem_coe.1 hyy)).2
      have hpp' := (mem_filter.1 (mem_coe.1 hyy')).2
      have h₁ : yy.2.1 = yy'.2.1 := (Prod.ext_iff.1 heq).1
      have h₂ : yy.1.1 = yy'.1.1 := (Prod.ext_iff.1 heq).2
      rw [← hpp'] at hpp
      exact Prod.ext (Prod.ext h₂ (Prod.ext_iff.1 hpp).1) (Prod.ext h₁ (Prod.ext_iff.1 hpp).2)
  · intro yy hyy
    obtain ⟨hmem, -, he, -⟩ := mem_filter.1 hyy
    obtain ⟨h₁, h₂⟩ := mem_product.1 hmem
    exact mem_filter.2 ⟨mem_product.2 ⟨(mem_states_iff.1 h₁).2.1, (mem_states_iff.1 h₂).2.1⟩,
      he.listEdge⟩

open scoped Classical in
/-- The bad states inject, list by list, into the positions `P` with `G ∣ P₁` that are bad. -/
theorem card_bad_le {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) (Y d₀ : ℝ) :
    #{y ∈ states x d Y d₀ | ¬ IsGood x d Y d₀ y.1 y.2} ≤
      ∑ p ∈ lists x d (padCount x),
        #{P ∈ positions d Y d₀ | (listProd p : ℤ) ∣ P.1 ∧ ¬ IsGood x d Y d₀ P p} := by
  rw [card_eq_sum_card_fiberwise (f := fun y => y.2) (t := lists x d (padCount x))]
  · refine sum_le_sum fun p _ => card_le_card_of_injOn (fun y => y.1) ?_ ?_
    · intro y hy
      rw [mem_coe, filter_filter, mem_filter] at hy
      obtain ⟨hst, hbad, hp⟩ := hy
      obtain ⟨hpos, hl, hdvd⟩ := mem_states_iff.1 hst
      rw [← hp]
      refine mem_coe.2 (mem_filter.2 ⟨hpos, ?_, hbad⟩)
      exact_mod_cast listProd_dvd_of_dvd hdisj (fun i h => lists_slot_mem_band hl i h)
        (lists_group_injective hl) hdvd
    · intro y hy y' hy' heq
      have hp := (mem_filter.1 (mem_coe.1 hy)).2
      have hp' := (mem_filter.1 (mem_coe.1 hy')).2
      exact Prod.ext heq (hp.trans hp'.symm)
  · intro y hy
    exact (mem_states_iff.1 (mem_filter.1 hy).1).2.1

/-! ### Bad counts at fixed lists -/

/-- The interval bounds of the congruence counts (`exists_card_cong_le`) at the constant
`C₁`. -/
def CongBound (C₁ : ℝ) : Prop :=
  ∀ U V : ℝ, 2 ≤ U → 2 ≤ V → ∀ G a : ℕ, Squarefree (G * a) → ∀ z : ℤ, z ≠ 0 →
    IsCoprime z (a : ℤ) → ∀ k : ℤ,
    IntervalBound (rootBox U V) (fun P => (G : ℤ) ∣ P.1 ∧
        (a : ℤ) ∣ z * rootC P.1 P.2 + (k - ⌊(z : ℝ) * rootRatio P⌋) * P.1)
      (90 * U * V / ((G : ℝ) * a)) (3 * |(z : ℝ)| *
        (C₁ * U * V * ((G : ℝ) * a) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2)))

/-- `exists_card_cong_le` as interval bounds. -/
theorem exists_congBound : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ CongBound C₁ := by
  obtain ⟨C₁, hC₁, h⟩ := exists_card_cong_le
  refine ⟨C₁, hC₁, fun U V hU hV G a hS z hz hza k α β hα hαβ hβ => ?_⟩
  have := h U V hU hV G a hS z hz hza k α β hα hαβ hβ
  simp only [and_assoc]
  refine this.trans (le_of_eq ?_)
  ring

open scoped Classical in
/-- The bad-count hypothesis at fixed `x, d, Y, d₀`, from `eventually_card_not_isGood_le`. -/
def BadCountBound (x alo : ℝ) (d : Data K) (Y d₀ : ℝ) : Prop :=
  ∀ p ∈ lists x d (padCount x), ∀ T : Finset (ℕ × ℕ), (∀ P ∈ T, 0 < P.1) →
    ∀ (Φ : ℕ × ℕ → Prop) [DecidablePred Φ] (A E : ℝ), 0 ≤ A → 0 ≤ E →
      IntervalBound T Φ A E →
      (#{P ∈ T | Φ P ∧ ¬ IsGood x d Y d₀ P p} : ℝ) ≤
        A * Real.exp (-Real.log x ^ alo / 4) + E * badIntervals x d Y p

/-- `IsCoprime (D (b - a)) a` from `(D, a) = (b, a) = 1`. -/
theorem isCoprime_mul_sub {D b a : ℤ} (hD : IsCoprime D a) (hb : IsCoprime b a) :
    IsCoprime (D * (b - a)) a := by
  refine hD.mul_left ?_
  obtain ⟨u, v, h⟩ := hb
  exact ⟨u, v + u, by linear_combination h⟩

/-- `z ≠ 0` when `(z, a) = 1` and `a ≥ 2`. -/
theorem ne_zero_of_isCoprime {z : ℤ} {a : ℕ} (h : IsCoprime z (a : ℤ)) (ha : 2 ≤ a) : z ≠ 0 := by
  rintro rfl
  rw [isCoprime_zero_left, Int.isUnit_iff] at h
  omega

/-- The coprimality of a source list product `G = D b` with a new last product `a`. -/
theorem isCoprime_of_coprime {J : ℕ} {p : Lists K J} {a : ℕ}
    (h : Nat.Coprime (listProd p) a) :
    IsCoprime ((padProd p : ℤ) * ((lastProd p : ℤ) - a)) (a : ℤ) := by
  rw [listProd_eq_padProd_mul_lastProd] at h
  exact isCoprime_mul_sub (Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_right h))
    (Nat.isCoprime_iff_coprime.2 (Nat.Coprime.coprime_mul_left h))

open scoped Classical in
/-- At fixed lists, the bad positions `P` with `G ∣ P₁` number at most
`90 UV/G · e^{-L^{a₋}/4} + 3 E N`: the congruence count with `a = z = 1`. -/
theorem card_bad_dvd_le {x alo : ℝ} {d : Data K} {Y d₀ C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hC : CongBound C₁)
    (hB : BadCountBound x alo d Y d₀)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hU : 2 ≤ d₀ * Y * d.Hm) (hV : 2 ≤ d.Hn) {p : Lists K (padCount x)}
    (hp : p ∈ lists x d (padCount x)) :
    (#{P ∈ positions d Y d₀ | (listProd p : ℤ) ∣ P.1 ∧ ¬ IsGood x d Y d₀ P p} : ℝ) ≤
      90 * (d₀ * Y * d.Hm) * d.Hn / listProd p * Real.exp (-Real.log x ^ alo / 4) +
        3 * (C₁ * (d₀ * Y * d.Hm) * d.Hn * (listProd p : ℝ) ^ 4 *
          min (d₀ * Y * d.Hm) d.Hn ^ (-(1 / 5 : ℝ)) + (16 * (d₀ * Y * d.Hm) + d.Hn + 2)) *
          badIntervals x d Y p := by
  set U := d₀ * Y * d.Hm
  set G := listProd p
  have hS : Squarefree (G * 1) := by rw [mul_one]; exact squarefree_listProd hdisj hp
  have hI := hC U d.Hn hU hV G 1 hS 1 one_ne_zero isCoprime_one_left 0
  have hT : ∀ P ∈ rootBox U d.Hn, 0 < P.1 := fun P hP => by
    have := (mem_rootBox_bounds (by linarith) (by linarith) hP).1
    exact_mod_cast (show (0 : ℝ) < U by linarith).trans_le this
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < d.Hn := by linarith
  have hcount := hB p hp (rootBox U d.Hn) hT _ _ _ (by positivity) (by positivity) hI
  rw [positions_eq_rootBox]
  refine (Nat.cast_le.2 (card_le_card fun P hP => ?_)).trans (hcount.trans (le_of_eq ?_))
  · rw [mem_filter] at hP ⊢
    exact ⟨hP.1, ⟨hP.2.1, Nat.cast_one (R := ℤ) ▸ one_dvd _⟩, hP.2.2⟩
  · push_cast
    ring

open scoped Classical in
/-- Raw part at a list pair: the pairs `(P, Q)` with `G ∣ P₁`, `a ∣ Q₁`,
`det(P, Q) = D (b - a)` and `P` bad number at most
`17 (90 UV/(G a) · e^{-L^{a₋}/4} + 3 |z| E N)`. -/
theorem card_joint_le {x alo : ℝ} {d : Data K} {Y d₀ C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hC : CongBound C₁)
    (hB : BadCountBound x alo d Y d₀)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hU : 2 ≤ d₀ * Y * d.Hm) (hV : 2 ≤ d.Hn) (hY : 1 ≤ Y) {p p' : Lists K (padCount x)}
    (hp : p ∈ lists x d (padCount x)) (hp' : p' ∈ lists x d (padCount x))
    (he : ListEdge Y d₀ p p') :
    (#{PQ ∈ positions d Y d₀ ×ˢ positions d Y d₀ | (listProd p : ℤ) ∣ PQ.1.1 ∧
        (lastProd p' : ℤ) ∣ PQ.2.1 ∧
        det PQ.1 PQ.2 = padProd p * ((lastProd p : ℤ) - lastProd p') ∧
        ¬ IsGood x d Y d₀ PQ.1 p} : ℝ) ≤
      17 * (90 * (d₀ * Y * d.Hm) * d.Hn / ((listProd p : ℝ) * lastProd p') *
          Real.exp (-Real.log x ^ alo / 4) +
        3 * |((padProd p : ℤ) * ((lastProd p : ℤ) - lastProd p') : ℝ)| *
          (C₁ * (d₀ * Y * d.Hm) * d.Hn * ((listProd p : ℝ) * lastProd p') ^ 4 *
            min (d₀ * Y * d.Hm) d.Hn ^ (-(1 / 5 : ℝ)) + (16 * (d₀ * Y * d.Hm) + d.Hn + 2)) *
          badIntervals x d Y p) := by
  set U := d₀ * Y * d.Hm
  set G := listProd p
  set a := lastProd p'
  set z : ℤ := (padProd p : ℤ) * ((lastProd p : ℤ) - a)
  have hS : Squarefree (G * a) := squarefree_listProd_mul_lastProd hdisj hp hp' he.2.1
  have hza : IsCoprime z (a : ℤ) := isCoprime_of_coprime (Nat.squarefree_mul_iff.1 hS).1
  have ha2 : 2 ≤ a := by
    have : (1 : ℝ) < a := by linarith [he.2.2.2.2.2.2.1]
    exact_mod_cast this
  have hz : z ≠ 0 := ne_zero_of_isCoprime hza ha2
  have hT : ∀ P ∈ rootBox U d.Hn, 0 < P.1 := fun P hP => by
    have := (mem_rootBox_bounds (by linarith) (by linarith) hP).1
    exact_mod_cast (show (0 : ℝ) < U by linarith).trans_le this
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < d.Hn := by linarith
  have hA : 0 ≤ 90 * U * d.Hn / ((G : ℝ) * a) := by positivity
  have hE : 0 ≤ 3 * |(z : ℝ)| * (C₁ * U * d.Hn * ((G : ℝ) * a) ^ 4 *
      min U d.Hn ^ (-(1 / 5 : ℝ)) + (16 * U + d.Hn + 2)) := by positivity
  have hpairs := card_pairs_le (U := U) (V := d.Hn) (by linarith) (by linarith) G a z
    (fun P => ¬ IsGood x d Y d₀ P p)
  rw [positions_eq_rootBox]
  refine (Nat.cast_le.2 hpairs).trans ?_
  push_cast
  calc ∑ k ∈ range 17, (#{P ∈ rootBox U d.Hn | ((G : ℤ) ∣ P.1 ∧
        (a : ℤ) ∣ z * rootC P.1 P.2 + ((k : ℤ) - ⌊(z : ℝ) * rootRatio P⌋) * P.1) ∧
        ¬ IsGood x d Y d₀ P p} : ℝ)
      ≤ ∑ _k ∈ range 17, (90 * U * d.Hn / ((G : ℝ) * a) * Real.exp (-Real.log x ^ alo / 4) +
          3 * |(z : ℝ)| * (C₁ * U * d.Hn * ((G : ℝ) * a) ^ 4 *
            min U d.Hn ^ (-(1 / 5 : ℝ)) + (16 * U + d.Hn + 2)) * badIntervals x d Y p) := by
        refine sum_le_sum fun k _ => ?_
        have hI := hC U d.Hn hU hV G a hS z hz hza k
        have h := hB p hp (rootBox U d.Hn) hT _ _ _ hA hE hI
        refine (Nat.cast_le.2 (card_le_card fun P hP => ?_)).trans (h.trans (le_of_eq ?_))
        · rw [mem_filter] at hP ⊢
          exact hP
        · ring
    _ = _ := by
        have hzr : (z : ℝ) = (padProd p : ℝ) * ((lastProd p : ℝ) - a) := by
          simp only [z]
          push_cast
          ring
        rw [sum_const, card_range, nsmul_eq_mul, hzr]
        push_cast
        ring

open scoped Classical in
/-- Raw part at a list pair, reversed: the pairs `(Q, P)` with `G' ∣ Q₁`, `b ∣ P₁`,
`det(Q, P) = D (a - b)` and `Q` bad. -/
theorem card_joint_le' {x alo : ℝ} {d : Data K} {Y d₀ C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hC : CongBound C₁)
    (hB : BadCountBound x alo d Y d₀)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hU : 2 ≤ d₀ * Y * d.Hm) (hV : 2 ≤ d.Hn) (hY : 1 ≤ Y) {p p' : Lists K (padCount x)}
    (hp : p ∈ lists x d (padCount x)) (hp' : p' ∈ lists x d (padCount x))
    (he : ListEdge Y d₀ p p') :
    (#{QP ∈ positions d Y d₀ ×ˢ positions d Y d₀ | (listProd p' : ℤ) ∣ QP.1.1 ∧
        (lastProd p : ℤ) ∣ QP.2.1 ∧
        det QP.1 QP.2 = padProd p * ((lastProd p' : ℤ) - lastProd p) ∧
        ¬ IsGood x d Y d₀ QP.1 p'} : ℝ) ≤
      17 * (90 * (d₀ * Y * d.Hm) * d.Hn / ((listProd p' : ℝ) * lastProd p) *
          Real.exp (-Real.log x ^ alo / 4) +
        3 * |((padProd p : ℤ) * ((lastProd p' : ℤ) - lastProd p) : ℝ)| *
          (C₁ * (d₀ * Y * d.Hm) * d.Hn * ((listProd p' : ℝ) * lastProd p) ^ 4 *
            min (d₀ * Y * d.Hm) d.Hn ^ (-(1 / 5 : ℝ)) + (16 * (d₀ * Y * d.Hm) + d.Hn + 2)) *
          badIntervals x d Y p') := by
  set U := d₀ * Y * d.Hm
  set G := listProd p'
  set a := lastProd p
  have hD : padProd p' = padProd p := padProd_eq_of_pads he.1
  set z : ℤ := (padProd p : ℤ) * ((lastProd p' : ℤ) - a)
  -- the last labels of the source avoid the labels of the target
  have hban : ∀ i i' h', p i (Fin.last _) ≠ p' i' h' := by
    intro i i' h' heq
    refine Fin.lastCases (fun heq => he.2.1 i' i _ heq.symm) (fun h heq => ?_) h' heq
    rw [he.1 i' h] at heq
    have hinj := label_injective hdisj (fun i h => lists_slot_mem_band hp i h)
      (lists_group_injective hp)
    have := congrArg Prod.snd (hinj (a₁ := (i, Fin.last _)) (a₂ := (i', h.castSucc)) heq)
    exact Fin.castSucc_ne_last h this.symm
  have hS : Squarefree (G * a) := squarefree_listProd_mul_lastProd hdisj hp' hp hban
  have hza : IsCoprime z (a : ℤ) := by
    have := isCoprime_of_coprime (Nat.squarefree_mul_iff.1 hS).1
    rwa [hD] at this
  have ha2 : 2 ≤ a := by
    have : (1 : ℝ) < a := by linarith [he.2.2.2.2.1]
    exact_mod_cast this
  have hz : z ≠ 0 := ne_zero_of_isCoprime hza ha2
  have hT : ∀ P ∈ rootBox U d.Hn, 0 < P.1 := fun P hP => by
    have := (mem_rootBox_bounds (by linarith) (by linarith) hP).1
    exact_mod_cast (show (0 : ℝ) < U by linarith).trans_le this
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < d.Hn := by linarith
  have hA : 0 ≤ 90 * U * d.Hn / ((G : ℝ) * a) := by positivity
  have hE : 0 ≤ 3 * |(z : ℝ)| * (C₁ * U * d.Hn * ((G : ℝ) * a) ^ 4 *
      min U d.Hn ^ (-(1 / 5 : ℝ)) + (16 * U + d.Hn + 2)) := by positivity
  have hpairs := card_pairs_le (U := U) (V := d.Hn) (by linarith) (by linarith) G a z
    (fun P => ¬ IsGood x d Y d₀ P p')
  rw [positions_eq_rootBox]
  refine (Nat.cast_le.2 hpairs).trans ?_
  push_cast
  calc ∑ k ∈ range 17, (#{P ∈ rootBox U d.Hn | ((G : ℤ) ∣ P.1 ∧
        (a : ℤ) ∣ z * rootC P.1 P.2 + ((k : ℤ) - ⌊(z : ℝ) * rootRatio P⌋) * P.1) ∧
        ¬ IsGood x d Y d₀ P p'} : ℝ)
      ≤ ∑ _k ∈ range 17, (90 * U * d.Hn / ((G : ℝ) * a) * Real.exp (-Real.log x ^ alo / 4) +
          3 * |(z : ℝ)| * (C₁ * U * d.Hn * ((G : ℝ) * a) ^ 4 *
            min U d.Hn ^ (-(1 / 5 : ℝ)) + (16 * U + d.Hn + 2)) * badIntervals x d Y p') := by
        refine sum_le_sum fun k _ => ?_
        have hI := hC U d.Hn hU hV G a hS z hz hza k
        have h := hB p' hp' (rootBox U d.Hn) hT _ _ _ hA hE hI
        refine (Nat.cast_le.2 (card_le_card fun P hP => ?_)).trans (h.trans (le_of_eq ?_))
        · rw [mem_filter] at hP ⊢
          exact hP
        · ring
    _ = _ := by
        have hzr : (z : ℝ) = (padProd p : ℝ) * ((lastProd p' : ℝ) - a) := by
          simp only [z]
          push_cast
          ring
        rw [sum_const, card_range, nsmul_eq_mul, hzr]
        push_cast
        ring

/-! ### Sizes -/

/-- The labels of a list have product at most `exp(4K L^{1/2})` (as `listProd_le_exp`). -/
theorem listProd_le_exp' {C CX alo ahi g x : ℝ} {d : Data K}
    (hd : Admissible C CX alo ahi g x d) (hahi : ahi < 1 / 5) (hL : 1 ≤ Real.log x)
    {p : Lists K (padCount x)} (hp : p ∈ lists x d (padCount x)) :
    (listProd p : ℝ) ≤ Real.exp (4 * K * Real.log x ^ (1 / 2 : ℝ)) := by
  set L := Real.log x
  have hlabel : ∀ i h, (p i h : ℝ) ≤ Real.exp (2 * L ^ ahi) := by
    intro i h
    have h₁ := Real.rpow_le_rpow_of_exponent_le hL (hd.window i).2
    exact (le_exp_of_mem_band (lists_slot_mem_band hp i h)).trans
      (Real.exp_le_exp.2 (by linarith))
  have hJ : (padCount x : ℝ) + 1 ≤ 2 * L ^ (1 / 100 : ℝ) := by
    have h₁ : (padCount x : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
    have h₂ : 1 ≤ L ^ (1 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
    linarith
  have hexp : L ^ (1 / 100 : ℝ) * L ^ ahi ≤ L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hLa : 0 ≤ L ^ ahi := by positivity
  have hJa : ((padCount x : ℝ) + 1) * L ^ ahi ≤ 2 * L ^ (1 / 2 : ℝ) := by nlinarith
  unfold listProd
  push_cast
  calc ∏ i, ∏ h, (p i h : ℝ) ≤ ∏ _i : Fin K, ∏ _h : Fin (padCount x + 1), Real.exp (2 * L ^ ahi) :=
        prod_le_prod₀ (fun i _ => prod_nonneg fun h _ => Nat.cast_nonneg _) fun i _ =>
          prod_le_prod₀ (fun h _ => Nat.cast_nonneg _) fun h _ => hlabel i h
    _ = Real.exp (K * ((padCount x + 1 : ℕ) * (2 * L ^ ahi))) := by
        rw [prod_const, prod_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
          ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ ≤ Real.exp (4 * K * L ^ (1 / 2 : ℝ)) := by
        refine Real.exp_le_exp.2 ?_
        have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        push_cast
        nlinarith

/-- The last product divides the list product. -/
theorem lastProd_le_listProd {J : ℕ} {p : Lists K J} (hp : 0 < listProd p) :
    lastProd p ≤ listProd p :=
  Nat.le_of_dvd hp (by rw [listProd_eq_padProd_mul_lastProd]; exact Dvd.intro_left _ rfl)

/-- The pad product divides the list product. -/
theorem padProd_le_listProd {J : ℕ} {p : Lists K J} (hp : 0 < listProd p) :
    padProd p ≤ listProd p :=
  Nat.le_of_dvd hp (by rw [listProd_eq_padProd_mul_lastProd]; exact Dvd.intro _ rfl)

/-- `log₂ n ≤ 2 log n` for `n ≥ 1`. -/
theorem natLog_le_two_mul_log {n : ℕ} (hn : n ≠ 0) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h := Nat.pow_log_le_self 2 hn
  have h' : ((2 : ℝ)) ^ Nat.log 2 n ≤ n := by exact_mod_cast h
  have hlog := Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at hlog
  have h2 : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  nlinarith

/-! ### The decomposition -/

open scoped Classical in
/-- The bad mass splits into the raw and comparison parts with bad source or bad target. -/
theorem sum_bad_mul_eq {α : Type*} (s : Finset α) (good : α → Prop) (E R : α → α → Prop)
    (W κ : ℝ) :
    ∑ y₁ ∈ s, ∑ y₂ ∈ s, ((if good y₁ then (0 : ℝ) else 1) + (if good y₂ then 0 else 1)) *
        (if E y₁ y₂ then W * ((if R y₁ y₂ then 1 else 0) + κ) else 0) =
      W * ((#{yy ∈ s ×ˢ s | ¬ good yy.1 ∧ E yy.1 yy.2 ∧ R yy.1 yy.2} : ℝ) +
          #{yy ∈ s ×ˢ s | ¬ good yy.2 ∧ E yy.1 yy.2 ∧ R yy.1 yy.2}) +
        W * κ * (∑ y₁ ∈ s.filter (fun y => ¬ good y), (#{y₂ ∈ s | E y₁ y₂} : ℝ) +
          ∑ y₂ ∈ s.filter (fun y => ¬ good y), (#{y₁ ∈ s | E y₁ y₂} : ℝ)) := by
  have h₁ : (#{yy ∈ s ×ˢ s | ¬ good yy.1 ∧ E yy.1 yy.2 ∧ R yy.1 yy.2} : ℝ) =
      ∑ y₁ ∈ s, ∑ y₂ ∈ s, if ¬ good y₁ ∧ E y₁ y₂ ∧ R y₁ y₂ then 1 else 0 := by
    rw [natCast_card_filter, sum_product]
  have h₂ : (#{yy ∈ s ×ˢ s | ¬ good yy.2 ∧ E yy.1 yy.2 ∧ R yy.1 yy.2} : ℝ) =
      ∑ y₁ ∈ s, ∑ y₂ ∈ s, if ¬ good y₂ ∧ E y₁ y₂ ∧ R y₁ y₂ then 1 else 0 := by
    rw [natCast_card_filter, sum_product]
  have h₃ : ∑ y₁ ∈ s.filter (fun y => ¬ good y), (#{y₂ ∈ s | E y₁ y₂} : ℝ) =
      ∑ y₁ ∈ s, ∑ y₂ ∈ s, if ¬ good y₁ ∧ E y₁ y₂ then 1 else 0 := by
    rw [sum_filter]
    refine sum_congr rfl fun y₁ _ => ?_
    by_cases h : good y₁
    · simp [h]
    · simp only [h, not_false_eq_true, true_and, ↓reduceIte]
      exact natCast_card_filter _ _
  have h₄ : ∑ y₂ ∈ s.filter (fun y => ¬ good y), (#{y₁ ∈ s | E y₁ y₂} : ℝ) =
      ∑ y₁ ∈ s, ∑ y₂ ∈ s, if ¬ good y₂ ∧ E y₁ y₂ then 1 else 0 := by
    rw [sum_filter, sum_comm]
    refine sum_congr rfl fun y₂ _ => ?_
    by_cases h : good y₂
    · simp [h]
    · simp only [h, not_false_eq_true, true_and, ↓reduceIte]
      exact natCast_card_filter _ _
  rw [h₁, h₂, h₃, h₄]
  simp only [mul_add, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun y₁ _ => sum_congr rfl fun y₂ _ => ?_
  by_cases h1 : good y₁ <;> by_cases h2 : good y₂ <;> by_cases hE : E y₁ y₂ <;>
    by_cases hR : R y₁ y₂ <;> simp [h1, h2, hE, hR] <;> ring

/-! ### Size bounds in terms of `L^{1/2}` -/

/-- `M^K ≤ exp(K L^{1/2})` for `M = J + 1`. -/
theorem padCount_pow_le {x : ℝ} (hL : 1 ≤ Real.log x) :
    ((padCount x : ℝ) + 1) ^ K ≤ Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) := by
  rw [Real.exp_nat_mul]
  gcongr
  refine (Real.add_one_le_exp _).trans (Real.exp_le_exp.2 ?_)
  exact (Nat.floor_le (by positivity)).trans
    (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))

/-- `B = exp(2 ∑ L^{a_i}) ≤ exp(2K L^{1/2})` for exponents at most `1/5`. -/
theorem labelBound_le {x : ℝ} {d : Data K} (hL : 1 ≤ Real.log x) (ha : ∀ i, d.a i ≤ 1 / 5) :
    labelBound x d ≤ Real.exp (2 * K * Real.log x ^ (1 / 2 : ℝ)) := by
  unfold labelBound
  refine Real.exp_le_exp.2 ?_
  have h : ∑ i, Real.log x ^ d.a i ≤ ∑ _i : Fin K, Real.log x ^ (1 / 2 : ℝ) :=
    sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_le hL ((ha i).trans (by norm_num))
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  linarith

/-- `exp(c K L^{1/2}) = t^c` with `t = exp(K L^{1/2})`. -/
theorem exp_mul_eq_pow (c : ℕ) (y : ℝ) : Real.exp (c * y) = Real.exp y ^ c := by
  rw [← Real.exp_nat_mul]

/-- `badIntervals ≤ 6 t^{17}` with `t = exp(K L^{1/2})`, when `1 ≤ Y`, `Y` and the list product
are at most `t^4 = exp(4K L^{1/2})`, and the exponents are at most `1/5`. -/
theorem badIntervals_le {x : ℝ} {d : Data K} (hL : 1 ≤ Real.log x) (ha : ∀ i, d.a i ≤ 1 / 5)
    {Y : ℝ} (hY : 1 ≤ Y) (hYE : Y ≤ Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) ^ 4)
    {J : ℕ} (hJ : J = padCount x) {p : Lists K J}
    (hG : (listProd p : ℝ) ≤ Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) ^ 4) :
    badIntervals x d Y p ≤ 6 * Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) ^ 17 := by
  subst hJ
  set u := Real.log x ^ (1 / 2 : ℝ)
  set t := Real.exp (K * u)
  set n := ⌊Y ^ (1 / 5 : ℝ)⌋₊
  have hu : 1 ≤ u := Real.one_le_rpow hL (by norm_num)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ht : 1 ≤ t := Real.one_le_exp (by positivity)
  have hn : (n : ℝ) ≤ t ^ 4 := by
    refine (Nat.floor_le (by positivity)).trans (le_trans ?_ hYE)
    simpa using Real.rpow_le_rpow_of_exponent_le hY (by norm_num : (1 / 5 : ℝ) ≤ 1)
  have hM : ((padCount x : ℝ) + 1) ^ K ≤ t := padCount_pow_le hL
  have hB : labelBound x d ≤ t ^ 2 := by
    have := labelBound_le hL ha
    rwa [show 2 * (K : ℝ) * u = ((2 : ℕ) : ℝ) * (K * u) by push_cast; ring,
      exp_mul_eq_pow] at this
  have hB1 := one_le_labelBound (by linarith) d
  have h2K : (2 : ℝ) ^ K ≤ t := by
    simp only [t]
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast]
    gcongr
    calc (2 : ℝ) ≤ 1 + u := by linarith
      _ ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hG0 : (0 : ℝ) ≤ listProd p := Nat.cast_nonneg _
  have ht4 : 1 ≤ t ^ 4 := one_le_pow₀ ht
  have ht8 : 1 ≤ t ^ 8 := one_le_pow₀ ht
  -- the two terms
  have ht₁ : ((padCount x : ℝ) + 1) ^ K * n * (2 * n * listProd p + 1) ≤ 3 * t ^ 17 := by
    calc ((padCount x : ℝ) + 1) ^ K * n * (2 * n * listProd p + 1)
        ≤ t * t ^ 4 * (2 * t ^ 4 * t ^ 4 + t ^ 8) := by
          gcongr
      _ = 3 * t ^ 13 := by ring
      _ ≤ 3 * t ^ 17 := by gcongr; norm_num
  have ht₂ : 2 ^ K * labelBound x d * (((padCount x : ℝ) + 1) ^ K * labelBound x d) ^ 2 *
      (2 * listProd p * labelBound x d ^ 2 + 1) ≤ 3 * t ^ 17 := by
    have hB2 : 1 ≤ (t ^ 2) ^ 2 := one_le_pow₀ (one_le_pow₀ ht)
    calc 2 ^ K * labelBound x d * (((padCount x : ℝ) + 1) ^ K * labelBound x d) ^ 2 *
          (2 * listProd p * labelBound x d ^ 2 + 1)
        ≤ t * t ^ 2 * (t * t ^ 2) ^ 2 * (2 * t ^ 4 * (t ^ 2) ^ 2 + t ^ 4 * (t ^ 2) ^ 2) := by
          gcongr
          nlinarith
      _ = 3 * t ^ 17 := by ring
  unfold badIntervals
  linarith

/-- At most `t^4` lists, `t = exp(K L^{1/2})`: there are `∏_i |𝒫_i|^M ≤ exp(2 M ∑ L^{a_i})` of
them and `M L^{1/5} ≤ 2 L^{1/2}`. -/
theorem card_lists_le_pow {x : ℝ} {d : Data K} (hL : 1 ≤ Real.log x)
    (ha : ∀ i, d.a i ≤ 1 / 5) :
    ((lists x d (padCount x)).card : ℝ) ≤ Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) ^ 4 := by
  set L := Real.log x
  have hcard : (lists x d (padCount x)).card ≤
      ∏ i, (band x (d.a i)).card ^ (padCount x + 1) := by
    refine (card_filter_le _ _).trans (le_of_eq ?_)
    rw [Fintype.card_piFinset]
    exact prod_congr rfl fun i _ => by
      rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  have hJ : (padCount x : ℝ) + 1 ≤ 2 * L ^ (1 / 100 : ℝ) := by
    have h₁ : (padCount x : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
    have h₂ : 1 ≤ L ^ (1 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
    linarith
  have hexp : L ^ (1 / 100 : ℝ) * L ^ (1 / 5 : ℝ) ≤ L ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h15 : 0 ≤ L ^ (1 / 5 : ℝ) := by positivity
  calc ((lists x d (padCount x)).card : ℝ)
      ≤ ∏ i, ((band x (d.a i)).card : ℝ) ^ (padCount x + 1) := by exact_mod_cast hcard
    _ ≤ ∏ _i : Fin K, Real.exp (2 * L ^ (1 / 5 : ℝ)) ^ (padCount x + 1) := by
        refine prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
        gcongr
        exact (card_band_le _ _).trans (Real.exp_le_exp.2 (by
          have := Real.rpow_le_rpow_of_exponent_le hL (ha i)
          linarith))
    _ = Real.exp (K * ((padCount x + 1 : ℕ) * (2 * L ^ (1 / 5 : ℝ)))) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ ≤ Real.exp (K * L ^ (1 / 2 : ℝ)) ^ 4 := by
        rw [← exp_mul_eq_pow]
        refine Real.exp_le_exp.2 ?_
        push_cast
        have : ((padCount x : ℝ) + 1) * (2 * L ^ (1 / 5 : ℝ)) ≤ 4 * L ^ (1 / 2 : ℝ) := by nlinarith
        nlinarith

/-- `(2^K)^{M + 1} ≤ t^3` with `t = exp(K L^{1/2})`. -/
theorem two_pow_pow_le {x : ℝ} (hL : 1 ≤ Real.log x) :
    ((2 : ℝ) ^ K) ^ (padCount x + 2) ≤ Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) ^ 3 := by
  set L := Real.log x
  have hJ : (padCount x : ℝ) + 2 ≤ 3 * L ^ (1 / 2 : ℝ) := by
    have h₁ : (padCount x : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
    have h₂ : L ^ (1 / 100 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    have h₃ : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL (by norm_num)
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [← pow_mul, ← exp_mul_eq_pow]
  calc (2 : ℝ) ^ (K * (padCount x + 2)) ≤ Real.exp 1 ^ (K * (padCount x + 2)) := by gcongr
    _ = Real.exp ((K * (padCount x + 2) : ℕ) * 1) := by rw [exp_mul_eq_pow]
    _ ≤ Real.exp ((3 : ℕ) * (K * L ^ (1 / 2 : ℝ))) := by
        refine Real.exp_le_exp.2 ?_
        push_cast
        have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        nlinarith

/-! ### Asymptotics -/

/-- Eventually `exp(-L^{1/10}/8) ≤ L^{3A₀}`. -/
theorem eventually_exp_le_rpow (A₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-Real.log x ^ (1 / 10 : ℝ) / 8) ≤ Real.log x ^ (3 * A₀) := by
  filter_upwards [eventually_mul_rpow_mul_exp_le (by norm_num : (0 : ℝ) < 1 / 20) 1 0 (-(3 * A₀)),
    eventually_le_rpow_log (by norm_num : (0 : ℝ) < 1 / 20) 8,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx h8 hL
  simp only [neg_neg, Real.rpow_zero, one_mul, mul_one] at hx
  refine le_trans (Real.exp_le_exp.2 ?_) hx
  -- `L^{1/10} = (L^{1/20})² ≥ 8 L^{1/20}`
  have hsq : Real.log x ^ (1 / 10 : ℝ) =
      Real.log x ^ (1 / 20 : ℝ) * Real.log x ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  rw [hsq]
  nlinarith

/-- Eventually `(3L)^K ≤ exp(L^{1/10}/8)`. -/
theorem eventually_pow_le_exp (K : ℕ) :
    ∀ᶠ x : ℝ in atTop, (3 * Real.log x) ^ K ≤ Real.exp (Real.log x ^ (1 / 10 : ℝ) / 8) := by
  filter_upwards [eventually_mul_rpow_mul_exp_le (by norm_num : (0 : ℝ) < 1 / 20) (3 ^ K) K 0,
    eventually_le_rpow_log (by norm_num : (0 : ℝ) < 1 / 20) 8,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx h8 hL
  rw [neg_zero, Real.rpow_zero, Real.rpow_natCast, Real.exp_neg, ← div_eq_mul_inv,
    div_le_one (Real.exp_pos _)] at hx
  rw [mul_pow]
  refine hx.trans (Real.exp_le_exp.2 ?_)
  have hsq : Real.log x ^ (1 / 10 : ℝ) =
      Real.log x ^ (1 / 20 : ℝ) * Real.log x ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  rw [hsq]
  nlinarith

/-- The error asymptotics: with `t = exp(K L^{1/2})` and `c ≥ 0`, eventually
`T = c t^{70} exp(-L^{0.99}/5)` satisfies `T ≤ L^{3A₀} exp(-L^{1/5}/8)` and
`T (3L)^K ≤ exp(-L^{1/5}/8)`. -/
theorem eventually_error_le (K : ℕ) (A₀ c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ x : ℝ in atTop,
      c * Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) ^ 70 *
          Real.exp (-Real.log x ^ (99 / 100 : ℝ) / 5) ≤
        Real.log x ^ (3 * A₀) * Real.exp (-Real.log x ^ (1 / 5 : ℝ) / 8) ∧
      c * Real.exp (K * Real.log x ^ (1 / 2 : ℝ)) ^ 70 *
          Real.exp (-Real.log x ^ (99 / 100 : ℝ) / 5) * (3 * Real.log x) ^ K ≤
        Real.exp (-Real.log x ^ (1 / 5 : ℝ) / 8) := by
  filter_upwards [eventually_mul_rpow_mul_exp_le (by norm_num : (0 : ℝ) < 1 / 2) 1 0 (-(3 * A₀)),
    eventually_pow_le_exp K, eventually_le_rpow_log (by norm_num : (0 : ℝ) < 1 / 2) c,
    eventually_le_rpow_log (by norm_num : (0 : ℝ) < 49 / 100) (5 * (70 * K + 5)),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hA hpow hcu h49 hL
  set L := Real.log x
  set u := L ^ (1 / 2 : ℝ)
  simp only [neg_neg, Real.rpow_zero, one_mul, mul_one] at hA
  have hu : 1 ≤ u := Real.one_le_rpow hL (by norm_num)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h10 : L ^ (1 / 10 : ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h5 : L ^ (1 / 5 : ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have h15 : 0 ≤ L ^ (1 / 5 : ℝ) := by positivity
  have h99 : L ^ (99 / 100 : ℝ) = u * L ^ (49 / 100 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hc' : c ≤ Real.exp u := hcu.trans (by linarith [Real.add_one_le_exp u])
  have hpow' : (3 * L) ^ K ≤ Real.exp u := hpow.trans (Real.exp_le_exp.2 (by linarith))
  have hpow1 : 1 ≤ (3 * L) ^ K := one_le_pow₀ (by linarith)
  -- the key exponent comparison
  have hkey : c * Real.exp (K * u) ^ 70 * Real.exp (-L ^ (99 / 100 : ℝ) / 5) * (3 * L) ^ K ≤
      Real.exp (-u) * Real.exp (-L ^ (1 / 5 : ℝ) / 8) := by
    rw [← exp_mul_eq_pow]
    calc c * Real.exp ((70 : ℕ) * (K * u)) * Real.exp (-L ^ (99 / 100 : ℝ) / 5) * (3 * L) ^ K
        ≤ Real.exp u * Real.exp ((70 : ℕ) * (K * u)) * Real.exp (-L ^ (99 / 100 : ℝ) / 5) *
            Real.exp u := by gcongr
      _ = Real.exp (u + (70 : ℕ) * (K * u) + -L ^ (99 / 100 : ℝ) / 5 + u) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-u + -L ^ (1 / 5 : ℝ) / 8) := by
          refine Real.exp_le_exp.2 ?_
          rw [h99]
          push_cast
          nlinarith
      _ = Real.exp (-u) * Real.exp (-L ^ (1 / 5 : ℝ) / 8) := Real.exp_add _ _
  have hexpu : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE : 0 ≤ Real.exp (-L ^ (1 / 5 : ℝ) / 8) := (Real.exp_pos _).le
  constructor
  · calc c * Real.exp (K * u) ^ 70 * Real.exp (-L ^ (99 / 100 : ℝ) / 5)
        ≤ c * Real.exp (K * u) ^ 70 * Real.exp (-L ^ (99 / 100 : ℝ) / 5) * (3 * L) ^ K :=
          le_mul_of_one_le_right (by positivity) hpow1
      _ ≤ Real.exp (-u) * Real.exp (-L ^ (1 / 5 : ℝ) / 8) := hkey
      _ ≤ L ^ (3 * A₀) * Real.exp (-L ^ (1 / 5 : ℝ) / 8) := by gcongr
  · calc _ ≤ Real.exp (-u) * Real.exp (-L ^ (1 / 5 : ℝ) / 8) := hkey
      _ ≤ 1 * Real.exp (-L ^ (1 / 5 : ℝ) / 8) := by gcongr
      _ = _ := one_mul _

/-! ### Assembly -/

/-- The root-residue error and the faces are at most `(C₁ s + 19) UV μ^{-1/5}`, with
`μ = min(U, V) ≥ 1`. -/
theorem err_le {U V C₁ s : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    C₁ * U * V * s * min U V ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2) ≤
      (C₁ * s + 19) * (U * V * min U V ^ (-(1 / 5 : ℝ))) := by
  set μ := min U V
  have hμ1 : 1 ≤ μ := le_min hU hV
  have hμ5 : μ ^ (1 / 5 : ℝ) ≤ μ := RootResidue.rpow_le_self_of_one_le hμ1 (by norm_num)
  have hμ0 : 0 < μ ^ (1 / 5 : ℝ) := by positivity
  have hneg : μ ^ (-(1 / 5 : ℝ)) = (μ ^ (1 / 5 : ℝ))⁻¹ := Real.rpow_neg (by linarith) _
  -- `U ≤ U V μ^{-1/5}` and `V ≤ U V μ^{-1/5}`, since `μ^{1/5} ≤ min(U, V)`
  have hUV : U ≤ U * V * μ ^ (-(1 / 5 : ℝ)) := by
    rw [hneg, mul_assoc, ← div_eq_mul_inv, le_mul_iff_one_le_right (by linarith),
      one_le_div hμ0]
    exact hμ5.trans (min_le_right _ _)
  have hVU : V ≤ U * V * μ ^ (-(1 / 5 : ℝ)) := by
    rw [hneg, mul_comm U V, mul_assoc, ← div_eq_mul_inv, le_mul_iff_one_le_right (by linarith),
      one_le_div hμ0]
    exact hμ5.trans (min_le_left _ _)
  nlinarith

/-- `|D (b - a)| ≤ 8 d₀ Y` on a list edge. -/
theorem abs_padProd_mul_sub_le {Y d₀ : ℝ} {J : ℕ} {p p' : Lists K J}
    (he : ListEdge Y d₀ p p') :
    |((padProd p : ℤ) * ((lastProd p : ℤ) - lastProd p') : ℝ)| ≤ 8 * d₀ * Y ∧
      |((padProd p : ℤ) * ((lastProd p' : ℤ) - lastProd p) : ℝ)| ≤ 8 * d₀ * Y := by
  obtain ⟨-, -, hD₁, hD₂, hb₁, hb₂, ha₁, ha₂⟩ := he
  have hY : 0 < Y := by linarith [Nat.cast_nonneg (α := ℝ) (lastProd p)]
  have hD : (0 : ℝ) ≤ padProd p := Nat.cast_nonneg _
  have hd0 : 0 ≤ 2 * d₀ := by linarith
  have hba : |(lastProd p : ℝ) - lastProd p'| ≤ 4 * Y := by
    rw [abs_le]
    constructor <;> linarith
  have hab : |(lastProd p' : ℝ) - lastProd p| ≤ 4 * Y := by
    rw [abs_le]
    constructor <;> linarith
  push_cast
  rw [abs_mul, abs_mul, abs_of_nonneg hD]
  constructor
  · calc (padProd p : ℝ) * |(lastProd p : ℝ) - lastProd p'| ≤ (2 * d₀) * (4 * Y) := by
          gcongr
    _ = 8 * d₀ * Y := by ring
  · calc (padProd p : ℝ) * |(lastProd p' : ℝ) - lastProd p| ≤ (2 * d₀) * (4 * Y) := by
          gcongr
    _ = 8 * d₀ * Y := by ring

/-- `badIntervals ≥ 0`. -/
theorem badIntervals_nonneg (x : ℝ) (d : Data K) (Y : ℝ) {J : ℕ} (p : Lists K J) :
    0 ≤ badIntervals x d Y p := by
  unfold badIntervals labelBound
  positivity

/-- The error of one congruence count is at most the uniform error
`Ē = 3 (8t⁸) ((C₁ t^{32} + 19) UV μ^{-1/5}) (6 t^{17})`, for `|z| ≤ 8 t⁸`, `S ≤ t⁸` and at most
`6 t^{17}` intervals. -/
theorem err_total_le {U V C₁ t z G' N : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V) (hC₁ : 0 ≤ C₁)
    (ht : 1 ≤ t) (hz : |z| ≤ 8 * t ^ 8) (hG0 : 0 ≤ G') (hG : G' ≤ t ^ 8) (hN0 : 0 ≤ N)
    (hN : N ≤ 6 * t ^ 17) :
    3 * |z| * (C₁ * U * V * G' ^ 4 * min U V ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2)) * N ≤
      3 * (8 * t ^ 8) * ((C₁ * (t ^ 8) ^ 4 + 19) * (U * V * min U V ^ (-(1 / 5 : ℝ)))) *
        (6 * t ^ 17) := by
  have hμ : 0 ≤ min U V ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg (le_min (by linarith) (by linarith)) _
  have hU0 : 0 ≤ U := by linarith
  have hV0 : 0 ≤ V := by linarith
  calc 3 * |z| * (C₁ * U * V * G' ^ 4 * min U V ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2)) * N
      ≤ 3 * (8 * t ^ 8) * (C₁ * U * V * (t ^ 8) ^ 4 * min U V ^ (-(1 / 5 : ℝ)) +
          (16 * U + V + 2)) * (6 * t ^ 17) := by gcongr
    _ ≤ _ := by
        gcongr
        exact err_le hU hV

/-- The final bookkeeping: the raw parts are `1530 UV ε + 17 Π Ē` each, the comparison parts
carry the factor `W κ · 17 (10Y + 1) Λ ≤ 2^K 748 L^{3A₀} Λ'`, and `ε, T ≤ L^{3A₀} e₈`,
`Λ' ε, Λ' T ≤ e₈`, where `Π Ē ≤ UV T`. -/
theorem badMass_final_combine {m W RS RT CS CT nb Λn Λ' Pm Ē P ε Y A e₈ T : ℝ}
    (hm0 : 0 ≤ m) (hW0 : 0 ≤ W) (hWK : W ≤ 2 ^ K) (hY : 1 ≤ Y) (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hPm0 : 0 ≤ Pm) (hĒ0 : 0 ≤ Ē) (hnb0 : 0 ≤ nb)
    (hRS : m * W * RS ≤ 1530 * P * ε + 17 * Pm * Ē)
    (hRT : m * W * RT ≤ 1530 * P * ε + 17 * Pm * Ē)
    (hCS : CS ≤ nb * (17 * (10 * Y + 1) * Λn)) (hCT : CT ≤ nb * (17 * (10 * Y + 1) * Λn))
    (hnb : m * nb ≤ 90 * P * ε + Pm * Ē) (hΛ0 : 0 ≤ Λn) (hΛ : Λn ≤ Λ')
    (hPĒ : Pm * Ē ≤ P * T) (hε0 : 0 ≤ ε) (hεA : ε ≤ A * e₈) (hTA : T ≤ A * e₈)
    (hΛε : Λ' * ε ≤ e₈) (hΛT : Λ' * T ≤ e₈) :
    m * (W * (RS + RT) + W * (4 * A / Y) * (CS + CT)) ≤
      (3094 + 2 ^ (K + 1) * 748 * 91) * P * A * e₈ := by
  have hY0 : 0 < Y := by linarith
  have hPĒ0 : 0 ≤ 90 * P * ε + Pm * Ē :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hP) hε0) (mul_nonneg hPm0 hĒ0)
  have hcA : 0 ≤ 2 ^ K * 748 * A := mul_nonneg (by positivity) hA
  have hWκ : 0 ≤ W * (4 * A / Y) := mul_nonneg hW0 (div_nonneg (by linarith) hY0.le)
  have hFac : 0 ≤ 17 * (10 * Y + 1) * Λn := mul_nonneg (by linarith) hΛ0
  -- the comparison factor
  have hfac : W * (4 * A / Y) * (17 * (10 * Y + 1) * Λn) ≤ 2 ^ K * 748 * A * Λn := by
    have h₁ : (4 * A / Y) * (17 * (10 * Y + 1)) ≤ 748 * A := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hY0]
      nlinarith
    calc W * (4 * A / Y) * (17 * (10 * Y + 1) * Λn) =
          W * ((4 * A / Y) * (17 * (10 * Y + 1))) * Λn := by ring
      _ ≤ 2 ^ K * (748 * A) * Λn :=
          mul_le_mul_of_nonneg_right (mul_le_mul hWK h₁ (mul_nonneg (div_nonneg (by linarith)
            hY0.le) (by linarith)) (by positivity)) hΛ0
      _ = 2 ^ K * 748 * A * Λn := by ring
  have hgen : ∀ Z, Z ≤ nb * (17 * (10 * Y + 1) * Λn) →
      m * (W * (4 * A / Y) * Z) ≤ 2 ^ K * 748 * A * (91 * P * e₈) := by
    intro Z hZ
    calc m * (W * (4 * A / Y) * Z) ≤ m * (W * (4 * A / Y) * (nb * (17 * (10 * Y + 1) * Λn))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hWκ) hm0
      _ = W * (4 * A / Y) * (17 * (10 * Y + 1) * Λn) * (m * nb) := by ring
      _ ≤ 2 ^ K * 748 * A * Λn * (90 * P * ε + Pm * Ē) :=
          mul_le_mul hfac hnb (mul_nonneg hm0 hnb0) (mul_nonneg hcA hΛ0)
      _ ≤ 2 ^ K * 748 * A * (Λ' * (90 * P * ε + P * T)) := by
          rw [mul_assoc (2 ^ K * 748 * A)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul hΛ (add_le_add le_rfl hPĒ) hPĒ0
            (hΛ0.trans hΛ)) hcA
      _ = 2 ^ K * 748 * A * (P * (90 * (Λ' * ε) + Λ' * T)) := by ring
      _ ≤ 2 ^ K * 748 * A * (P * (90 * e₈ + e₈)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add (by linarith) hΛT)
            hP) hcA
      _ = 2 ^ K * 748 * A * (91 * P * e₈) := by ring
  have hraw : 1530 * P * ε + 17 * Pm * Ē ≤ 1547 * P * (A * e₈) := by
    have h₁ : 17 * Pm * Ē ≤ 17 * (P * (A * e₈)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hPĒ.trans (mul_le_mul_of_nonneg_left hTA hP))
        (by norm_num)
    have h₂ : 1530 * P * ε ≤ 1530 * P * (A * e₈) :=
      mul_le_mul_of_nonneg_left hεA (mul_nonneg (by norm_num) hP)
    linarith
  calc m * (W * (RS + RT) + W * (4 * A / Y) * (CS + CT))
      = m * W * RS + m * W * RT + (m * (W * (4 * A / Y) * CS) + m * (W * (4 * A / Y) * CT)) := by
        ring
    _ ≤ 1547 * P * (A * e₈) + 1547 * P * (A * e₈) +
          (2 ^ K * 748 * A * (91 * P * e₈) + 2 ^ K * 748 * A * (91 * P * e₈)) :=
        add_le_add (add_le_add (hRS.trans hraw) (hRT.trans hraw))
          (add_le_add (hgen _ hCS) (hgen _ hCT))
    _ = (3094 + 2 ^ (K + 1) * 748 * 91) * P * A * e₈ := by ring

/-- `log 16 ≤ 3`. -/
theorem log_sixteen_le : Real.log 16 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  norm_num at h
  linarith

/-- `n ≤ n²` for a natural number. -/
theorem natCast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  exact_mod_cast Nat.le_self_pow two_ne_zero n

/-- `6 + 16 K u + 2 c ≤ u² = L` once `u ≥ 16K + 6 + 2c ≥ 1` with `c ≥ 0`. -/
theorem affine_le_sq {u L K c : ℝ} (hu1 : 1 ≤ u) (huu : u * u = L) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (h : 16 * K + 6 + 2 * c ≤ u) : 6 + 16 * K * u + 2 * c ≤ L := by
  have h₂ : (16 * K + 6 + 2 * c) * 1 ≤ (16 * K + 6 + 2 * c) * u :=
    mul_le_mul_of_nonneg_left hu1 (by positivity)
  have h₃ : (16 * K + 6 + 2 * c) * u ≤ u * u := mul_le_mul_of_nonneg_right h (by linarith)
  nlinarith

/-- `C₁ t^{32} + 19 ≤ (C₁ + 19) t^{32}` for `t ≥ 1`. -/
theorem add_le_mul_pow (C₁ : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    C₁ * (t ^ 8) ^ 4 + 19 ≤ (C₁ + 19) * t ^ 32 := by
  have h₁ : (1 : ℝ) ≤ t ^ 32 := one_le_pow₀ ht
  have h₂ : (t ^ 8) ^ 4 = t ^ 32 := by rw [← pow_mul]
  rw [h₂]
  linarith [mul_le_mul_of_nonneg_left h₁ (by norm_num : (0 : ℝ) ≤ 19)]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- **The bad mass** (`eventually_badMass_le` with `badMass` unfolded): the absolute row mass of
`𝒯` on pairs with a bad source or a bad target is at most `C₀ UV L^{3A₀} exp(-L^{a₋}/8)`,
where `UV = d₀ Y X`. -/
theorem eventually_stateMass_mul_sum_le {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) (hg : 0 < g) (A₀ : ℝ) :
    ∃ C₀ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      stateMass x d * ∑ s : State x d (2 ^ j) (2 ^ k), ∑ s' : State x d (2 ^ j) (2 ^ k),
        ((if IsGood x d (2 ^ j) (2 ^ k) s.1.1 s.1.2 then 0 else 1) +
            (if IsGood x d (2 ^ j) (2 ^ k) s'.1.1 s'.1.2 then 0 else 1)) *
          ‖rowOp q A₀ x d (2 ^ j) (2 ^ k) s s'‖ ≤
        C₀ * (2 ^ k * 2 ^ j * d.X) * Real.log x ^ (3 * A₀) *
          Real.exp (-Real.log x ^ alo / 8) := by
  obtain ⟨C₁, hC₁, hCB⟩ := exists_congBound
  set c : ℝ := 144 * (C₁ + 19) with hc_def
  have hc : 0 ≤ c := by positivity
  refine ⟨3094 + 2 ^ (K + 1) * 748 * 91, ?_⟩
  filter_upwards [eventually_card_not_isGood_le (K := K) (C := C) (CX := CX) (ahi := ahi) halo hg,
    eventually_band_disjoint hg, eventually_harmonicMass_band halo.le,
    eventually_exp_le_rpow A₀, eventually_pow_le_exp K, eventually_error_le K A₀ c hc,
    eventually_le_rpow_log (by norm_num : (0 : ℝ) < 1 / 2) (16 * K + 6 + 2 * Real.log CX),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with x hBC hdisj' hVx hE1 hE2 hE3 hE4 hL hx1 d hd j k
  set L := Real.log x with hLdef
  set u := L ^ (1 / 2 : ℝ) with hu_def
  set t := Real.exp (K * u) with ht_def
  set Y : ℝ := 2 ^ j with hY_def
  set d₀ : ℝ := 2 ^ k with hd₀_def
  set e₈ := Real.exp (-L ^ alo / 8) with he₈
  have hY1 : 1 ≤ Y := one_le_pow₀ one_le_two
  have hd₀1 : 1 ≤ d₀ := one_le_pow₀ one_le_two
  have hY0 : 0 < Y := by linarith
  have hd₀0 : 0 < d₀ := by linarith
  have hL0 : 0 < L := by linarith
  -- the scales: `H_m, H_n ≥ x^γ ≥ exp(L^{0.99})`
  have hγ : L ^ (-(1 / 100 : ℝ)) ≤ d.γ := hd.γ_ge
  have hxγ : Real.exp (L ^ (99 / 100 : ℝ)) ≤ x ^ d.γ := by
    have h₁ : L * L ^ (-(1 / 100 : ℝ)) = L ^ (99 / 100 : ℝ) := by
      rw [← Real.rpow_one_add' hL0.le (by norm_num)]
      norm_num
    calc Real.exp (L ^ (99 / 100 : ℝ)) = x ^ L ^ (-(1 / 100 : ℝ)) := by
          rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < x), ← hLdef, h₁]
      _ ≤ x ^ d.γ := Real.rpow_le_rpow_of_exponent_le hx1 hγ
  have hexp2 : (2 : ℝ) ≤ Real.exp (L ^ (99 / 100 : ℝ)) := by
    have : 1 ≤ L ^ (99 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
    linarith [Real.add_one_le_exp (L ^ (99 / 100 : ℝ))]
  have hHm : Real.exp (L ^ (99 / 100 : ℝ)) ≤ d.Hm := hxγ.trans hd.Hm_ge
  have hHn : Real.exp (L ^ (99 / 100 : ℝ)) ≤ d.Hn := hxγ.trans hd.Hn_ge
  have hHm0 : 0 < d.Hm := by linarith
  have hHn0 : 0 < d.Hn := by linarith
  have hX0 : 0 ≤ d.X := by unfold Data.X; positivity
  have hRHS : 0 ≤ (3094 + 2 ^ (K + 1) * 748 * 91) * (2 ^ k * 2 ^ j * d.X) * L ^ (3 * A₀) *
      e₈ := by
    positivity
  by_cases hT : ∃ s s' : State x d Y d₀, rowOp q A₀ x d Y d₀ s s' ≠ 0
  swap
  · push Not at hT
    simp only [hT, norm_zero, mul_zero, sum_const_zero]
    exact hRHS
  obtain ⟨s₀, s₀', h0⟩ := hT
  obtain ⟨hD₁, -, -, hηb, -⟩ := rowOp_ne_zero h0
  have hb := lt_of_dyadicBump_ne_zero hηb
  rw [one_lt_div hY0, div_lt_iff₀ hY0] at hb
  have ht1 : 1 ≤ t := Real.one_le_exp (by positivity)
  have hexp4 : Real.exp (4 * K * u) = t ^ 4 := by
    rw [show 4 * (K : ℝ) * u = ((4 : ℕ) : ℝ) * (K * u) by push_cast; ring, exp_mul_eq_pow]
  obtain ⟨-, hband₀, -, -⟩ := state_props s₀
  have hpos₀ : 0 < listProd s₀.1.2 :=
    listProd_pos fun i h => TypeII.band_prime (hband₀ i h)
  have hlist₀ : (listProd s₀.1.2 : ℝ) ≤ t ^ 4 := (listProd_le_exp hd hahi hL s₀).trans hexp4.le
  have hYt : Y ≤ t ^ 4 :=
    hb.1.le.trans ((Nat.cast_le.2 (lastProd_le_listProd hpos₀)).trans hlist₀)
  have hd₀t : d₀ ≤ t ^ 4 :=
    hD₁.trans ((Nat.cast_le.2 (padProd_le_listProd hpos₀)).trans hlist₀)
  -- there is a band, so `a₋ ≤ 1/5` and `exp(L^{a₋}) ≤ b < 4Y`
  have hK0 : K ≠ 0 := by
    rintro rfl
    have : lastProd s₀.1.2 = 1 := by simp [lastProd]
    rw [this, Nat.cast_one] at hb
    linarith [hb.1]
  set i₀ : Fin K := ⟨0, Nat.pos_of_ne_zero hK0⟩
  have halo5 : alo ≤ 1 / 5 := (hd.window i₀).1.trans ((hd.window i₀).2.trans hahi.le)
  have ha5 : ∀ i, d.a i ≤ 1 / 5 := fun i => (hd.window i).2.trans hahi.le
  have hY4 : Real.exp (L ^ alo) ≤ 4 * Y := by
    have h₁ : Real.exp (L ^ alo) ≤ s₀.1.2 i₀ (Fin.last _) :=
      (Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL (hd.window i₀).1)).trans
        (exp_le_of_mem_band (hband₀ i₀ _))
    have h₂ : s₀.1.2 i₀ (Fin.last _) ≤ lastProd s₀.1.2 :=
      single_le_prod (fun i _ => (TypeII.band_prime (hband₀ i _)).one_lt.le) (mem_univ i₀)
    have h₂' : (s₀.1.2 i₀ (Fin.last _) : ℝ) ≤ lastProd s₀.1.2 := by exact_mod_cast h₂
    linarith [hb.2]
  have hB : BadCountBound x alo d Y d₀ := hBC d hd Y d₀ hY4
  have hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdisj' _ _ (hd.gap i j h)
    · exact (hdisj' _ _ (hd.gap j i h)).symm
  -- `1 ≤ W = ∏ V_i^{-1} ≤ 2^K`
  have hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1 :=
    fun i => hVx _ (hd.window i).1
  have hbm1 : d.bandMass x ≤ 1 := by
    calc d.bandMass x ≤ ∏ _i : Fin K, (1 : ℝ) :=
          prod_le_prod₀ (fun i _ => by linarith [(hV i).1]) fun i _ => (hV i).2
      _ = 1 := prod_const_one
  have hbm2 : (1 / 2 : ℝ) ^ K ≤ d.bandMass x := by
    calc (1 / 2 : ℝ) ^ K = ∏ _i : Fin K, (1 / 2 : ℝ) := by
          rw [prod_const, card_univ, Fintype.card_fin]
      _ ≤ d.bandMass x := prod_le_prod₀ (fun _ _ => by norm_num) fun i _ => (hV i).1
  have hbm0 : 0 < d.bandMass x := lt_of_lt_of_le (by positivity) hbm2
  set W := (d.bandMass x)⁻¹ with hW_def
  have hW1 : 1 ≤ W := one_le_inv₀ hbm0 |>.2 hbm1
  have hWK : W ≤ 2 ^ K := by
    have := inv_anti₀ (by positivity) hbm2
    rwa [one_div, inv_pow, inv_inv] at this
  set St := states x d Y d₀ with hSt
  set κ := 4 * L ^ (3 * A₀) / Y with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set RS := (#{yy ∈ St ×ˢ St | ¬ IsGood x d Y d₀ yy.1.1 yy.1.2 ∧
    RowEdge Y d₀ yy.1.1 yy.1.2 yy.2.1 yy.2.2 ∧ RawEdge yy.1.1 yy.1.2 yy.2.1 yy.2.2} : ℝ)
  set RT := (#{yy ∈ St ×ˢ St | ¬ IsGood x d Y d₀ yy.2.1 yy.2.2 ∧
    RowEdge Y d₀ yy.1.1 yy.1.2 yy.2.1 yy.2.2 ∧ RawEdge yy.1.1 yy.1.2 yy.2.1 yy.2.2} : ℝ)
  set CS := ∑ y₁ ∈ St.filter (fun y => ¬ IsGood x d Y d₀ y.1 y.2),
    (#{y₂ ∈ St | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} : ℝ)
  set CT := ∑ y₂ ∈ St.filter (fun y => ¬ IsGood x d Y d₀ y.1 y.2),
    (#{y₁ ∈ St | RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2} : ℝ)
  -- step 1: the entries of `𝒯` by `norm_rowOp_le`, then the decomposition
  have hconv : ∀ G : (ℕ × ℕ) × Lists K (padCount x) → (ℕ × ℕ) × Lists K (padCount x) → ℝ,
      ∑ s : State x d Y d₀, ∑ s' : State x d Y d₀, G s.1 s'.1 =
        ∑ y₁ ∈ St, ∑ y₂ ∈ St, G y₁ y₂ := by
    intro G
    rw [← sum_coe_sort St (fun y₁ => ∑ y₂ ∈ St, G y₁ y₂)]
    exact sum_congr rfl fun s _ => sum_coe_sort St (G s.1)
  have hstep : ∑ s : State x d Y d₀, ∑ s' : State x d Y d₀,
      ((if IsGood x d Y d₀ s.1.1 s.1.2 then 0 else 1) +
          (if IsGood x d Y d₀ s'.1.1 s'.1.2 then 0 else 1)) *
        ‖rowOp q A₀ x d Y d₀ s s'‖ ≤ W * (RS + RT) + W * κ * (CS + CT) := by
    calc _ ≤ ∑ s : State x d Y d₀, ∑ s' : State x d Y d₀,
          ((if IsGood x d Y d₀ s.1.1 s.1.2 then 0 else 1) +
            (if IsGood x d Y d₀ s'.1.1 s'.1.2 then 0 else 1)) *
          (if RowEdge Y d₀ s.1.1 s.1.2 s'.1.1 s'.1.2 then
            W * ((if RawEdge s.1.1 s.1.2 s'.1.1 s'.1.2 then 1 else 0) + κ) else 0) := by
          refine sum_le_sum fun s _ => sum_le_sum fun s' _ => ?_
          refine mul_le_mul_of_nonneg_left (norm_rowOp_le hq hq₁.le hL0 hbm0 hY0 hd₀0 s s') ?_
          split_ifs <;> norm_num
      _ = ∑ y₁ ∈ St, ∑ y₂ ∈ St,
          ((if IsGood x d Y d₀ y₁.1 y₁.2 then 0 else 1) +
            (if IsGood x d Y d₀ y₂.1 y₂.2 then 0 else 1)) *
          (if RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2 then
            W * ((if RawEdge y₁.1 y₁.2 y₂.1 y₂.2 then 1 else 0) + κ) else 0) :=
          hconv fun y₁ y₂ => ((if IsGood x d Y d₀ y₁.1 y₁.2 then 0 else 1) +
            (if IsGood x d Y d₀ y₂.1 y₂.2 then 0 else 1)) *
          (if RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2 then
            W * ((if RawEdge y₁.1 y₁.2 y₂.1 y₂.2 then 1 else 0) + κ) else 0)
      _ = W * (RS + RT) + W * κ * (CS + CT) :=
          sum_bad_mul_eq St (fun y => IsGood x d Y d₀ y.1 y.2)
            (fun y₁ y₂ => RowEdge Y d₀ y₁.1 y₁.2 y₂.1 y₂.2)
            (fun y₁ y₂ => RawEdge y₁.1 y₁.2 y₂.1 y₂.2) W κ
  -- the uniform error `Ē`
  set U := d₀ * Y * d.Hm with hU_def
  set V := d.Hn with hV_def
  set μ := min U V with hμ_def
  set ε := Real.exp (-L ^ alo / 4) with hε
  have hU1 : d.Hm ≤ U := by
    have : 1 ≤ d₀ * Y := one_le_mul_of_one_le_of_one_le hd₀1 hY1
    calc d.Hm = 1 * d.Hm := (one_mul _).symm
      _ ≤ d₀ * Y * d.Hm := mul_le_mul_of_nonneg_right this hHm0.le
  have hU2 : 2 ≤ U := by linarith
  have hV2 : 2 ≤ V := by linarith
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  set Ē := 3 * (8 * t ^ 8) * ((C₁ * (t ^ 8) ^ 4 + 19) * (U * V * μ ^ (-(1 / 5 : ℝ)))) *
    (6 * t ^ 17) with hĒ_def
  have hĒ0 : 0 ≤ Ē := by positivity
  have hĒ : ∀ z G' N : ℝ, |z| ≤ 8 * t ^ 8 → 0 ≤ G' → G' ≤ t ^ 8 → 0 ≤ N → N ≤ 6 * t ^ 17 →
      3 * |z| * (C₁ * U * V * G' ^ 4 * μ ^ (-(1 / 5 : ℝ)) + (16 * U + V + 2)) * N ≤ Ē :=
    fun z G' N hz hG0 hG hN0 hN =>
      err_total_le (by linarith) (by linarith) hC₁ ht1 hz hG0 hG hN0 hN
  have hz8 : 8 * d₀ * Y ≤ 8 * t ^ 8 := by
    have := mul_le_mul hd₀t hYt hY0.le (by positivity)
    nlinarith
  have hGt : ∀ p ∈ lists x d (padCount x), (listProd p : ℝ) ≤ t ^ 4 := fun p hp =>
    (listProd_le_exp' hd hahi hL hp).trans hexp4.le
  have hlast : ∀ p ∈ lists x d (padCount x), (lastProd p : ℝ) ≤ t ^ 4 := by
    intro p hp
    have hpos : 0 < listProd p :=
      listProd_pos fun i h => TypeII.band_prime (lists_slot_mem_band hp i h)
    exact (Nat.cast_le.2 (lastProd_le_listProd hpos)).trans (hGt p hp)
  have hNt : ∀ p ∈ lists x d (padCount x), badIntervals x d Y p ≤ 6 * t ^ 17 := fun p hp =>
    badIntervals_le hL ha5 hY1 hYt rfl (hGt p hp)
  have ht48 : t ^ 4 * t ^ 4 = t ^ 8 := by ring
  have ht4 : t ^ 4 ≤ t ^ 8 := pow_le_pow_right₀ ht1 (by norm_num)
  set filt := (lists x d (padCount x) ×ˢ lists x d (padCount x)).filter
    (fun pp => ListEdge Y d₀ pp.1 pp.2) with hfilt
  -- the raw parts
  have hRS : RS ≤ ∑ pp ∈ filt,
      17 * (90 * U * V / ((listProd pp.1 : ℝ) * lastProd pp.2) * ε + Ē) := by
    refine (Nat.cast_le.2 (card_raw_le hdisj Y d₀)).trans ?_
    push_cast
    refine sum_le_sum fun pp hpp => ?_
    obtain ⟨hmem, he⟩ := mem_filter.1 hpp
    obtain ⟨hp, hp'⟩ := mem_product.1 hmem
    refine (card_joint_le hC₁ hCB hB hdisj hU2 hV2 hY1 hp hp' he).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hĒ _ ((listProd pp.1 : ℝ) * lastProd pp.2)
        _ ?_ (by positivity) ?_ (badIntervals_nonneg _ _ _ _) (hNt _ hp))) (by norm_num))
    · exact (abs_padProd_mul_sub_le he).1.trans hz8
    · rw [← ht48]
      exact mul_le_mul (hGt _ hp) (hlast _ hp') (Nat.cast_nonneg _) (by positivity)
  have hRT : RT ≤ ∑ pp ∈ filt,
      17 * (90 * U * V / ((listProd pp.2 : ℝ) * lastProd pp.1) * ε + Ē) := by
    refine (Nat.cast_le.2 (card_raw_le' hdisj Y d₀)).trans ?_
    push_cast
    refine sum_le_sum fun pp hpp => ?_
    obtain ⟨hmem, he⟩ := mem_filter.1 hpp
    obtain ⟨hp, hp'⟩ := mem_product.1 hmem
    refine (card_joint_le' hC₁ hCB hB hdisj hU2 hV2 hY1 hp hp' he).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hĒ _ ((listProd pp.2 : ℝ) * lastProd pp.1)
        _ ?_ (by positivity) ?_ (badIntervals_nonneg _ _ _ _) (hNt _ hp'))) (by norm_num))
    · exact (abs_padProd_mul_sub_le he).2.trans hz8
    · rw [← ht48]
      exact mul_le_mul (hGt _ hp') (hlast _ hp) (Nat.cast_nonneg _) (by positivity)
  -- the bad sources and targets
  set Λn : ℝ := ((Nat.log 2 ⌊16 * U⌋₊ ^ K : ℕ) : ℝ) with hΛn
  set nb : ℝ := (#{y ∈ St | ¬ IsGood x d Y d₀ y.1 y.2} : ℝ) with hnb
  have hbad : nb ≤ ∑ p ∈ lists x d (padCount x), (90 * U * V / listProd p * ε + Ē) := by
    refine (Nat.cast_le.2 (card_bad_le hdisj Y d₀)).trans ?_
    push_cast
    refine sum_le_sum fun p hp => (card_bad_dvd_le hC₁ hCB hB hdisj hU2 hV2 hp).trans
      (add_le_add le_rfl ?_)
    have := hĒ 1 (listProd p) (badIntervals x d Y p) (by rw [abs_one]; nlinarith)
      (Nat.cast_nonneg _) ((hGt p hp).trans ht4) (badIntervals_nonneg _ _ _ _) (hNt p hp)
    rwa [abs_one, mul_one] at this
  have hCS : CS ≤ nb * (17 * (10 * Y + 1) * Λn) := by
    calc CS ≤ ∑ _y₁ ∈ St.filter (fun y => ¬ IsGood x d Y d₀ y.1 y.2),
          17 * (10 * Y + 1) * Λn :=
          sum_le_sum fun y₁ hy₁ => card_targets_le hY0.le hU0 hV0.le (mem_filter.1 hy₁).1
      _ = nb * (17 * (10 * Y + 1) * Λn) := by rw [sum_const, nsmul_eq_mul]
  have hCT : CT ≤ nb * (17 * (10 * Y + 1) * Λn) := by
    calc CT ≤ ∑ _y₂ ∈ St.filter (fun y => ¬ IsGood x d Y d₀ y.1 y.2),
          17 * (10 * Y + 1) * Λn :=
          sum_le_sum fun y₂ hy₂ => card_sources_le hY0.le hU0 hV0.le (mem_filter.1 hy₂).1
      _ = nb * (17 * (10 * Y + 1) * Λn) := by rw [sum_const, nsmul_eq_mul]
  -- the masses
  set m := stateMass x d with hm_def
  have hm0 : 0 ≤ m := stateMass_nonneg x d
  have hmW : m * W = W ^ (padCount x + 2) := by
    rw [hm_def, stateMass, ← hW_def, ← pow_succ]
  set nL : ℝ := ((lists x d (padCount x)).card : ℝ) with hnL
  set Pm := m * W * nL ^ 2 with hPm
  have hnLt : nL ≤ t ^ 4 := card_lists_le_pow hL ha5
  have hPmt : Pm ≤ t ^ 11 := by
    have h₁ : m * W ≤ t ^ 3 := by
      rw [hmW]
      exact (pow_le_pow_left₀ (by linarith) hWK _).trans (two_pow_pow_le hL)
    have h₂ : nL ^ 2 ≤ (t ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnLt 2
    calc Pm ≤ t ^ 3 * (t ^ 4) ^ 2 :=
          mul_le_mul h₁ h₂ (by positivity) (by positivity)
      _ = t ^ 11 := by ring
  have hPm0 : 0 ≤ Pm := by positivity
  have hmnL : m * nL ≤ Pm := by
    have h₁ : nL ≤ nL ^ 2 := natCast_le_sq _
    calc m * nL = m * 1 * nL := by ring
      _ ≤ m * W * nL ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hW1 hm0) h₁ (Nat.cast_nonneg _)
            (mul_nonneg hm0 (by linarith))
  have hfiltc : (filt.card : ℝ) ≤ nL ^ 2 := by
    have := card_filter_le (lists x d (padCount x) ×ˢ lists x d (padCount x))
      (fun pp => ListEdge Y d₀ pp.1 pp.2)
    rw [card_product] at this
    rw [hnL, sq]
    exact_mod_cast this
  have hmW0 : 0 ≤ m * W := mul_nonneg hm0 (by linarith)
  have hRS' : m * W * RS ≤ 1530 * (U * V) * ε + 17 * Pm * Ē := by
    have hmass := mass_mul_sum_inv_le hbm0 Y d₀
    rw [← hW_def, ← hm_def] at hmass
    calc m * W * RS ≤ m * W * ∑ pp ∈ filt,
          17 * (90 * U * V / ((listProd pp.1 : ℝ) * lastProd pp.2) * ε + Ē) :=
          mul_le_mul_of_nonneg_left hRS hmW0
      _ = ∑ pp ∈ filt, (1530 * (U * V) * ε * (m * W *
            (((listProd pp.1 : ℕ) : ℝ) * (lastProd pp.2 : ℕ))⁻¹) + 17 * (m * W) * Ē) := by
          rw [mul_sum]
          refine sum_congr rfl fun pp _ => ?_
          rw [div_eq_mul_inv]
          ring
      _ = 1530 * (U * V) * ε * (m * W * ∑ pp ∈ filt,
            (((listProd pp.1 : ℕ) : ℝ) * (lastProd pp.2 : ℕ))⁻¹) +
            17 * (m * W * filt.card) * Ē := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul]
          ring
      _ ≤ 1530 * (U * V) * ε * 1 + 17 * Pm * Ē := by
          refine add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity)) ?_
          refine mul_le_mul_of_nonneg_right ?_ hĒ0
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfiltc hmW0) (by norm_num)
      _ = 1530 * (U * V) * ε + 17 * Pm * Ē := by ring
  have hRT' : m * W * RT ≤ 1530 * (U * V) * ε + 17 * Pm * Ē := by
    have hmass := mass_mul_sum_inv_le' hbm0 Y d₀
    rw [← hW_def, ← hm_def] at hmass
    calc m * W * RT ≤ m * W * ∑ pp ∈ filt,
          17 * (90 * U * V / ((listProd pp.2 : ℝ) * lastProd pp.1) * ε + Ē) :=
          mul_le_mul_of_nonneg_left hRT hmW0
      _ = ∑ pp ∈ filt, (1530 * (U * V) * ε * (m * W *
            (((listProd pp.2 : ℕ) : ℝ) * (lastProd pp.1 : ℕ))⁻¹) + 17 * (m * W) * Ē) := by
          rw [mul_sum]
          refine sum_congr rfl fun pp _ => ?_
          rw [div_eq_mul_inv]
          ring
      _ = 1530 * (U * V) * ε * (m * W * ∑ pp ∈ filt,
            (((listProd pp.2 : ℕ) : ℝ) * (lastProd pp.1 : ℕ))⁻¹) +
            17 * (m * W * filt.card) * Ē := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul]
          ring
      _ ≤ 1530 * (U * V) * ε * 1 + 17 * Pm * Ē := by
          refine add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity)) ?_
          refine mul_le_mul_of_nonneg_right ?_ hĒ0
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfiltc hmW0) (by norm_num)
      _ = 1530 * (U * V) * ε + 17 * Pm * Ē := by ring
  have hnb' : m * nb ≤ 90 * (U * V) * ε + Pm * Ē := by
    have hmass := stateMass_mul_sum_inv_listProd_le x d
    rw [← hm_def] at hmass
    calc m * nb ≤ m * ∑ p ∈ lists x d (padCount x), (90 * U * V / listProd p * ε + Ē) :=
          mul_le_mul_of_nonneg_left hbad hm0
      _ = ∑ p ∈ lists x d (padCount x), (90 * (U * V) * ε * (m * ((listProd p : ℕ) : ℝ)⁻¹) +
            m * Ē) := by
          rw [mul_sum]
          refine sum_congr rfl fun p _ => ?_
          rw [div_eq_mul_inv]
          ring
      _ = 90 * (U * V) * ε * (m * ∑ p ∈ lists x d (padCount x), ((listProd p : ℕ) : ℝ)⁻¹) +
            m * nL * Ē := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_const, nsmul_eq_mul]
          ring
      _ ≤ 90 * (U * V) * ε * 1 + Pm * Ē :=
          add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity))
            (mul_le_mul_of_nonneg_right hmnL hĒ0)
      _ = 90 * (U * V) * ε + Pm * Ē := by ring
  -- `Λ ≤ (3L)^K`
  have hΛ : Λn ≤ (3 * L) ^ K := by
    have hn0 : ⌊16 * U⌋₊ ≠ 0 := (Nat.floor_pos.2 (by linarith)).ne'
    have hlogU : Real.log (⌊16 * U⌋₊ : ℝ) ≤ Real.log (16 * U) :=
      Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) (Nat.floor_le (by linarith))
    have h16 := log_sixteen_le
    have hlogd : Real.log d₀ ≤ 4 * K * u := by
      have := Real.log_le_log hd₀0 (hd₀t.trans hexp4.symm.le)
      rwa [Real.log_exp] at this
    have hlogY : Real.log Y ≤ 4 * K * u := by
      have := Real.log_le_log hY0 (hYt.trans hexp4.symm.le)
      rwa [Real.log_exp] at this
    have hHmx : d.Hm ≤ CX * x := by
      have h₁ := hd.X_le
      have h₂ : d.Hm * 1 ≤ d.Hm * d.Hn := mul_le_mul_of_nonneg_left (by linarith) hHm0.le
      linarith
    have hlogHm : Real.log d.Hm ≤ Real.log CX + L := by
      have := Real.log_le_log hHm0 hHmx
      rwa [Real.log_mul (by linarith) (by linarith)] at this
    have hlog16U : Real.log (16 * U) = Real.log 16 + Real.log d₀ + Real.log Y + Real.log d.Hm := by
      simp only [hU_def]
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      ring
    have huu : u * u = L := by
      rw [hu_def, ← Real.rpow_add hL0]
      norm_num
    have hu1 : 1 ≤ u := Real.one_le_rpow hL (by norm_num)
    have hCX0 : 0 ≤ Real.log CX := Real.log_nonneg hCX
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hlog : (Nat.log 2 ⌊16 * U⌋₊ : ℝ) ≤ 3 * L := by
      refine (natLog_le_two_mul_log hn0).trans ?_
      have h₁ := affine_le_sq hu1 huu hK hCX0 hE4
      linarith
    rw [hΛn, Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hlog K
  -- the error is negligible
  set T := c * t ^ 70 * Real.exp (-L ^ (99 / 100 : ℝ) / 5) with hT_def
  have hμη : μ ^ (-(1 / 5 : ℝ)) ≤ Real.exp (-L ^ (99 / 100 : ℝ) / 5) := by
    have hμ : Real.exp (L ^ (99 / 100 : ℝ)) ≤ μ := le_min (hHm.trans hU1) hHn
    calc μ ^ (-(1 / 5 : ℝ)) ≤ Real.exp (L ^ (99 / 100 : ℝ)) ^ (-(1 / 5 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hμ (by norm_num)
      _ = Real.exp (-L ^ (99 / 100 : ℝ) / 5) := by
          rw [← Real.exp_mul]
          ring_nf
  have hPĒ : Pm * Ē ≤ U * V * T := by
    have hC32 : C₁ * (t ^ 8) ^ 4 + 19 ≤ (C₁ + 19) * t ^ 32 := add_le_mul_pow C₁ ht1
    have hĒ' : Ē ≤ 144 * (C₁ + 19) * t ^ 57 * (U * V * Real.exp (-L ^ (99 / 100 : ℝ) / 5)) := by
      calc Ē = 144 * t ^ 25 * (C₁ * (t ^ 8) ^ 4 + 19) * (U * V * μ ^ (-(1 / 5 : ℝ))) := by
            simp only [hĒ_def]
            ring
        _ ≤ 144 * t ^ 25 * ((C₁ + 19) * t ^ 32) *
              (U * V * Real.exp (-L ^ (99 / 100 : ℝ) / 5)) := by gcongr
        _ = 144 * (C₁ + 19) * t ^ 57 * (U * V * Real.exp (-L ^ (99 / 100 : ℝ) / 5)) := by ring
    calc Pm * Ē ≤ t ^ 11 * (144 * (C₁ + 19) * t ^ 57 *
          (U * V * Real.exp (-L ^ (99 / 100 : ℝ) / 5))) := mul_le_mul hPmt hĒ' hĒ0 (by positivity)
      _ = c * t ^ 68 * Real.exp (-L ^ (99 / 100 : ℝ) / 5) * (U * V) := by
          simp only [hc_def]
          ring
      _ ≤ c * t ^ 70 * Real.exp (-L ^ (99 / 100 : ℝ) / 5) * (U * V) := by
          have h7 : t ^ 68 ≤ t ^ 70 := pow_le_pow_right₀ ht1 (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h7 hc) (Real.exp_pos _).le) (by positivity)
      _ = U * V * T := by simp only [hT_def]; ring
  have h10 : L ^ (1 / 10 : ℝ) ≤ L ^ alo := Real.rpow_le_rpow_of_exponent_le hL halo.le
  have h15 : L ^ alo ≤ L ^ (1 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL halo5
  have hεe : ε = e₈ * e₈ := by
    rw [hε, he₈, ← Real.exp_add]
    ring_nf
  have he₈A : e₈ ≤ L ^ (3 * A₀) := (Real.exp_le_exp.2 (by linarith)).trans hE1
  have hεA : ε ≤ L ^ (3 * A₀) * e₈ := by
    rw [hεe]
    exact mul_le_mul_of_nonneg_right he₈A (Real.exp_pos _).le
  have h5e : Real.exp (-L ^ (1 / 5 : ℝ) / 8) ≤ e₈ := Real.exp_le_exp.2 (by linarith)
  have hTA : T ≤ L ^ (3 * A₀) * e₈ :=
    hE3.1.trans (mul_le_mul_of_nonneg_left h5e (by positivity))
  have hΛε : (3 * L) ^ K * ε ≤ e₈ := by
    calc (3 * L) ^ K * ε ≤ Real.exp (L ^ alo / 8) * ε :=
          mul_le_mul_of_nonneg_right (hE2.trans (Real.exp_le_exp.2 (by linarith)))
            (Real.exp_pos _).le
      _ = e₈ := by
          rw [hε, he₈, ← Real.exp_add]
          ring_nf
  have hΛT : (3 * L) ^ K * T ≤ e₈ := by
    rw [mul_comm]
    exact hE3.2.trans h5e
  have hnb0 : 0 ≤ nb := Nat.cast_nonneg _
  have hΛ0 : 0 ≤ Λn := Nat.cast_nonneg _
  have hUV : (2 : ℝ) ^ k * 2 ^ j * d.X = U * V := by
    simp only [hU_def, hV_def, hY_def, hd₀_def, Data.X]
    ring
  rw [hUV]
  calc m * ∑ s : State x d Y d₀, ∑ s' : State x d Y d₀,
        ((if IsGood x d Y d₀ s.1.1 s.1.2 then 0 else 1) +
            (if IsGood x d Y d₀ s'.1.1 s'.1.2 then 0 else 1)) *
          ‖rowOp q A₀ x d Y d₀ s s'‖
      ≤ m * (W * (RS + RT) + W * κ * (CS + CT)) := mul_le_mul_of_nonneg_left hstep hm0
    _ ≤ (3094 + 2 ^ (K + 1) * 748 * 91) * (U * V) * L ^ (3 * A₀) * e₈ :=
        badMass_final_combine hm0 (by linarith) hWK hY1 (by positivity) (by positivity) hPm0 hĒ0
          hnb0
          hRS' hRT' hCS hCT hnb' hΛ0 hΛ hPĒ (Real.exp_pos _).le hεA hTA hΛε hΛT

end Erdos408.OneSided
