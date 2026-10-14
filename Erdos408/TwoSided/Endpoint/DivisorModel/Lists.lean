module

public import Erdos408.TwoSided.Endpoint.DivisorModel.Truncation

/-!
# The marked weights in list form

Step 1 of Lemma E1 (`blueprint/two_sided_correlation.md` §6.1): both marked weights are list
forms in the sense of `DivModel.listForm`.

* `DivModel.markedWeight_eq_listForm`: for pairwise disjoint groups `G i`,
  `𝒲(n) = ∑_{β, β_i ∈ G i} [β ⊆ D(n)] ∏_i V_i⁻¹ · q^{|D(n) \ β|}`, one prime per group.
* `DivModel.markedListWeight_eq_listForm`: `W_S^b(n)` over the lists `groupLists P S` of
  distinct primes in the slots `S g`, damped by `q₀` off the represented primes.

With the weight sums `∑_j [R_j ⊆ D(n)] |c_j|` (the normalized list counts of step 5) and the
masses `∑_j |c_j| / ∏ R_j` (the brackets of step 4) of both forms.
-/

@[expose] public section

namespace Erdos408.TwoSided.DivModel

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### One prime per group -/

/-- The coefficient `∏_i V_i⁻¹` of a list of `𝒲`. -/
noncomputable def bandCoeff (G : ι → Finset ℕ) : ℂ :=
  ∏ i, ((harmonicMass (G i))⁻¹ : ℂ)

/-- A list with one prime from each of pairwise disjoint groups is injective. -/
theorem injective_of_mem_piFinset {G : ι → Finset ℕ}
    (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j)) {β : ι → ℕ}
    (hβ : β ∈ Fintype.piFinset G) : Function.Injective β := by
  intro i j h
  by_contra hij
  exact disjoint_left.1 (hG i j hij) (Fintype.mem_piFinset.1 hβ i)
    (h ▸ Fintype.mem_piFinset.1 hβ j)

/-- The represented set of a list lies in the union of the groups. -/
theorem image_subset_biUnion {G : ι → Finset ℕ} {β : ι → ℕ} (hβ : β ∈ Fintype.piFinset G) :
    univ.image β ⊆ univ.biUnion G := by
  intro p hp
  obtain ⟨i, -, rfl⟩ := mem_image.1 hp
  exact mem_biUnion.2 ⟨i, mem_univ i, Fintype.mem_piFinset.1 hβ i⟩

/-- The lists represented at `n` are those of the primes dividing `n`. -/
theorem filter_piFinset_eq (G : ι → Finset ℕ) (n : ℕ) :
    (Fintype.piFinset G).filter (fun β => univ.image β ⊆ divs (univ.biUnion G) n) =
      Fintype.piFinset fun i => (G i).filter (· ∣ n) := by
  ext β
  simp only [mem_filter, Fintype.mem_piFinset, divs, image_subset_iff, mem_univ, true_imp_iff,
    mem_biUnion, true_and]
  constructor
  · rintro ⟨h₁, h₂⟩ i
    exact ⟨h₁ i, (h₂ i).2⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => ⟨⟨i, (h i).1⟩, (h i).2⟩⟩

omit [DecidableEq ι] in
/-- `|D(n)| = ∑_i ω_i(n)` for pairwise disjoint groups. -/
theorem card_divs_biUnion {G : ι → Finset ℕ} (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (n : ℕ) : #(divs (univ.biUnion G) n) = ∑ i, primeCount (G i) n := by
  rw [divs, filter_biUnion, card_biUnion]
  · rfl
  · intro i _ j _ hij
    exact disjoint_filter_filter (hG i j hij)

/-- **Step 1 for the bands.** For pairwise disjoint groups and `w = q` on their union,
`𝒲(n)` is the list form with one prime per group. -/
theorem markedWeight_eq_listForm {G : ι → Finset ℕ}
    (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j)) (q : ℝ) {w : ℕ → ℂ}
    (hw : ∀ p ∈ univ.biUnion G, w p = q) (n : ℕ) :
    (markedWeight univ q G n : ℂ) =
      listForm (univ.biUnion G) (Fintype.piFinset G) (fun β => univ.image β)
        (fun _ => bandCoeff G) w n := by
  set D := divs (univ.biUnion G) n
  -- each represented list contributes `c q^{|D| - |ι|}`
  have hterm : ∀ β ∈ Fintype.piFinset fun i => (G i).filter (· ∣ n),
      bandCoeff G * ∏ p ∈ D \ univ.image β, w p =
        bandCoeff G * (q : ℂ) ^ (#D - Fintype.card ι) := by
    intro β hβ
    have hβG : β ∈ Fintype.piFinset G :=
      Fintype.mem_piFinset.2 fun i => (mem_filter.1 (Fintype.mem_piFinset.1 hβ i)).1
    have hsub : univ.image β ⊆ D := by
      have := (filter_piFinset_eq G n).symm ▸ hβ
      exact (mem_filter.1 this).2
    rw [prod_congr rfl fun p hp => hw p (divs_subset _ n (sdiff_subset hp)), prod_const,
      card_sdiff_of_subset hsub, card_image_of_injective _ (injective_of_mem_piFinset hG hβG),
      card_univ]
  unfold listForm
  rw [← sum_filter, filter_piFinset_eq, sum_congr rfl hterm, sum_const, Fintype.card_piFinset,
    nsmul_eq_mul]
  have hcard : ∀ i, #((G i).filter (· ∣ n)) = primeCount (G i) n := fun i => rfl
  simp only [hcard]
  unfold markedWeight bandCoeff
  rw [card_divs_biUnion hG, card_univ]
  by_cases h0 : ∀ i, 1 ≤ primeCount (G i) n
  · have hle : Fintype.card ι ≤ ∑ i, primeCount (G i) n := by
      rw [Fintype.card_eq_sum_ones]
      exact sum_le_sum fun i _ => h0 i
    rw [← Nat.cast_sub hle, zpow_natCast]
    push_cast
    rw [prod_div_distrib, div_eq_mul_inv, ← prod_inv_distrib]
    ring
  · push Not at h0
    obtain ⟨i, hi⟩ := h0
    have hi0 : primeCount (G i) n = 0 := by omega
    have hp : ∏ j, primeCount (G j) n = 0 := prod_eq_zero (mem_univ i) hi0
    rw [hp, prod_eq_zero (mem_univ i) (by rw [hi0, Nat.cast_zero, zero_div])]
    simp

/-- The weight sum of the band lists at `n` is `∏_i ω_i(n)/V_i ≤ 2^{|ι|} 2^{|D(n)|}`, for
`V_i ≥ 1/2`. -/
theorem sum_norm_bandCoeff_le {G : ι → Finset ℕ} (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (G i)) (n : ℕ) :
    (∑ β ∈ Fintype.piFinset G,
        if univ.image β ⊆ divs (univ.biUnion G) n then ‖bandCoeff G‖ else 0) ≤
      2 ^ Fintype.card ι * 2 ^ #(divs (univ.biUnion G) n) := by
  rw [← sum_filter, filter_piFinset_eq, sum_const, Fintype.card_piFinset, nsmul_eq_mul,
    card_divs_biUnion hG, ← prod_pow_eq_pow_sum, Fintype.card_eq_sum_ones,
    ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  unfold bandCoeff
  rw [norm_prod, Nat.cast_prod, ← prod_mul_distrib]
  refine prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  have hV0 : 0 < harmonicMass (G i) := by linarith [hV i]
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hV0.le]
  have h1 : (harmonicMass (G i))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hV0 (by norm_num)]
    linarith [hV i]
  have h2 : (#((G i).filter (· ∣ n)) : ℝ) ≤ 2 ^ primeCount (G i) n := by
    exact_mod_cast Nat.lt_two_pow_self.le
  calc (#((G i).filter (· ∣ n)) : ℝ) * (harmonicMass (G i))⁻¹ ≤ 2 ^ primeCount (G i) n * 2 :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ = 2 ^ 1 * 2 ^ primeCount (G i) n := by ring

/-- The mass of the band lists: `∑_β |c| / ∏_i β_i = ∏_i V_i⁻¹ V_i ≤ 1`. -/
theorem sum_norm_bandCoeff_div_le {G : ι → Finset ℕ}
    (hG : ∀ i j, i ≠ j → Disjoint (G i) (G j)) :
    ∑ β ∈ Fintype.piFinset G, ‖bandCoeff G‖ / ∏ p ∈ univ.image β, (p : ℝ) ≤ 1 := by
  have hV0 : ∀ i, 0 ≤ harmonicMass (G i) := fun i =>
    sum_nonneg fun p _ => by positivity
  have hterm : ∀ β ∈ Fintype.piFinset G, ‖bandCoeff G‖ / ∏ p ∈ univ.image β, (p : ℝ) =
      ∏ i, (harmonicMass (G i))⁻¹ * (1 / (β i : ℝ)) := by
    intro β hβ
    rw [prod_image fun i _ j _ h => injective_of_mem_piFinset hG hβ h, bandCoeff, norm_prod,
      prod_mul_distrib, div_eq_mul_inv, ← prod_inv_distrib]
    congr 1
    · refine prod_congr rfl fun i _ => ?_
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hV0 i)]
    · simp
  have hpu := (prod_univ_sum G fun i (y : ℕ) => (harmonicMass (G i))⁻¹ * (1 / (y : ℝ))).symm
  beta_reduce at hpu
  rw [sum_congr rfl hterm, hpu]
  refine prod_le_one₀ (fun i _ => sum_nonneg fun p _ =>
    mul_nonneg (inv_nonneg.2 (hV0 i)) (by positivity)) fun i _ => ?_
  rw [← mul_sum]
  exact inv_mul_le_one_of_le₀ le_rfl (hV0 i)

/-! ### Lists in the slots -/

/-- The lists of `W_S^b`: in each slot of `S g` a prime of `P g`, distinct within the group,
and `1` in every other slot. -/
noncomputable def groupLists (P : ι → Finset ℕ) {M : ℕ} (S : ι → Finset (Fin M)) :
    Finset (ι → Fin M → ℕ) :=
  (Fintype.piFinset fun g => Fintype.piFinset fun i => if i ∈ S g then P g else {1}).filter
    fun p => ∀ g, Set.InjOn (p g) (S g)

/-- The represented primes `⋃_g p_g(S g)` of a list. -/
def groupRep {M : ℕ} (S : ι → Finset (Fin M)) (p : ι → Fin M → ℕ) : Finset ℕ :=
  univ.biUnion fun g => (S g).image (p g)

/-- The coefficient `∏_g V_g^{-|S g|} b(p)` of a list of `W_S^b`. -/
noncomputable def groupCoeff (P : ι → Finset ℕ) {M : ℕ} (S : ι → Finset (Fin M))
    (b : (ι → Fin M → ℕ) → ℂ) (p : ι → Fin M → ℕ) : ℂ :=
  (∏ g, ((harmonicMass (P g))⁻¹ : ℂ) ^ #(S g)) * b p

/-- A slot of a list holds a prime of its group. -/
theorem mem_of_mem_groupLists {P : ι → Finset ℕ} {M : ℕ} {S : ι → Finset (Fin M)}
    {p : ι → Fin M → ℕ} (hp : p ∈ groupLists P S) {g : ι} {i : Fin M} (hi : i ∈ S g) :
    p g i ∈ P g := by
  have := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 hp).1 g) i
  rwa [ite_eq_left hi] at this

/-- The represented primes lie in the union of the groups. -/
theorem groupRep_subset {P : ι → Finset ℕ} {M : ℕ} {S : ι → Finset (Fin M)}
    {p : ι → Fin M → ℕ} (hp : p ∈ groupLists P S) : groupRep S p ⊆ univ.biUnion P := by
  intro x hx
  obtain ⟨g, -, hx⟩ := mem_biUnion.1 hx
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
  exact mem_biUnion.2 ⟨g, mem_univ g, mem_of_mem_groupLists hp hi⟩

/-- The represented primes of a list number `∑_g |S g|`. -/
theorem card_groupRep {P : ι → Finset ℕ} (hP : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {M : ℕ}
    {S : ι → Finset (Fin M)} {p : ι → Fin M → ℕ} (hp : p ∈ groupLists P S) :
    #(groupRep S p) = ∑ g, #(S g) := by
  rw [groupRep, card_biUnion]
  · exact sum_congr rfl fun g _ => card_image_of_injOn ((mem_filter.1 hp).2 g)
  · intro g _ h _ hgh
    refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    obtain ⟨j, hj, hj'⟩ := mem_image.1 hx'
    exact disjoint_left.1 (hP g h hgh) (mem_of_mem_groupLists hp hi)
      (hj' ▸ mem_of_mem_groupLists hp hj)

/-- The lists represented at `n` are `slotLists P S n`. -/
theorem filter_groupLists_eq (P : ι → Finset ℕ) {M : ℕ} (S : ι → Finset (Fin M)) (n : ℕ) :
    (groupLists P S).filter (fun p => groupRep S p ⊆ divs (univ.biUnion P) n) =
      slotLists P S n := by
  ext p
  simp only [groupLists, slotLists, mem_filter]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨h₁, fun g => ⟨h₂ g, fun i hi => ?_⟩⟩
    exact (mem_filter.1 (h₃ (mem_biUnion.2 ⟨g, mem_univ g, mem_image_of_mem _ hi⟩))).2
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨h₁, fun g => (h₂ g).1⟩, fun x hx => ?_⟩
    obtain ⟨g, -, hx⟩ := mem_biUnion.1 hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    exact mem_filter.2 ⟨groupRep_subset (p := p) (mem_filter.2 ⟨h₁, fun g => (h₂ g).1⟩)
      (mem_biUnion.2 ⟨g, mem_univ g, mem_image_of_mem _ hi⟩), (h₂ g).2 i hi⟩

/-- **Step 1 for the groups.** For pairwise disjoint groups and `w = q₀` on their union,
`W_S^b(n)` is the list form over `groupLists P S`. -/
theorem markedListWeight_eq_listForm {P : ι → Finset ℕ}
    (hP : ∀ g h, g ≠ h → Disjoint (P g) (P h)) (q₀ : ℝ) {M : ℕ} (S : ι → Finset (Fin M))
    (b : (ι → Fin M → ℕ) → ℂ) {w : ℕ → ℂ} (hw : ∀ p ∈ univ.biUnion P, w p = q₀) (n : ℕ) :
    markedListWeight P q₀ S b n =
      listForm (univ.biUnion P) (groupLists P S) (groupRep S) (groupCoeff P S b) w n := by
  set D := divs (univ.biUnion P) n
  have hD : #D = groupPrimeCount P n := card_divs_biUnion hP n
  have hterm : ∀ p ∈ slotLists P S n, groupCoeff P S b p * ∏ x ∈ D \ groupRep S p, w x =
      groupCoeff P S b p * (q₀ : ℂ) ^ (#D - ∑ g, #(S g)) := by
    intro p hp
    rw [← filter_groupLists_eq] at hp
    obtain ⟨hp₁, hp₂⟩ := mem_filter.1 hp
    rw [prod_congr rfl fun x hx => hw x (divs_subset _ n (sdiff_subset hx)), prod_const,
      card_sdiff_of_subset hp₂, card_groupRep hP hp₁]
  unfold listForm
  rw [← sum_filter, filter_groupLists_eq, sum_congr rfl hterm, ← sum_mul]
  unfold markedListWeight groupCoeff
  rw [← mul_sum]
  rcases (slotLists P S n).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · simp [he]
  · have hp₀' := hp₀
    rw [← filter_groupLists_eq] at hp₀'
    obtain ⟨hp₁, hp₂⟩ := mem_filter.1 hp₀'
    have hle : ∑ g, #(S g) ≤ #D := by
      rw [← card_groupRep hP hp₁]
      exact card_le_card hp₂
    rw [hD] at hle ⊢
    have hz : ((groupPrimeCount P n : ℤ) - ∑ g, ((S g).card : ℤ)) =
        ((groupPrimeCount P n - ∑ g, #(S g) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle, Nat.cast_sum]
    rw [hz, zpow_natCast]
    push_cast
    ring

/-- The weight sum of the slot lists at `n`: at most `(B^{|ι|} 2^{|D(n)|})^{m+1}` with
`B = max 1 v₋⁻¹`, for `|S g| ≤ m + 1`, `V_g ≥ v₋ > 0` and `|b| ≤ 1`. -/
theorem sum_norm_groupCoeff_le {P : ι → Finset ℕ} {M m : ℕ} {S : ι → Finset (Fin M)}
    {b : (ι → Fin M → ℕ) → ℂ} {vlo : ℝ} (hvlo : 0 < vlo)
    (hV : ∀ g, vlo ≤ harmonicMass (P g)) (hS : ∀ g, #(S g) ≤ m + 1) (hb : ∀ p, ‖b p‖ ≤ 1)
    (hP : ∀ g h, g ≠ h → Disjoint (P g) (P h)) (n : ℕ) :
    (∑ p ∈ groupLists P S,
        if groupRep S p ⊆ divs (univ.biUnion P) n then ‖groupCoeff P S b p‖ else 0) ≤
      ((max 1 vlo⁻¹) ^ Fintype.card ι * 2 ^ #(divs (univ.biUnion P) n)) ^ (m + 1) := by
  set B := max 1 vlo⁻¹
  have hV0 : ∀ g, 0 < harmonicMass (P g) := fun g => hvlo.trans_le (hV g)
  rw [← sum_filter, filter_groupLists_eq]
  -- each list has weight at most `∏_g V_g^{-|S g|}`
  have h1 : ∀ p ∈ slotLists P S n, ‖groupCoeff P S b p‖ ≤
      ∏ g, (harmonicMass (P g))⁻¹ ^ #(S g) := by
    intro p _
    rw [groupCoeff, norm_mul, norm_prod]
    have : ∀ g, ‖((harmonicMass (P g))⁻¹ : ℂ) ^ #(S g)‖ = (harmonicMass (P g))⁻¹ ^ #(S g) :=
      fun g => by
        rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hV0 g).le]
    simp only [this]
    calc _ ≤ (∏ g, (harmonicMass (P g))⁻¹ ^ #(S g)) * 1 :=
          mul_le_mul_of_nonneg_left (hb p)
            (prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2 (hV0 g).le) _)
      _ = _ := mul_one _
  -- there are at most `∏_g ω_g^{|S g|}` lists
  have h2 : #(slotLists P S n) ≤ ∏ g, primeCount (P g) n ^ #(S g) := by
    have hsub : slotLists P S n ⊆ Fintype.piFinset fun g => Fintype.piFinset fun i =>
        if i ∈ S g then (P g).filter (· ∣ n) else {1} := by
      intro p hp
      obtain ⟨hp₁, hp₂⟩ := mem_filter.1 hp
      refine Fintype.mem_piFinset.2 fun g => Fintype.mem_piFinset.2 fun i => ?_
      have := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hp₁ g) i
      split_ifs with hi
      · rw [ite_eq_left hi] at this
        exact mem_filter.2 ⟨this, (hp₂ g).2 i hi⟩
      · rwa [ite_eq_right hi] at this
    refine (card_le_card hsub).trans_eq ?_
    rw [Fintype.card_piFinset]
    refine prod_congr rfl fun g _ => ?_
    rw [Fintype.card_piFinset]
    have : ∀ i, #(if i ∈ S g then (P g).filter (· ∣ n) else {1}) =
        if i ∈ S g then primeCount (P g) n else 1 := by
      intro i
      split_ifs <;> rfl
    simp only [this]
    rw [Fintype.prod_ite_mem, prod_const]
  calc ∑ p ∈ slotLists P S n, ‖groupCoeff P S b p‖
      ≤ ∑ _p ∈ slotLists P S n, ∏ g, (harmonicMass (P g))⁻¹ ^ #(S g) := sum_le_sum h1
    _ = #(slotLists P S n) * ∏ g, (harmonicMass (P g))⁻¹ ^ #(S g) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (∏ g, (primeCount (P g) n : ℝ) ^ #(S g)) * ∏ g, (harmonicMass (P g))⁻¹ ^ #(S g) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h2)
          (prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2 (hV0 g).le) _)
    _ = ∏ g, ((primeCount (P g) n : ℝ) * (harmonicMass (P g))⁻¹) ^ #(S g) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl fun g _ => (mul_pow _ _ _).symm
    _ ≤ ∏ g, (B * 2 ^ primeCount (P g) n) ^ (m + 1) := by
        refine prod_le_prod₀ (fun g _ => pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (inv_nonneg.2 (hV0 g).le)) _) fun g _ => ?_
        have hB1 : 1 ≤ B := le_max_left _ _
        have hω : (primeCount (P g) n : ℝ) ≤ 2 ^ primeCount (P g) n := by
          exact_mod_cast Nat.lt_two_pow_self.le
        have h21 : (1 : ℝ) ≤ 2 ^ primeCount (P g) n := one_le_pow₀ (by norm_num)
        have hinv : (harmonicMass (P g))⁻¹ ≤ B :=
          ((inv_le_inv₀ (hV0 g) hvlo).2 (hV g)).trans (le_max_right _ _)
        have hbase : (primeCount (P g) n : ℝ) * (harmonicMass (P g))⁻¹ ≤
            B * 2 ^ primeCount (P g) n := by
          rw [mul_comm]
          exact mul_le_mul hinv hω (Nat.cast_nonneg _) (by linarith)
        have hone : 1 ≤ B * 2 ^ primeCount (P g) n := by nlinarith
        calc ((primeCount (P g) n : ℝ) * (harmonicMass (P g))⁻¹) ^ #(S g)
            ≤ (B * 2 ^ primeCount (P g) n) ^ #(S g) :=
              pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.2 (hV0 g).le)) hbase _
          _ ≤ (B * 2 ^ primeCount (P g) n) ^ (m + 1) := pow_le_pow_right₀ hone (hS g)
    _ = (B ^ Fintype.card ι * 2 ^ #(divs (univ.biUnion P) n)) ^ (m + 1) := by
        rw [prod_pow, prod_mul_distrib, prod_const, card_univ, prod_pow_eq_pow_sum,
          card_divs_biUnion hP]

/-- The mass of the slot lists: `∑_p |c_p| / ∏ p ≤ ∏_g (∑_{p ∈ P g} 1/(V_g p))^{|S g|} = 1`,
for `|b| ≤ 1` and pairwise disjoint groups of positive mass. -/
theorem sum_norm_groupCoeff_div_le {P : ι → Finset ℕ} {M : ℕ} {S : ι → Finset (Fin M)}
    {b : (ι → Fin M → ℕ) → ℂ} (hV0 : ∀ g, 0 < harmonicMass (P g)) (hb : ∀ p, ‖b p‖ ≤ 1)
    (hP : ∀ g h, g ≠ h → Disjoint (P g) (P h)) :
    ∑ p ∈ groupLists P S, ‖groupCoeff P S b p‖ / ∏ x ∈ groupRep S p, (x : ℝ) ≤ 1 := by
  set f : ι → Fin M → ℕ → ℝ := fun g i y => if i ∈ S g then (harmonicMass (P g))⁻¹ / y else 1
  have hterm : ∀ p ∈ groupLists P S,
      ‖groupCoeff P S b p‖ / ∏ x ∈ groupRep S p, (x : ℝ) ≤ ∏ g, ∏ i, f g i (p g i) := by
    intro p hp
    have hprod : ∏ x ∈ groupRep S p, (x : ℝ) = ∏ g, ∏ i ∈ S g, (p g i : ℝ) := by
      rw [groupRep, prod_biUnion]
      · exact prod_congr rfl fun g _ => prod_image ((mem_filter.1 hp).2 g)
      · intro g _ h _ hgh
        refine disjoint_left.2 fun x hx hx' => ?_
        obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
        obtain ⟨j, hj, hj'⟩ := mem_image.1 hx'
        exact disjoint_left.1 (hP g h hgh) (mem_of_mem_groupLists hp hi)
          (hj' ▸ mem_of_mem_groupLists hp hj)
    have hf : ∀ g, ∏ i, f g i (p g i) = ∏ i ∈ S g, (harmonicMass (P g))⁻¹ / (p g i : ℝ) :=
      fun g => Fintype.prod_ite_mem (S g) _
    simp only [hf]
    have hA : 0 ≤ ∏ g, (harmonicMass (P g))⁻¹ ^ #(S g) :=
      prod_nonneg fun g _ => pow_nonneg (inv_nonneg.2 (hV0 g).le) _
    have heq : (∏ g, (harmonicMass (P g))⁻¹ ^ #(S g)) / ∏ g, ∏ i ∈ S g, (p g i : ℝ) =
        ∏ g, ∏ i ∈ S g, (harmonicMass (P g))⁻¹ / (p g i : ℝ) := by
      rw [← prod_div_distrib]
      refine prod_congr rfl fun g _ => ?_
      rw [prod_div_distrib, prod_const]
    rw [hprod, ← heq, groupCoeff, norm_mul, norm_prod]
    have hnorm : ∀ g, ‖((harmonicMass (P g))⁻¹ : ℂ) ^ #(S g)‖ =
        (harmonicMass (P g))⁻¹ ^ #(S g) := fun g => by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hV0 g).le]
    simp only [hnorm]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hA (hb p))
      (prod_nonneg fun g _ => prod_nonneg fun i _ => Nat.cast_nonneg _)
  have hf0 : ∀ g i y, 0 ≤ f g i y := by
    intro g i y
    simp only [f]
    split_ifs
    · exact div_nonneg (inv_nonneg.2 (hV0 g).le) (Nat.cast_nonneg _)
    · exact zero_le_one
  refine (sum_le_sum hterm).trans ?_
  refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p _ _ =>
    prod_nonneg fun g _ => prod_nonneg fun i _ => hf0 g i (p g i)).trans ?_
  have hpu := (prod_univ_sum (fun g => Fintype.piFinset fun i => if i ∈ S g then P g else {1})
    fun g (pg : Fin M → ℕ) => ∏ i, f g i (pg i)).symm
  beta_reduce at hpu
  rw [hpu]
  refine prod_le_one₀ (fun g _ => sum_nonneg fun pg _ =>
    prod_nonneg fun i _ => hf0 g i (pg i)) fun g _ => ?_
  have hpu' := (prod_univ_sum (fun i => if i ∈ S g then P g else {1})
    fun i (y : ℕ) => f g i y).symm
  rw [hpu']
  refine prod_le_one₀ (fun i _ => sum_nonneg fun y _ => hf0 g i y) fun i _ => ?_
  by_cases hi : i ∈ S g
  · simp only [f, ite_eq_left hi]
    rw [show ∑ y ∈ P g, (harmonicMass (P g))⁻¹ / (y : ℝ) =
        (harmonicMass (P g))⁻¹ * harmonicMass (P g) by
      rw [harmonicMass, mul_sum]
      exact sum_congr rfl fun y _ => by ring]
    exact inv_mul_le_one_of_le₀ le_rfl (hV0 g).le
  · simp only [f, ite_eq_right hi, sum_singleton, le_refl]

end Erdos408.TwoSided.DivModel
