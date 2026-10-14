module

public import Erdos408.TwoSided.Setup

/-!
# The stripping bijection

Lemma G4 of `blueprint/two_sided_correlation.md` §4.3, for the cutoff pairing `Π^Ψ` of a
pattern with free slots `C g ⊆ Fin J` (PD §6.2, (6.14)–(6.15); WD §5.2). The encoding:

* the *shared* labels `s ∈ auxLabels P (sharedSlots C)`: a prime of `P g` in each shared slot
  `i ∉ C g` of the first `J`, and `1` in the free slots;
* the *unshared* part `l ∈ unsharedLists P C`: a prime of `P g` in each slot of
  `unsharedSlots C g` (the free slots, `castSucc`, and the final one), and `1` elsewhere;
* `merge C s l` is the list with `l` in the unshared slots and `s` in the shared ones; it is a
  bijection from shared labels and unshared parts onto all lists (`sum_allLists_eq`).

With `D_R = sharedProduct C s`, the cutoff pairing becomes a sum over the auxiliary labels
`a`, the shared labels `s`, the unshared parts `l, l'` of the source and the target, and the
stripped position `w = n / D_R` (`physSum_eq_sum_strip`); the target list shares `s`.
-/

@[expose] public section

namespace Erdos408.TwoSided

namespace Restore

open Finset

variable {ι : Type} {J : ℕ}

/-! ### Slots and lists -/

/-- The shared slots `{i : i ∉ C g}` of group `g` among the first `J`. -/
def sharedSlots (C : ι → Finset (Fin J)) (g : ι) : Finset (Fin J) :=
  univ \ C g

/-- A slot of the first `J` is unshared exactly when it is free. -/
lemma castSucc_mem_unsharedSlots {C : ι → Finset (Fin J)} {g : ι} {i : Fin J} :
    i.castSucc ∈ unsharedSlots C g ↔ i ∈ C g := by
  simp [unsharedSlots, Fin.castSucc_ne_last]

/-- The final slot is unshared. -/
lemma last_mem_unsharedSlots (C : ι → Finset (Fin J)) (g : ι) :
    Fin.last J ∈ unsharedSlots C g :=
  mem_insert_self _ _

/-- The list with unshared part `l` and shared labels `s`. -/
def merge (C : ι → Finset (Fin J)) (s : ι → Fin J → ℕ) (l : ι → Fin (J + 1) → ℕ) :
    ι → Fin (J + 1) → ℕ :=
  fun g j => if j ∈ unsharedSlots C g then l g j else (Fin.snoc (s g) 1 : Fin (J + 1) → ℕ) j

/-- The shared labels of a list, `1` in the free slots. -/
def shared (C : ι → Finset (Fin J)) (p : ι → Fin (J + 1) → ℕ) : ι → Fin J → ℕ :=
  fun g i => if i ∈ C g then 1 else p g i.castSucc

/-- The unshared part of a list, padded with `1`. -/
def pad (C : ι → Finset (Fin J)) (p : ι → Fin (J + 1) → ℕ) : ι → Fin (J + 1) → ℕ :=
  fun g j => if j ∈ unsharedSlots C g then p g j else 1

/-- A merged list carries its unshared part in the unshared slots. -/
lemma merge_of_mem {C : ι → Finset (Fin J)} {s : ι → Fin J → ℕ} {l : ι → Fin (J + 1) → ℕ}
    {g : ι} {j : Fin (J + 1)} (hj : j ∈ unsharedSlots C g) : merge C s l g j = l g j :=
  ite_eq_left hj

/-- A merged list carries its shared labels in the shared slots. -/
lemma merge_castSucc_of_notMem {C : ι → Finset (Fin J)} {s : ι → Fin J → ℕ}
    {l : ι → Fin (J + 1) → ℕ} {g : ι} {i : Fin J} (hi : i ∉ C g) :
    merge C s l g i.castSucc = s g i := by
  rw [merge, ite_eq_right (fun h => hi (castSucc_mem_unsharedSlots.1 h)), Fin.snoc_castSucc]

/-- A slot outside `unsharedSlots C g` is `i.castSucc` for a shared `i`. -/
lemma exists_castSucc_of_notMem {C : ι → Finset (Fin J)} {g : ι} {j : Fin (J + 1)}
    (hj : j ∉ unsharedSlots C g) : ∃ i, i ∉ C g ∧ j = i.castSucc := by
  induction j using Fin.lastCases with
  | last => exact absurd (last_mem_unsharedSlots C g) hj
  | cast i => exact ⟨i, fun h => hj (castSucc_mem_unsharedSlots.2 h), rfl⟩

/-- A list is the merge of its shared labels and its unshared part. -/
lemma merge_shared_pad (C : ι → Finset (Fin J)) (p : ι → Fin (J + 1) → ℕ) :
    merge C (shared C p) (pad C p) = p := by
  funext g j
  by_cases hj : j ∈ unsharedSlots C g
  · rw [merge_of_mem hj, pad, ite_eq_left hj]
  · obtain ⟨i, hi, rfl⟩ := exists_castSucc_of_notMem hj
    rw [merge_castSucc_of_notMem hi, shared, ite_eq_right hi]

variable [Fintype ι] [DecidableEq ι]

/-- All lists of primes of the groups in `M` slots. -/
noncomputable def allLists (P : ι → Finset ℕ) (M : ℕ) : Finset (ι → Fin M → ℕ) :=
  Fintype.piFinset fun g => Fintype.piFinset fun _ : Fin M => P g

/-- The unshared parts: a prime of `P g` in each unshared slot, `1` elsewhere. -/
noncomputable def unsharedLists (P : ι → Finset ℕ) (C : ι → Finset (Fin J)) :
    Finset (ι → Fin (J + 1) → ℕ) :=
  Fintype.piFinset fun g => Fintype.piFinset fun j =>
    if j ∈ unsharedSlots C g then P g else {1}

/-- The shared product `D_R = ∏_g ∏_{i ∉ C g} s_{g,i}`. -/
def sharedProduct (C : ι → Finset (Fin J)) (s : ι → Fin J → ℕ) : ℕ :=
  ∏ g, ∏ i ∈ sharedSlots C g, s g i

/-- Membership in `unsharedLists`, slot by slot. -/
lemma mem_unsharedLists {P : ι → Finset ℕ} {C : ι → Finset (Fin J)}
    {l : ι → Fin (J + 1) → ℕ} :
    l ∈ unsharedLists P C ↔ ∀ g j, l g j ∈ if j ∈ unsharedSlots C g then P g else {1} := by
  simp only [unsharedLists, Fintype.mem_piFinset]

/-- Membership in `allLists`, slot by slot. -/
lemma mem_allLists {P : ι → Finset ℕ} {M : ℕ} {p : ι → Fin M → ℕ} :
    p ∈ allLists P M ↔ ∀ g j, p g j ∈ P g := by
  simp only [allLists, Fintype.mem_piFinset]

/-- Shared labels are `1` in the free slots. -/
lemma eq_one_of_mem_sharedLabels {P : ι → Finset ℕ} {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C)) {g : ι} {i : Fin J}
    (hi : i ∈ C g) : s g i = 1 := by
  have := mem_auxLabels.1 hs g i
  rwa [ite_eq_right (by simp [sharedSlots, hi]), mem_singleton] at this

/-- Shared labels lie in `P g` in the shared slots. -/
lemma mem_of_mem_sharedLabels {P : ι → Finset ℕ} {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C)) {g : ι} {i : Fin J}
    (hi : i ∉ C g) : s g i ∈ P g := by
  have := mem_auxLabels.1 hs g i
  rwa [ite_eq_left (by simp [sharedSlots, hi])] at this

/-- Unshared parts are `1` in the shared slots. -/
lemma eq_one_of_mem_unsharedLists {P : ι → Finset ℕ} {C : ι → Finset (Fin J)}
    {l : ι → Fin (J + 1) → ℕ} (hl : l ∈ unsharedLists P C) {g : ι} {j : Fin (J + 1)}
    (hj : j ∉ unsharedSlots C g) : l g j = 1 := by
  have := mem_unsharedLists.1 hl g j
  rwa [ite_eq_right hj, mem_singleton] at this

/-- Unshared parts lie in `P g` in the unshared slots. -/
lemma mem_of_mem_unsharedLists {P : ι → Finset ℕ} {C : ι → Finset (Fin J)}
    {l : ι → Fin (J + 1) → ℕ} (hl : l ∈ unsharedLists P C) {g : ι} {j : Fin (J + 1)}
    (hj : j ∈ unsharedSlots C g) : l g j ∈ P g := by
  have := mem_unsharedLists.1 hl g j
  rwa [ite_eq_left hj] at this

/-- The unshared part of a merged list. -/
lemma pad_merge {P : ι → Finset ℕ} {C : ι → Finset (Fin J)} {s : ι → Fin J → ℕ}
    {l : ι → Fin (J + 1) → ℕ} (hl : l ∈ unsharedLists P C) : pad C (merge C s l) = l := by
  funext g j
  by_cases hj : j ∈ unsharedSlots C g
  · rw [pad, ite_eq_left hj, merge_of_mem hj]
  · rw [pad, ite_eq_right hj, eq_one_of_mem_unsharedLists hl hj]

/-- The shared labels of a merged list. -/
lemma shared_merge {P : ι → Finset ℕ} {C : ι → Finset (Fin J)} {s : ι → Fin J → ℕ}
    (hs : s ∈ auxLabels P (sharedSlots C)) (l : ι → Fin (J + 1) → ℕ) :
    shared C (merge C s l) = s := by
  funext g i
  by_cases hi : i ∈ C g
  · rw [shared, ite_eq_left hi, eq_one_of_mem_sharedLabels hs hi]
  · rw [shared, ite_eq_right hi, merge_castSucc_of_notMem hi]

/-- **G4, the lists.** Summing over all lists is summing over the shared labels and the
unshared parts. -/
lemma sum_allLists_eq {R : Type*} [AddCommMonoid R] (P : ι → Finset ℕ)
    (C : ι → Finset (Fin J)) (f : (ι → Fin (J + 1) → ℕ) → R) :
    ∑ p ∈ allLists P (J + 1), f p =
      ∑ s ∈ auxLabels P (sharedSlots C), ∑ l ∈ unsharedLists P C, f (merge C s l) := by
  rw [← sum_product (f := fun sl : (ι → Fin J → ℕ) × (ι → Fin (J + 1) → ℕ) =>
    f (merge C sl.1 sl.2))]
  refine sum_nbij' (fun p => (shared C p, pad C p)) (fun sl => merge C sl.1 sl.2) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_allLists] at hp
    refine (mem_product.2 ⟨mem_auxLabels.2 fun g i => ?_,
      mem_unsharedLists.2 fun g j => ?_⟩)
    · dsimp only
      by_cases hi : i ∈ C g
      · rw [ite_eq_right (by simp [sharedSlots, hi]), shared, ite_eq_left hi]
        exact mem_singleton_self 1
      · rw [ite_eq_left (by simp [sharedSlots, hi]), shared, ite_eq_right hi]
        exact hp g _
    · dsimp only
      by_cases hj : j ∈ unsharedSlots C g
      · rw [ite_eq_left hj, pad, ite_eq_left hj]
        exact hp g j
      · rw [ite_eq_right hj, pad, ite_eq_right hj]
        exact mem_singleton_self 1
  · rintro ⟨s, l⟩ hsl
    obtain ⟨hs, hl⟩ := mem_product.1 hsl
    refine mem_allLists.2 fun g j => ?_
    by_cases hj : j ∈ unsharedSlots C g
    · rw [merge_of_mem hj]
      exact mem_of_mem_unsharedLists hl hj
    · obtain ⟨i, hi, rfl⟩ := exists_castSucc_of_notMem hj
      rw [merge_castSucc_of_notMem hi]
      exact mem_of_mem_sharedLabels hs hi
  · intro p _
    exact merge_shared_pad C p
  · rintro ⟨s, l⟩ hsl
    obtain ⟨hs, hl⟩ := mem_product.1 hsl
    exact Prod.ext (shared_merge hs l) (pad_merge hl)
  · intro p _
    simp only [merge_shared_pad]

/-- The shared labels are determined by the shared slots of their merges. -/
lemma eq_of_merge_castSucc {P : ι → Finset ℕ} {C : ι → Finset (Fin J)}
    {s s' : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    (hs' : s' ∈ auxLabels P (sharedSlots C)) {l l' : ι → Fin (J + 1) → ℕ}
    (h : ∀ g, ∀ i, i ∉ C g → merge C s' l' g i.castSucc = merge C s l g i.castSucc) :
    s' = s := by
  funext g i
  by_cases hi : i ∈ C g
  · rw [eq_one_of_mem_sharedLabels hs hi, eq_one_of_mem_sharedLabels hs' hi]
  · have := h g i hi
    rwa [merge_castSucc_of_notMem hi, merge_castSucc_of_notMem hi] at this

/-- Shared labels of distinct primes in disjoint groups: their product divides every common
multiple. -/
lemma sharedProduct_dvd {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    (hinj : ∀ g, Set.InjOn (s g) (sharedSlots C g)) {n : ℕ}
    (hdvd : ∀ g, ∀ i ∈ sharedSlots C g, s g i ∣ n) : sharedProduct C s ∣ n := by
  have hmem : ∀ g, ∀ i ∈ sharedSlots C g, s g i ∈ P g := fun g i hi =>
    mem_of_mem_sharedLabels hs (by simpa [sharedSlots] using hi)
  have himg := prod_image (s := univ.sigma (sharedSlots C)) (g := fun x => s x.1 x.2)
    (f := fun q : ℕ => q)
  rw [sharedProduct, prod_sigma', ← himg]
  · refine prod_primes_dvd n (fun q hq => ?_) fun q hq => ?_
    · obtain ⟨⟨g, i⟩, hx, rfl⟩ := mem_image.1 hq
      exact (hprime g _ (hmem g i (mem_sigma.1 hx).2)).prime
    · obtain ⟨⟨g, i⟩, hx, rfl⟩ := mem_image.1 hq
      exact hdvd g i (mem_sigma.1 hx).2
  · rintro ⟨g, i⟩ hx ⟨g', i'⟩ hy heq
    have hx' := (mem_sigma.1 (mem_coe.1 hx)).2
    have hy' := (mem_sigma.1 (mem_coe.1 hy)).2
    simp only at heq
    obtain rfl : g = g' := by
      by_contra hne
      exact disjoint_left.1 (hdisj g g' hne) (hmem g i hx') (heq ▸ hmem g' i' hy')
    have : i = i' := hinj g hx' hy' heq
    rw [this]

/-- Shared labels have a positive product. -/
lemma sharedProduct_pos {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    {C : ι → Finset (Fin J)} {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C)) :
    0 < sharedProduct C s :=
  prod_pos fun g _ => prod_pos fun i hi =>
    (hprime g _ (mem_of_mem_sharedLabels hs (by simpa [sharedSlots] using hi))).pos

/-- Reindexing the positions `n ∈ [1, N]` that are multiples of `D` by `n = D w`. -/
lemma sum_Icc_eq_sum_mul {R : Type*} [AddCommMonoid R] {D N : ℕ} (hD : 0 < D) (f : ℕ → R)
    (hf : ∀ n, f n ≠ 0 → D ∣ n) :
    ∑ n ∈ Icc 1 N, f n = ∑ w ∈ Icc 1 N, if D * w ≤ N then f (D * w) else 0 := by
  symm
  rw [← sum_filter, ← sum_image fun w₁ _ w₂ _ h => Nat.eq_of_mul_eq_mul_left hD h]
  refine sum_subset (fun n hn => ?_) fun n hn hn' => ?_
  · obtain ⟨w, hw, rfl⟩ := mem_image.1 hn
    obtain ⟨hw, hwN⟩ := mem_filter.1 hw
    exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD.ne' (by
      have := (mem_Icc.1 hw).1; omega)), hwN⟩
  · by_contra h
    obtain ⟨w, rfl⟩ := hf _ h
    refine hn' (mem_image.2 ⟨w, mem_filter.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, (mem_Icc.1 hn).2⟩, rfl⟩)
    · have := (mem_Icc.1 hn).1
      rcases Nat.eq_zero_or_pos w with hw | hw
      · rw [hw, mul_zero] at this
        omega
      · exact hw
    · exact (Nat.le_mul_of_pos_left w hD).trans (mem_Icc.1 hn).2

/-! ### The cutoff pairing over all lists -/

/-- The value of a summand of the cutoff pairing at source `(n, p)`, target list `p'` and
auxiliary labels `a`. -/
noncomputable def physValue (x q₀ : ℝ) (P : ι → Finset ℕ) (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) (n : ℕ) (p p' : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) :
    ℂ :=
  ((∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
      (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) *
      (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) : ℝ) : ℂ) * K p p' a *
    ((Ψ (n / (x * edgeProduct C p a)) / n * F n * G (n + edgeProduct C p a) *
      q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
      q₀ ^ (groupPrimeCount P (n + edgeProduct C p a) - (J + 1) * Fintype.card ι) : ℝ) : ℂ)

/-- The cutoff pairing `Π^Ψ_C` (`cutoffPairing` of `Graph/Insertion.lean`), restated. -/
noncomputable def physSum (x q₀ : ℝ) (P : ι → Finset ℕ) (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x ^ 2⌋₊, ∑ p ∈ physicalLists P (J + 1) n, ∑ a ∈ auxLabels P C,
    ∑ p' ∈ (physicalLists P (J + 1) (n + edgeProduct C p a)).filter (fun p' =>
        ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
          ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j),
      physValue x q₀ P C K F G Ψ n p p' a

/-- The conditions on a summand of the cutoff pairing: physical source and target lists, the
target sharing the source labels outside `C`, and the ban. -/
def PhysCond (C : ι → Finset (Fin J)) (n : ℕ) (p p' : ι → Fin (J + 1) → ℕ)
    (a : ι → Fin J → ℕ) : Prop :=
  (∀ h, Function.Injective (p h) ∧ ∀ i, p h i ∣ n) ∧
    (∀ h, Function.Injective (p' h) ∧ ∀ i, p' h i ∣ n + edgeProduct C p a) ∧
    ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
      ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j

open Classical in
/-- A summand of the cutoff pairing over all lists, `0` off its support. -/
noncomputable def physTerm (x q₀ : ℝ) (P : ι → Finset ℕ) (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) (n : ℕ) (p p' : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) :
    ℂ :=
  if PhysCond C n p p' a then physValue x q₀ P C K F G Ψ n p p' a else 0

/-- The cutoff pairing sums `physTerm` over all lists. -/
lemma physSum_eq_sum_allLists (x q₀ : ℝ) (P : ι → Finset ℕ) (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) :
    physSum x q₀ P C K F G Ψ =
      ∑ n ∈ Icc 1 ⌊x ^ 2⌋₊, ∑ p ∈ allLists P (J + 1), ∑ a ∈ auxLabels P C,
        ∑ p' ∈ allLists P (J + 1), physTerm x q₀ P C K F G Ψ n p p' a := by
  unfold physSum physicalLists allLists
  refine sum_congr rfl fun n _ => ?_
  rw [sum_filter]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : ∀ h, Function.Injective (p h) ∧ ∀ i, p h i ∣ n
  · rw [ite_eq_left hp]
    refine sum_congr rfl fun a _ => ?_
    rw [filter_filter, sum_filter]
    refine sum_congr rfl fun p' _ => ?_
    unfold physTerm PhysCond
    by_cases hp' : (∀ h, Function.Injective (p' h) ∧ ∀ i, p' h i ∣ n + edgeProduct C p a) ∧
        ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
          ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j
    · rw [ite_eq_left hp', ite_eq_left ⟨hp, hp'⟩]
    · rw [ite_eq_right hp', ite_eq_right fun h => hp' h.2]
  · rw [ite_eq_right hp]
    exact (sum_eq_zero fun a _ => sum_eq_zero fun p' _ =>
      ite_eq_right fun h => hp h.1).symm

/-- **G4 (stripping bijection, exact).** The cutoff pairing is a sum over the auxiliary labels
`a`, the shared labels `s`, the unshared parts `l, l'` of source and target and the stripped
position `w`, at the source position `n = D_R w` and the lists `merge C s l`, `merge C s l'`. -/
theorem physSum_eq_sum_strip (x q₀ : ℝ) {P : ι → Finset ℕ}
    (hprime : ∀ g, ∀ p ∈ P g, p.Prime) (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h))
    (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) :
    physSum x q₀ P C K F G Ψ =
      ∑ a ∈ auxLabels P C, ∑ s ∈ auxLabels P (sharedSlots C), ∑ l ∈ unsharedLists P C,
        ∑ l' ∈ unsharedLists P C, ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊,
          if sharedProduct C s * w ≤ ⌊x ^ 2⌋₊ then
            physTerm x q₀ P C K F G Ψ (sharedProduct C s * w) (merge C s l) (merge C s l') a
          else 0 := by
  set T := physTerm x q₀ P C K F G Ψ
  rw [physSum_eq_sum_allLists, sum_comm]
  rw [sum_congr rfl fun p _ => sum_comm]
  rw [sum_congr rfl fun p _ => sum_congr rfl fun a _ => sum_comm]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_allLists_eq P C]
  refine sum_congr rfl fun s hs => sum_congr rfl fun l _ => ?_
  rw [sum_allLists_eq P C, sum_eq_single_of_mem s hs]
  · refine sum_congr rfl fun l' _ => ?_
    refine sum_Icc_eq_sum_mul (sharedProduct_pos hprime hs) _ fun n hn => ?_
    have hc : PhysCond C n (merge C s l) (merge C s l') a := by
      by_contra hc
      exact hn (ite_eq_right hc)
    refine sharedProduct_dvd hprime hdisj hs (fun g i hi j hj hij => ?_) fun g i hi => ?_
    · have hi' : i ∉ C g := by simpa [sharedSlots] using hi
      have hj' : j ∉ C g := by simpa [sharedSlots] using hj
      have := (hc.1 g).1 (a₁ := i.castSucc) (a₂ := j.castSucc)
        (by rw [merge_castSucc_of_notMem hi', merge_castSucc_of_notMem hj']; exact hij)
      exact Fin.castSucc_injective _ this
    · have hi' : i ∉ C g := by simpa [sharedSlots] using hi
      have := (hc.1 g).2 i.castSucc
      rwa [merge_castSucc_of_notMem hi'] at this
  · intro s' hs' hne
    refine sum_eq_zero fun l' _ => sum_eq_zero fun n _ => ite_eq_right fun hc => hne ?_
    exact eq_of_merge_castSucc hs hs' fun g i hi => (hc.2.2 g).1 i hi

end Restore

end Erdos408.TwoSided
