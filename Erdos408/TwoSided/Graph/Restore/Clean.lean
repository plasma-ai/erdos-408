import Erdos408.TwoSided.Graph.Restore.Mass

/-!
# The clean summands

The consequence of G4 in `blueprint/two_sided_correlation.md` §4.3 (PD (6.14)). The stripped
correlation of a pattern `(C, K)` (`stripSum`) is a sum over the same indices as the cutoff
pairing after G4 (`stripSum_eq_sum`): auxiliary labels `a`, shared labels `s` (against their
mass, which is `1`), unshared parts `l, l'` and stripped positions `w`. When `(a, s, w)` is
*clean* (the shared labels are distinct and divide neither `w` nor `w + D_C`, and the free
labels avoid the shared labels and do not divide `w`), the two summands agree
(`physTerm_eq_stripTerm`):

* the physical conditions at `n = D_R w` are the represented-list conditions at `w` and
  `w + D_C` (`physCond_merge_iff`);
* `ω(D_R w) = ∑_g |Sh_g| + ω(w)` gives the damping, and the mass of the source lists splits as
  `∏ μ(s) · D_R · ∏ V^{-t}` (6.14);
* `F(D_R w) = F(w)`, `G(D_R w') = G(w')` and `Ψ(n / (x D)) / n = D_R⁻¹ Ψ(w / (x D_C)) / w`.
-/

namespace Erdos408.TwoSided

namespace Restore

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ}

/-! ### The stripped correlation -/

/-- `q₀^{ω(n) - ∑ t_g} ∏_g V_g^{-t_g}`, the prefactor of `markedListWeight` on the unshared
slots. -/
noncomputable def listDamping (P : ι → Finset ℕ) (q₀ : ℝ) (C : ι → Finset (Fin J)) (n : ℕ) :
    ℝ :=
  q₀ ^ ((groupPrimeCount P n : ℤ) - ∑ g, ((unsharedSlots C g).card : ℤ)) *
    ∏ g, (harmonicMass (P g))⁻¹ ^ (unsharedSlots C g).card

/-- The stripped correlation of a pattern `(C, K)`: free labels with law `∏ μ_g`, shift
`D_C`, and the kernel summed over the represented lists of both endpoints. -/
noncomputable def stripSum (x q₀ : ℝ) (P : ι → Finset ℕ) (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) : ℂ :=
  ∑ a ∈ auxLabels P C, (labelMass P C a : ℂ) *
    ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊,
      ((Ψ (w / (x * slotProduct C a)) / w * F w * G (w + slotProduct C a) *
          (listDamping P q₀ C w * listDamping P q₀ C (w + slotProduct C a)) : ℝ) : ℂ) *
        ∑ l ∈ slotLists P (unsharedSlots C) w,
          ∑ l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a), K l l' a

open Classical in
/-- A summand of the stripped correlation, against the mass of the shared labels `s`. -/
noncomputable def stripTerm (x q₀ : ℝ) (P : ι → Finset ℕ) (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) (a s : ι → Fin J → ℕ) (l l' : ι → Fin (J + 1) → ℕ) (w : ℕ) :
    ℂ :=
  ((labelMass P (sharedSlots C) s * labelMass P C a *
      (Ψ (w / (x * slotProduct C a)) / w * F w * G (w + slotProduct C a) *
        (listDamping P q₀ C w * listDamping P q₀ C (w + slotProduct C a))) : ℝ) : ℂ) *
    if l ∈ slotLists P (unsharedSlots C) w ∧
        l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a) then K l l' a else 0

/-- The represented lists of the unshared slots are unshared parts. -/
lemma slotLists_eq_filter (P : ι → Finset ℕ) (C : ι → Finset (Fin J)) (n : ℕ) :
    slotLists P (unsharedSlots C) n = (unsharedLists P C).filter fun l =>
      ∀ g, Set.InjOn (l g) (unsharedSlots C g) ∧ ∀ j ∈ unsharedSlots C g, l g j ∣ n :=
  rfl

/-- The represented lists are unshared parts. -/
lemma slotLists_subset (P : ι → Finset ℕ) (C : ι → Finset (Fin J)) (n : ℕ) :
    slotLists P (unsharedSlots C) n ⊆ unsharedLists P C :=
  filter_subset _ _

/-- The stripped correlation is a sum over the indices of G4, against the mass of the shared
labels. -/
lemma stripSum_eq_sum (x q₀ : ℝ) {P : ι → Finset ℕ} (hV : ∀ g, harmonicMass (P g) ≠ 0)
    (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) :
    stripSum x q₀ P C K F G Ψ =
      ∑ a ∈ auxLabels P C, ∑ s ∈ auxLabels P (sharedSlots C), ∑ l ∈ unsharedLists P C,
        ∑ l' ∈ unsharedLists P C, ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊,
          stripTerm x q₀ P C K F G Ψ a s l l' w := by
  unfold stripSum
  refine sum_congr rfl fun a _ => ?_
  set X : ℕ → ℝ := fun w => Ψ (w / (x * slotProduct C a)) / w * F w *
    G (w + slotProduct C a) *
    (listDamping P q₀ C w * listDamping P q₀ C (w + slotProduct C a))
  have hterm : ∀ s l l' w, stripTerm x q₀ P C K F G Ψ a s l l' w =
      (labelMass P (sharedSlots C) s : ℂ) * ((labelMass P C a : ℂ) * ((X w : ℝ) : ℂ) *
        if l ∈ slotLists P (unsharedSlots C) w ∧
          l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a) then K l l' a else 0) := by
    intro s l l' w
    rw [stripTerm]
    simp only [X, Complex.ofReal_mul]
    ring
  calc _ = ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊, (labelMass P C a : ℂ) * ((X w : ℝ) : ℂ) *
        ∑ l ∈ slotLists P (unsharedSlots C) w,
          ∑ l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a), K l l' a := by
        rw [mul_sum]
        exact sum_congr rfl fun w _ => by ring
    _ = ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊, ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C,
        (labelMass P C a : ℂ) * ((X w : ℝ) : ℂ) *
          if l ∈ slotLists P (unsharedSlots C) w ∧
            l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a) then K l l' a else 0 := by
        refine sum_congr rfl fun w _ => ?_
        simp_rw [← mul_sum]
        congr 1
        symm
        simp_rw [ite_and, sum_ite_irrel, sum_const_zero]
        rw [sum_ite_mem, inter_eq_right.2 (slotLists_subset P C _)]
        refine sum_congr rfl fun l _ => ?_
        rw [sum_ite_mem, inter_eq_right.2 (slotLists_subset P C _)]
    _ = ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C, ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊,
        (labelMass P C a : ℂ) * ((X w : ℝ) : ℂ) *
          if l ∈ slotLists P (unsharedSlots C) w ∧
            l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a) then K l l' a else 0 := by
        rw [sum_comm]
        exact sum_congr rfl fun l _ => sum_comm
    _ = ∑ s ∈ auxLabels P (sharedSlots C), (labelMass P (sharedSlots C) s : ℂ) *
        ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C, ∑ w ∈ Icc 1 ⌊x ^ 2⌋₊,
          (labelMass P C a : ℂ) * ((X w : ℝ) : ℂ) *
            if l ∈ slotLists P (unsharedSlots C) w ∧
              l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a) then K l l' a else 0 := by
        rw [← sum_mul, ← Complex.ofReal_sum, sum_labelMass hV, Complex.ofReal_one, one_mul]
    _ = _ := by
        simp_rw [mul_sum, hterm]

/-! ### Shared products -/

/-- A group prime divides the shared product exactly when it is a shared label of its
group. -/
lemma dvd_sharedProduct_iff {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C)) {g : ι} {p : ℕ}
    (hp : p ∈ P g) : p ∣ sharedProduct C s ↔ ∃ i ∈ sharedSlots C g, s g i = p := by
  have hpp := hprime g p hp
  constructor
  · intro h
    obtain ⟨g', -, hg'⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 h
    obtain ⟨i, hi, hi'⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hg'
    have hsi : s g' i ∈ P g' :=
      mem_of_mem_sharedLabels hs (by simpa [sharedSlots] using hi)
    have heq : p = s g' i :=
      (Nat.prime_dvd_prime_iff_eq hpp (hprime g' _ hsi)).1 hi'
    obtain rfl : g = g' := by
      by_contra hne
      exact disjoint_left.1 (hdisj g g' hne) hp (heq ▸ hsi)
    exact ⟨i, hi, heq.symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact (dvd_prod_of_mem _ hi).trans (dvd_prod_of_mem (fun g => ∏ i ∈ sharedSlots C g, s g i)
      (mem_univ g))

/-- The number of `P g`-primes of `D_R m`, when the shared labels are distinct and do not
divide `m`. -/
lemma primeCount_sharedProduct_mul {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    (hinj : ∀ g, Set.InjOn (s g) (sharedSlots C g)) {m : ℕ}
    (hm : ∀ g, ∀ i ∈ sharedSlots C g, ¬ s g i ∣ m) (g : ι) :
    primeCount (P g) (sharedProduct C s * m) = (sharedSlots C g).card + primeCount (P g) m := by
  unfold primeCount
  have hsplit : (P g).filter (· ∣ sharedProduct C s * m) =
      (sharedSlots C g).image (s g) ∪ (P g).filter (· ∣ m) := by
    ext p
    simp only [mem_filter, mem_union, mem_image]
    constructor
    · rintro ⟨hp, hdvd⟩
      rcases (Nat.Prime.dvd_mul (hprime g p hp)).1 hdvd with h | h
      · exact Or.inl ((dvd_sharedProduct_iff hprime hdisj hs hp).1 h)
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨hp, h⟩)
      · have hsi : s g i ∈ P g :=
          mem_of_mem_sharedLabels hs (by simpa [sharedSlots] using hi)
        exact ⟨hsi, ((dvd_sharedProduct_iff hprime hdisj hs hsi).2 ⟨i, hi, rfl⟩).mul_right m⟩
      · exact ⟨hp, h.mul_left _⟩
  rw [hsplit, card_union_of_disjoint, card_image_of_injOn (hinj g)]
  rw [disjoint_left]
  rintro p hp hp'
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hp
  exact hm g i hi (mem_filter.1 hp').2

/-- `ω(D_R m) = ∑_g |Sh_g| + ω(m)`, when the shared labels are distinct and do not divide
`m`. -/
lemma groupPrimeCount_sharedProduct_mul {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    (hinj : ∀ g, Set.InjOn (s g) (sharedSlots C g)) {m : ℕ}
    (hm : ∀ g, ∀ i ∈ sharedSlots C g, ¬ s g i ∣ m) :
    groupPrimeCount P (sharedProduct C s * m) =
      ∑ g, (sharedSlots C g).card + groupPrimeCount P m := by
  unfold groupPrimeCount
  rw [← sum_add_distrib]
  exact sum_congr rfl fun g _ => primeCount_sharedProduct_mul hprime hdisj hs hinj hm g

omit [Fintype ι] [DecidableEq ι] in
/-- `|Sh_g| + t_g = J + 1`. -/
lemma card_sharedSlots_add (C : ι → Finset (Fin J)) (g : ι) :
    (sharedSlots C g).card + (unsharedSlots C g).card = J + 1 := by
  have h₁ : (sharedSlots C g).card = J - (C g).card := by
    rw [sharedSlots, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have h₂ : (C g).card ≤ J := by
    simpa using card_le_univ (C g)
  rw [h₁, card_unsharedSlots]
  omega

omit [DecidableEq ι] in
/-- The edge product of a merged list is `D_R D_C`. -/
lemma edgeProduct_merge (C : ι → Finset (Fin J)) (s : ι → Fin J → ℕ)
    (l : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) :
    edgeProduct C (merge C s l) a = sharedProduct C s * slotProduct C a := by
  unfold edgeProduct sharedProduct slotProduct
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun g _ => ?_
  have h : ∀ i, (if i ∈ C g then a g i else merge C s l g i.castSucc) =
      if i ∈ C g then a g i else s g i := fun i => by
    by_cases hi : i ∈ C g
    · rw [ite_eq_left hi, ite_eq_left hi]
    · rw [ite_eq_right hi, ite_eq_right hi, merge_castSucc_of_notMem hi]
  simp_rw [h]
  rw [prod_ite, mul_comm]
  congr 1
  · refine prod_congr ?_ fun _ _ => rfl
    ext i
    simp [sharedSlots]
  · refine prod_congr ?_ fun _ _ => rfl
    ext i
    simp

/-! ### The physical conditions on merged lists -/

/-- A physical merged list at `D_R m` has its unshared part represented at `m`. -/
lemma unshared_of_physical {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C)) {l : ι → Fin (J + 1) → ℕ}
    (hl : l ∈ unsharedLists P C) {m : ℕ}
    (h : ∀ g, Function.Injective (merge C s l g) ∧ ∀ j, merge C s l g j ∣ sharedProduct C s * m)
    (g : ι) : Set.InjOn (l g) (unsharedSlots C g) ∧ ∀ j ∈ unsharedSlots C g, l g j ∣ m := by
  refine ⟨fun j₁ hj₁ j₂ hj₂ he => (h g).1 ?_, fun j hj => ?_⟩
  · rwa [merge_of_mem hj₁, merge_of_mem hj₂]
  · have hlj := mem_of_mem_unsharedLists hl hj
    have hdvd := (h g).2 j
    rw [merge_of_mem hj] at hdvd
    rcases (Nat.Prime.dvd_mul (hprime g _ hlj)).1 hdvd with h' | h'
    · obtain ⟨i, hi, hsi⟩ := (dvd_sharedProduct_iff hprime hdisj hs hlj).1 h'
      have hi' : i ∉ C g := by simpa [sharedSlots] using hi
      have := (h g).1 (a₁ := i.castSucc) (a₂ := j)
        (by rw [merge_castSucc_of_notMem hi', merge_of_mem hj, hsi])
      exact absurd (this ▸ hj) fun h'' => hi' (castSucc_mem_unsharedSlots.1 h'')
    · exact h'

omit [DecidableEq ι] in
/-- A merged list whose unshared part is represented at `m`, with distinct shared labels not
dividing `m`, is physical at `D_R m`. -/
lemma physical_of_unshared {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hinj : ∀ g, Set.InjOn (s g) (sharedSlots C g))
    {l : ι → Fin (J + 1) → ℕ} {m : ℕ} (hm : ∀ g, ∀ i ∈ sharedSlots C g, ¬ s g i ∣ m)
    (hl : ∀ g, Set.InjOn (l g) (unsharedSlots C g) ∧ ∀ j ∈ unsharedSlots C g, l g j ∣ m)
    (g : ι) :
    Function.Injective (merge C s l g) ∧ ∀ j, merge C s l g j ∣ sharedProduct C s * m := by
  have hsh : ∀ {i}, i ∉ C g → i ∈ sharedSlots C g := fun hi => by simpa [sharedSlots] using hi
  constructor
  · intro j₁ j₂ he
    by_cases hj₁ : j₁ ∈ unsharedSlots C g <;> by_cases hj₂ : j₂ ∈ unsharedSlots C g
    · rw [merge_of_mem hj₁, merge_of_mem hj₂] at he
      exact (hl g).1 hj₁ hj₂ he
    · obtain ⟨i, hi, rfl⟩ := exists_castSucc_of_notMem hj₂
      rw [merge_of_mem hj₁, merge_castSucc_of_notMem hi] at he
      exact absurd (he ▸ (hl g).2 j₁ hj₁) (hm g i (hsh hi))
    · obtain ⟨i, hi, rfl⟩ := exists_castSucc_of_notMem hj₁
      rw [merge_of_mem hj₂, merge_castSucc_of_notMem hi] at he
      exact absurd (he ▸ (hl g).2 j₂ hj₂) (hm g i (hsh hi))
    · obtain ⟨i₁, hi₁, rfl⟩ := exists_castSucc_of_notMem hj₁
      obtain ⟨i₂, hi₂, rfl⟩ := exists_castSucc_of_notMem hj₂
      rw [merge_castSucc_of_notMem hi₁, merge_castSucc_of_notMem hi₂] at he
      rw [hinj g (hsh hi₁) (hsh hi₂) he]
  · intro j
    by_cases hj : j ∈ unsharedSlots C g
    · rw [merge_of_mem hj]
      exact ((hl g).2 j hj).mul_left _
    · obtain ⟨i, hi, rfl⟩ := exists_castSucc_of_notMem hj
      rw [merge_castSucc_of_notMem hi]
      exact ((dvd_prod_of_mem _ (hsh hi)).trans
        (dvd_prod_of_mem (fun g => ∏ i ∈ sharedSlots C g, s g i) (mem_univ g))).mul_right m

/-- `(a, s, w)` is clean: the shared labels are distinct and divide neither `w` nor
`w + D_C`, and the free labels avoid the shared labels and do not divide `w`. -/
def Clean (C : ι → Finset (Fin J)) (a s : ι → Fin J → ℕ) (w : ℕ) : Prop :=
  (∀ g, Set.InjOn (s g) (sharedSlots C g)) ∧
    (∀ g, ∀ i ∈ sharedSlots C g, ¬ s g i ∣ w ∧ ¬ s g i ∣ w + slotProduct C a) ∧
    (∀ g, ∀ i ∈ C g, ∀ i' ∈ sharedSlots C g, a g i ≠ s g i') ∧
    ∀ g, ∀ i ∈ C g, ¬ a g i ∣ w

/-- **The physical conditions, clean case.** At a clean `(a, s, w)`, the conditions of the
cutoff pairing at `n = D_R w` are the represented-list conditions at `w` and `w + D_C`. -/
lemma physCond_merge_iff {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {C : ι → Finset (Fin J)}
    {a s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    {l l' : ι → Fin (J + 1) → ℕ} (hl : l ∈ unsharedLists P C) (hl' : l' ∈ unsharedLists P C)
    {w : ℕ} (hc : Clean C a s w) :
    PhysCond C (sharedProduct C s * w) (merge C s l) (merge C s l') a ↔
      l ∈ slotLists P (unsharedSlots C) w ∧
        l' ∈ slotLists P (unsharedSlots C) (w + slotProduct C a) := by
  obtain ⟨hinj, hsw, has, haw⟩ := hc
  have hE : sharedProduct C s * w + edgeProduct C (merge C s l) a =
      sharedProduct C s * (w + slotProduct C a) := by
    rw [edgeProduct_merge, mul_add]
  simp only [slotLists_eq_filter, mem_filter, PhysCond, hE]
  constructor
  · rintro ⟨h₁, h₂, -⟩
    exact ⟨⟨hl, unshared_of_physical hprime hdisj hs hl h₁⟩,
      ⟨hl', unshared_of_physical hprime hdisj hs hl' h₂⟩⟩
  · rintro ⟨⟨-, h₁⟩, ⟨-, h₂⟩⟩
    refine ⟨physical_of_unshared hinj (fun g i hi => (hsw g i hi).1) h₁,
      physical_of_unshared hinj (fun g i hi => (hsw g i hi).2) h₂, fun g => ⟨fun i hi => ?_,
      fun i hi j => ?_⟩⟩
    · rw [merge_castSucc_of_notMem hi, merge_castSucc_of_notMem hi]
    · have hsh : ∀ {i}, i ∉ C g → i ∈ sharedSlots C g := fun hi => by
        simpa [sharedSlots] using hi
      by_cases hj : j ∈ unsharedSlots C g
      · rw [merge_of_mem hj, merge_of_mem hj]
        refine ⟨fun he => haw g i hi (he ▸ (h₁ g).2 j hj), fun he => haw g i hi ?_⟩
        have hD : a g i ∣ slotProduct C a :=
          (dvd_prod_of_mem _ hi).trans (dvd_prod_of_mem (fun g => ∏ i ∈ C g, a g i)
            (mem_univ g))
        exact (Nat.dvd_add_right hD).1 (by rw [add_comm]; exact he ▸ (h₂ g).2 j hj)
      · obtain ⟨i', hi', rfl⟩ := exists_castSucc_of_notMem hj
        rw [merge_castSucc_of_notMem hi', merge_castSucc_of_notMem hi']
        exact ⟨has g i hi i' (hsh hi'), has g i hi i' (hsh hi')⟩

/-! ### The clean summands agree -/

/-- A represented list of the unshared slots at `m` forces `ω(m) ≥ ∑_g t_g`. -/
lemma sum_card_le_groupPrimeCount {P : ι → Finset ℕ} {C : ι → Finset (Fin J)}
    {l : ι → Fin (J + 1) → ℕ} {m : ℕ} (hl : l ∈ slotLists P (unsharedSlots C) m) :
    ∑ g, (unsharedSlots C g).card ≤ groupPrimeCount P m := by
  rw [slotLists_eq_filter, mem_filter] at hl
  refine sum_le_sum fun g _ => ?_
  refine card_le_card_of_injOn (l g) (fun j hj => ?_) (hl.2 g).1
  exact mem_filter.2 ⟨mem_of_mem_unsharedLists hl.1 hj, (hl.2 g).2 j hj⟩

/-- The damping at `D_R m` is the stripped damping at `m`, (6.14). -/
lemma pow_groupPrimeCount_sharedProduct_mul {P : ι → Finset ℕ}
    (hprime : ∀ g, ∀ p ∈ P g, p.Prime) (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h))
    {C : ι → Finset (Fin J)} {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    (hinj : ∀ g, Set.InjOn (s g) (sharedSlots C g)) {m : ℕ}
    (hm : ∀ g, ∀ i ∈ sharedSlots C g, ¬ s g i ∣ m)
    (ht : ∑ g, (unsharedSlots C g).card ≤ groupPrimeCount P m) (q₀ : ℝ) :
    q₀ ^ (groupPrimeCount P (sharedProduct C s * m) - (J + 1) * Fintype.card ι) =
      q₀ ^ ((groupPrimeCount P m : ℤ) - ∑ g, ((unsharedSlots C g).card : ℤ)) := by
  have hM : (J + 1) * Fintype.card ι =
      ∑ g, (sharedSlots C g).card + ∑ g, (unsharedSlots C g).card := by
    rw [← sum_add_distrib, sum_congr rfl fun g _ => card_sharedSlots_add C g, sum_const,
      card_univ, smul_eq_mul, mul_comm]
  rw [groupPrimeCount_sharedProduct_mul hprime hdisj hs hinj hm, hM,
    Nat.add_sub_add_left, ← zpow_natCast, Nat.cast_sub ht, Nat.cast_sum]

/-- The mass of the source lists, (6.14):
`∏ V^{-M} ∏ μ(a) ∏ V^{-t} = ∏ μ(s) D_R ∏ μ(a) ∏ V^{-2t}`. -/
lemma physWeight_eq {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    {C : ι → Finset (Fin J)} {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    (a : ι → Fin J → ℕ) :
    ∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) * (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) *
        (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) =
      labelMass P (sharedSlots C) s * sharedProduct C s * labelMass P C a *
        (∏ g, (harmonicMass (P g))⁻¹ ^ (unsharedSlots C g).card) ^ 2 := by
  have hs0 : ∀ g, ∏ i ∈ sharedSlots C g, (s g i : ℝ) ≠ 0 := fun g =>
    prod_ne_zero_iff.2 fun i hi => Nat.cast_ne_zero.2
      (hprime g _ (mem_of_mem_sharedLabels hs (by simpa [sharedSlots] using hi))).ne_zero
  have hμ : labelMass P (sharedSlots C) s * sharedProduct C s =
      ∏ g, (harmonicMass (P g))⁻¹ ^ (sharedSlots C g).card := by
    unfold labelMass sharedProduct
    rw [Nat.cast_prod, ← prod_mul_distrib]
    refine prod_congr rfl fun g _ => ?_
    simp_rw [mul_inv]
    rw [prod_mul_distrib, prod_const, Nat.cast_prod, mul_assoc, prod_inv_distrib,
      inv_mul_cancel₀ (hs0 g), mul_one]
  have hstep : ∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
        (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) *
        (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) =
      (∏ g, (harmonicMass (P g))⁻¹ ^ (sharedSlots C g).card) * labelMass P C a *
        (∏ g, (harmonicMass (P g))⁻¹ ^ (unsharedSlots C g).card) *
        ∏ g, (harmonicMass (P g))⁻¹ ^ (unsharedSlots C g).card := by
    unfold labelMass
    rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun g _ => ?_
    have h := card_sharedSlots_add C g
    rw [card_unsharedSlots] at h ⊢
    rw [show J + 1 = (sharedSlots C g).card + ((C g).card + 1) from h.symm, pow_add]
    ring
  rw [hstep, ← hμ]
  ring

/-- **The clean summands agree** (PD (6.14)). At a clean `(a, s, w)`, the summand of the
cutoff pairing after G4 is the summand of the stripped correlation, given the invariance of
`F, G, K` and that the support of `Ψ(w/(x D_C))` lies below `x²/D_R`. -/
lemma physTerm_eq_stripTerm {x q₀ : ℝ} {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h)) {C : ι → Finset (Fin J)}
    {K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ}
    {F G : ℕ → ℝ} {Ψ : ℝ → ℝ} {a s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C))
    {l l' : ι → Fin (J + 1) → ℕ} (hl : l ∈ unsharedLists P C) (hl' : l' ∈ unsharedLists P C)
    {w : ℕ} (hc : Clean C a s w) (hF : F (sharedProduct C s * w) = F w)
    (hG : G (sharedProduct C s * (w + slotProduct C a)) = G (w + slotProduct C a))
    (hK : K (merge C s l) (merge C s l') a = K l l' a)
    (hN : Ψ (w / (x * slotProduct C a)) ≠ 0 → sharedProduct C s * w ≤ ⌊x ^ 2⌋₊) :
    (if sharedProduct C s * w ≤ ⌊x ^ 2⌋₊ then
        physTerm x q₀ P C K F G Ψ (sharedProduct C s * w) (merge C s l) (merge C s l') a
      else 0) = stripTerm x q₀ P C K F G Ψ a s l l' w := by
  set DR := sharedProduct C s
  set DC := slotProduct C a
  have hDR : (DR : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (sharedProduct_pos hprime hs).ne'
  have hE : edgeProduct C (merge C s l) a = DR * DC := edgeProduct_merge C s l a
  have hΨ : Ψ (((DR * w : ℕ) : ℝ) / (x * ((DR * DC : ℕ) : ℝ))) = Ψ (w / (x * DC)) := by
    congr 1
    push_cast
    rw [show x * (DR * DC) = DR * (x * DC) by ring]
    exact mul_div_mul_left _ _ hDR
  by_cases hψ : Ψ (w / (x * DC)) = 0
  · have h₁ : stripTerm x q₀ P C K F G Ψ a s l l' w = 0 := by
      unfold stripTerm
      rw [hψ]
      simp
    rw [h₁]
    split_ifs with h
    · unfold physTerm physValue
      split_ifs
      · rw [hE, hΨ, hψ]
        simp
      · rfl
    · rfl
  rw [ite_eq_left (hN hψ)]
  unfold physTerm stripTerm
  have hiff := physCond_merge_iff hprime hdisj hs hl hl' hc
  by_cases hcond : PhysCond C (DR * w) (merge C s l) (merge C s l') a
  · obtain ⟨hSL, hSL'⟩ := hiff.1 hcond
    obtain ⟨hinj, hsw, -, -⟩ := hc
    rw [ite_eq_left hcond, ite_eq_left ⟨hSL, hSL'⟩]
    unfold physValue
    rw [hE, hK, show DR * w + DR * DC = DR * (w + DC) by ring, hG, hΨ, hF,
      pow_groupPrimeCount_sharedProduct_mul hprime hdisj hs hinj (fun g i hi => (hsw g i hi).1)
        (sum_card_le_groupPrimeCount hSL),
      pow_groupPrimeCount_sharedProduct_mul hprime hdisj hs hinj (fun g i hi => (hsw g i hi).2)
        (sum_card_le_groupPrimeCount hSL'), physWeight_eq hprime hs a]
    rw [mul_right_comm, ← Complex.ofReal_mul]
    congr 2
    unfold listDamping
    push_cast
    field_simp
    ring
  · rw [ite_eq_right hcond, ite_eq_right fun h => hcond (hiff.2 h), mul_zero]

end Restore

end Erdos408.TwoSided
