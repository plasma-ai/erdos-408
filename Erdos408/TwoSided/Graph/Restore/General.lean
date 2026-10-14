import Erdos408.TwoSided.Graph.Restore.Bound

/-!
# Restoring the suppressed restrictions

Lemma G5 of `blueprint/two_sided_correlation.md` §4.4 for a general pattern `(C, K)`, as an
explicit inequality (`norm_physSum_sub_stripSum_le`). After G4 both the cutoff pairing and the
stripped correlation are sums over `(a, s, l, l', w)`; at a clean `(a, s, w)` the summands
agree, and otherwise each is at most `μ(s) μ(a) B / w` after summing over `l, l'`. The unclean
mass (`sum_mass_not_clean_le`) is a union bound over the suppressed restrictions (PD §6.2,
after (6.16)):

1. two shared labels of a group coincide: `≤ s_P J² sup μ`;
2. a shared label divides `w (w + D_C)` or equals a free label: `≤ J (2Ω + m₀ s_P) sup μ`;
3. a free label divides `w` (the label ban): `≤ m₀ Ω sup μ`.

The physical injectivity across shared and unshared slots is implied once (2) is excluded.
-/

namespace Erdos408.TwoSided

namespace Restore

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ}

/-! ### Invariance under the shared product -/

/-- A function invariant under multiplication by the group primes is invariant under the shared
product. -/
lemma eq_of_invariant_sharedProduct {P : ι → Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ p ∈ univ.biUnion P, ∀ n, f (p * n) = f n) {C : ι → Finset (Fin J)}
    {s : ι → Fin J → ℕ} (hs : s ∈ auxLabels P (sharedSlots C)) (n : ℕ) :
    f (sharedProduct C s * n) = f n := by
  have key : ∀ D D' : ℕ, (∀ n, f (D * n) = f n) → (∀ n, f (D' * n) = f n) →
      ∀ n, f (D * D' * n) = f n := fun D D' hD hD' n => by rw [mul_assoc, hD, hD']
  refine prod_induction _ (fun D => ∀ n, f (D * n) = f n) key (fun n => by rw [one_mul])
    (fun g _ => ?_) n
  refine prod_induction _ (fun D => ∀ n, f (D * n) = f n) key (fun n => by rw [one_mul])
    (fun i hi => hf _ ?_)
  exact mem_biUnion.2 ⟨g, mem_univ g, mem_of_mem_sharedLabels hs (by
    simpa [sharedSlots] using hi)⟩

/-! ### Indicators -/

/-- `∑_{p ∈ P_g} μ_g(p) = 1`. -/
private lemma sum_inv_harmonicMass_mul {S : Finset ℕ} (hS : harmonicMass S ≠ 0) :
    ∑ p ∈ S, (harmonicMass S * p)⁻¹ = 1 := by
  simp_rw [mul_inv]
  rw [← mul_sum]
  have h : ∑ p ∈ S, (p : ℝ)⁻¹ = harmonicMass S := by simp [harmonicMass]
  rw [h, inv_mul_cancel₀ hS]

/-- The indicator of an existential is at most the sum of the indicators. -/
private lemma ite_exists_le_sum {α : Type*} (t : Finset α) (R : α → Prop) [DecidablePred R]
    {_ : Decidable (∃ i ∈ t, R i)} :
    (if ∃ i ∈ t, R i then (1 : ℝ) else 0) ≤ ∑ i ∈ t, if R i then 1 else 0 := by
  split_ifs with h
  · obtain ⟨i, hi, hR⟩ := h
    calc (1 : ℝ) = if R i then 1 else 0 := (ite_eq_left hR).symm
      _ ≤ ∑ i ∈ t, if R i then 1 else 0 :=
        single_le_sum (f := fun i => if R i then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) hi
  · exact sum_nonneg fun i _ => by split_ifs <;> norm_num

omit [Fintype ι] [DecidableEq ι] in
/-- The number of `P g`-primes satisfying `R`, weighted by `μ_g ≤ μ₀`. -/
lemma sum_filter_inv_le {P : ι → Finset ℕ} {μ₀ : ℝ}
    (hμ : ∀ g, ∀ p ∈ P g, (harmonicMass (P g) * p)⁻¹ ≤ μ₀) (g : ι) (R : ℕ → Prop)
    [DecidablePred R] :
    ∑ p ∈ (P g).filter R, (harmonicMass (P g) * p)⁻¹ ≤ μ₀ * ((P g).filter R).card := by
  rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum fun p hp => hμ g p (mem_filter.1 hp).1

/-- The mass of the labels with some slot satisfying `R`. -/
lemma sum_labelMass_mul_ite_exists_le {P : ι → Finset ℕ} (hV : ∀ g, 0 < harmonicMass (P g))
    (S : ι → Finset (Fin J)) (R : ι → Fin J → ℕ → Prop) [∀ g i, DecidablePred (R g i)] :
    ∑ x ∈ auxLabels P S, labelMass P S x *
        (if ∃ g ∈ univ, ∃ i ∈ S g, R g i (x g i) then 1 else 0) ≤
      ∑ g, ∑ i ∈ S g, ∑ p ∈ (P g).filter (R g i), (harmonicMass (P g) * p)⁻¹ := by
  have hV' : ∀ g, harmonicMass (P g) ≠ 0 := fun g => (hV g).ne'
  calc _ ≤ ∑ x ∈ auxLabels P S, labelMass P S x *
        ∑ g, ∑ i ∈ S g, (if R g i (x g i) then 1 else 0) := by
        refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (labelMass_nonneg P S x)
        refine (ite_exists_le_sum univ _).trans (sum_le_sum fun g _ => ?_)
        exact ite_exists_le_sum (S g) _
    _ = ∑ g, ∑ i ∈ S g, ∑ x ∈ auxLabels P S, labelMass P S x *
        (if R g i (x g i) then 1 else 0) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun g _ => sum_comm
    _ = _ := sum_congr rfl fun g _ => sum_congr rfl fun i hi =>
        sum_labelMass_mul_ite hV' S hi (R g i)

/-- The mass of the shared labels with two coinciding slots in a group. -/
lemma sum_labelMass_mul_ite_not_injOn_le {P : ι → Finset ℕ}
    (hV : ∀ g, 0 < harmonicMass (P g)) {μ₀ : ℝ} (hμ₀ : 0 ≤ μ₀)
    (hμ : ∀ g, ∀ p ∈ P g, (harmonicMass (P g) * p)⁻¹ ≤ μ₀) (S : ι → Finset (Fin J)) :
    ∑ x ∈ auxLabels P S, labelMass P S x *
        (if ∃ g ∈ univ, ∃ i ∈ S g, ∃ j ∈ S g, i ≠ j ∧ x g i = x g j then 1 else 0) ≤
      μ₀ * ∑ g, ((S g).card : ℝ) ^ 2 := by
  have hV' : ∀ g, harmonicMass (P g) ≠ 0 := fun g => (hV g).ne'
  have hsum1 : ∀ g, ∑ p ∈ P g, (harmonicMass (P g) * p)⁻¹ = 1 := fun g =>
    sum_inv_harmonicMass_mul (hV' g)
  calc _ ≤ ∑ x ∈ auxLabels P S, labelMass P S x *
        ∑ g, ∑ i ∈ S g, ∑ j ∈ S g, (if i ≠ j ∧ x g i = x g j then 1 else 0) := by
        refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (labelMass_nonneg P S x)
        refine (ite_exists_le_sum univ _).trans (sum_le_sum fun g _ => ?_)
        refine (ite_exists_le_sum (S g) _).trans (sum_le_sum fun i _ => ?_)
        exact ite_exists_le_sum (S g) _
    _ = ∑ g, ∑ i ∈ S g, ∑ j ∈ S g, ∑ x ∈ auxLabels P S, labelMass P S x *
        (if i ≠ j ∧ x g i = x g j then 1 else 0) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun g _ => ?_
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ ≤ ∑ g, ∑ i ∈ S g, ∑ j ∈ S g, μ₀ := by
        refine sum_le_sum fun g _ => sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
        by_cases hij : i = j
        · simp only [hij, ne_eq, not_true_eq_false, false_and, ite_false, mul_zero,
            sum_const_zero]
          exact hμ₀
        · simp only [ne_eq, hij, not_false_eq_true, true_and]
          rw [sum_labelMass_mul_ite_eq hV' S hi hj hij]
          calc ∑ p ∈ P g, (harmonicMass (P g) * p)⁻¹ ^ 2
              ≤ ∑ p ∈ P g, μ₀ * (harmonicMass (P g) * p)⁻¹ := sum_le_sum fun p hp => by
                rw [sq]
                exact mul_le_mul_of_nonneg_right (hμ g p hp)
                  (inv_nonneg.2 (mul_nonneg (hV g).le (Nat.cast_nonneg _)))
            _ = μ₀ := by rw [← mul_sum, hsum1, mul_one]
    _ = μ₀ * ∑ g, ((S g).card : ℝ) ^ 2 := by
        simp only [sum_const, nsmul_eq_mul, mul_sum]
        exact sum_congr rfl fun g _ => by ring

/-- Indicators of equivalent propositions agree, whatever their decision procedures. -/
private lemma ite_one_zero_congr {p q : Prop} {_ : Decidable p} {_ : Decidable q} (h : p ↔ q) :
    (if p then (1 : ℝ) else 0) = if q then 1 else 0 := by
  split_ifs <;> tauto

/-- The number of `P g`-primes dividing `w` or `w'`, or among the free labels of `g`. -/
private lemma card_filter_or_le (S : Finset ℕ) (w w' : ℕ) (T : Finset ℕ) :
    ((S.filter fun v => v ∣ w ∨ v ∣ w' ∨ v ∈ T).card : ℝ) ≤
      primeCount S w + primeCount S w' + T.card := by
  unfold primeCount
  rw [filter_or, filter_or]
  have h₁ := card_union_le (S.filter (· ∣ w)) (S.filter (· ∣ w') ∪ S.filter (· ∈ T))
  have h₂ := card_union_le (S.filter (· ∣ w')) (S.filter (· ∈ T))
  have h₃ : (S.filter (· ∈ T)).card ≤ T.card := card_le_card fun v hv => (mem_filter.1 hv).2
  have : ((S.filter (· ∣ w) ∪ (S.filter (· ∣ w') ∪ S.filter (· ∈ T))).card : ℕ) ≤
      (S.filter (· ∣ w)).card + (S.filter (· ∣ w')).card + T.card := by omega
  exact_mod_cast this

open Classical in
/-- **The unclean mass.** Summed against the masses of the free and the shared labels, the
indicator of an unclean `(a, s, w)` is at most `μ₀ (s_P J² + J (2Ω + m₀ s_P) + m₀ Ω)`. -/
lemma sum_mass_not_clean_le {P : ι → Finset ℕ} (hV : ∀ g, 0 < harmonicMass (P g))
    {C : ι → Finset (Fin J)} {m₀ : ℕ} (hC : ∀ g, (C g).card ≤ m₀) {μ₀ Ω : ℝ}
    (hμ₀ : 0 ≤ μ₀) (hμ : ∀ g, ∀ p ∈ P g, (harmonicMass (P g) * p)⁻¹ ≤ μ₀) {w : ℕ}
    (hΩ₁ : (groupPrimeCount P w : ℝ) ≤ Ω)
    (hΩ₂ : ∀ a ∈ auxLabels P C, (groupPrimeCount P (w + slotProduct C a) : ℝ) ≤ Ω) :
    ∑ a ∈ auxLabels P C, labelMass P C a * ∑ s ∈ auxLabels P (sharedSlots C),
        labelMass P (sharedSlots C) s * (if Clean C a s w then 0 else 1) ≤
      μ₀ * (Fintype.card ι * J ^ 2 + J * (2 * Ω + m₀ * Fintype.card ι) + m₀ * Ω) := by
  have hV' : ∀ g, harmonicMass (P g) ≠ 0 := fun g => (hV g).ne'
  set A : (ι → Fin J → ℕ) → Prop := fun s =>
    ∃ g ∈ univ, ∃ i ∈ sharedSlots C g, ∃ j ∈ sharedSlots C g, i ≠ j ∧ s g i = s g j
  set R : (ι → Fin J → ℕ) → ι → Fin J → ℕ → Prop := fun a g _ v =>
    v ∣ w ∨ v ∣ w + slotProduct C a ∨ v ∈ (C g).image (a g)
  set D : (ι → Fin J → ℕ) → Prop := fun a => ∃ g ∈ univ, ∃ i ∈ C g, a g i ∣ w
  have hind : ∀ a s, (if Clean C a s w then (0 : ℝ) else 1) ≤
      (if A s then 1 else 0) +
        (if ∃ g ∈ univ, ∃ i ∈ sharedSlots C g, R a g i (s g i) then 1 else 0) +
        (if D a then 1 else 0) := by
    intro a s
    have h₀ : ∀ q : Prop, ∀ _ : Decidable q, (0 : ℝ) ≤ if q then 1 else 0 := fun q _ => by
      split_ifs <;> norm_num
    by_cases hc : Clean C a s w
    · rw [ite_eq_left hc]
      exact add_nonneg (add_nonneg (h₀ _ _) (h₀ _ _)) (h₀ _ _)
    · rw [ite_eq_right hc]
      have : A s ∨ (∃ g ∈ univ, ∃ i ∈ sharedSlots C g, R a g i (s g i)) ∨ D a := by
        by_contra h
        refine hc ⟨fun g i hi j hj he => ?_, fun g i hi => ⟨fun hd => ?_, fun hd => ?_⟩,
          fun g i hi i' hi' he => ?_, fun g i hi hd => ?_⟩
        · by_contra hne
          exact h (Or.inl ⟨g, mem_univ g, i, hi, j, hj, hne, he⟩)
        · exact h (Or.inr (Or.inl ⟨g, mem_univ g, i, hi, Or.inl hd⟩))
        · exact h (Or.inr (Or.inl ⟨g, mem_univ g, i, hi, Or.inr (Or.inl hd)⟩))
        · exact h (Or.inr (Or.inl ⟨g, mem_univ g, i', hi',
            Or.inr (Or.inr (mem_image.2 ⟨i, hi, he⟩))⟩))
        · exact h (Or.inr (Or.inr ⟨g, mem_univ g, i, hi, hd⟩))
      rcases this with h | h | h
      · rw [ite_eq_left h]
        linarith [h₀ (∃ g ∈ univ, ∃ i ∈ sharedSlots C g, R a g i (s g i)) inferInstance,
          h₀ (D a) inferInstance]
      · rw [ite_eq_left h]
        linarith [h₀ (A s) inferInstance, h₀ (D a) inferInstance]
      · rw [ite_eq_left h]
        linarith [h₀ (A s) inferInstance,
          h₀ (∃ g ∈ univ, ∃ i ∈ sharedSlots C g, R a g i (s g i)) inferInstance]
  -- the three masses
  have hA : ∑ s ∈ auxLabels P (sharedSlots C), labelMass P (sharedSlots C) s *
      (if A s then 1 else 0) ≤ μ₀ * (Fintype.card ι * J ^ 2) := by
    refine le_trans (le_of_eq (sum_congr rfl fun s _ => by
      congr 1; exact ite_one_zero_congr Iff.rfl))
      ((sum_labelMass_mul_ite_not_injOn_le hV hμ₀ hμ (sharedSlots C)).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hμ₀
    rw [← nsmul_eq_mul, ← card_univ, ← sum_const]
    refine sum_le_sum fun g _ => ?_
    have : (sharedSlots C g).card ≤ J := by simpa using card_le_univ (sharedSlots C g)
    have : ((sharedSlots C g).card : ℝ) ≤ J := by exact_mod_cast this
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hBC : ∀ a ∈ auxLabels P C, ∑ s ∈ auxLabels P (sharedSlots C),
      labelMass P (sharedSlots C) s *
        (if ∃ g ∈ univ, ∃ i ∈ sharedSlots C g, R a g i (s g i) then 1 else 0) ≤
      μ₀ * (J * (2 * Ω + m₀ * Fintype.card ι)) := by
    intro a ha
    refine le_trans (le_of_eq (sum_congr rfl fun s _ => by congr 1))
      ((sum_labelMass_mul_ite_exists_le hV (sharedSlots C) (R a)).trans ?_)
    calc _ ≤ ∑ g, ∑ i ∈ sharedSlots C g, μ₀ * (primeCount (P g) w +
          primeCount (P g) (w + slotProduct C a) + (C g).card) := by
          refine sum_le_sum fun g _ => sum_le_sum fun i _ => ?_
          refine (sum_filter_inv_le hμ g _).trans (mul_le_mul_of_nonneg_left ?_ hμ₀)
          exact (card_filter_or_le _ _ _ _).trans (by gcongr; exact_mod_cast card_image_le)
      _ ≤ ∑ g, (J : ℝ) * (μ₀ * (primeCount (P g) w +
          primeCount (P g) (w + slotProduct C a) + (C g).card)) := by
          refine sum_le_sum fun g _ => ?_
          rw [sum_const, nsmul_eq_mul]
          have : (sharedSlots C g).card ≤ J := by simpa using card_le_univ (sharedSlots C g)
          have : ((sharedSlots C g).card : ℝ) ≤ J := by exact_mod_cast this
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = μ₀ * (J * (groupPrimeCount P w + groupPrimeCount P (w + slotProduct C a) +
          ∑ g, ((C g).card : ℝ))) := by
          unfold groupPrimeCount
          push_cast
          rw [← sum_add_distrib, ← sum_add_distrib, mul_sum, mul_sum]
          exact sum_congr rfl fun g _ => by ring
      _ ≤ μ₀ * (J * (2 * Ω + m₀ * Fintype.card ι)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
            hμ₀
          have hCs : ∑ g, ((C g).card : ℝ) ≤ m₀ * Fintype.card ι := by
            rw [mul_comm, ← nsmul_eq_mul, ← card_univ, ← sum_const]
            exact sum_le_sum fun g _ => by exact_mod_cast hC g
          linarith [hΩ₂ a ha]
  have hD : ∑ a ∈ auxLabels P C, labelMass P C a * (if D a then 1 else 0) ≤
      μ₀ * (m₀ * Ω) := by
    refine le_trans (le_of_eq (sum_congr rfl fun a _ => by
      congr 1; exact ite_one_zero_congr Iff.rfl))
      ((sum_labelMass_mul_ite_exists_le hV C fun _ _ v => v ∣ w).trans ?_)
    calc _ ≤ ∑ g, ∑ i ∈ C g, μ₀ * (primeCount (P g) w : ℝ) :=
          sum_le_sum fun g _ => sum_le_sum fun i _ => sum_filter_inv_le hμ g _
      _ ≤ ∑ g, (m₀ : ℝ) * (μ₀ * primeCount (P g) w) := by
          refine sum_le_sum fun g _ => ?_
          rw [sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC g) (by positivity)
      _ = μ₀ * (m₀ * groupPrimeCount P w) := by
          unfold groupPrimeCount
          push_cast
          rw [mul_sum, mul_sum]
          exact sum_congr rfl fun g _ => by ring
      _ ≤ μ₀ * (m₀ * Ω) := by gcongr
  have hμa := sum_labelMass hV' C
  have hμs := sum_labelMass hV' (sharedSlots C)
  calc _ ≤ ∑ a ∈ auxLabels P C, labelMass P C a *
        (μ₀ * (Fintype.card ι * J ^ 2) + μ₀ * (J * (2 * Ω + m₀ * Fintype.card ι)) +
          (if D a then 1 else 0)) := by
        refine sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ (labelMass_nonneg P C a)
        calc _ ≤ ∑ s ∈ auxLabels P (sharedSlots C), labelMass P (sharedSlots C) s *
              ((if A s then 1 else 0) +
                (if ∃ g ∈ univ, ∃ i ∈ sharedSlots C g, R a g i (s g i) then 1 else 0) +
                (if D a then 1 else 0)) :=
              sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hind a s)
                (labelMass_nonneg P (sharedSlots C) s)
          _ = ∑ s ∈ auxLabels P (sharedSlots C), labelMass P (sharedSlots C) s *
                (if A s then 1 else 0) +
              ∑ s ∈ auxLabels P (sharedSlots C), labelMass P (sharedSlots C) s *
                (if ∃ g ∈ univ, ∃ i ∈ sharedSlots C g, R a g i (s g i) then 1 else 0) +
              (∑ s ∈ auxLabels P (sharedSlots C), labelMass P (sharedSlots C) s) *
                (if D a then 1 else 0) := by
              rw [sum_mul, ← sum_add_distrib, ← sum_add_distrib]
              exact sum_congr rfl fun s _ => by ring
          _ ≤ _ := by
              rw [hμs, one_mul]
              exact add_le_add (add_le_add hA (hBC a ha)) le_rfl
    _ = μ₀ * (Fintype.card ι * J ^ 2) + μ₀ * (J * (2 * Ω + m₀ * Fintype.card ι)) +
        ∑ a ∈ auxLabels P C, labelMass P C a * (if D a then 1 else 0) := by
        rw [show ∑ a ∈ auxLabels P C, labelMass P C a *
            (μ₀ * (Fintype.card ι * J ^ 2) + μ₀ * (J * (2 * Ω + m₀ * Fintype.card ι)) +
              (if D a then 1 else 0)) =
            (∑ a ∈ auxLabels P C, labelMass P C a) * (μ₀ * (Fintype.card ι * J ^ 2)) +
            (∑ a ∈ auxLabels P C, labelMass P C a) * (μ₀ * (J * (2 * Ω + m₀ * Fintype.card ι))) +
            ∑ a ∈ auxLabels P C, labelMass P C a * (if D a then 1 else 0) by
          rw [sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
          exact sum_congr rfl fun a _ => by ring, hμa]
        ring
    _ ≤ μ₀ * (Fintype.card ι * J ^ 2) + μ₀ * (J * (2 * Ω + m₀ * Fintype.card ι)) +
        μ₀ * (m₀ * Ω) := add_le_add le_rfl hD
    _ = _ := by ring

/-! ### The summands at `(a, s, w)` -/

/-- The physical summands at `(a, s, w)`, summed over the unshared parts. -/
lemma sum_norm_physTerm_le {x q₀ : ℝ} {P : ι → Finset ℕ} (hprime : ∀ g, ∀ p ∈ P g, p.Prime)
    (hV : ∀ g, 0 < harmonicMass (P g)) (hq₀ : 0 < q₀) (hq₀₁ : q₀ ≤ 1)
    {C : ι → Finset (Fin J)}
    {K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ} {κK : ℝ}
    (hK : ∀ p p' a, ‖K p p' a‖ ≤ κK) {F G : ℕ → ℝ} {Ψ : ℝ → ℝ} {M₀ LF LG Λ₀ : ℝ}
    (hΨ : ∀ y, |Ψ y| ≤ M₀) (hLF : 0 ≤ LF) (hF : ∀ n, 1 ≤ n → n ≤ ⌊x ^ 2⌋₊ → |F n| ≤ LF)
    (hG : ∀ n, |G n| ≤ LG) (hΛ : ∀ n, listWeight P q₀ C n ≤ Λ₀) {a s : ι → Fin J → ℕ}
    (hs : s ∈ auxLabels P (sharedSlots C)) {w : ℕ} (hw : 1 ≤ w) :
    ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C,
        ‖if sharedProduct C s * w ≤ ⌊x ^ 2⌋₊ then
          physTerm x q₀ P C K F G Ψ (sharedProduct C s * w) (merge C s l) (merge C s l') a
        else 0‖ ≤
      labelMass P (sharedSlots C) s * labelMass P C a *
        (targetMass P C ^ 2 * κK * M₀ * LF * LG * Λ₀ ^ 2) / w := by
  have hκ : 0 ≤ κK := (norm_nonneg _).trans (hK (fun _ _ => 0) (fun _ _ => 0) fun _ _ => 0)
  have hM : 0 ≤ M₀ := (abs_nonneg _).trans (hΨ 0)
  have hLG : 0 ≤ LG := (abs_nonneg _).trans (hG 0)
  have hμs := labelMass_nonneg P (sharedSlots C) s
  have hμa := labelMass_nonneg P C a
  have hT := targetMass_nonneg hV C
  set c := labelMass P (sharedSlots C) s * labelMass P C a * targetMass P C ^ 2 * κK * M₀ *
    LF * LG / w
  have hc : 0 ≤ c := by positivity
  set DR := sharedProduct C s
  set DC := slotProduct C a
  have hW₁ := listWeight_nonneg P hq₀ C (DR * w)
  have hW₂ := listWeight_nonneg P hq₀ C (DR * (w + DC))
  calc _ ≤ ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C,
        (if ∀ g, ∀ j ∈ unsharedSlots C g, l g j ∣ DR * w then (1 : ℝ) else 0) *
          (if ∀ g, ∀ j ∈ unsharedSlots C g, l' g j ∣ DR * (w + DC) then 1 else 0) *
          (c * q₀ ^ ((groupPrimeCount P (DR * w) : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
            q₀ ^ ((groupPrimeCount P (DR * (w + DC)) : ℤ) -
              ((J + 1) * Fintype.card ι : ℕ))) :=
        sum_le_sum fun l _ => sum_le_sum fun l' _ =>
          norm_physTerm_le hprime hV hq₀ hq₀₁ hK hΨ hLF hF hG hs hw l l'
    _ = (∑ l ∈ unsharedLists P C,
          (if ∀ g, ∀ j ∈ unsharedSlots C g, l g j ∣ DR * w then (1 : ℝ) else 0)) *
        (∑ l' ∈ unsharedLists P C,
          (if ∀ g, ∀ j ∈ unsharedSlots C g, l' g j ∣ DR * (w + DC) then (1 : ℝ) else 0)) *
        (c * q₀ ^ ((groupPrimeCount P (DR * w) : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
          q₀ ^ ((groupPrimeCount P (DR * (w + DC)) : ℤ) -
            ((J + 1) * Fintype.card ι : ℕ))) := by
        rw [sum_mul_sum, sum_mul]
        exact sum_congr rfl fun l _ => by rw [sum_mul]
    _ = c * (listWeight P q₀ C (DR * w) * listWeight P q₀ C (DR * (w + DC))) := by
        rw [sum_boole, sum_boole]
        unfold listWeight listCount
        ring
    _ ≤ c * (Λ₀ * Λ₀) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hΛ _) (hΛ _) hW₂ (hW₁.trans (hΛ _))) hc
    _ = _ := by
        simp only [c]
        ring

/-- The stripped summands at `(a, s, w)`, summed over the unshared parts. -/
lemma sum_norm_stripTerm_le {x q₀ : ℝ} {P : ι → Finset ℕ} (hV : ∀ g, 0 < harmonicMass (P g))
    (hq₀ : 0 < q₀) (hq₀₁ : q₀ ≤ 1) {C : ι → Finset (Fin J)}
    {K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ} {κK : ℝ}
    (hK : ∀ p p' a, ‖K p p' a‖ ≤ κK) {F G : ℕ → ℝ} {Ψ : ℝ → ℝ} {M₀ LF LG Λ₀ : ℝ}
    (hΨ : ∀ y, |Ψ y| ≤ M₀) (hLF : 0 ≤ LF) (hF : ∀ n, 1 ≤ n → n ≤ ⌊x ^ 2⌋₊ → |F n| ≤ LF)
    (hG : ∀ n, |G n| ≤ LG) (hΛ : ∀ n, listWeight P q₀ C n ≤ Λ₀) (a s : ι → Fin J → ℕ)
    {w : ℕ} (hw : w ∈ Icc 1 ⌊x ^ 2⌋₊) :
    ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C,
        ‖stripTerm x q₀ P C K F G Ψ a s l l' w‖ ≤
      labelMass P (sharedSlots C) s * labelMass P C a *
        (targetMass P C ^ 2 * κK * M₀ * LF * LG * Λ₀ ^ 2) / w := by
  have hκ : 0 ≤ κK := (norm_nonneg _).trans (hK (fun _ _ => 0) (fun _ _ => 0) fun _ _ => 0)
  have hM : 0 ≤ M₀ := (abs_nonneg _).trans (hΨ 0)
  have hLG : 0 ≤ LG := (abs_nonneg _).trans (hG 0)
  have hμs := labelMass_nonneg P (sharedSlots C) s
  have hμa := labelMass_nonneg P C a
  have hT := targetMass_nonneg hV C
  set c := labelMass P (sharedSlots C) s * labelMass P C a * targetMass P C ^ 2 * κK * M₀ *
    LF * LG / w
  have hc : 0 ≤ c := by positivity
  set DC := slotProduct C a
  have hq₁ := zpow_nonneg hq₀.le ((groupPrimeCount P w : ℤ) - ((J + 1) * Fintype.card ι : ℕ))
  have hq₂ := zpow_nonneg hq₀.le
    ((groupPrimeCount P (w + DC) : ℤ) - ((J + 1) * Fintype.card ι : ℕ))
  have hcount : ∀ n, ((slotLists P (unsharedSlots C) n).card : ℝ) ≤ listCount P C n := by
    intro n
    unfold listCount
    refine Nat.cast_le.2 (card_le_card fun l hl => ?_)
    rw [slotLists_eq_filter, mem_filter] at hl
    exact mem_filter.2 ⟨hl.1, fun g => (hl.2 g).2⟩
  have hW₁ := listWeight_nonneg P hq₀ C w
  have hW₂ := listWeight_nonneg P hq₀ C (w + DC)
  calc _ ≤ ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C,
        (if l ∈ slotLists P (unsharedSlots C) w then (1 : ℝ) else 0) *
          (if l' ∈ slotLists P (unsharedSlots C) (w + DC) then 1 else 0) *
          (c * q₀ ^ ((groupPrimeCount P w : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
            q₀ ^ ((groupPrimeCount P (w + DC) : ℤ) - ((J + 1) * Fintype.card ι : ℕ))) :=
        sum_le_sum fun l _ => sum_le_sum fun l' _ =>
          norm_stripTerm_le hV hq₀ hq₀₁ hK hΨ hLF hF hG a s hw l l'
    _ = c * ((q₀ ^ ((groupPrimeCount P w : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
          (slotLists P (unsharedSlots C) w).card) *
        (q₀ ^ ((groupPrimeCount P (w + DC) : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
          (slotLists P (unsharedSlots C) (w + DC)).card)) := by
        rw [show ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C,
            (if l ∈ slotLists P (unsharedSlots C) w then (1 : ℝ) else 0) *
              (if l' ∈ slotLists P (unsharedSlots C) (w + DC) then 1 else 0) *
              (c * q₀ ^ ((groupPrimeCount P w : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
                q₀ ^ ((groupPrimeCount P (w + DC) : ℤ) - ((J + 1) * Fintype.card ι : ℕ))) =
            (∑ l ∈ unsharedLists P C,
              (if l ∈ slotLists P (unsharedSlots C) w then (1 : ℝ) else 0)) *
            (∑ l' ∈ unsharedLists P C,
              (if l' ∈ slotLists P (unsharedSlots C) (w + DC) then (1 : ℝ) else 0)) *
            (c * q₀ ^ ((groupPrimeCount P w : ℤ) - ((J + 1) * Fintype.card ι : ℕ)) *
              q₀ ^ ((groupPrimeCount P (w + DC) : ℤ) - ((J + 1) * Fintype.card ι : ℕ))) by
          rw [sum_mul_sum, sum_mul]
          exact sum_congr rfl fun l _ => by rw [sum_mul]]
        rw [sum_ite_mem, sum_ite_mem, inter_eq_right.2 (slotLists_subset P C _),
          inter_eq_right.2 (slotLists_subset P C _), sum_const, sum_const, nsmul_one,
          nsmul_one]
        ring
    _ ≤ c * (listWeight P q₀ C w * listWeight P q₀ C (w + DC)) := by
        unfold listWeight
        gcongr
        · exact Nat.cast_le.1 (hcount _)
        · exact Nat.cast_le.1 (hcount _)
    _ ≤ c * (Λ₀ * Λ₀) := mul_le_mul_of_nonneg_left
        (mul_le_mul (hΛ _) (hΛ _) hW₂ (hW₁.trans (hΛ _))) hc
    _ = _ := by
        simp only [c]
        ring

/-! ### Lemma G5 for a general pattern -/

open Classical in
/-- **Lemma G5, explicitly.** For a pattern `(C, K)` with `|C g| ≤ m₀`, a kernel `|K| ≤ κ_K`
depending only on the unshared parts, `F` and `G` invariant under the group primes, `μ_g ≤ μ₀`,
`Λ ≤ Λ₀`, `ω ≤ Ω` at both endpoints, and the support of `Ψ(w/(x D_C))` below `x²/D_R`,
the cutoff pairing is the stripped correlation up to
`2 B (∑_{w ≤ x²} 1/w) μ₀ (s_P J² + J (2Ω + m₀ s_P) + m₀ Ω)`,
`B = T² κ_K M₀ L_F L_G Λ₀²`. -/
theorem norm_physSum_sub_stripSum_le {x q₀ : ℝ} {P : ι → Finset ℕ}
    (hprime : ∀ g, ∀ p ∈ P g, p.Prime) (hdisj : ∀ g h, g ≠ h → Disjoint (P g) (P h))
    (hV : ∀ g, 0 < harmonicMass (P g)) (hq₀ : 0 < q₀) (hq₀₁ : q₀ ≤ 1)
    {C : ι → Finset (Fin J)} {m₀ : ℕ} (hC : ∀ g, (C g).card ≤ m₀)
    {K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ} {κK : ℝ}
    (hK : ∀ p p' a, ‖K p p' a‖ ≤ κK)
    (hKpad : ∀ p p' a, K p p' a = K (pad C p) (pad C p') a)
    {F G : ℕ → ℝ} {Ψ : ℝ → ℝ} {M₀ LF LG μ₀ Λ₀ Ω : ℝ}
    (hΨ : ∀ y, |Ψ y| ≤ M₀) (hLF : 0 ≤ LF) (hF : ∀ n, 1 ≤ n → n ≤ ⌊x ^ 2⌋₊ → |F n| ≤ LF)
    (hFinv : ∀ p ∈ univ.biUnion P, ∀ n, F (p * n) = F n) (hG : ∀ n, |G n| ≤ LG)
    (hGinv : ∀ p ∈ univ.biUnion P, ∀ n, G (p * n) = G n)
    (hμ₀ : 0 ≤ μ₀) (hμ : ∀ g, ∀ p ∈ P g, (harmonicMass (P g) * p)⁻¹ ≤ μ₀)
    (hΛ : ∀ n, listWeight P q₀ C n ≤ Λ₀)
    (hΩ₁ : ∀ w ∈ Icc 1 ⌊x ^ 2⌋₊, (groupPrimeCount P w : ℝ) ≤ Ω)
    (hΩ₂ : ∀ a ∈ auxLabels P C, ∀ w ∈ Icc 1 ⌊x ^ 2⌋₊,
      (groupPrimeCount P (w + slotProduct C a) : ℝ) ≤ Ω)
    (hsupp : ∀ a ∈ auxLabels P C, ∀ s ∈ auxLabels P (sharedSlots C), ∀ w : ℕ,
      Ψ (w / (x * slotProduct C a)) ≠ 0 → sharedProduct C s * w ≤ ⌊x ^ 2⌋₊) :
    ‖physSum x q₀ P C K F G Ψ - stripSum x q₀ P C K F G Ψ‖ ≤
      2 * (targetMass P C ^ 2 * κK * M₀ * LF * LG * Λ₀ ^ 2) *
        (∑ w ∈ Icc 1 ⌊x ^ 2⌋₊, (1 : ℝ) / w) *
        (μ₀ * (Fintype.card ι * J ^ 2 + J * (2 * Ω + m₀ * Fintype.card ι) + m₀ * Ω)) := by
  have hV' : ∀ g, harmonicMass (P g) ≠ 0 := fun g => (hV g).ne'
  set N := ⌊x ^ 2⌋₊
  set B := targetMass P C ^ 2 * κK * M₀ * LF * LG * Λ₀ ^ 2
  have hκ : 0 ≤ κK := (norm_nonneg _).trans (hK (fun _ _ => 0) (fun _ _ => 0) fun _ _ => 0)
  have hM : 0 ≤ M₀ := (abs_nonneg _).trans (hΨ 0)
  have hLG : 0 ≤ LG := (abs_nonneg _).trans (hG 0)
  have hT := targetMass_nonneg hV C
  have hB : 0 ≤ B := by positivity
  set Φ : (ι → Fin J → ℕ) → (ι → Fin J → ℕ) → (ι → Fin (J + 1) → ℕ) →
      (ι → Fin (J + 1) → ℕ) → ℕ → ℂ := fun a s l l' w =>
    (if sharedProduct C s * w ≤ N then
        physTerm x q₀ P C K F G Ψ (sharedProduct C s * w) (merge C s l) (merge C s l') a
      else 0) - stripTerm x q₀ P C K F G Ψ a s l l' w
  have hdiff : physSum x q₀ P C K F G Ψ - stripSum x q₀ P C K F G Ψ =
      ∑ a ∈ auxLabels P C, ∑ s ∈ auxLabels P (sharedSlots C), ∑ w ∈ Icc 1 N,
        ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C, Φ a s l l' w := by
    rw [physSum_eq_sum_strip x q₀ hprime hdisj, stripSum_eq_sum x q₀ hV', ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun s _ => ?_
    simp_rw [← sum_sub_distrib]
    rw [sum_congr rfl fun l _ => sum_comm, sum_comm]
  have hterm : ∀ a ∈ auxLabels P C, ∀ s ∈ auxLabels P (sharedSlots C), ∀ w ∈ Icc 1 N,
      ‖∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C, Φ a s l l' w‖ ≤
        (if Clean C a s w then 0 else 1) *
          (2 * (labelMass P (sharedSlots C) s * labelMass P C a * B / w)) := by
    intro a ha s hs w hw
    by_cases hc : Clean C a s w
    · rw [ite_eq_left hc, zero_mul, norm_le_zero_iff]
      refine sum_eq_zero fun l hl => sum_eq_zero fun l' hl' => sub_eq_zero.2 ?_
      exact physTerm_eq_stripTerm hprime hdisj hs hl hl' hc
        (eq_of_invariant_sharedProduct hFinv hs w)
        (eq_of_invariant_sharedProduct hGinv hs _)
        (by rw [hKpad, pad_merge hl, pad_merge hl']) (hsupp a ha s hs w)
    · rw [ite_eq_right hc, one_mul]
      calc _ ≤ ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C, ‖Φ a s l l' w‖ :=
            (norm_sum_le _ _).trans (sum_le_sum fun l _ => norm_sum_le _ _)
        _ ≤ ∑ l ∈ unsharedLists P C, ∑ l' ∈ unsharedLists P C,
            (‖if sharedProduct C s * w ≤ N then
                physTerm x q₀ P C K F G Ψ (sharedProduct C s * w) (merge C s l)
                  (merge C s l') a
              else 0‖ + ‖stripTerm x q₀ P C K F G Ψ a s l l' w‖) :=
            sum_le_sum fun l _ => sum_le_sum fun l' _ => norm_sub_le _ _
        _ ≤ labelMass P (sharedSlots C) s * labelMass P C a * B / w +
            labelMass P (sharedSlots C) s * labelMass P C a * B / w := by
            simp_rw [sum_add_distrib]
            exact add_le_add
              (sum_norm_physTerm_le hprime hV hq₀ hq₀₁ hK hΨ hLF hF hG hΛ hs
                (mem_Icc.1 hw).1)
              (sum_norm_stripTerm_le hV hq₀ hq₀₁ hK hΨ hLF hF hG hΛ a s hw)
        _ = _ := by ring
  rw [hdiff]
  calc _ ≤ ∑ a ∈ auxLabels P C, ∑ s ∈ auxLabels P (sharedSlots C), ∑ w ∈ Icc 1 N,
        (if Clean C a s w then 0 else 1) *
          (2 * (labelMass P (sharedSlots C) s * labelMass P C a * B / w)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun a ha => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun s hs => ?_)
        exact (norm_sum_le _ _).trans (sum_le_sum fun w hw => hterm a ha s hs w hw)
    _ = ∑ w ∈ Icc 1 N, 2 * B * (1 / w) * ∑ a ∈ auxLabels P C, labelMass P C a *
        ∑ s ∈ auxLabels P (sharedSlots C), labelMass P (sharedSlots C) s *
          (if Clean C a s w then 0 else 1) := by
        have hswap : ∀ f : (ι → Fin J → ℕ) → (ι → Fin J → ℕ) → ℕ → ℝ,
            ∑ a ∈ auxLabels P C, ∑ s ∈ auxLabels P (sharedSlots C), ∑ w ∈ Icc 1 N, f a s w =
              ∑ w ∈ Icc 1 N, ∑ a ∈ auxLabels P C, ∑ s ∈ auxLabels P (sharedSlots C),
                f a s w := fun f =>
          (sum_congr rfl fun a _ => sum_comm).trans sum_comm
        rw [hswap]
        refine sum_congr rfl fun w _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun s _ => ?_
        ring
    _ ≤ ∑ w ∈ Icc 1 N, 2 * B * (1 / w) *
        (μ₀ * (Fintype.card ι * J ^ 2 + J * (2 * Ω + m₀ * Fintype.card ι) + m₀ * Ω)) := by
        refine sum_le_sum fun w hw => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_mass_not_clean_le hV hC hμ₀ hμ (hΩ₁ w hw) fun a ha => hΩ₂ a ha w hw
    _ = _ := by
        rw [← sum_mul, ← mul_sum]

end Restore

end Erdos408.TwoSided
