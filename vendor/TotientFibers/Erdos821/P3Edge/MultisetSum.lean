import Erdos821.P3Edge.BoundedMem

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

variable {α : Type*} [Fintype α] [DecidableEq α]

-- Finite set of multisets of fixed card over a finite alphabet.
lemma multiset_fixed_card_finite (N : ℕ) :
    Set.Finite {z : Multiset α | z.card = N} := by
  classical
  have hle : {z : Multiset α | z.card = N} ⊆ {z : Multiset α | z.card ≤ N} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    omega
  exact (finite_multiset_bounded α N).subset hle

-- Multiset factorial denominator.
def multFact (z : Multiset α) : ℝ :=
  ∏ u ∈ z.toFinset, ((z.count u).factorial : ℝ)

lemma multFact_pos (z : Multiset α) : 0 < multFact z := by
  unfold multFact
  apply Finset.prod_pos
  intro u _
  positivity

-- Sum over multisets of fixed size with factorial denominators.
-- This is the exponential generating function identity needed for
-- column source-memory sums: weighted multiset sums collapse to
-- (sum w)^N / N!.
--
-- Proof by induction on the alphabet (Finset.univ), splitting
-- multisets by the count of a distinguished element and using
-- the binomial theorem. Each step is J- and x-independent.
lemma multiset_sum_eq
    (w : α → ℝ) (N : ℕ) :
    ∑ z ∈ (multiset_fixed_card_finite (α := α) N).toFinset,
      ((z.map w).prod / multFact z) =
      (∑ a, w a) ^ N / (N.factorial : ℝ) := by
  classical
  -- Induct on univ.
  have key : ∀ (s : Finset α), ∀ (N : ℕ),
      ∑ z ∈ ((multiset_fixed_card_finite N).toFinset.filter
        (fun z => ∀ a ∈ z, a ∈ s)),
        ((z.map w).prod / multFact z) =
        (∑ a ∈ s, w a) ^ N / (N.factorial : ℝ) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro N
      by_cases hN : N = 0
      · subst hN
        have hset : ((multiset_fixed_card_finite 0).toFinset.filter
            (fun z : Multiset α => ∀ a ∈ z, a ∈ (∅ : Finset α))) = {0} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · intro hz
            have hcard : z.card = 0 := by
              have h1 := (multiset_fixed_card_finite 0).mem_toFinset.mp hz.1
              simpa using h1
            have hz0 : z = 0 := Multiset.card_eq_zero.mp hcard
            exact hz0
          · intro hz
            subst hz
            constructor
            · apply (multiset_fixed_card_finite 0).mem_toFinset.mpr
              simp
            · intro a ha
              simpa using ha
        rw [hset]
        simp [multFact]
      · have hset : ((multiset_fixed_card_finite N).toFinset.filter
            (fun z : Multiset α => ∀ a ∈ z, a ∈ (∅ : Finset α))) = ∅ := by
          ext z
          simp only [Finset.mem_filter, Finset.notMem_empty]
          constructor
          · intro hz
            have hmem : ∃ a, a ∈ z := by
              have hcard : z.card = N := by
                have h1 := (multiset_fixed_card_finite N).mem_toFinset.mp hz.1
                simpa using h1
              have hpos : 0 < z.card := by omega
              exact Multiset.card_pos_iff_exists_mem.mp hpos
            obtain ⟨a, ha⟩ := hmem
            have hcon := hz.2 a ha
            simpa using hcon
          · intro hz
            simpa using hz
        rw [hset]
        simp only [Finset.sum_empty]
        rw [zero_pow hN, zero_div]
    | @insert a s has ih =>
      intro N
      -- Split by count of a.
      have hsplit : ((multiset_fixed_card_finite N).toFinset.filter
          (fun z : Multiset α => ∀ b ∈ z, b ∈ insert a s)) =
          Finset.biUnion (Finset.range (N + 1)) (fun k =>
            ((multiset_fixed_card_finite N).toFinset.filter
              (fun z : Multiset α => z.count a = k ∧ ∀ b ∈ z, b ∈ insert a s))) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
        constructor
        · intro hz
          have hcard : z.card = N := by
            have h1 := (multiset_fixed_card_finite N).mem_toFinset.mp hz.1
            simpa using h1
          have hk : z.count a ≤ N := le_trans (Multiset.count_le_card a z) (le_of_eq hcard)
          exact ⟨z.count a, Nat.lt_succ_of_le hk, hz.1, rfl, hz.2⟩
        · intro hz
          obtain ⟨k, _, hmem, _, hcond⟩ := hz
          exact ⟨hmem, hcond⟩
      -- Disjointness for biUnion sum.
      have hdisj : ∀ k ∈ Finset.range (N + 1), ∀ l ∈ Finset.range (N + 1), k ≠ l →
          Disjoint (((multiset_fixed_card_finite N).toFinset.filter
            (fun z : Multiset α => z.count a = k ∧ ∀ b ∈ z, b ∈ insert a s)))
            (((multiset_fixed_card_finite N).toFinset.filter
            (fun z : Multiset α => z.count a = l ∧ ∀ b ∈ z, b ∈ insert a s))) := by
        intro k _ l _ hkl
        apply Finset.disjoint_filter.mpr
        intro z _ hk hl
        exact hkl (hk.1.symm.trans hl.1)
      have hdisj' : Set.PairwiseDisjoint (↑(Finset.range (N + 1)))
          (fun k => ((multiset_fixed_card_finite N).toFinset.filter
            (fun z : Multiset α => z.count a = k ∧ ∀ b ∈ z, b ∈ insert a s))) := by
        intro k hk l hl hkl
        exact hdisj k (Finset.mem_coe.mp hk) l (Finset.mem_coe.mp hl) hkl
      rw [hsplit, Finset.sum_biUnion hdisj']
      -- Each k-piece: w(a)^k/k! times rest sum over s.
      have hpiece : ∀ k ∈ Finset.range (N + 1),
          ∑ z ∈ ((multiset_fixed_card_finite N).toFinset.filter
            (fun z : Multiset α => z.count a = k ∧ ∀ b ∈ z, b ∈ insert a s)),
            ((z.map w).prod / multFact z) =
          (w a ^ k / (k.factorial : ℝ)) *
            ((∑ b ∈ s, w b) ^ (N - k) / (((N - k).factorial : ℕ) : ℝ)) := by
        intro k hk
        have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        -- Bijection: z ↦ z.filter (· ≠ a), inverse rest ↦ rest + k•a.
        -- Both preserve products/factorials with split k! factor.
        have hbij : ((multiset_fixed_card_finite N).toFinset.filter
            (fun z : Multiset α => z.count a = k ∧ ∀ b ∈ z, b ∈ insert a s)) =
            ((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)).image
              (fun y => y + Multiset.replicate k a) := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_image]
          constructor
          · intro hz
            have hcard : z.card = N := by
              have h1 := (multiset_fixed_card_finite N).mem_toFinset.mp hz.1
              simpa using h1
            have hcount : z.count a = k := hz.2.1
            let y := z.filter (fun b => b ≠ a)
            have hy_card : y.card = N - k := by
              have h1 : (z.filter (fun b => b = a)).card = k := by
                rw [Multiset.filter_eq']
                simp [hcount]
              have h2 : z.filter (fun b => b ≠ a) + z.filter (fun b => b = a) = z := by
                have h := Multiset.filter_add_not (p := fun b => b = a) z
                rwa [add_comm] at h
              have h3 : y.card + (z.filter (fun b => b = a)).card = z.card := by
                rw [← Multiset.card_add, h2]
              omega
            have hy_mem : ∀ b ∈ y, b ∈ s := by
              intro b hb
              have hbz : b ∈ z := Multiset.mem_of_mem_filter hb
              have hbne : b ≠ a := (Multiset.mem_filter.mp hb).2
              have hins := hz.2.2 b hbz
              simp only [Finset.mem_insert] at hins
              rcases hins with rfl | hs
              · exact absurd rfl hbne
              · exact hs
            have hy_fin : y ∈ (multiset_fixed_card_finite (N - k)).toFinset := by
              apply (multiset_fixed_card_finite (N - k)).mem_toFinset.mpr
              simpa [hy_card] using hy_card
            refine ⟨y, ⟨hy_fin, hy_mem⟩, ?_⟩
            -- z = y + k•a
            have hz_eq : z = y + Multiset.replicate k a := by
              have h1 : z.filter (fun b => b = a) = Multiset.replicate k a := by
                rw [Multiset.filter_eq']
                simp [hcount]
              have h2 : z.filter (fun b => b ≠ a) + z.filter (fun b => b = a) = z := by
                have h := Multiset.filter_add_not (p := fun b => b = a) z
                rwa [add_comm] at h
              rw [← h2, h1]
            exact hz_eq.symm
          · intro hz
            obtain ⟨y, ⟨hy_fin, hy_mem⟩, rfl⟩ := hz
            have hy_card : y.card = N - k := by
              have h1 := (multiset_fixed_card_finite (N - k)).mem_toFinset.mp hy_fin
              simpa using h1
            have hcount_y : y.count a = 0 := by
              by_contra hne
              have hpos : 0 < y.count a := Nat.pos_of_ne_zero hne
              have ha_mem : a ∈ y := Multiset.count_pos.mp hpos
              have hs := hy_mem a ha_mem
              exact has hs
            constructor
            · apply (multiset_fixed_card_finite N).mem_toFinset.mpr
              simp [hy_card, hkN]
            · constructor
              · simp [Multiset.count_add, hcount_y, Multiset.count_replicate_self]
              · intro b hb
                simp only [Finset.mem_insert]
                have hmem : b ∈ y ∨ b ∈ Multiset.replicate k a := by
                  simpa [Multiset.mem_add] using hb
                rcases hmem with hy | hr
                · exact Or.inr (hy_mem b hy)
                · have hba : b = a := Multiset.mem_replicate.mp hr |>.2
                  exact Or.inl hba
        rw [hbij]
        -- Image sum: injectivity of rest ↦ rest + k•a on rest set.
        have hinj : Set.InjOn (fun y : Multiset α => y + Multiset.replicate k a)
            ((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)) := by
          intro y1 h1 y2 h2 heq
          simp only [] at heq
          have h1' : y1 ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)) := Finset.mem_coe.mp h1
          have h2' : y2 ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)) := Finset.mem_coe.mp h2
          have hy1_mem : ∀ b ∈ y1, b ∈ s := (Finset.mem_filter.mp h1').2
          have hy2_mem : ∀ b ∈ y2, b ∈ s := (Finset.mem_filter.mp h2').2
          have h1f : (y1 + Multiset.replicate k a).filter (fun b => b ≠ a) = y1 := by
            have hf : (Multiset.replicate k a).filter (fun b => b ≠ a) = 0 := by
              apply Multiset.filter_eq_nil.mpr
              intro x hx
              have hxeq : x = a := (Multiset.mem_replicate.mp hx).2
              simp [hxeq]
            have hy1 : y1.filter (fun b => b ≠ a) = y1 := by
              apply Multiset.filter_eq_self.mpr
              intro b hb
              have hs := hy1_mem b hb
              intro hba
              subst hba
              exact has hs
            simp [Multiset.filter_add, hf, hy1]
          have h2f : (y2 + Multiset.replicate k a).filter (fun b => b ≠ a) = y2 := by
            have hf : (Multiset.replicate k a).filter (fun b => b ≠ a) = 0 := by
              apply Multiset.filter_eq_nil.mpr
              intro x hx
              have hxeq : x = a := (Multiset.mem_replicate.mp hx).2
              simp [hxeq]
            have hy2 : y2.filter (fun b => b ≠ a) = y2 := by
              apply Multiset.filter_eq_self.mpr
              intro b hb
              have hs := hy2_mem b hb
              intro hba
              subst hba
              exact has hs
            simp [Multiset.filter_add, hf, hy2]
          have heq2 := congrArg (Multiset.filter (fun b => b ≠ a)) heq
          rw [h1f, h2f] at heq2
          exact heq2
        -- Convert image sum to sum over rest.
        have hsum_eq : ∑ z ∈ (((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)).image
              (fun y => y + Multiset.replicate k a)),
            ((z.map w).prod / multFact z) =
            ∑ y ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)),
            (((y + Multiset.replicate k a).map w).prod / multFact (y + Multiset.replicate k a)) := by
          exact Finset.sum_image hinj
        rw [hsum_eq]
        -- Split products: (rest + k•a).map w prod = rest.prod * w(a)^k.
        have hsplit_prod : ∀ y : Multiset α,
            ((y + Multiset.replicate k a).map w).prod =
              (y.map w).prod * w a ^ k := by
          intro y
          rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate]
        -- Split multFact: multFact(rest + k•a) = multFact(rest) * k! (since a∉rest).
        have hsplit_fact : ∀ y ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
            (fun y : Multiset α => ∀ b ∈ y, b ∈ s)),
            multFact (y + Multiset.replicate k a) = multFact y * (k.factorial : ℝ) := by
          intro y hy
          have hy_mem : ∀ b ∈ y, b ∈ s := (Finset.mem_filter.mp hy).2
          have hcount_y : y.count a = 0 := by
            by_contra hne
            have hpos : 0 < y.count a := Nat.pos_of_ne_zero hne
            have ha_mem : a ∈ y := Multiset.count_pos.mp hpos
            exact has (hy_mem a ha_mem)
          unfold multFact
          -- toFinset splits: a is new element (count k>0? if k=0, no new? careful).
          by_cases hk0 : k = 0
          · subst hk0
            simp
          · have hfin_eq : (y + Multiset.replicate k a).toFinset = insert a y.toFinset := by
              ext b
              simp only [Multiset.mem_toFinset]
              simp only [Finset.mem_insert, Multiset.mem_add,
                Multiset.mem_replicate]
              constructor
              · intro hb
                rcases hb with hyb | ⟨_, rfl⟩
                · exact Or.inr (Multiset.mem_toFinset.mpr hyb)
                · exact Or.inl rfl
              · intro hb
                rcases hb with rfl | hyb
                · exact Or.inr ⟨hk0, rfl⟩
                · exact Or.inl (Multiset.mem_toFinset.mp hyb)
            rw [hfin_eq]
            have ha_not : a ∉ y.toFinset := by
              intro hmem
              have ha_y : a ∈ y := Multiset.mem_toFinset.mp hmem
              have hpos : 0 < y.count a := Multiset.count_pos.mpr ha_y
              omega
            rw [Finset.prod_insert ha_not]
            have hcount_add : ∀ b ∈ y.toFinset, (y + Multiset.replicate k a).count b = y.count b := by
              intro b hb
              have hb_mem : b ∈ y := Multiset.mem_toFinset.mp hb
              have hba : b ≠ a := by
                intro hba
                have hs := hy_mem b hb_mem
                rw [hba] at hs
                exact has hs
              rw [Multiset.count_add]
              have hrep : (Multiset.replicate k a).count b = 0 := by
                rw [Multiset.count_replicate, if_neg (Ne.symm hba)]
              omega
            have hcount_a : (y + Multiset.replicate k a).count a = k := by
              rw [Multiset.count_add, hcount_y]
              simp
            rw [hcount_a]
            -- Remaining products equal.
            have hrest : ∏ u ∈ y.toFinset, ((((y + Multiset.replicate k a).count u).factorial : ℕ) : ℝ) =
                ∏ u ∈ y.toFinset, (((y.count u).factorial : ℕ) : ℝ) := by
              apply Finset.prod_congr rfl
              intro b hb
              rw [hcount_add b hb]
            rw [hrest]
            ring
        -- Combine via factoring + induction hypothesis.
        have hsum_rest : ∑ y ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
            (fun y : Multiset α => ∀ b ∈ y, b ∈ s)),
            ((y.map w).prod / multFact y) =
            (∑ b ∈ s, w b) ^ (N - k) / (((N - k).factorial : ℕ) : ℝ) := ih (N - k)
        have hterm_eq : ∀ y ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
            (fun y : Multiset α => ∀ b ∈ y, b ∈ s)),
            (((y + Multiset.replicate k a).map w).prod / multFact (y + Multiset.replicate k a)) =
            ((y.map w).prod / multFact y) * (w a ^ k / (k.factorial : ℝ)) := by
          intro y hy
          rw [hsplit_prod, hsplit_fact y hy]
          ring
        calc ∑ y ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
            (fun y : Multiset α => ∀ b ∈ y, b ∈ s)),
            (((y + Multiset.replicate k a).map w).prod / multFact (y + Multiset.replicate k a))
            = ∑ y ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)),
              (((y.map w).prod / multFact y) * (w a ^ k / (k.factorial : ℝ))) := by
              apply Finset.sum_congr rfl
              intro y hy
              exact hterm_eq y hy
          _ = (∑ y ∈ ((multiset_fixed_card_finite (N - k)).toFinset.filter
              (fun y : Multiset α => ∀ b ∈ y, b ∈ s)),
              ((y.map w).prod / multFact y)) * (w a ^ k / (k.factorial : ℝ)) := by
              rw [Finset.sum_mul]
          _ = _ := by
              rw [hsum_rest]
              ring
      -- Sum over k via binomial theorem.
      calc ∑ k ∈ Finset.range (N + 1),
            ∑ z ∈ ((multiset_fixed_card_finite N).toFinset.filter
              (fun z : Multiset α => z.count a = k ∧ ∀ b ∈ z, b ∈ insert a s)),
              ((z.map w).prod / multFact z)
          = ∑ k ∈ Finset.range (N + 1),
              (w a ^ k / (k.factorial : ℝ)) *
                ((∑ b ∈ s, w b) ^ (N - k) / (((N - k).factorial : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hpiece k hk
        _ = ∑ k ∈ Finset.range (N + 1),
              ((N.choose k : ℝ) * w a ^ k * (∑ b ∈ s, w b) ^ (N - k) / (N.factorial : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            have hfact : ((N.choose k : ℕ) : ℝ) * ((k.factorial : ℕ) : ℝ) * (((N - k).factorial : ℕ) : ℝ)
                = (N.factorial : ℝ) := by
              have h2 : N.choose k * k.factorial * (N - k).factorial = N.factorial :=
                Nat.choose_mul_factorial_mul_factorial hkN
              exact_mod_cast h2
            have hk0 : ((k.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
            have hNk0 : ((((N - k).factorial : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
            have hN0 : ((N.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
            have h1 : (w a ^ k / (k.factorial : ℝ)) *
                ((∑ b ∈ s, w b) ^ (N - k) / (((N - k).factorial : ℕ) : ℝ)) =
                (w a ^ k * (∑ b ∈ s, w b) ^ (N - k)) / (((k.factorial : ℕ) : ℝ) * (((N - k).factorial : ℕ) : ℝ)) := by
              ring
            have h2 : ((N.choose k : ℝ) * w a ^ k * (∑ b ∈ s, w b) ^ (N - k) / (N.factorial : ℝ)) =
                (w a ^ k * (∑ b ∈ s, w b) ^ (N - k)) * ((N.choose k : ℝ) / (N.factorial : ℝ)) := by
              ring
            rw [h1, h2]
            have hAB : (1 : ℝ) / (((k.factorial : ℕ) : ℝ) * (((N - k).factorial : ℕ) : ℝ)) =
                ((N.choose k : ℝ) / (N.factorial : ℝ)) := by
              rw [div_eq_div_iff (mul_ne_zero hk0 hNk0) hN0]
              linarith [hfact]
            have hF : (w a ^ k * (∑ b ∈ s, w b) ^ (N - k)) /
                (((k.factorial : ℕ) : ℝ) * (((N - k).factorial : ℕ) : ℝ)) =
                (w a ^ k * (∑ b ∈ s, w b) ^ (N - k)) *
                  (1 / (((k.factorial : ℕ) : ℝ) * (((N - k).factorial : ℕ) : ℝ))) := by
              ring
            rw [hF, hAB]
        _ = (∑ b ∈ insert a s, w b) ^ N / (N.factorial : ℝ) := by
            have hbin : (∑ b ∈ insert a s, w b) ^ N =
                ∑ k ∈ Finset.range (N + 1),
                  ((N.choose k : ℝ) * w a ^ k * (∑ b ∈ s, w b) ^ (N - k)) := by
              rw [Finset.sum_insert has, add_pow]
              apply Finset.sum_congr rfl
              intro k _
              ring
            rw [hbin, Finset.sum_div]
  -- Apply with s = univ.
  have hfull := key Finset.univ N
  have hfilter_eq : ((multiset_fixed_card_finite N).toFinset.filter
      (fun z : Multiset α => ∀ a_1 ∈ z, a_1 ∈ Finset.univ)) =
      (multiset_fixed_card_finite N).toFinset := by
    apply Finset.filter_true_of_mem
    intro z _
    intro a _
    exact Finset.mem_univ a
  rw [hfilter_eq] at hfull
  simpa using hfull

-- Bounded version: with sums ≤ 2, multiset sums ≤ 2^N/N!.
lemma multiset_sum_le
    (w : α → ℝ) (hwnn : ∀ a, 0 ≤ w a) (hw2 : ∑ a, w a ≤ 2) (N : ℕ) :
    ∑ z ∈ (multiset_fixed_card_finite N).toFinset,
      ((z.map w).prod / multFact z) ≤ (2 : ℝ) ^ N / (N.factorial : ℝ) := by
  rw [multiset_sum_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc (∑ a, w a) ^ N ≤ (2 : ℝ) ^ N := by
        apply pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => hwnn a)) hw2 N

end Erdos821.P3Edge
