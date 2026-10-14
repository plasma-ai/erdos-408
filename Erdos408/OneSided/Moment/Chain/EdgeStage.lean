import Erdos408.OneSided.Moment.Chain.GhostStage

/-!
# The edge step of the memory identity

One edge `ℰ` after the ghost at the visit `t`, with a fixed admissible free choice: the
memory part of the choice is the set `St` of stored groups and the promotion flags `fl`. The
`ρ` factors of the edge are attributed to the adjacent visits (`Moment/Chain/GhostStage.lean`),
so the memory weight is the product of the label weights (`memLabelWeight`): `S(x)` for a
promotion and `c_p` for a fresh prime.

`edge_stage`: summed over `St` and `fl` with distinct fresh labels, the memory weight times
the lifespan product at `t + 1` is the post-ghost lifespan product at `t`. With the leaving
primes `b_i` and the entering primes `a_i` of the free choice:

* every other prime keeps its status; a staying prime keeps its line, since it is a pad;
* `b_i` becomes pending (`i ∈ St`) or dead, and the two values add up to its post-ghost
  value (`postValue_leave`);
* `a_i` becomes active, promoted from its anchor (weight `S(x) ∈ {0, 1}`) or fresh (weight
  `c_p`, only if unborn), which is `postValue_enter_*`.

The summand factors over the groups (`edge_summand_eq_prod`), and the sums over `St` and `fl`
are products of per-group sums.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section EdgeStage

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

variable {x d Y d₀ u v r B}

/-- The sum over the subsets of the groups of a product of per-group factors. -/
theorem sum_finset_prod_decide (H : Fin K → Bool → ℝ) :
    ∑ St : Finset (Fin K), ∏ i, H i (decide (i ∈ St)) = ∏ i, (H i true + H i false) := by
  classical
  rw [prod_add, powerset_univ]
  refine sum_congr rfl fun St _ => ?_
  rw [← prod_filter_mul_prod_filter_not univ fun i => i ∈ St]
  congr 1
  · rw [filter_mem_eq_inter, univ_inter]
    exact prod_congr rfl fun i hi => by simp [hi]
  · rw [show univ.filter (fun i => i ∉ St) = univ \ St by ext; simp]
    exact prod_congr rfl fun i hi => by simp [(mem_sdiff.1 hi).2]

section Choice

variable {s : ChainState x d Y d₀ u v r B} {c₀ : FreeChoice x d Y d₀ u v r}

/-- The prime leaving group `i`: the unshared slot of the reordered source. -/
abbrev leavePrime (s : ChainState x d Y d₀ u v r B) (c₀ : FreeChoice x d Y d₀ u v r)
    (i : Fin K) : ℕ :=
  edgeSrc s (toEdge₀ c₀) i (Fin.last _)

/-- The leaving primes are in their bands. -/
theorem leavePrime_mem_band (i : Fin K) : leavePrime s c₀ i ∈ band x (d.a i) :=
  mem_band_of_mem_lists s.2.1.2 i _

/-- The entering primes are in their bands. -/
theorem enterPrime_mem_band (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) (i : Fin K) :
    c₀.2.2.1 i ∈ band x (d.a i) := by
  simp only [freeChoices, mem_product, Fintype.mem_piFinset] at hc₀
  exact hc₀.2.2.1 i

/-- A prime of the band `𝒫_i` is a band prime. -/
theorem mem_bandPrimes_of_band {i : Fin K} {p : ℕ} (hp : p ∈ band x (d.a i)) :
    p ∈ bandPrimes x d :=
  mem_biUnion.2 ⟨i, mem_univ _, hp⟩

/-- With disjoint bands, primes of the bands of `i` and `j` agree only if `i = j`. -/
theorem eq_of_mem_band (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {i j : Fin K} {p : ℕ} (hi : p ∈ band x (d.a i)) (hj : p ∈ band x (d.a j)) : i = j := by
  by_contra h
  exact disjoint_left.1 (hdisj i j h) hi hj

/-- The particle promoted into group `i`: the entering prime at its target line. -/
def promPart (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) (i : Fin K) : Particle x d :=
  ⟨(c₀.2.2.1 i, lineOf (c₀.2.2.1 i) c₀.2.1.1), mem_particles.2
    ⟨mem_bandPrimes_of_band (enterPrime_mem_band hc₀ i),
      lineOf_le (prime_of_mem_bandPrimes (mem_bandPrimes_of_band
        (enterPrime_mem_band hc₀ i))).pos _⟩⟩

/-- The particle stored from group `i`: the leaving prime at its source line. -/
def storePart (s : ChainState x d Y d₀ u v r B) (c₀ : FreeChoice x d Y d₀ u v r) (i : Fin K) :
    Particle x d :=
  ⟨(leavePrime s c₀ i, lineOf (leavePrime s c₀ i) s.1.1), mem_particles.2
    ⟨mem_bandPrimes_of_band (leavePrime_mem_band i),
      lineOf_le (prime_of_mem_bandPrimes (mem_bandPrimes_of_band
        (leavePrime_mem_band i))).pos _⟩⟩

/-- The label weight: the memory at the promoted particle, or the birth constant. -/
theorem memLabelWeight_toEdge (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) (N : ℕ)
    (St : Finset (Fin K)) (fl : Fin K → Bool) (i : Fin K) :
    memLabelWeight q x d N s.2.2.1 (toEdge c₀ St fl) i =
      if fl i then (s.2.2.1 (promPart hc₀ i) : ℝ) else birthConst q N (c₀.2.2.1 i) := by
  classical
  by_cases hf : fl i = true
  · rw [memLabelWeight, ite_eq_left (show ((toEdge c₀ St fl).2.2.2.1 i).2 = true from hf),
      ite_eq_left hf, Fintype.sum_eq_single (promPart hc₀ i)]
    · exact ite_eq_left rfl
    · exact fun xp hxp => ite_eq_right fun h => hxp (Subtype.ext h)
  · simp only [memLabelWeight, toEdge, hf, ite_false, Bool.false_eq_true]
    rfl

/-- The memory after the edge. -/
theorem edgeMem_toEdge (St : Finset (Fin K)) (fl : Fin K → Bool) (xp : Particle x d) :
    edgeMem s (toEdge c₀ St fl) xp = s.2.2.1 xp -
      (univ.filter fun i => fl i = true ∧
        (c₀.2.2.1 i, lineOf (c₀.2.2.1 i) c₀.2.1.1) = xp.1).card +
      (St.filter fun i => (leavePrime s c₀ i, lineOf (leavePrime s c₀ i) s.1.1) = xp.1).card :=
  rfl

/-- The fresh labels of the edge. -/
theorem freshBirths_toEdge (St : Finset (Fin K)) (fl : Fin K → Bool) :
    freshBirths (toEdge c₀ St fl) = ∑ i, if fl i then 0 else {c₀.2.2.1 i} :=
  rfl

/-! ### The leaving and entering primes of an admissible choice -/

section Admissible

variable (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
  (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) (hv : FreeValid x d Y d₀ u v r B s (toEdge₀ c₀))

include hdisj in
/-- The leaving primes are distinct. -/
theorem leavePrime_injective : Function.Injective (leavePrime s c₀) := fun i j h =>
  eq_of_mem_band hdisj (leavePrime_mem_band i) (h ▸ leavePrime_mem_band j)

include hdisj hc₀ in
/-- The entering primes are distinct. -/
theorem enterPrime_injective : Function.Injective fun i => c₀.2.2.1 i := fun i j h =>
  eq_of_mem_band hdisj (enterPrime_mem_band hc₀ i) ((show c₀.2.2.1 i = c₀.2.2.1 j from h) ▸
    enterPrime_mem_band hc₀ j)

include hv in
/-- No prime both enters and leaves. -/
theorem enterPrime_ne_leavePrime (i j : Fin K) : c₀.2.2.1 i ≠ leavePrime s c₀ j :=
  hv.2.1 i j _

include hv in
/-- An entering prime is not in the source lists. -/
theorem enterPrime_not_act (i : Fin K) : ¬∃ i' h, s.2.1.1 i' h = c₀.2.2.1 i :=
  ((enter_iff hv _).2 ⟨i, rfl⟩).1

include hv in
/-- An entering prime is in the target lists. -/
theorem enterPrime_tgt (i : Fin K) : ∃ i' h, edgeTgt s (toEdge₀ c₀) i' h = c₀.2.2.1 i :=
  ((enter_iff hv _).2 ⟨i, rfl⟩).2

include hdisj hv in
/-- A leaving prime is not in the target lists. -/
theorem leavePrime_not_tgt (i : Fin K) :
    ¬∃ i' h, edgeTgt s (toEdge₀ c₀) i' h = leavePrime s c₀ i :=
  ((leave_iff hv hdisj _).2 ⟨i, rfl⟩).2

end Admissible

end Choice

/-! ### The memory after the edge -/

section Memory

variable {s : ChainState x d Y d₀ u v r B} {c₀ : FreeChoice x d Y d₀ u v r}
  (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
  (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) (hv : FreeValid x d Y d₀ u v r B s (toEdge₀ c₀))
  {Bn : Multiset ℕ} (hS : Consistent s.2.1.1 s.2.2.1 Bn)

/-- The promotion flags and the births are compatible: a promoted prime is pending at its
target line, and a fresh prime is unborn. -/
def EdgeGood (hc₀ : c₀ ∈ freeChoices x d Y d₀ u v r) (Bn : Multiset ℕ) (fl : Fin K → Bool) :
    Prop :=
  ∀ i, (fl i = true → s.2.2.1 (promPart hc₀ i) ≠ 0) ∧ (fl i = false → c₀.2.2.1 i ∉ Bn)

open scoped Classical in
include hdisj hv hS in
/-- On a compatible choice, the memory after the edge is `1` at the stored particles, `0` at
the promoted ones, and unchanged elsewhere. -/
theorem edgeMem_eq (St : Finset (Fin K)) (fl : Fin K → Bool) (xp : Particle x d) :
    edgeMem s (toEdge c₀ St fl) xp =
      if ∃ i ∈ St, storePart s c₀ i = xp then 1
      else if ∃ i, fl i = true ∧ promPart hc₀ i = xp then 0 else s.2.2.1 xp := by
  rw [edgeMem_toEdge]
  set P := (univ.filter fun i => fl i = true ∧
    (c₀.2.2.1 i, lineOf (c₀.2.2.1 i) c₀.2.1.1) = xp.1).card
  set Q := (St.filter fun i => (leavePrime s c₀ i, lineOf (leavePrime s c₀ i) s.1.1) = xp.1).card
  have hP₁ : P ≤ 1 := card_le_one.2 fun i hi j hj => enterPrime_injective hdisj hc₀
    (congrArg Prod.fst (((mem_filter.1 hi).2.2).trans (mem_filter.1 hj).2.2.symm))
  have hQ₁ : Q ≤ 1 := card_le_one.2 fun i hi j hj => leavePrime_injective hdisj
    (congrArg Prod.fst (((mem_filter.1 hi).2).trans (mem_filter.1 hj).2.symm))
  have hS₁ := hS.le_one xp
  by_cases hst : ∃ i ∈ St, storePart s c₀ i = xp
  · obtain ⟨i, hi, rfl⟩ := hst
    rw [ite_eq_left ⟨i, hi, rfl⟩]
    -- the leaving prime is active, so not pending and not promoted
    have hS₀ : s.2.2.1 (storePart s c₀ i) = 0 := by
      by_contra h
      exact hS.pend_inactive _ h ⟨i, _, rfl⟩
    have hP₀ : P = 0 := card_eq_zero.2 (filter_eq_empty_iff.2 fun j _ h =>
      enterPrime_ne_leavePrime hv j i (congrArg Prod.fst h.2))
    have hQ₀ : Q ≠ 0 := card_ne_zero.2 ⟨i, mem_filter.2 ⟨hi, rfl⟩⟩
    rw [hS₀, hP₀]
    omega
  · rw [ite_eq_right hst]
    have hQ₀ : Q = 0 := card_eq_zero.2 (filter_eq_empty_iff.2 fun i hi h =>
      hst ⟨i, hi, Subtype.ext h⟩)
    rw [hQ₀, add_zero]
    by_cases hpr : ∃ i, fl i = true ∧ promPart hc₀ i = xp
    · obtain ⟨i, hfi, rfl⟩ := hpr
      rw [ite_eq_left ⟨i, hfi, rfl⟩]
      have hP₀ : P ≠ 0 := card_ne_zero.2 ⟨i, mem_filter.2 ⟨mem_univ _, hfi, rfl⟩⟩
      omega
    · rw [ite_eq_right hpr]
      have hP₀ : P = 0 := card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ h =>
        hpr ⟨i, h.1, Subtype.ext h.2⟩)
      rw [hP₀, Nat.sub_zero]

open scoped Classical in
/-- The multiplicity of `p` among the fresh labels. -/
theorem count_freshBirths (St : Finset (Fin K)) (fl : Fin K → Bool) (p : ℕ) :
    Multiset.count p (freshBirths (toEdge c₀ St fl)) =
      (univ.filter fun i => fl i = false ∧ c₀.2.2.1 i = p).card := by
  rw [freshBirths_toEdge, Multiset.count_sum', card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases hf : fl i = true
  · simp [hf]
  · simp [hf, Multiset.count_singleton, eq_comm]

open scoped Classical in
include hdisj hc₀ hv hS in
/-- On a compatible choice, the state after the edge is consistent. -/
theorem consistent_edgeMem (St : Finset (Fin K)) {fl : Fin K → Bool}
    (hg : EdgeGood (s := s) hc₀ Bn fl) :
    Consistent (edgeTgt s (toEdge c₀ St fl)) (edgeMem s (toEdge c₀ St fl))
      (Bn + freshBirths (toEdge c₀ St fl)) := by
  have hmem := edgeMem_eq hdisj hc₀ hv hS St fl
  have htgt : edgeTgt s (toEdge c₀ St fl) = edgeTgt s (toEdge₀ c₀) := rfl
  -- a promoted particle is pending in the source memory, hence born
  have hprom : ∀ i, fl i = true → c₀.2.2.1 i ∈ Bn := fun i hfi =>
    hS.pend_mem (promPart hc₀ i) ((hg i).1 hfi)
  have hfresh : ∀ i, fl i = false → c₀.2.2.1 i ∈ freshBirths (toEdge c₀ St fl) := fun i hfi => by
    rw [← Multiset.count_pos, count_freshBirths]
    exact card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, hfi, rfl⟩⟩
  -- the nonzero entries of the new memory: stored particles and old unpromoted ones
  have hnz : ∀ xp, edgeMem s (toEdge c₀ St fl) xp ≠ 0 →
      (∃ i ∈ St, storePart s c₀ i = xp) ∨
        ((¬∃ i, fl i = true ∧ promPart hc₀ i = xp) ∧ s.2.2.1 xp ≠ 0) := by
    intro xp h
    rw [hmem] at h
    by_cases hst : ∃ i ∈ St, storePart s c₀ i = xp
    · exact Or.inl hst
    · rw [ite_eq_right hst] at h
      by_cases hpr : ∃ i, fl i = true ∧ promPart hc₀ i = xp
      · rw [ite_eq_left hpr] at h
        exact absurd rfl h
      · rw [ite_eq_right hpr] at h
        exact Or.inr ⟨hpr, h⟩
  refine ⟨?_, ?_, fun xp => ?_, fun xp h => ?_, fun xp h => ?_, fun xp xp' h h' hp => ?_⟩
  · -- the fresh labels are distinct and unborn
    refine Multiset.nodup_iff_count_le_one.2 fun p => ?_
    rw [Multiset.count_add, count_freshBirths]
    have h₁ := Multiset.nodup_iff_count_le_one.1 hS.nodup p
    have h₂ : (univ.filter fun i => fl i = false ∧ c₀.2.2.1 i = p).card ≤ 1 :=
      card_le_one.2 fun i hi j hj => enterPrime_injective hdisj hc₀
        ((mem_filter.1 hi).2.2.trans (mem_filter.1 hj).2.2.symm)
    by_cases h₃ : (univ.filter fun i => fl i = false ∧ c₀.2.2.1 i = p).card = 0
    · omega
    · obtain ⟨i, hi⟩ := card_ne_zero.1 h₃
      obtain ⟨-, hfi, rfl⟩ := mem_filter.1 hi
      rw [Multiset.count_eq_zero.2 ((hg i).2 hfi)]
      omega
  · -- the target lists are born
    intro i h
    rcases (mem_edgeTgt_iff s _ _).1 ⟨i, h, rfl⟩ with ⟨i', k, hk⟩ | ⟨i', hi'⟩
    · rw [← hk]
      exact Multiset.mem_add.2 (Or.inl (hS.act_mem _ _))
    · rw [← hi']
      cases hfi : fl i'
      · exact Multiset.mem_add.2 (Or.inr (hfresh i' hfi))
      · exact Multiset.mem_add.2 (Or.inl (hprom i' hfi))
  · rw [hmem]
    have := hS.le_one xp
    split_ifs <;> omega
  · rcases hnz xp h with ⟨i, -, rfl⟩ | ⟨-, h₀⟩
    · exact Multiset.mem_add.2 (Or.inl (hS.act_mem i _))
    · exact Multiset.mem_add.2 (Or.inl (hS.pend_mem xp h₀))
  · rcases hnz xp h with ⟨i, -, rfl⟩ | ⟨hpr, h₀⟩
    · rw [htgt]
      exact leavePrime_not_tgt hdisj hv i
    · -- an old pending prime that enters must be promoted, which it is not
      intro hin
      rw [htgt] at hin
      obtain ⟨j, hj⟩ := (enter_iff hv _).1 ⟨hS.pend_inactive xp h₀, hin⟩
      cases hfj : fl j
      · exact (hg j).2 hfj (by rw [show c₀.2.2.1 j = xp.1.1 from hj]; exact hS.pend_mem xp h₀)
      · exact hpr ⟨j, hfj, hS.pend_unique _ _ ((hg j).1 hfj) h₀ hj⟩
  · rcases hnz xp h with ⟨i, -, rfl⟩ | ⟨-, h₀⟩ <;> rcases hnz xp' h' with ⟨j, -, rfl⟩ | ⟨-, h₀'⟩
    · rw [leavePrime_injective hdisj hp]
    · exact absurd ⟨i, _, hp⟩ (hS.pend_inactive _ h₀')
    · exact absurd ⟨j, _, hp.symm⟩ (hS.pend_inactive _ h₀)
    · exact hS.pend_unique xp xp' h₀ h₀' hp

open scoped Classical in
include hdisj hc₀ hv hS in
/-- The statuses after a compatible edge: the entering primes are active, the leaving primes
pending (if stored) or dead, and every other prime keeps its status. -/
theorem statusOf_edge (St : Finset (Fin K)) {fl : Fin K → Bool} (hg : EdgeGood (s := s) hc₀ Bn fl)
    (p : ℕ) :
    statusOf (edgeTgt s (toEdge c₀ St fl)) (edgeMem s (toEdge c₀ St fl))
        (Bn + freshBirths (toEdge c₀ St fl)) p =
      if ∃ i, c₀.2.2.1 i = p then .active
      else if h : ∃ i, leavePrime s c₀ i = p then
        (if h.choose ∈ St then .pending (lineOf p s.1.1) else .dead)
      else statusOf s.2.1.1 s.2.2.1 Bn p := by
  have hc := consistent_edgeMem hdisj hc₀ hv hS St hg
  have hmem := edgeMem_eq hdisj hc₀ hv hS St fl
  have htgt : edgeTgt s (toEdge c₀ St fl) = edgeTgt s (toEdge₀ c₀) := rfl
  by_cases ha : ∃ i, c₀.2.2.1 i = p
  · rw [ite_eq_left ha, statusOf_eq_active_iff, htgt]
    obtain ⟨i, rfl⟩ := ha
    exact enterPrime_tgt hv i
  rw [ite_eq_right ha]
  by_cases hb : ∃ i, leavePrime s c₀ i = p
  · rw [dite_eq_left hb]
    obtain hi := hb.choose_spec
    set i := hb.choose
    have hna : ¬∃ i' h, edgeTgt s (toEdge c₀ St fl) i' h = p := by
      rw [htgt, ← hi]
      exact leavePrime_not_tgt hdisj hv i
    by_cases hiSt : i ∈ St
    · rw [ite_eq_left hiSt]
      have h1 : edgeMem s (toEdge c₀ St fl) (storePart s c₀ i) ≠ 0 := by
        rw [hmem, ite_eq_left ⟨i, hiSt, rfl⟩]
        exact one_ne_zero
      rw [← hi]
      exact statusOf_of_pend hc h1
    · rw [ite_eq_right hiSt, statusOf_of_none hna fun xp hxp => ?_, ite_eq_left ?_]
      · rw [← hi]
        exact Multiset.mem_add.2 (Or.inl (hS.act_mem i _))
      · rw [hmem]
        have hst : ¬∃ j ∈ St, storePart s c₀ j = xp := fun ⟨j, hj, hjx⟩ => hiSt (by
          have : leavePrime s c₀ j = leavePrime s c₀ i := (congrArg (·.1.1) hjx).trans
            (hxp.trans hi.symm)
          rwa [← leavePrime_injective hdisj this])
        rw [ite_eq_right hst]
        split_ifs
        · rfl
        · by_contra h0
          exact hS.pend_inactive xp h0 ⟨i, _, hi.trans hxp.symm⟩
  · rw [dite_eq_right hb]
    refine (statusOf_congr hS hc ?_ (fun xp hxp => ?_) ?_).symm
    · rw [htgt]
      constructor
      · intro h
        by_contra h'
        exact hb ((leave_iff hv hdisj p).1 ⟨h, h'⟩)
      · intro h
        by_contra h'
        exact ha ((enter_iff hv p).1 ⟨h', h⟩)
    · rw [hmem, ite_eq_right fun ⟨j, _, hj⟩ => hb ⟨j, (congrArg (·.1.1) hj).trans hxp⟩,
        ite_eq_right fun ⟨j, _, hj⟩ => ha ⟨j, (congrArg (·.1.1) hj).trans hxp⟩]
    · rw [Multiset.mem_add]
      refine ⟨Or.inl, fun h => h.resolve_right fun h' => ?_⟩
      rw [← Multiset.count_pos, count_freshBirths] at h'
      obtain ⟨i, hi⟩ := card_pos.1 h'
      exact ha ⟨i, (mem_filter.1 hi).2.2⟩

/-- The band primes other than the leaving and the entering ones. -/
def restPrimes (s : ChainState x d Y d₀ u v r B) (c₀ : FreeChoice x d Y d₀ u v r) : Finset ℕ :=
  bandPrimes x d \ (univ.image (leavePrime s c₀) ∪ univ.image fun i => c₀.2.2.1 i)

include hdisj hc₀ hv in
/-- A product over the band primes splits into the other primes, the leaving primes and the
entering primes. -/
theorem prod_bandPrimes_split (f : ℕ → ℝ) :
    ∏ p ∈ bandPrimes x d, f p =
      (∏ p ∈ restPrimes s c₀, f p) * (∏ i, f (leavePrime s c₀ i)) * ∏ i, f (c₀.2.2.1 i) := by
  classical
  have hsub : univ.image (leavePrime s c₀) ∪ (univ.image fun i => c₀.2.2.1 i) ⊆ bandPrimes x d := by
    intro p hp
    rcases mem_union.1 hp with h | h <;> obtain ⟨i, -, rfl⟩ := mem_image.1 h
    · exact mem_bandPrimes_of_band (leavePrime_mem_band i)
    · exact mem_bandPrimes_of_band (enterPrime_mem_band hc₀ i)
  have hdis : Disjoint (univ.image (leavePrime s c₀)) (univ.image fun i => c₀.2.2.1 i) := by
    refine disjoint_left.2 fun p h h' => ?_
    obtain ⟨i, -, rfl⟩ := mem_image.1 h
    obtain ⟨j, -, hj⟩ := mem_image.1 h'
    exact enterPrime_ne_leavePrime hv j i hj
  rw [← prod_sdiff hsub, prod_union hdis, prod_image fun i _ j _ h => leavePrime_injective hdisj h,
    prod_image fun i _ j _ h => enterPrime_injective hdisj hc₀ h, restPrimes]
  ring

open scoped Classical in
include hdisj hc₀ hv hS in
/-- **The edge summand as a product over the groups**: the memory weight times the lifespan
product after the edge is the product of the unchanged primes' values times per-group factors
of the stored flag and the promotion flag. -/
theorem edge_summand_eq_prod (hB : (bandPrimes x d).card ≤ B) (N t : ℕ)
    (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (St : Finset (Fin K)) (fl : Fin K → Bool) :
    (if MemValid x d Y d₀ u v r B s (toEdge c₀ St fl) then
        ∏ i, memLabelWeight q x d N s.2.2.1 (toEdge c₀ St fl) i else 0) *
      (if (Bn + freshBirths (toEdge c₀ St fl)).Nodup then 1 else 0) *
      lifeProd q N π (t + 1) (edgeTgt s (toEdge c₀ St fl)) (edgeMem s (toEdge c₀ St fl))
        (Bn + freshBirths (toEdge c₀ St fl)) =
    (∏ p ∈ restPrimes s c₀, primeLife q N π p (t + 1) (statusOf s.2.1.1 s.2.2.1 Bn p)) *
      ∏ i, (primeLife q N π (leavePrime s c₀ i) (t + 1)
          (if i ∈ St then .pending (lineOf (leavePrime s c₀ i) s.1.1) else .dead) *
        ((if fl i then (s.2.2.1 (promPart hc₀ i) : ℝ)
          else if c₀.2.2.1 i ∈ Bn then 0 else birthConst q N (c₀.2.2.1 i)) *
          primeLife q N π (c₀.2.2.1 i) (t + 1) .active)) := by
  by_cases hg : EdgeGood (s := s) hc₀ Bn fl
  · have hc := consistent_edgeMem hdisj hc₀ hv hS St hg
    -- the memory restrictions and the distinctness hold
    have hm : MemValid x d Y d₀ u v r B s (toEdge c₀ St fl) := by
      refine ⟨fun i hfi => ⟨promPart hc₀ i, rfl, Nat.one_le_iff_ne_zero.2 ((hg i).1 hfi)⟩,
        fun i _ => (storePart s c₀ i).2, mem_memStates.2 ((memSize_le_card hc).trans hB)⟩
    rw [ite_eq_left hm, ite_eq_left hc.nodup, mul_one, lifeProd,
      prod_bandPrimes_split hdisj hc₀ hv]
    -- the statuses after the edge
    have hrest : ∀ p ∈ restPrimes s c₀, statusOf (edgeTgt s (toEdge c₀ St fl))
        (edgeMem s (toEdge c₀ St fl)) (Bn + freshBirths (toEdge c₀ St fl)) p =
          statusOf s.2.1.1 s.2.2.1 Bn p := by
      intro p hp
      have hp' := (mem_sdiff.1 hp).2
      rw [statusOf_edge hdisj hc₀ hv hS St hg, ite_eq_right fun ⟨i, hi⟩ => hp' (mem_union.2
        (Or.inr (mem_image.2 ⟨i, mem_univ _, hi⟩))), dite_eq_right fun ⟨i, hi⟩ => hp'
        (mem_union.2 (Or.inl (mem_image.2 ⟨i, mem_univ _, hi⟩)))]
    have hleave : ∀ i, statusOf (edgeTgt s (toEdge c₀ St fl))
        (edgeMem s (toEdge c₀ St fl)) (Bn + freshBirths (toEdge c₀ St fl)) (leavePrime s c₀ i) =
          if i ∈ St then .pending (lineOf (leavePrime s c₀ i) s.1.1) else .dead := by
      intro i
      have hb : ∃ j, leavePrime s c₀ j = leavePrime s c₀ i := ⟨i, rfl⟩
      rw [statusOf_edge hdisj hc₀ hv hS St hg, ite_eq_right fun ⟨j, hj⟩ =>
        enterPrime_ne_leavePrime hv j i hj, dite_eq_left hb,
        leavePrime_injective hdisj hb.choose_spec]
    have henter : ∀ i, statusOf (edgeTgt s (toEdge c₀ St fl))
        (edgeMem s (toEdge c₀ St fl)) (Bn + freshBirths (toEdge c₀ St fl)) (c₀.2.2.1 i) =
          .active := fun i => by
      rw [statusOf_edge hdisj hc₀ hv hS St hg, ite_eq_left ⟨i, rfl⟩]
    rw [prod_congr (s₁ := restPrimes s c₀) rfl fun p hp =>
      congrArg (primeLife q N π p (t + 1)) (hrest p hp)]
    simp only [hleave, henter]
    -- the label weights
    have hw : ∀ i, memLabelWeight q x d N s.2.2.1 (toEdge c₀ St fl) i =
        if fl i then (s.2.2.1 (promPart hc₀ i) : ℝ)
        else if c₀.2.2.1 i ∈ Bn then 0 else birthConst q N (c₀.2.2.1 i) := fun i => by
      rw [memLabelWeight_toEdge q hc₀]
      cases hfi : fl i
      · simp [(hg i).2 hfi]
      · rfl
    simp only [hw, prod_mul_distrib]
    ring
  · -- an incompatible flag kills both sides
    simp only [EdgeGood, not_forall] at hg
    obtain ⟨i, hi⟩ := hg
    have hR : (if fl i then (s.2.2.1 (promPart hc₀ i) : ℝ)
        else if c₀.2.2.1 i ∈ Bn then 0 else birthConst q N (c₀.2.2.1 i)) = 0 := by
      cases hfi : fl i
      · have : c₀.2.2.1 i ∈ Bn := by
          by_contra h
          exact hi ⟨fun h' => by simp [hfi] at h', fun _ => h⟩
        simp [this]
      · have : s.2.2.1 (promPart hc₀ i) = 0 := by
          by_contra h
          exact hi ⟨fun _ => h, fun h' => by simp [hfi] at h'⟩
        simp [this]
    refine Eq.trans ?_ (mul_eq_zero_of_right _ (prod_eq_zero (mem_univ i) ?_)).symm
    swap
    · rw [hR, zero_mul, mul_zero]
    by_cases hfi : fl i
    · -- a promotion from an empty particle
      have hm : ¬MemValid x d Y d₀ u v r B s (toEdge c₀ St fl) := by
        rintro ⟨hm, -, -⟩
        obtain ⟨xp, hxp, h1⟩ := hm i hfi
        have : xp = promPart hc₀ i := Subtype.ext hxp
        subst this
        exact hi ⟨fun _ => (Nat.one_le_iff_ne_zero.1 h1), fun h => by simp [hfi] at h⟩
      rw [ite_eq_right hm, zero_mul, zero_mul]
    · -- a fresh label already born
      have hB' : c₀.2.2.1 i ∈ Bn := by
        by_contra h
        exact hi ⟨fun h' => absurd h' hfi, fun _ => h⟩
      have hnd : ¬(Bn + freshBirths (toEdge c₀ St fl)).Nodup := by
        intro hnd
        have h₁ := Multiset.nodup_iff_count_le_one.1 hnd (c₀.2.2.1 i)
        rw [Multiset.count_add, count_freshBirths] at h₁
        have h₂ := Multiset.count_pos.2 hB'
        have h₃ : 0 < (univ.filter fun j => fl j = false ∧ c₀.2.2.1 j = c₀.2.2.1 i).card :=
          card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, by simpa using hfi, rfl⟩⟩
        omega
      rw [ite_eq_right hnd, mul_zero, zero_mul]

open scoped Classical in
include hdisj hc₀ hv hS in
/-- **The edge step**: with an admissible free choice from the post-ghost state at `t < N`,
summed over the stored groups and the promotion flags with distinct fresh labels, the memory
weight times the lifespan product at `t + 1` is the post-ghost lifespan product at `t`. -/
theorem edge_stage (hB : (bandPrimes x d).card ≤ B) {N t : ℕ} (htN : t < N)
    (π : Fin (N + 1) → FreeState x d Y d₀ u v r)
    (hline : ∀ p, pathLines p π t = lineOf p s.1.1)
    (hline' : ∀ p, pathLines p π (t + 1) = lineOf p c₀.2.1.1)
    (hact' : ∀ p, t + 1 ∈ activeSet p π ↔ ∃ i h, edgeTgt s (toEdge₀ c₀) i h = p) :
    ∑ St : Finset (Fin K), ∑ fl : Fin K → Bool,
      (if MemValid x d Y d₀ u v r B s (toEdge c₀ St fl) then
          ∏ i, memLabelWeight q x d N s.2.2.1 (toEdge c₀ St fl) i else 0) *
        (if (Bn + freshBirths (toEdge c₀ St fl)).Nodup then 1 else 0) *
        lifeProd q N π (t + 1) (edgeTgt s (toEdge c₀ St fl)) (edgeMem s (toEdge c₀ St fl))
          (Bn + freshBirths (toEdge c₀ St fl)) =
      postProd q N π t s.2.1.1 s.2.2.1 Bn := by
  set H : Fin K → Bool → ℝ := fun i b => primeLife q N π (leavePrime s c₀ i) (t + 1)
    (if b then .pending (lineOf (leavePrime s c₀ i) s.1.1) else .dead) with hH
  set Λ : Fin K → Bool → ℝ := fun i f => (if f then (s.2.2.1 (promPart hc₀ i) : ℝ)
    else if c₀.2.2.1 i ∈ Bn then 0 else birthConst q N (c₀.2.2.1 i)) *
      primeLife q N π (c₀.2.2.1 i) (t + 1) .active with hΛ
  set R := ∏ p ∈ restPrimes s c₀, primeLife q N π p (t + 1) (statusOf s.2.1.1 s.2.2.1 Bn p)
  -- step: the summand factors over the groups
  have hsum : ∀ St : Finset (Fin K), ∀ fl : Fin K → Bool,
      (if MemValid x d Y d₀ u v r B s (toEdge c₀ St fl) then
          ∏ i, memLabelWeight q x d N s.2.2.1 (toEdge c₀ St fl) i else 0) *
        (if (Bn + freshBirths (toEdge c₀ St fl)).Nodup then 1 else 0) *
        lifeProd q N π (t + 1) (edgeTgt s (toEdge c₀ St fl)) (edgeMem s (toEdge c₀ St fl))
          (Bn + freshBirths (toEdge c₀ St fl)) =
      R * ((∏ i, H i (decide (i ∈ St))) * ∏ i, Λ i (fl i)) := by
    intro St fl
    rw [edge_summand_eq_prod q hdisj hc₀ hv hS hB N t π St fl, ← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    simp only [hH, hΛ, decide_eq_true_eq]
  simp only [hsum, ← mul_sum, ← sum_mul]
  rw [sum_finset_prod_decide, ← Fintype.prod_sum]
  simp only [Fintype.sum_bool]
  -- step: the post-ghost product splits the same way
  rw [postProd, prod_bandPrimes_split hdisj hc₀ hv, mul_assoc]
  have hN : t + 1 ≤ N := htN
  have hA := fun p => activeSet_subset p π
  congr 1
  · -- the other primes are unchanged
    refine prod_congr rfl fun p hp => ?_
    have hp' := (mem_sdiff.1 hp).2
    have hnb : ¬∃ i, leavePrime s c₀ i = p := fun ⟨i, hi⟩ =>
      hp' (mem_union.2 (Or.inl (mem_image.2 ⟨i, mem_univ _, hi⟩)))
    have hna : ¬∃ i, c₀.2.2.1 i = p := fun ⟨i, hi⟩ =>
      hp' (mem_union.2 (Or.inr (mem_image.2 ⟨i, mem_univ _, hi⟩)))
    by_cases hact₀ : ∃ i h, s.2.1.1 i h = p
    · have hstay : ∃ i h, edgeTgt s (toEdge₀ c₀) i h = p := by
        by_contra h
        exact hnb ((leave_iff hv hdisj p).1 ⟨hact₀, h⟩)
      rw [(statusOf_eq_active_iff p).2 hact₀, primePost, primeLife, postValue_stay]
      rw [hline', hline]
      exact (lineOf_eq_of_stay hv (prime_of_mem_bandPrimes (mem_sdiff.1 hp).1) hact₀ hstay).symm
    · have hidle : t + 1 ∉ activeSet p π := fun h =>
        hna ((enter_iff hv p).1 ⟨hact₀, (hact' p).1 h⟩)
      rw [primePost, primeLife, postValue_idle hidle]
      exact fun h => hact₀ ((statusOf_eq_active_iff p).1 h)
  congr 1
  · -- a leaving prime is stored or dropped
    refine prod_congr rfl fun i _ => ?_
    have hst : statusOf s.2.1.1 s.2.2.1 Bn (leavePrime s c₀ i) = .active :=
      (statusOf_eq_active_iff _).2 ⟨i, _, rfl⟩
    rw [hst, primePost, postValue_leave, hline]
    rfl
  · -- an entering prime is promoted or fresh
    refine prod_congr rfl fun i _ => ?_
    have hin : t + 1 ∈ activeSet (c₀.2.2.1 i) π := (hact' _).2 (enterPrime_tgt hv i)
    simp only [hΛ, ite_true, Bool.false_eq_true, ite_false, ← add_mul]
    cases hst : statusOf s.2.1.1 s.2.2.1 Bn (c₀.2.2.1 i) with
    | active => exact absurd ((statusOf_eq_active_iff _).1 hst) (enterPrime_not_act hv i)
    | pending ℓ =>
      obtain ⟨xp, hxp, hS₀⟩ := exists_of_statusOf_eq_pending hst
      have hB' : c₀.2.2.1 i ∈ Bn := by
        have := hS.pend_mem xp hS₀
        rwa [show xp.1.1 = c₀.2.2.1 i from congrArg Prod.fst hxp] at this
      rw [primePost, postValue_enter_pending hin hN, ite_eq_left hB', add_zero, hline']
      congr 1
      by_cases hℓ : ℓ = lineOf (c₀.2.2.1 i) c₀.2.1.1
      · have : promPart hc₀ i = xp := Subtype.ext (by rw [hxp, hℓ]; rfl)
        rw [ite_eq_left hℓ, this, le_antisymm (hS.le_one xp) (Nat.one_le_iff_ne_zero.2 hS₀)]
        simp
      · rw [ite_eq_right hℓ]
        have : s.2.2.1 (promPart hc₀ i) = 0 := by
          by_contra h
          have := hS.pend_unique _ _ h hS₀ (by rw [hxp]; rfl)
          exact hℓ ((congrArg Prod.snd hxp).symm.trans
            (congrArg (fun y : Particle x d => y.1.2) this).symm)
        simp [this]
    | dead =>
      have h0 : s.2.2.1 (promPart hc₀ i) = 0 :=
        eq_zero_of_statusOf (p := c₀.2.2.1 i) hS (fun ℓ h => by rw [hst] at h; cases h) rfl
      rw [primePost, postValue_enter_dead hin, h0, ite_eq_left (mem_of_statusOf_eq_dead hst)]
      simp
    | unborn =>
      have h0 : s.2.2.1 (promPart hc₀ i) = 0 :=
        eq_zero_of_statusOf (p := c₀.2.2.1 i) hS (fun ℓ h => by rw [hst] at h; cases h) rfl
      rw [primePost, postValue_enter_unborn hin, h0,
        ite_eq_right (notMem_of_statusOf_eq_unborn hst)]
      simp only [Nat.cast_zero, zero_add]
      rfl

end Memory


end EdgeStage

end Erdos408.OneSided
