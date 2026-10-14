import Erdos408.OneSided.Moment.Chain.Induction

/-!
# The memory identity S3

`lineAverage_rootMoment_eq_chain` (`blueprint/one_sided_type_ii.md` §12, PD
`mem:operator-history`): the line average of the root moment is `∏_p b'_p` times the
distinct-birth history sum with the cap `memCap`.

By S1 (`lineAverage_rootMoment_eq`) the line average is
`σ ∑_π [z_0 = z_N = e₁] A⁰-weight(π) ∏_p primeFactor_p(π)`. On the other side
(`distinctSum_eq_sum_distinctFold`) only the initial states at `e₁` with empty memory count.
Such a state is consistent with the births of its initial labels, and the memory identity
along the path (`distinctFold_eq_path` at `t = 0`) turns its running sum into the path sum
from its lists with the lifespan product. At `t = 0` an initial label has value
`∑_ℓ Λ_0(ℓ)` and every other prime is unborn, with value `c_p ∑_ℓ Λ_0(ℓ)`; the initial
measure `∏ ν(act) = σ ∏_{p listed} c_p` supplies the missing `c_p`, and
`b'_p c_p ∑_ℓ Λ_0(ℓ) = primeFactor_p` (`initial_weight_eq`).
-/

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section Identity

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

variable {x d Y d₀ u v r B}

/-- The chain state with the position and the lists of a line-free state, and empty memory. -/
def chainOfFree (a : FreeState x d Y d₀ u v r) : ChainState x d Y d₀ u v r B :=
  (a.1.1, ⟨a.1.2, (freeRootModel d Y d₀ u v r).mem_lists a⟩,
    ⟨0, mem_memStates.2 (by simp [memSize])⟩)

/-- The free part of `chainOfFree a` is `a`. -/
theorem chainFree_chainOfFree (a : FreeState x d Y d₀ u v r) :
    chainFree (chainOfFree (B := B) a) = a :=
  rfl

/-- A prime is an initial birth exactly when it is listed. -/
theorem mem_initBirths {J : ℕ} {act : Lists K J} {p : ℕ} :
    p ∈ initBirths act ↔ ∃ i h, act i h = p := by
  simp only [initBirths, Multiset.mem_sum, mem_univ, true_and, Multiset.mem_singleton]
  exact ⟨fun ⟨i, h, hp⟩ => ⟨i, h, hp.symm⟩, fun ⟨i, h, hp⟩ => ⟨i, h, hp.symm⟩⟩

open scoped Classical in
/-- With disjoint bands, the labels of valid lists are distinct. -/
theorem initBirths_nodup (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {J : ℕ} {act : Lists K J} (hact : act ∈ lists x d J) : (initBirths act).Nodup := by
  refine Multiset.nodup_iff_count_le_one.2 fun p => ?_
  -- the multiplicity of `p` counts the slots with label `p`
  have hcount : Multiset.count p (initBirths act) =
      ∑ i, (univ.filter fun h => act i h = p).card := by
    simp only [initBirths, Multiset.count_sum', Multiset.count_singleton, card_eq_sum_ones,
      sum_filter]
    exact sum_congr rfl fun i _ => sum_congr rfl fun h _ => by simp [eq_comm]
  rw [hcount]
  by_cases hp : ∃ i h, act i h = p
  · obtain ⟨i, h, rfl⟩ := hp
    rw [sum_eq_single i]
    · exact card_le_one.2 fun k hk k' hk' => injective_of_mem_lists hact i
        ((mem_filter.1 hk).2.trans (mem_filter.1 hk').2.symm)
    · intro j _ hji
      refine card_eq_zero.2 (filter_eq_empty_iff.2 fun k _ hk => ?_)
      exact disjoint_left.1 (hdisj j i hji) (mem_band_of_mem_lists hact j k)
        (hk ▸ mem_band_of_mem_lists hact i h)
    · exact fun h' => absurd (mem_univ i) h'
  · push Not at hp
    simp [hp]

/-- The initial state with empty memory is consistent with the births of its labels. -/
theorem consistent_init (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {J : ℕ} {act : Lists K J} (hact : act ∈ lists x d J) :
    Consistent act (0 : Particle x d → ℕ) (initBirths act) :=
  ⟨initBirths_nodup hdisj hact, fun i h => mem_initBirths.2 ⟨i, h, rfl⟩, fun _ => Nat.zero_le _,
    fun _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩

/-- The line-free tail at the first visit is the line factor of S1. -/
theorem lifeTail_zero_eq_lineFactor {N : ℕ} (π : Fin (N + 1) → FreeState x d Y d₀ u v r)
    (p ℓ : ℕ) :
    lifeTail N (pathLines p π) (dampDefect q N) (activeSet p π) 0 ℓ = lineFactor q p π ℓ := by
  rw [lineFactor_eq_prod, lifeTail, ← range_eq_Ico]
  rfl

variable {q} in
/-- The birth weight `ν(p)` of a prime of `𝒫_i` is `V_i⁻¹ c_p`. -/
theorem primeWeight_eq (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {N : ℕ} {i : Fin K} {p : ℕ} (hp : p ∈ band x (d.a i)) :
    primeWeight q x d N p = (harmonicMass (band x (d.a i)))⁻¹ * birthConst q N p := by
  rw [primeWeight, primeMass_eq hdisj hp, birthConst, one_div, mul_assoc, mul_inv]

open scoped Classical in
/-- The product over the slots of a valid list is the product over its labels. -/
theorem prod_slots_eq (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {J : ℕ} {act : Lists K J} (hact : act ∈ lists x d J) (f : ℕ → ℝ) :
    ∏ i, ∏ h, f (act i h) =
      ∏ p ∈ bandPrimes x d, if ∃ i h, act i h = p then f p else 1 := by
  rw [prod_ite, prod_const_one, mul_one, ← Fintype.prod_prod_type' (f := fun i h => f (act i h))]
  -- the slots are in bijection with the listed band primes
  have hinj : Set.InjOn (fun ih : Fin K × Fin (J + 1) => act ih.1 ih.2)
      ((univ : Finset (Fin K × Fin (J + 1))) : Set (Fin K × Fin (J + 1))) := by
    rintro ⟨i, h⟩ - ⟨i', h'⟩ - he
    simp only at he
    have hii : i = i' := by
      by_contra hne
      exact disjoint_left.1 (hdisj i i' hne) (mem_band_of_mem_lists hact i h)
        (he ▸ mem_band_of_mem_lists hact i' h')
    subst hii
    exact Prod.ext rfl (injective_of_mem_lists hact i he)
  have himage : univ.image (fun ih : Fin K × Fin (J + 1) => act ih.1 ih.2) =
      (bandPrimes x d).filter fun p => ∃ i h, act i h = p := by
    ext p
    simp only [mem_image, mem_univ, true_and, mem_filter, Prod.exists]
    constructor
    · rintro ⟨i, h, rfl⟩
      exact ⟨mem_biUnion.2 ⟨i, mem_univ _, mem_band_of_mem_lists hact i h⟩, i, h, rfl⟩
    · rintro ⟨-, i, h, rfl⟩
      exact ⟨i, h, rfl⟩
  rw [← himage, prod_image hinj]

open scoped Classical in
/-- **The initial weight**: for a path starting at the line-free state `a`, the baselines,
the initial measure and the lifespan product at `t = 0` give `σ ∏_p primeFactor_p`. -/
theorem initial_weight_eq (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {N : ℕ}
    (hbig : ∀ p ∈ bandPrimes x d, N < p) (π : Fin (N + 1) → FreeState x d Y d₀ u v r)
    (a : FreeState x d Y d₀ u v r) (hπ : π 0 = a) :
    (∏ p ∈ bandPrimes x d, baseline q N p) *
        chainMeasure q x d Y d₀ u v r B N (chainOfFree a) *
        lifeProd q N π 0 a.1.2 (0 : Particle x d → ℕ) (initBirths a.1.2) =
      stateMass x d *
        ∏ p ∈ bandPrimes x d, primeFactor p N (pathLines p π) (dampDefect q N) (activeSet p π) := by
  have hact := (freeRootModel d Y d₀ u v r).mem_lists a
  -- step: the initial measure is `σ ∏_{p listed} c_p`
  have hmw : memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (0 : Particle x d → ℕ)
      = 1 := by
    simp [memWeight]
  have hμ : chainMeasure q x d Y d₀ u v r B N (chainOfFree a) =
      stateMass x d * ∏ p ∈ bandPrimes x d, if ∃ i h, a.1.2 i h = p then birthConst q N p
        else 1 := by
    have h₁ : ∏ i, ∏ h, primeWeight q x d N (a.1.2 i h) =
        (∏ i, ∏ _h : Fin (padCount x + 1), (harmonicMass (band x (d.a i)))⁻¹) *
          ∏ i, ∏ h, birthConst q N (a.1.2 i h) := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun h _ => primeWeight_eq hdisj (mem_band_of_mem_lists hact i h)
    have h₂ : ∏ i, ∏ _h : Fin (padCount x + 1), (harmonicMass (band x (d.a i)))⁻¹ =
        stateMass x d := by
      simp only [prod_const, card_univ, Fintype.card_fin, stateMass, Data.bandMass,
        prod_pow, prod_inv_distrib]
    rw [chainMeasure, chainOfFree, hmw, mul_one]
    change ∏ i, ∏ h, primeWeight q x d N (a.1.2 i h) = _
    rw [h₁, h₂, prod_slots_eq hdisj hact]
  -- step: the lifespan values at the first visit
  have hlife : ∀ p ∈ bandPrimes x d,
      primeLife q N π p 0 (statusOf a.1.2 (0 : Particle x d → ℕ) (initBirths a.1.2) p) =
      (if ∃ i h, a.1.2 i h = p then 1 else birthConst q N p) *
        ∑ ℓ ∈ range (p + 1), lineFactor q p π ℓ := by
    intro p hp
    have hp₀ : 0 < p := (prime_of_mem_bandPrimes hp).pos
    simp only [← lifeTail_zero_eq_lineFactor q π p]
    by_cases hl : ∃ i h, a.1.2 i h = p
    · have h0 : (0 : ℕ) ∈ activeSet p π := by
        have := mem_activeSet p π 0
        rw [hπ] at this
        exact this.2 hl
      rw [(statusOf_eq_active_iff p).2 hl, ite_eq_left hl, one_mul, primeLife,
        lifeValue_zero_active (fun j _ => pathLines_le π hp₀ j) h0]
    · rw [statusOf_of_none (S := (0 : Particle x d → ℕ)) hl fun _ _ => rfl,
        ite_eq_right (mt mem_initBirths.1 hl),
        ite_eq_right hl, primeLife, lifeValue_zero_unborn]
  rw [hμ, lifeProd, prod_congr rfl hlife,
    show ∀ a b c e : ℝ, a * (b * c) * e = b * (a * c * e) from fun _ _ _ _ => by ring,
    ← prod_mul_distrib, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  -- step: `b'_p c_p ∑_ℓ Λ_0(ℓ) = primeFactor_p`
  have hb := (baseline_mul_pos hq (hbig p hp)).ne'
  have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
  have hb' : baseline q N p ≠ 0 := fun h => hb (by rw [h, mul_zero])
  rw [primeFactor_eq_sum_lineFactor, birthConst]
  split_ifs
  · field_simp
  · field_simp

/-- A chain state with empty memory comes from its free part. -/
theorem chainOfFree_chainFree {s : ChainState x d Y d₀ u v r B} (hs : memSize s.2.2.1 = 0) :
    chainOfFree (chainFree s) = s := by
  refine Prod.ext rfl (Prod.ext rfl (Subtype.ext (funext fun xp => ?_)))
  exact (Nat.eq_zero_of_le_zero (hs ▸ le_memSize s.2.2.1 xp)).symm

open scoped Classical in
/-- The initial states of the history sum are the line-free states with empty memory. -/
theorem sum_chainInit (F G : ChainState x d Y d₀ u v r B → ℂ) :
    ∑ s, F s * chainInit x d Y d₀ u v r B s * G s =
      ∑ a : FreeState x d Y d₀ u v r,
        if a.1.1.1 = (1, 0) then F (chainOfFree a) * G (chainOfFree a) else 0 := by
  symm
  refine sum_bij_ne_zero (fun a _ _ => chainOfFree a) (fun _ _ _ => mem_univ _)
    (fun a _ _ a' _ _ h => by rw [← chainFree_chainOfFree (B := B) a, h, chainFree_chainOfFree])
    (fun s _ hs => ?_) (fun a _ ha => ?_)
  · have hi : s.1.1 = (1, 0) ∧ memSize s.2.2.1 = 0 := by
      by_contra h
      exact hs (by rw [chainInit, ite_eq_right h, mul_zero, zero_mul])
    refine ⟨chainFree s, mem_univ _, ?_, chainOfFree_chainFree hi.2⟩
    rw [ite_eq_left (show (chainFree s).1.1.1 = (1, 0) from hi.1), chainOfFree_chainFree hi.2]
    rw [chainInit, ite_eq_left hi, mul_one] at hs
    exact hs
  · by_cases h : a.1.1.1 = (1, 0)
    · rw [ite_eq_left h, chainInit, ite_eq_left ⟨h, by simp [chainOfFree, memSize]⟩, mul_one]
    · exact absurd (ite_eq_right h) ha

variable (x d Y d₀ u v r) in
/-- **S3, the memory identity**: with disjoint bands, band primes larger than `N`, and bands
of positive mass, the line average of the root moment is `∏_p b'_p` times the distinct-birth
history sum, with `N = 2R` and the cap `B` the number of band primes. -/
theorem lineAverage_rootMoment_eq_chain (hq : 0 < q) (hR : 0 < momentPower x)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hbig : ∀ p ∈ bandPrimes x d, 2 * momentPower x < p)
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) :
    lineAverage x d (rootMoment q A₀ x d Y d₀ u v r) =
      (∏ p ∈ bandPrimes x d, (baseline q (2 * momentPower x) p : ℂ)) *
        distinctSum q A₀ x d Y d₀ u v r (memCap x d) (2 * momentPower x) := by
  classical
  rw [lineAverage_rootMoment_eq hq hR hdisj, distinctSum_eq_sum_distinctFold, sum_chainInit,
    mul_sum]
  set N := 2 * momentPower x with hN
  -- step: group the paths by their first state
  rw [mul_sum, ← sum_fiberwise univ fun π : Fin (N + 1) → FreeState x d Y d₀ u v r => π 0]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : a.1.1.1 = (1, 0)
  swap
  · rw [ite_eq_right ha, mul_zero]
    refine sum_eq_zero fun π hπ => ?_
    rw [(mem_filter.1 hπ).2, ite_eq_right fun h => ha h.1, zero_mul, zero_mul, mul_zero]
  rw [ite_eq_left ha]
  -- step: the memory identity along the path from the initial state
  have hS := consistent_init (x := x) hdisj ((freeRootModel d Y d₀ u v r).mem_lists a)
  have hpath := distinctFold_eq_path q A₀ hq hdisj hV (B := memCap x d) le_rfl hbig N 0
    (zero_add N) (fun _ => a) (chainOfFree a) (initBirths a.1.2) hS
  have hρ : pendingHits x d (chainOfFree (B := memCap x d) a).1.1
      (chainOfFree (B := memCap x d) a).2.2.1 = 0 := sum_eq_zero fun xp _ => by
    simp only [chainOfFree]
    exact ite_self _
  rw [hρ, pow_zero, one_mul] at hpath
  rw [show initBirths (chainOfFree (B := memCap x d) a).2.1.1 = initBirths a.1.2 from rfl, hpath,
    mul_sum, mul_sum]
  -- step: the paths through `a` at the first visit are the paths starting at `a`
  have hset : pathsFrom (fun _ => a) 0 (chainFree (chainOfFree (B := memCap x d) a)) =
      univ.filter fun π : Fin (N + 1) → FreeState x d Y d₀ u v r => π 0 = a := by
    ext π
    rw [mem_pathsFrom, mem_filter, chainFree_chainOfFree]
    simp only [not_lt_zero, false_imp_iff, implies_true, true_and, mem_univ]
    exact ⟨fun h => h 0 rfl, fun h j hj => by rw [show j = 0 from Fin.ext hj, h]⟩
  rw [hset]
  refine sum_congr rfl fun π hπ => ?_
  have hπ0 : π 0 = a := (mem_filter.1 hπ).2
  have hw : weightFrom A₀ π 0 = pathWeight A₀ x d Y d₀ u v r π := by
    rw [weightFrom, filter_true_of_mem fun j _ => Nat.zero_le _, pathWeight]
  have hinit := initial_weight_eq q (B := memCap x d) hq hdisj hbig π a hπ0
  have hend : endInd π = if (π (Fin.last N)).1.1.1 = (1, 0) then (1 : ℂ) else 0 := rfl
  have hinit' := congrArg (fun r : ℝ => (r : ℂ)) hinit
  push_cast at hinit'
  have hl : lifeProd q N π 0 (chainOfFree (B := memCap x d) a).2.1.1
      (chainOfFree (B := memCap x d) a).2.2.1 (initBirths a.1.2) =
      lifeProd q N π 0 a.1.2 (0 : Particle x d → ℕ) (initBirths a.1.2) := rfl
  rw [hw, hend, hπ0, hl]
  by_cases hlast : (π (Fin.last N)).1.1.1 = (1, 0)
  · rw [ite_eq_left ⟨ha, hlast⟩, ite_eq_left hlast]
    linear_combination (pathWeight A₀ x d Y d₀ u v r π) * hinit'.symm
  · rw [ite_eq_right fun h => hlast h.2, ite_eq_right hlast]
    ring

end Identity

end Erdos408.OneSided
