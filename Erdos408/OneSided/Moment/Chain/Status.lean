module

public import Erdos408.OneSided.Moment.Chain.Births
public import Erdos408.OneSided.Moment.Chain.Free
public import Erdos408.OneSided.Moment.Chain.Lifespan

/-!
# The primes of a chain state

With distinct births every prime carries at most one *token*: an active slot or a pending
particle. Along the running form of the history sum (`Moment/Chain/Births.lean`) a chain state
comes with the multiset `Bn` of primes born so far, and each band prime has a `Status`
(`statusOf`): active (in the lists), pending with an anchor (a particle of the memory),
dead (born, but neither active nor pending), or unborn.

* `Consistent act S Bn`: the births so far are distinct, contain the active primes and the
  pending primes, the memory has multiplicities at most one, and no prime is both active and
  pending or pending twice. Consistent memories have size at most the number of band primes
  (`memSize_le_card`).
* The lifespan values of `Moment/Chain/Lifespan.lean` along a path `π`, with lines
  `[z_j]_p`, the defects `η'_j`, the active visits of `p` and `c_p = ((p + 1) b'_p)⁻¹`, are
  `primeLife` (before the ghost) and `primePost` (after it); their products over the band
  primes at the statuses of a state are `lifeProd` and `postProd`.
* `prod_particles_ite`: a product over particles that is trivial except at one designated
  anchor per prime is a product over the band primes.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section Status

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

variable {x d}

open scoped Classical in
/-- The status of the prime `p` in a state with lists `act`, memory `S` and births `Bn`. -/
def statusOf {J : ℕ} (act : Lists K J) (S : Particle x d → ℕ) (Bn : Multiset ℕ) (p : ℕ) :
    Status :=
  if ∃ i h, act i h = p then .active
  else if h : ∃ xp : Particle x d, xp.1.1 = p ∧ S xp ≠ 0 then .pending (Classical.choose h).1.2
  else if p ∈ Bn then .dead else .unborn

/-- A consistent state: distinct births containing the active and the pending primes, and at
most one token per prime. -/
structure Consistent {J : ℕ} (act : Lists K J) (S : Particle x d → ℕ) (Bn : Multiset ℕ) :
    Prop where
  nodup : Bn.Nodup
  act_mem : ∀ i h, act i h ∈ Bn
  le_one : ∀ xp, S xp ≤ 1
  pend_mem : ∀ xp, S xp ≠ 0 → xp.1.1 ∈ Bn
  pend_inactive : ∀ xp, S xp ≠ 0 → ¬∃ i h, act i h = xp.1.1
  pend_unique : ∀ xp xp', S xp ≠ 0 → S xp' ≠ 0 → xp.1.1 = xp'.1.1 → xp = xp'

variable {J : ℕ} {act : Lists K J} {S : Particle x d → ℕ} {Bn : Multiset ℕ}

/-- The status is active exactly for the listed primes. -/
theorem statusOf_eq_active_iff (p : ℕ) :
    statusOf act S Bn p = .active ↔ ∃ i h, act i h = p := by
  classical
  unfold statusOf
  by_cases h₁ : ∃ i h, act i h = p
  · simp [h₁]
  · simp only [h₁, ite_false]
    split_ifs <;> simp

/-- A pending particle gives its prime the pending status with its anchor. -/
theorem statusOf_of_pend (hS : Consistent act S Bn) {xp : Particle x d} (hxp : S xp ≠ 0) :
    statusOf act S Bn xp.1.1 = .pending xp.1.2 := by
  classical
  have h : ∃ xp' : Particle x d, xp'.1.1 = xp.1.1 ∧ S xp' ≠ 0 := ⟨xp, rfl, hxp⟩
  rw [statusOf, ite_eq_right (hS.pend_inactive xp hxp), dite_eq_left h]
  have hs := Classical.choose_spec h
  rw [hS.pend_unique _ _ hs.2 hxp hs.1]

/-- A prime with no token is dead or unborn according to its birth. -/
theorem statusOf_of_none {p : ℕ} (h₁ : ¬∃ i h, act i h = p)
    (h₂ : ∀ xp : Particle x d, xp.1.1 = p → S xp = 0) :
    statusOf act S Bn p = if p ∈ Bn then .dead else .unborn := by
  classical
  have h : ¬∃ xp : Particle x d, xp.1.1 = p ∧ S xp ≠ 0 := fun ⟨xp, hp, hxp⟩ => hxp (h₂ xp hp)
  rw [statusOf, ite_eq_right h₁, dite_eq_right h]

/-- A dead prime is born. -/
theorem mem_of_statusOf_eq_dead {p : ℕ} (h : statusOf act S Bn p = .dead) : p ∈ Bn := by
  classical
  unfold statusOf at h
  split_ifs at h with h₁ h₂ h₃
  exact h₃

/-- An unborn prime is not born. -/
theorem notMem_of_statusOf_eq_unborn {p : ℕ} (h : statusOf act S Bn p = .unborn) : p ∉ Bn := by
  classical
  unfold statusOf at h
  split_ifs at h with h₁ h₂ h₃
  exact h₃

/-- A prime that is not pending has no particle in the memory, unless it is active. -/
theorem eq_zero_of_statusOf {p : ℕ} (hS : Consistent act S Bn)
    (h : ∀ ℓ, statusOf act S Bn p ≠ .pending ℓ)
    {xp : Particle x d} (hxp : xp.1.1 = p) : S xp = 0 := by
  by_contra h0
  exact h _ (hxp ▸ statusOf_of_pend hS h0)

/-- A pending status comes from a pending particle. -/
theorem exists_of_statusOf_eq_pending {p ℓ : ℕ} (h : statusOf act S Bn p = .pending ℓ) :
    ∃ xp : Particle x d, xp.1 = (p, ℓ) ∧ S xp ≠ 0 := by
  classical
  unfold statusOf at h
  split_ifs at h with h₁ h₂
  · cases h
    obtain ⟨hp, hS⟩ := Classical.choose_spec h₂
    exact ⟨_, Prod.ext hp rfl, hS⟩

/-- A prime without a pending particle. -/
theorem statusOf_ne_pending_iff {p : ℕ} :
    (∀ ℓ, statusOf act S Bn p ≠ .pending ℓ) ↔ ∀ xp : Particle x d, xp.1.1 = p → S xp = 0 ∨
      ∃ i h, act i h = p := by
  classical
  constructor
  · intro h xp hp
    by_contra hc
    obtain ⟨hc₁, hc₂⟩ := not_or.1 hc
    have hs : statusOf act S Bn p = .pending (Classical.choose
        (⟨xp, hp, hc₁⟩ : ∃ xp : Particle x d, xp.1.1 = p ∧ S xp ≠ 0)).1.2 := by
      rw [statusOf, ite_eq_right hc₂, dite_eq_left]
    exact h _ hs
  · intro h ℓ hs
    obtain ⟨xp, hxp, hS⟩ := exists_of_statusOf_eq_pending hs
    have hp : xp.1.1 = p := congrArg Prod.fst hxp
    rcases h xp hp with h0 | ha
    · exact hS h0
    · unfold statusOf at hs
      rw [ite_eq_left ha] at hs
      cases hs

/-- The status of `p` depends only on its activity, its particles and its birth. -/
theorem statusOf_congr {J' : ℕ} {act' : Lists K J'} {S' : Particle x d → ℕ} {Bn' : Multiset ℕ}
    (hS : Consistent act S Bn) (hS' : Consistent act' S' Bn') {p : ℕ}
    (ha : (∃ i h, act i h = p) ↔ ∃ i h, act' i h = p)
    (hm : ∀ xp : Particle x d, xp.1.1 = p → S xp = S' xp) (hB : p ∈ Bn ↔ p ∈ Bn') :
    statusOf act S Bn p = statusOf act' S' Bn' p := by
  by_cases h₁ : ∃ i h, act i h = p
  · rw [(statusOf_eq_active_iff p).2 h₁, (statusOf_eq_active_iff p).2 (ha.1 h₁)]
  by_cases h₂ : ∃ xp : Particle x d, xp.1.1 = p ∧ S xp ≠ 0
  · obtain ⟨xp, rfl, hxp⟩ := h₂
    rw [statusOf_of_pend hS hxp, statusOf_of_pend hS' ((hm xp rfl) ▸ hxp)]
  · push Not at h₂
    rw [statusOf_of_none h₁ h₂, statusOf_of_none (fun h => h₁ (ha.2 h))
      fun xp hxp => (hm xp hxp) ▸ h₂ xp hxp]
    simp only [hB]

/-- A particle is a band prime with a line `ℓ ≤ p`. -/
theorem mem_particles {p ℓ : ℕ} : (p, ℓ) ∈ particles x d ↔ p ∈ bandPrimes x d ∧ ℓ ≤ p := by
  simp only [particles, mem_biUnion, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨p', hp', ℓ', hℓ', rfl, rfl⟩
    exact ⟨hp', Nat.lt_succ_iff.1 hℓ'⟩
  · rintro ⟨hp, hℓ⟩
    exact ⟨p, hp, ℓ, Nat.lt_succ_iff.2 hℓ, rfl, rfl⟩

/-- The line `[z]_p` is at most `p`. -/
theorem lineOf_le {p : ℕ} (hp : 0 < p) (z : ℤ × ℤ) : lineOf p z ≤ p := by
  have : NeZero p := ⟨hp.ne'⟩
  unfold lineOf
  split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt _).le

/-- The band primes are primes. -/
theorem prime_of_mem_bandPrimes {p : ℕ} (hp : p ∈ bandPrimes x d) : p.Prime := by
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  exact (mem_filter.1 hpi).2

/-- A consistent memory has at most one particle per band prime. -/
theorem memSize_le_card (hS : Consistent act S Bn) : memSize S ≤ (bandPrimes x d).card := by
  classical
  -- the memory counts its pending particles, which have distinct band primes
  have h₁ : memSize S = (univ.filter fun xp : Particle x d => S xp ≠ 0).card := by
    rw [memSize, card_eq_sum_ones, sum_filter]
    refine sum_congr rfl fun xp _ => ?_
    have := hS.le_one xp
    split_ifs with h <;> omega
  rw [h₁]
  refine card_le_card_of_injOn (fun xp => xp.1.1) (fun xp _ => ?_) fun xp hxp xp' hxp' h =>
    hS.pend_unique xp xp' (mem_filter.1 hxp).2 (mem_filter.1 hxp').2 h
  exact (mem_particles.1 (show (xp.1.1, xp.1.2) ∈ particles x d from xp.2)).1

/-- A product over particles that is trivial except at one designated anchor `g p ≤ p` per
prime is the product over the band primes of its designated values. -/
theorem prod_particles_ite (g : ℕ → ℕ) (hg : ∀ p ∈ bandPrimes x d, g p ≤ p) (F : ℕ → ℝ) :
    ∏ xp : Particle x d, (if xp.1.2 = g xp.1.1 then F xp.1.1 else 1) =
      ∏ p ∈ bandPrimes x d, F p := by
  classical
  rw [prod_coe_sort (particles x d) (fun y : ℕ × ℕ => if y.2 = g y.1 then F y.1 else 1),
    particles, prod_biUnion]
  · refine prod_congr rfl fun p hp => ?_
    rw [prod_image fun a _ b _ h => (Prod.mk.inj h).2]
    simp only
    rw [prod_ite_eq', ite_eq_left (mem_range.2 (Nat.lt_succ_of_le (hg p hp)))]
  · intro p _ p' _ hpp'
    simp only [Function.onFun]
    refine disjoint_left.2 fun y hy hy' => hpp' ?_
    obtain ⟨_, _, rfl⟩ := mem_image.1 hy
    obtain ⟨_, _, h⟩ := mem_image.1 hy'
    exact (congrArg Prod.fst h).symm

/-! ### The lifespan values along a path -/

/-- The birth constant `c_p = ((p + 1) b'_p)⁻¹`. -/
def birthConst (N p : ℕ) : ℝ := (((p : ℝ) + 1) * baseline q N p)⁻¹

variable {Y d₀ u v r}

/-- The lifespan value of `p` along the path `π` at the visit `t`, before the ghost. -/
def primeLife (N : ℕ) (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (p t : ℕ) (st : Status) : ℝ :=
  lifeValue p N (pathLines p π) (dampDefect q N) (activeSet p π) (birthConst q N p) t st

/-- The lifespan value of `p` along the path `π` at the visit `t`, after the ghost. -/
def primePost (N : ℕ) (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (p t : ℕ) (st : Status) : ℝ :=
  postValue p N (pathLines p π) (dampDefect q N) (activeSet p π) (birthConst q N p) t st

/-- The product of the lifespan values at the statuses of a state, before the ghost. -/
def lifeProd (N : ℕ) (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (t : ℕ) {J : ℕ}
    (act : Lists K J) (S : Particle x d → ℕ) (Bn : Multiset ℕ) : ℝ :=
  ∏ p ∈ bandPrimes x d, primeLife q N π p t (statusOf act S Bn p)

/-- The product of the lifespan values at the statuses of a state, after the ghost. -/
def postProd (N : ℕ) (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (t : ℕ) {J : ℕ}
    (act : Lists K J) (S : Particle x d → ℕ) (Bn : Multiset ℕ) : ℝ :=
  ∏ p ∈ bandPrimes x d, primePost q N π p t (statusOf act S Bn p)

/-- The lines along a path are at most the prime. -/
theorem pathLines_le {N : ℕ} (π : Fin (N + 1) → FreeState x d Y d₀ u v r) {p : ℕ} (hp : 0 < p)
    (j : ℕ) : pathLines p π j ≤ p := by
  unfold pathLines
  split_ifs
  · exact lineOf_le hp _
  · exact Nat.zero_le _

end Status

end Erdos408.OneSided
