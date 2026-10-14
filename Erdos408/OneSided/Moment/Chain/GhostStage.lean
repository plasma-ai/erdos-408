module

public import Erdos408.OneSided.Moment.Chain.Status

/-!
# The ghost step of the memory identity

One ghost `𝒢_t` on a consistent state, with the `ρ` factors of the two adjacent edges
attributed to the visit: the incoming target factor `ρ^{hits(S, z)}` and the outgoing source
factor `ρ^{hits(S⁺, z)}` (`visitWeight`). Per particle with `h ≤ 1` hits, the weight is
`ρ^h C(h, d) del^d surv^{h - d} (cre ν)^n ρ^{h - d + n}`, which is `ρ`-free
(PD `mem:rho-cancellation`): `q_t` for a surviving hit, `-η'_t` for a deletion, and
`-η'_t c_p` for a creation.

`ghost_stage`: summed over the ghost choices whose new batch is distinct from the earlier
births, the visit weight times the post-ghost lifespan product is the pre-ghost lifespan
product. The proof:

* the admissible choices with distinct births are the choices with `d ≤ h` and
  `n ≤ [hit ∧ unborn]` at every particle (`GhostOK`, `ghostOK_of_valid`, `valid_of_ghostOK`);
  they keep the state consistent (`consistent_ghostMem`);
* on such a choice, the summand is a product over particles (`ghost_summand_eq_prod`), since
  each prime has one designated particle (its pending particle, or else its hitting one)
  whose choice determines its new status;
* the sum of the product is the product of the per-particle sums (`sum_multBox_prod`), and
  each per-particle sum is a ghost identity of `Moment/Chain/Lifespan.lean` (`sum_ghostTerm`).
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}

section GhostStage

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

variable {x d Y d₀ u v r B}

/-- The memory after the ghost choice `g`: `S - D + n`. -/
def ghostMem (S : Particle x d → ℕ) (g : GhostChoice x d) : Particle x d → ℕ :=
  fun xp => S xp - g.1 xp + g.2 xp

/-- The ghost choice of the chain at the visit `t`, as a real product over particles. -/
def ghostProd (N t : ℕ) (z : ℤ × ℤ) (S : Particle x d → ℕ) (g : GhostChoice x d) : ℝ :=
  ∏ xp, ghostFactor (fun xp : Particle x d => primeWeight q x d N xp.1.1)
    (-dampDefect q N t / pendingWeight q) ((1 - dampDefect q N t) / pendingWeight q ^ 2)
    (fun xp : Particle x d => -dampDefect q N t * primeMass x d xp.1.1 / pendingWeight q) xp
    (hitPart (HitsAt x d z) S xp) (g.1 xp) (g.2 xp)

open scoped Classical in
/-- The weight of the visit `t`: the ghost coefficient with the incoming and outgoing pending
factors `ρ^{hits(S, z)}` and `ρ^{hits(S⁺, z)}`. -/
def visitWeight (N t : ℕ) (s : ChainState x d Y d₀ u v r B) (g : GhostChoice x d) : ℝ :=
  if GhostValid (HitsAt x d s.1.1) B s.2.2.1 g then
    pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 * ghostProd q N t s.1.1 s.2.2.1 g *
      pendingWeight q ^ pendingHits x d s.1.1 (ghostMem s.2.2.1 g)
  else 0

/-- The visit weight is the chain ghost coefficient with its two pending factors. -/
theorem visitWeight_eq (N t : ℕ) (s : ChainState x d Y d₀ u v r B) (g : GhostChoice x d) :
    ((visitWeight q N t s g : ℝ) : ℂ) =
      (pendingWeight q : ℂ) ^ pendingHits x d s.1.1 s.2.2.1 *
        chainGhostCoef q x d Y d₀ u v r B N t s g *
        (pendingWeight q : ℂ) ^
          pendingHits x d s.1.1 (chainGhostOut x d Y d₀ u v r B s g).2.2.1 := by
  classical
  by_cases hv : GhostValid (HitsAt x d s.1.1) B s.2.2.1 g
  · rw [visitWeight, ite_eq_left hv, chainGhostCoef, ghostCoef, ite_eq_left hv, chainGhostOut,
      ghostOut, dite_eq_left hv, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_pow]
    rfl
  · rw [visitWeight, ite_eq_right hv, chainGhostCoef, ghostCoef, ite_eq_right hv]
    simp

/-- The memory of the chain after an admissible ghost choice. -/
theorem chainGhostOut_mem {s : ChainState x d Y d₀ u v r B} {g : GhostChoice x d}
    (hv : GhostValid (HitsAt x d s.1.1) B s.2.2.1 g) :
    (chainGhostOut x d Y d₀ u v r B s g).2.2.1 = ghostMem s.2.2.1 g := by
  simp only [chainGhostOut, ghostOut, dite_eq_left hv]
  rfl

/-- The per-particle condition of an admissible ghost choice with distinct new births: at most
the hits are deleted, and only an unborn prime is created, once, at its hitting particle. -/
def GhostOK (z : ℤ × ℤ) (S : Particle x d → ℕ) (Bn : Multiset ℕ) (xp : Particle x d)
    (dd nn : ℕ) : Prop :=
  dd ≤ hitPart (HitsAt x d z) S xp ∧ nn ≤ if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0

open scoped Classical in
/-- The multiplicity of `p` in a batch. -/
theorem count_batchBirths (n : Particle x d → ℕ) (p : ℕ) :
    Multiset.count p (batchBirths n) = ∑ xp : Particle x d, if xp.1.1 = p then n xp else 0 := by
  rw [batchBirths, Multiset.count_sum']
  refine sum_congr rfl fun xp _ => ?_
  rw [Multiset.count_replicate]

/-- `p` is in a batch when one of its particles is created. -/
theorem mem_batchBirths {n : Particle x d → ℕ} {p : ℕ} :
    p ∈ batchBirths n ↔ ∃ xp : Particle x d, xp.1.1 = p ∧ n xp ≠ 0 := by
  simp only [batchBirths, Multiset.mem_sum, mem_univ, true_and, Multiset.mem_replicate]
  exact ⟨fun ⟨xp, h₁, h₂⟩ => ⟨xp, h₂.symm, h₁⟩, fun ⟨xp, h₁, h₂⟩ => ⟨xp, h₂, h₁.symm⟩⟩

/-- Two particles hitting `z` with the same prime are equal. -/
theorem eq_of_hitsAt {z : ℤ × ℤ} {xp xp' : Particle x d} (h : HitsAt x d z xp)
    (h' : HitsAt x d z xp') (hp : xp.1.1 = xp'.1.1) : xp = xp' := by
  refine Subtype.ext (Prod.ext hp ?_)
  rw [← h, ← h', hp]

/-- An admissible ghost choice with distinct new births satisfies the per-particle
conditions. -/
theorem ghostOK_of_valid {z : ℤ × ℤ} {S : Particle x d → ℕ} {Bn : Multiset ℕ}
    {g : GhostChoice x d} (hv : GhostValid (HitsAt x d z) B S g)
    (hnd : (Bn + batchBirths g.2).Nodup)
    (xp : Particle x d) : GhostOK z S Bn xp (g.1 xp) (g.2 xp) := by
  classical
  refine ⟨hv.1 xp, ?_⟩
  by_cases hh : HitsAt x d z xp
  · -- the prime of `xp` appears `n(xp)` times in the batchBirths
    have hc := (Multiset.nodup_iff_count_le_one.1 hnd) xp.1.1
    have hb : g.2 xp ≤ Multiset.count xp.1.1 (batchBirths g.2) := by
      rw [count_batchBirths]
      exact le_of_eq_of_le (by simp) (single_le_sum (f := fun y : Particle x d =>
        if y.1.1 = xp.1.1 then g.2 y else 0) (fun _ _ => Nat.zero_le _) (mem_univ xp))
    rw [Multiset.count_add] at hc
    by_cases hB : xp.1.1 ∈ Bn
    · rw [ite_eq_right fun h => h.2 hB]
      have := Multiset.one_le_count_iff_mem.2 hB
      omega
    · rw [ite_eq_left ⟨hh, hB⟩]
      omega
  · rw [hv.2.1 xp hh]
    exact Nat.zero_le _

variable {J : ℕ} {act : Lists K J}

/-- On a consistent state, the per-particle conditions keep the state consistent. -/
theorem consistent_ghostMem {z : ℤ × ℤ} {S : Particle x d → ℕ} {Bn : Multiset ℕ}
    (hS : Consistent act S Bn) {g : GhostChoice x d}
    (hok : ∀ xp, GhostOK z S Bn xp (g.1 xp) (g.2 xp)) :
    Consistent act (ghostMem S g) (Bn + batchBirths g.2) := by
  classical
  -- a created particle hits and has an unborn prime
  have hcre : ∀ xp, g.2 xp ≠ 0 → HitsAt x d z xp ∧ xp.1.1 ∉ Bn ∧ g.2 xp = 1 := by
    intro xp hn
    have h := (hok xp).2
    by_cases hc : HitsAt x d z xp ∧ xp.1.1 ∉ Bn
    · rw [ite_eq_left hc] at h
      exact ⟨hc.1, hc.2, by omega⟩
    · rw [ite_eq_right hc] at h
      omega
  have hnew : ∀ xp, ghostMem S g xp ≠ 0 → S xp ≠ 0 ∨ g.2 xp ≠ 0 := by
    intro xp h
    by_contra hc
    push Not at hc
    exact h (by simp [ghostMem, hc.1, hc.2])
  -- the new births are distinct and new
  have hnd : (Bn + batchBirths g.2).Nodup := by
    refine Multiset.nodup_iff_count_le_one.2 fun p => ?_
    have hterm : ∀ xp : Particle x d, (if xp.1.1 = p then g.2 xp else 0) ≤
        if xp.1.1 = p ∧ HitsAt x d z xp ∧ p ∉ Bn then 1 else 0 := by
      intro xp
      by_cases hp : xp.1.1 = p
      · subst hp
        have h := (hok xp).2
        simp only [true_and, ite_true]
        exact h
      · simp [hp]
    have hcard : (univ.filter fun xp : Particle x d =>
        xp.1.1 = p ∧ HitsAt x d z xp ∧ p ∉ Bn).card ≤ if p ∈ Bn then 0 else 1 := by
      split_ifs with hp
      · exact (card_eq_zero.2 (filter_eq_empty_iff.2 fun xp _ h => h.2.2 hp)).le
      · exact card_le_one.2 fun xp hxp xp' hxp' => by
          obtain ⟨-, h₁, h₂, -⟩ := mem_filter.1 hxp
          obtain ⟨-, h₁', h₂', -⟩ := mem_filter.1 hxp'
          exact eq_of_hitsAt h₂ h₂' (h₁.trans h₁'.symm)
    have hb : Multiset.count p (batchBirths g.2) ≤ if p ∈ Bn then 0 else 1 := by
      rw [count_batchBirths]
      refine le_trans (sum_le_sum fun xp _ => hterm xp) (le_of_eq_of_le ?_ hcard)
      rw [card_eq_sum_ones, sum_filter]
    have h₁ := Multiset.nodup_iff_count_le_one.1 hS.nodup p
    rw [Multiset.count_add]
    split_ifs at hb with hp
    · omega
    · rw [Multiset.count_eq_zero.2 hp]
      omega
  refine ⟨hnd, fun i h => Multiset.mem_add.2 (Or.inl (hS.act_mem i h)), fun xp => ?_,
    fun xp h => ?_, fun xp h => ?_, fun xp xp' h h' hp => ?_⟩
  · -- multiplicities stay at most one
    by_cases hn : g.2 xp = 0
    · have := hS.le_one xp
      simp only [ghostMem, hn, add_zero]
      omega
    · obtain ⟨-, hB, h1⟩ := hcre xp hn
      have hS0 : S xp = 0 := by
        by_contra h0
        exact hB (hS.pend_mem xp h0)
      simp [ghostMem, hS0, h1]
  · rcases hnew xp h with h₀ | h₀
    · exact Multiset.mem_add.2 (Or.inl (hS.pend_mem xp h₀))
    · exact Multiset.mem_add.2 (Or.inr (mem_batchBirths.2 ⟨xp, rfl, h₀⟩))
  · rcases hnew xp h with h₀ | h₀
    · exact hS.pend_inactive xp h₀
    · rintro ⟨i, k, hk⟩
      exact (hcre xp h₀).2.1 (hk ▸ hS.act_mem i k)
  · rcases hnew xp h with h₀ | h₀ <;> rcases hnew xp' h' with h₀' | h₀'
    · exact hS.pend_unique xp xp' h₀ h₀' hp
    · exact absurd (hp ▸ hS.pend_mem xp h₀) (hcre xp' h₀').2.1
    · exact absurd (hp.symm ▸ hS.pend_mem xp' h₀') (hcre xp h₀).2.1
    · exact eq_of_hitsAt (hcre xp h₀).1 (hcre xp' h₀').1 hp

/-- The per-particle conditions on a consistent state give an admissible ghost choice with
distinct new births. -/
theorem valid_of_ghostOK {z : ℤ × ℤ} {S : Particle x d → ℕ} {Bn : Multiset ℕ}
    (hS : Consistent act S Bn) (hB : (bandPrimes x d).card ≤ B) {g : GhostChoice x d}
    (hok : ∀ xp, GhostOK z S Bn xp (g.1 xp) (g.2 xp)) :
    GhostValid (HitsAt x d z) B S g ∧ (Bn + batchBirths g.2).Nodup := by
  have hc := consistent_ghostMem hS hok
  refine ⟨⟨fun xp => (hok xp).1, fun xp hh => ?_, (memSize_le_card hc).trans hB⟩, hc.nodup⟩
  have := (hok xp).2
  rw [ite_eq_right fun h => hh h.1] at this
  omega

/-! ### Designated particles -/

/-- The designated anchor of `p`: its pending anchor, or else its line at `z`. -/
def desLine (z : ℤ × ℤ) (act : Lists K J) (S : Particle x d → ℕ) (Bn : Multiset ℕ) (p : ℕ) : ℕ :=
  match statusOf act S Bn p with
  | .pending ℓ => ℓ
  | _ => lineOf p z

/-- The status of a prime after the choice `(dd, nn)` at its designated particle. -/
def localStatus (st : Status) (dd nn ℓh : ℕ) : Status :=
  match st with
  | .pending ℓ => if dd = 0 then .pending ℓ else .dead
  | .unborn => if nn = 0 then .unborn else .pending ℓh
  | .active => .active
  | .dead => .dead

/-- A function on particles, extended by zero to all pairs. -/
def extendParticle (f : Particle x d → ℕ) (y : ℕ × ℕ) : ℕ :=
  if h : y ∈ particles x d then f ⟨y, h⟩ else 0

/-- The extension agrees with the function on particles. -/
theorem extendParticle_val (f : Particle x d → ℕ) (xp : Particle x d) :
    extendParticle f xp.1 = f xp := by
  rw [extendParticle, dite_eq_left xp.2]

/-- The designated anchor is at most the prime. -/
theorem desLine_le (z : ℤ × ℤ) (S : Particle x d → ℕ) (Bn : Multiset ℕ) {p : ℕ}
    (hp : p ∈ bandPrimes x d) : desLine z act S Bn p ≤ p := by
  unfold desLine
  split
  · next ℓ h =>
    obtain ⟨xp, hxp, -⟩ := exists_of_statusOf_eq_pending h
    have := (mem_particles.1 (show (xp.1.1, xp.1.2) ∈ particles x d from xp.2)).2
    rw [hxp] at this
    exact this
  · exact lineOf_le (prime_of_mem_bandPrimes hp).pos z

/-- A particle with nonzero memory is designated. -/
theorem desLine_of_pend {S : Particle x d → ℕ} {Bn : Multiset ℕ} (hS : Consistent act S Bn)
    (z : ℤ × ℤ) {xp : Particle x d} (h : S xp ≠ 0) : desLine z act S Bn xp.1.1 = xp.1.2 := by
  rw [desLine, statusOf_of_pend hS h]

/-- The status after the ghost is the local status of the designated particle. -/
theorem statusOf_ghostMem {z : ℤ × ℤ} {S : Particle x d → ℕ} {Bn : Multiset ℕ}
    (hS : Consistent act S Bn) {g : GhostChoice x d}
    (hok : ∀ xp, GhostOK z S Bn xp (g.1 xp) (g.2 xp)) {p : ℕ} (hp : p ∈ bandPrimes x d) :
    statusOf act (ghostMem S g) (Bn + batchBirths g.2) p =
      localStatus (statusOf act S Bn p) (extendParticle g.1 (p, desLine z act S Bn p))
        (extendParticle g.2 (p, desLine z act S Bn p)) (lineOf p z) := by
  classical
  have hc := consistent_ghostMem hS hok
  -- a particle of a born prime is not created
  have hn₀ : ∀ xp : Particle x d, xp.1.1 ∈ Bn → g.2 xp = 0 := fun xp hB => by
    have := (hok xp).2
    rw [ite_eq_right fun h => h.2 hB] at this
    omega
  -- a particle outside the memory is not deleted
  have hd₀ : ∀ xp : Particle x d, S xp = 0 → g.1 xp = 0 := fun xp h0 => by
    have := (hok xp).1
    simp only [hitPart, h0, ite_self] at this
    omega
  cases hst : statusOf act S Bn p with
  | active =>
    rw [localStatus]
    exact (statusOf_eq_active_iff p).2 ((statusOf_eq_active_iff p).1 hst)
  | pending ℓ =>
    obtain ⟨xp, hxp, hS₀⟩ := exists_of_statusOf_eq_pending hst
    have hp' : xp.1.1 = p := congrArg Prod.fst hxp
    have hℓ : desLine z act S Bn p = ℓ := by rw [desLine, hst]
    have hext : ∀ f : Particle x d → ℕ, extendParticle f (p, desLine z act S Bn p) = f xp :=
      fun f => by
      rw [hℓ, ← hxp, extendParticle_val]
    simp only [localStatus, hext]
    have hB : p ∈ Bn := hp' ▸ hS.pend_mem xp hS₀
    by_cases hd : g.1 xp = 0
    · rw [ite_eq_left hd]
      have h1 : ghostMem S g xp ≠ 0 := by simp [ghostMem, hd, hS₀]
      rw [← hp', statusOf_of_pend hc h1, show xp.1.2 = ℓ from congrArg Prod.snd hxp]
    · rw [ite_eq_right hd]
      rw [statusOf_of_none (fun ha => hS.pend_inactive xp hS₀ (hp' ▸ ha)) fun y hy => ?_,
        ite_eq_left (Multiset.mem_add.2 (Or.inl hB))]
      by_cases hyx : y = xp
      · subst hyx
        have := hS.le_one y
        have := (hok y).1
        simp only [hitPart] at this
        simp only [ghostMem, hn₀ y (hy ▸ hB)]
        split_ifs at this <;> omega
      · have hy0 : S y = 0 := by
          by_contra h
          exact hyx (hS.pend_unique y xp h hS₀ (hy.trans hp'.symm))
        simp [ghostMem, hy0, hd₀ y hy0, hn₀ y (hy ▸ hB)]
  | dead | unborn =>
    -- a prime without a token
    have hna : ¬∃ i h, act i h = p := fun ha => by
      rw [(statusOf_eq_active_iff p).2 ha] at hst
      cases hst
    have hnp : ∀ y : Particle x d, y.1.1 = p → S y = 0 := fun y hy =>
      ((statusOf_ne_pending_iff.1 (fun ℓ h => by rw [hst] at h; cases h)) y hy).resolve_right hna
    have hsn := statusOf_of_none (Bn := Bn) hna hnp
    rw [hst] at hsn
    first
    | -- the dead case
      have hB : p ∈ Bn := by
        by_contra hB
        rw [ite_eq_right hB] at hsn
        cases hsn
      rw [localStatus, statusOf_of_none hna fun y hy => ?_,
        ite_eq_left (Multiset.mem_add.2 (Or.inl hB))]
      simp [ghostMem, hnp y hy, hd₀ y (hnp y hy), hn₀ y (hy ▸ hB)]
    | -- the unborn case: only the hitting particle can be created
      have hB : p ∉ Bn := by
        intro hB
        rw [ite_eq_left hB] at hsn
        cases hsn
      have hℓ : desLine z act S Bn p = lineOf p z := by rw [desLine, hst]
      have hmem : (p, lineOf p z) ∈ particles x d :=
        mem_particles.2 ⟨hp, lineOf_le (prime_of_mem_bandPrimes hp).pos z⟩
      set y₀ : Particle x d := ⟨(p, lineOf p z), hmem⟩
      have hext : ∀ f : Particle x d → ℕ, extendParticle f (p, desLine z act S Bn p) = f y₀ :=
        fun f => by
        rw [hℓ, extendParticle, dite_eq_left hmem]
      have hy : ∀ y : Particle x d, y.1.1 = p → y ≠ y₀ → g.2 y = 0 := fun y hy hne => by
        have := (hok y).2
        rw [ite_eq_right fun h => hne (eq_of_hitsAt h.1 (show HitsAt x d z y₀ from rfl) hy)] at this
        omega
      simp only [localStatus, hext]
      by_cases hn : g.2 y₀ = 0
      · rw [ite_eq_left hn, statusOf_of_none hna fun y hy' => ?_, ite_eq_right ?_]
        · rw [Multiset.mem_add, not_or, mem_batchBirths]
          refine ⟨hB, fun ⟨y, hy', hny⟩ => hny ?_⟩
          by_cases hyy : y = y₀
          · exact hyy ▸ hn
          · exact hy y hy' hyy
        · by_cases hyy : y = y₀
          · subst hyy
            simp [ghostMem, hnp _ hy', hn]
          · simp [ghostMem, hnp y hy', hy y hy' hyy]
      · rw [ite_eq_right hn]
        have h1 : ghostMem S g y₀ ≠ 0 := by simp [ghostMem, hn]
        exact statusOf_of_pend hc h1

/-! ### The ghost step as a product over particles -/

/-- The `ρ`-normalized ghost weight of one particle: `ρ^h C(h, d) del^d surv^{h-d} (cre ν)^n /
n! ρ^{h - d + n}`. -/
def ghostWeight (N t : ℕ) (z : ℤ × ℤ) (S : Particle x d → ℕ) (xp : Particle x d) (dd nn : ℕ) :
    ℝ :=
  pendingWeight q ^ hitPart (HitsAt x d z) S xp *
    ghostFactor (fun xp : Particle x d => primeWeight q x d N xp.1.1)
      (-dampDefect q N t / pendingWeight q) ((1 - dampDefect q N t) / pendingWeight q ^ 2)
      (fun xp : Particle x d => -dampDefect q N t * primeMass x d xp.1.1 / pendingWeight q) xp
      (hitPart (HitsAt x d z) S xp) dd nn *
    pendingWeight q ^ (hitPart (HitsAt x d z) S xp - dd + nn)

open scoped Classical in
/-- The summand of the ghost step at one particle: its normalized weight times, at the
designated particle of its prime, the post-ghost lifespan value of the new status. -/
def ghostTerm (N : ℕ) (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (t : ℕ) (z : ℤ × ℤ)
    (act : Lists K J) (S : Particle x d → ℕ) (Bn : Multiset ℕ) (xp : Particle x d) (dd nn : ℕ) :
    ℝ :=
  if GhostOK z S Bn xp dd nn then
    ghostWeight q N t z S xp dd nn *
      if xp.1.2 = desLine z act S Bn xp.1.1 then
        primePost q N π xp.1.1 t (localStatus (statusOf act S Bn xp.1.1) dd nn (lineOf xp.1.1 z))
      else 1
  else 0

/-- Under the per-particle conditions, the hits after the ghost are `h - d + n`. -/
theorem hitPart_ghostMem {z : ℤ × ℤ} {S : Particle x d → ℕ} {Bn : Multiset ℕ}
    {g : GhostChoice x d} {xp : Particle x d} (hok : GhostOK z S Bn xp (g.1 xp) (g.2 xp)) :
    hitPart (HitsAt x d z) (ghostMem S g) xp = hitPart (HitsAt x d z) S xp - g.1 xp + g.2 xp := by
  classical
  have h₂ := hok.2
  by_cases hh : HitsAt x d z xp
  · simp only [hitPart, hh, ite_true, ghostMem]
  · have h₁ := hok.1
    simp only [hitPart, hh, ite_false] at h₁ ⊢
    rw [ite_eq_right fun h => hh h.1] at h₂
    omega

open scoped Classical in
/-- The summand of the ghost step is the product of the per-particle summands. -/
theorem ghost_summand_eq_prod (hB : (bandPrimes x d).card ≤ B) (N t : ℕ)
    (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (s : ChainState x d Y d₀ u v r B)
    {Bn : Multiset ℕ} (hS : Consistent s.2.1.1 s.2.2.1 Bn) (g : GhostChoice x d) :
    visitWeight q N t s g * (if (Bn + batchBirths g.2).Nodup then 1 else 0) *
        postProd q N π t s.2.1.1 (ghostMem s.2.2.1 g) (Bn + batchBirths g.2) =
      ∏ xp, ghostTerm q N π t s.1.1 s.2.1.1 s.2.2.1 Bn xp (g.1 xp) (g.2 xp) := by
  by_cases hok : ∀ xp, GhostOK s.1.1 s.2.2.1 Bn xp (g.1 xp) (g.2 xp)
  · obtain ⟨hv, hnd⟩ := valid_of_ghostOK hS hB hok
    rw [visitWeight, ite_eq_left hv, ite_eq_left hnd, mul_one]
    simp only [ghostTerm, ite_eq_left (hok _)]
    rw [prod_mul_distrib]
    congr 1
    · -- the pending factors distribute over the particles
      have h₁ : pendingHits x d s.1.1 s.2.2.1 = ∑ xp, hitPart (HitsAt x d s.1.1) s.2.2.1 xp := rfl
      have h₂ : pendingHits x d s.1.1 (ghostMem s.2.2.1 g) =
          ∑ xp, (hitPart (HitsAt x d s.1.1) s.2.2.1 xp - g.1 xp + g.2 xp) := by
        change ∑ xp, hitPart (HitsAt x d s.1.1) (ghostMem s.2.2.1 g) xp = _
        exact sum_congr rfl fun xp _ => hitPart_ghostMem (hok xp)
      rw [h₁, h₂, ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum, ghostProd, ← prod_mul_distrib,
        ← prod_mul_distrib]
      rfl
    · -- the new statuses are read off the designated particles
      set F : ℕ → ℝ := fun p => primePost q N π p t (localStatus (statusOf s.2.1.1 s.2.2.1 Bn p)
        (extendParticle g.1 (p, desLine s.1.1 s.2.1.1 s.2.2.1 Bn p))
        (extendParticle g.2 (p, desLine s.1.1 s.2.1.1 s.2.2.1 Bn p)) (lineOf p s.1.1))
      have hR : ∀ xp : Particle x d, (if xp.1.2 = desLine s.1.1 s.2.1.1 s.2.2.1 Bn xp.1.1 then
          primePost q N π xp.1.1 t (localStatus (statusOf s.2.1.1 s.2.2.1 Bn xp.1.1) (g.1 xp)
            (g.2 xp) (lineOf xp.1.1 s.1.1)) else 1) =
          if xp.1.2 = desLine s.1.1 s.2.1.1 s.2.2.1 Bn xp.1.1 then F xp.1.1 else 1 := by
        intro xp
        by_cases h : xp.1.2 = desLine s.1.1 s.2.1.1 s.2.2.1 Bn xp.1.1
        · have hx : (xp.1.1, desLine s.1.1 s.2.1.1 s.2.2.1 Bn xp.1.1) = xp.1 := Prod.ext rfl h.symm
          simp only [ite_eq_left h, F, hx, extendParticle_val]
        · simp only [ite_eq_right h]
      rw [prod_congr rfl fun xp _ => hR xp, postProd, prod_particles_ite _
        (fun p hp => desLine_le s.1.1 s.2.2.1 Bn hp)]
      exact prod_congr rfl fun p hp => by rw [statusOf_ghostMem hS hok hp]
  · push Not at hok
    obtain ⟨xp, hxp⟩ := hok
    rw [prod_eq_zero (mem_univ xp) (by rw [ghostTerm, ite_eq_right hxp])]
    by_cases hv : GhostValid (HitsAt x d s.1.1) B s.2.2.1 g
    · by_cases hnd : (Bn + batchBirths g.2).Nodup
      · exact absurd (ghostOK_of_valid hv hnd xp) hxp
      · rw [ite_eq_right hnd, mul_zero, zero_mul]
    · rw [visitWeight, ite_eq_right hv, zero_mul, zero_mul]

/-! ### The per-particle sums -/

section Weights

variable {N t : ℕ} {z : ℤ × ℤ} {S : Particle x d → ℕ} {xp : Particle x d}

/-- A particle without hits that is neither deleted nor created has weight `1`. -/
theorem ghostWeight_idle (h : hitPart (HitsAt x d z) S xp = 0) :
    ghostWeight q N t z S xp 0 0 = 1 := by
  simp [ghostWeight, ghostFactor, h]

/-- A surviving pending hit has weight `q_t = 1 - η'_t` (PD `mem:rho-cancellation`). -/
theorem ghostWeight_survive (hq : 0 < q) (h : hitPart (HitsAt x d z) S xp = 1) :
    ghostWeight q N t z S xp 0 0 = 1 - dampDefect q N t := by
  have hρ : pendingWeight q ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  simp only [ghostWeight, ghostFactor, h]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, Nat.sub_zero, pow_one,
    Nat.factorial_zero, div_one, add_zero]
  field_simp

/-- A deleted pending hit has weight `-η'_t`. -/
theorem ghostWeight_delete (hq : 0 < q) (h : hitPart (HitsAt x d z) S xp = 1) :
    ghostWeight q N t z S xp 1 0 = -dampDefect q N t := by
  have hρ : pendingWeight q ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  simp only [ghostWeight, ghostFactor, h]
  field_simp
  simp

/-- A created particle has weight `-η'_t c_p`. -/
theorem ghostWeight_create (hq : 0 < q) (hV : primeMass x d xp.1.1 ≠ 0)
    (h : hitPart (HitsAt x d z) S xp = 0) :
    ghostWeight q N t z S xp 0 1 = -dampDefect q N t * birthConst q N xp.1.1 := by
  have hρ : pendingWeight q ≠ 0 := (Real.rpow_pos_of_pos hq _).ne'
  simp only [ghostWeight, ghostFactor, h, primeWeight, birthConst, one_div, mul_inv]
  field_simp
  simp

end Weights

open scoped Classical in
/-- `ghostTerm` with its hits and its creation bound evaluated. -/
theorem ghostTerm_eq {N : ℕ} {π : Fin (N + 1) → FreeState x d Y d₀ u v r} {t : ℕ} {z : ℤ × ℤ}
    {S : Particle x d → ℕ} {Bn : Multiset ℕ} {xp : Particle x d} {hh mm : ℕ}
    (hh_eq : hitPart (HitsAt x d z) S xp = hh)
    (hm_eq : (if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0) = mm) (dd nn : ℕ) :
    ghostTerm q N π t z act S Bn xp dd nn =
      if dd ≤ hh ∧ nn ≤ mm then
        ghostWeight q N t z S xp dd nn *
          if xp.1.2 = desLine z act S Bn xp.1.1 then
            primePost q N π xp.1.1 t
              (localStatus (statusOf act S Bn xp.1.1) dd nn (lineOf xp.1.1 z))
          else 1
      else 0 := by
  simp only [ghostTerm, GhostOK, hh_eq, hm_eq]

open scoped Classical in
/-- **The per-particle ghost sum**: at the designated particle of its prime, the sum over
the ghost choices is the pre-ghost lifespan value; at any other particle it is `1`. -/
theorem sum_ghostTerm (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (hB : (bandPrimes x d).card ≤ B) {N t : ℕ}
    (ht : t ≤ N) (π : Fin (N + 1) → FreeState x d Y d₀ u v r) {z : ℤ × ℤ}
    {S : Particle x d → ℕ} {Bn : Multiset ℕ} (hS : Consistent act S Bn)
    (hline : ∀ p, pathLines p π t = lineOf p z)
    (hact : ∀ p, t ∈ activeSet p π ↔ ∃ i h, act i h = p) (xp : Particle x d) :
    ∑ dd ∈ range (B + 1), ∑ nn ∈ range (B + 1), ghostTerm q N π t z act S Bn xp dd nn =
      if xp.1.2 = desLine z act S Bn xp.1.1 then
        primeLife q N π xp.1.1 t (statusOf act S Bn xp.1.1)
      else 1 := by
  have hp : xp.1.1 ∈ bandPrimes x d :=
    (mem_particles.1 (show (xp.1.1, xp.1.2) ∈ particles x d from xp.2)).1
  have hp₀ : 0 < xp.1.1 := (prime_of_mem_bandPrimes hp).pos
  have hB₁ : 1 ≤ B := (card_pos.2 ⟨xp.1.1, hp⟩).trans_le hB
  have hhle : hitPart (HitsAt x d z) S xp ≤ 1 := by
    unfold hitPart
    split_ifs
    · exact hS.le_one xp
    · exact Nat.zero_le _
  have hmle : (if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0) ≤ 1 := by split_ifs <;> omega
  -- step: only the choices `d, n ≤ 1` contribute
  have hsub : range 2 ⊆ range (B + 1) := range_subset_range.2 (by omega)
  have hzero : ∀ dd nn, (2 ≤ dd ∨ 2 ≤ nn) → ghostTerm q N π t z act S Bn xp dd nn = 0 := by
    intro dd nn h
    refine ite_eq_right fun hok => ?_
    have := hok.1
    have := hok.2
    omega
  have hsum : ∑ dd ∈ range (B + 1), ∑ nn ∈ range (B + 1), ghostTerm q N π t z act S Bn xp dd nn =
      ∑ dd ∈ range 2, ∑ nn ∈ range 2, ghostTerm q N π t z act S Bn xp dd nn := by
    rw [← sum_subset hsub fun dd _ hdd => sum_eq_zero fun nn _ => hzero dd nn
      (Or.inl (by simp at hdd; omega))]
    refine sum_congr rfl fun dd _ => (sum_subset hsub fun nn _ hnn => hzero dd nn
      (Or.inr (by simp at hnn; omega))).symm
  rw [hsum]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  -- the prime's activity at `t` and its mass
  have hVp : primeMass x d xp.1.1 ≠ 0 := by
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    rw [primeMass_eq hdisj hpi]
    exact (hV i).ne'
  have hLp : ∀ j ≤ N, pathLines xp.1.1 π j ≤ xp.1.1 := fun j _ => pathLines_le π hp₀ j
  have hA := activeSet_subset xp.1.1 π
  by_cases hdes : xp.1.2 = desLine z act S Bn xp.1.1
  · rw [ite_eq_left hdes]
    cases hst : statusOf act S Bn xp.1.1 with
    | active =>
      have ha := (statusOf_eq_active_iff xp.1.1).1 hst
      have hS₀ : S xp = 0 := by
        by_contra h
        exact hS.pend_inactive xp h ha
      obtain ⟨i, k, hk⟩ := ha
      have hBp : xp.1.1 ∈ Bn := hk ▸ hS.act_mem i k
      have hh₀ : hitPart (HitsAt x d z) S xp = 0 := by simp [hitPart, hS₀]
      have hm₀ : (if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0) = 0 :=
        ite_eq_right fun h => h.2 hBp
      simp only [ghostTerm_eq q hh₀ hm₀, ite_eq_left hdes, hst, localStatus, ghostWeight_idle q hh₀]
      norm_num
      exact (lifeValue_active ((hact xp.1.1).2 ⟨i, k, hk⟩) ht).symm
    | dead =>
      have hS₀ : S xp = 0 := eq_zero_of_statusOf hS (fun ℓ h => by rw [hst] at h; cases h) rfl
      have hBp := mem_of_statusOf_eq_dead hst
      have hna : t ∉ activeSet xp.1.1 π := fun h => by
        rw [(statusOf_eq_active_iff xp.1.1).2 ((hact xp.1.1).1 h)] at hst
        cases hst
      have hh₀ : hitPart (HitsAt x d z) S xp = 0 := by simp [hitPart, hS₀]
      have hm₀ : (if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0) = 0 :=
        ite_eq_right fun h => h.2 hBp
      simp only [ghostTerm_eq q hh₀ hm₀, ite_eq_left hdes, hst, localStatus, ghostWeight_idle q hh₀]
      norm_num
      exact (lifeValue_dead hna).symm
    | pending ℓ =>
      obtain ⟨xp', hxp', hS'⟩ := exists_of_statusOf_eq_pending hst
      have hℓ : desLine z act S Bn xp.1.1 = ℓ := by rw [desLine, hst]
      have hxx : xp' = xp := Subtype.ext (hxp'.trans (Prod.ext rfl (hdes.trans hℓ).symm))
      rw [hxx] at hS' hxp'
      have hS₁ : S xp = 1 := le_antisymm (hS.le_one xp) (Nat.one_le_iff_ne_zero.2 hS')
      have hBp : xp.1.1 ∈ Bn := hS.pend_mem xp hS'
      have hna : t ∉ activeSet xp.1.1 π := fun h => by
        rw [(statusOf_eq_active_iff xp.1.1).2 ((hact xp.1.1).1 h)] at hst
        cases hst
      have hm₀ : (if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0) = 0 :=
        ite_eq_right fun h => h.2 hBp
      have hℓ' : xp.1.2 = ℓ := congrArg Prod.snd hxp'
      by_cases hhit : HitsAt x d z xp
      · have hh₁ : hitPart (HitsAt x d z) S xp = 1 := by simp [hitPart, hhit, hS₁]
        have hLt : pathLines xp.1.1 π t = ℓ := by rw [hline, ← hℓ']; exact hhit
        simp only [ghostTerm_eq q hh₁ hm₀, ite_eq_left hdes, hst, localStatus,
          ghostWeight_survive q hq hh₁, ghostWeight_delete q hq hh₁]
        norm_num
        rw [primeLife, primePost, primePost, ← hLt, lifeValue_pending_hit hna ht]
        ring
      · have hh₀ : hitPart (HitsAt x d z) S xp = 0 := by simp [hitPart, hhit]
        have hLt : ℓ ≠ pathLines xp.1.1 π t := by
          rw [hline, ← hℓ']
          exact fun h => hhit h.symm
        simp only [ghostTerm_eq q hh₀ hm₀, ite_eq_left hdes, hst, localStatus,
          ghostWeight_idle q hh₀]
        norm_num
        exact (lifeValue_pending_miss hna ht hLt).symm
    | unborn =>
      have hS₀ : S xp = 0 := eq_zero_of_statusOf hS (fun ℓ h => by rw [hst] at h; cases h) rfl
      have hBp := notMem_of_statusOf_eq_unborn hst
      have hna : t ∉ activeSet xp.1.1 π := fun h => by
        rw [(statusOf_eq_active_iff xp.1.1).2 ((hact xp.1.1).1 h)] at hst
        cases hst
      have hℓ : desLine z act S Bn xp.1.1 = lineOf xp.1.1 z := by rw [desLine, hst]
      have hhit : HitsAt x d z xp := (hdes.trans hℓ).symm
      have hh₀ : hitPart (HitsAt x d z) S xp = 0 := by simp [hitPart, hS₀]
      have hm₁ : (if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0) = 1 := ite_eq_left ⟨hhit, hBp⟩
      simp only [ghostTerm_eq q hh₀ hm₁, ite_eq_left hdes, hst, localStatus,
        ghostWeight_idle q hh₀, ghostWeight_create q hq hVp hh₀]
      norm_num
      rw [primeLife, primePost, primePost, lifeValue_unborn hLp hA hna ht, hline]
      ring
  · rw [ite_eq_right hdes]
    have hS₀ : S xp = 0 := by
      by_contra h
      exact hdes (desLine_of_pend hS z h).symm
    have hh₀ : hitPart (HitsAt x d z) S xp = 0 := by simp [hitPart, hS₀]
    have hm₀ : (if HitsAt x d z xp ∧ xp.1.1 ∉ Bn then 1 else 0) = 0 := by
      refine ite_eq_right fun h => hdes ?_
      -- an unborn prime's hitting particle is designated
      have hna : ¬∃ i k, act i k = xp.1.1 := fun ⟨i, k, hk⟩ => h.2 (hk ▸ hS.act_mem i k)
      have hnp : ∀ y : Particle x d, y.1.1 = xp.1.1 → S y = 0 := fun y hy => by
        by_contra h0
        exact h.2 (hy ▸ hS.pend_mem y h0)
      rw [desLine, statusOf_of_none hna hnp, ite_eq_right h.2]
      exact h.1.symm
    simp only [ghostTerm_eq q hh₀ hm₀, ite_eq_right hdes, ghostWeight_idle q hh₀]
    norm_num

open scoped Classical in
/-- **The ghost step**: on a consistent state, summed over the ghost choices with distinct new
births, the visit weight times the post-ghost lifespan product is the pre-ghost lifespan
product. -/
theorem ghost_stage (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 0 < harmonicMass (band x (d.a i))) (hB : (bandPrimes x d).card ≤ B) {N t : ℕ}
    (ht : t ≤ N) (π : Fin (N + 1) → FreeState x d Y d₀ u v r) (s : ChainState x d Y d₀ u v r B)
    {Bn : Multiset ℕ} (hS : Consistent s.2.1.1 s.2.2.1 Bn)
    (hline : ∀ p, pathLines p π t = lineOf p s.1.1)
    (hact : ∀ p, t ∈ activeSet p π ↔ ∃ i h, s.2.1.1 i h = p) :
    ∑ g ∈ multBox B ×ˢ multBox B, visitWeight q N t s g *
        (if (Bn + batchBirths g.2).Nodup then 1 else 0) *
        postProd q N π t s.2.1.1 (ghostMem s.2.2.1 g) (Bn + batchBirths g.2) =
      lifeProd q N π t s.2.1.1 s.2.2.1 Bn := by
  rw [sum_congr rfl fun g _ => ghost_summand_eq_prod q hB N t π s hS g, sum_multBox_prod,
    prod_congr rfl fun xp _ => sum_ghostTerm q hq hdisj hV hB ht π hS hline hact xp]
  convert prod_particles_ite _ (fun p hp => desLine_le (act := s.2.1.1) s.1.1 s.2.2.1 Bn hp)
    (fun p => primeLife q N π p t (statusOf s.2.1.1 s.2.2.1 Bn p)) using 1
  rw [lifeProd]

end GhostStage

end Erdos408.OneSided
