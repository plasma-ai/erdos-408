import Erdos408.OneSided.Moment.PathExpansion
import Erdos408.OneSided.Memory.Ghost
import Erdos408.OneSided.Memory.Partition

/-!
# The memory chain

The operators of PD §4 at a real root (`blueprint/one_sided_type_ii.md` §12), as choice
operators on chain states.

* A chain state has a position `z`, active lists `act` and a memory `S` of size at most the
  cap `B`. The memory is a multiplicity function on particles `(p, ℓ)`, with `p` a band prime
  and `ℓ ≤ p`.
* The ghost `chainGhost j` is the ghost operation of `Memory/Ghost.lean` at the current
  position, with `del = -η'_j/ρ`, `surv = q_j/ρ²` and `cre(p, ℓ) = -η'_j V(p)/ρ`.
* The edge `chainEdge` makes these choices:
  - a source symmetrization;
  - the groups whose unshared source prime is stored as `(p, [z]_p)`;
  - a target `z'`;
  - for each group, a new label, either a promoted pending particle (weight `S(x)/V`) or a
    fresh prime (weight `ν(p)`, a birth);
  - a target symmetrization.

  The coefficient carries `ρ^{hits}` at both ends and the line-free kernel `κ` of the row
  operation, together with the ban, distinctness of the target lists, the pad dyad,
  `D ∣ det`, and goodness at both ends.

PD's global birth distinctness is not a local restriction, so it is imposed on the expanded
history. A history is a ghost choice at each of the `N + 1` visits and an edge choice at
each of the `N` edges; `chainProduct_eq_sum_history` expands `𝒢₀ ℰ 𝒢₁ ⋯ ℰ 𝒢_N` into
histories. Its births sit at fixed addresses (`BirthAddr`): the initial slots, the fresh
labels of each edge, and the batch indices of each ghost.

The memory identity S3, `lineAverage_rootMoment_eq_chain` in `Moment/Chain/Identity.lean`, is
`𝔼_ℓ rootMoment = (∏_p b'_p) ∑ [𝐛_init] w(history) [𝐛_fin]`, over histories with distinct
births and with the cap `B` the number of band primes.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

section Chain

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- The particles `(p, ℓ)`: a band prime `p` and a line `ℓ ≤ p`. -/
def particles : Finset (ℕ × ℕ) :=
  (bandPrimes x d).biUnion fun p => (range (p + 1)).image fun ℓ => (p, ℓ)

/-- The particle type. -/
abbrev Particle := ↥(particles x d)

/-- The harmonic mass of the band containing `p` (for disjoint bands, `V_i` when `p ∈ 𝒫_i`). -/
def primeMass (p : ℕ) : ℝ :=
  ∑ i, if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0

/-- The baseline `b'_p = 1 - (p + 1)⁻¹ ∑_{j ≤ N} η'_j`. -/
def baseline (N p : ℕ) : ℝ := 1 - ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j

/-- The birth weight `ν(p) = 1 / (V(p) (p + 1) b'_p)`. -/
def primeWeight (N p : ℕ) : ℝ := 1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p)

/-- The pending weight `ρ = q^{1/8}`: `0 < ρ < 1` and `ρ² > √q`. -/
def pendingWeight : ℝ := q ^ (1 / 8 : ℝ)

/-- The memory cap: with distinct births no more particles than band primes are pending. -/
def memCap : ℕ := (bandPrimes x d).card

/-- The chain states: a position, active lists, and a memory of size at most `B`. -/
abbrev ChainState :=
  ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × ↥(lists x d (padCount x)) ×
    MemState (Particle x d) B

/-- The measure of a chain state: `∏_{i,h} ν(act_{i,h})` times the memory weight. -/
def chainMeasure (N : ℕ) (s : ChainState x d Y d₀ u v r B) : ℝ :=
  (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
    memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1

/-- The number of pending particles hitting `z`, with multiplicity. -/
def pendingHits (z : ℤ × ℤ) (S : Particle x d → ℕ) : ℕ :=
  ∑ xp, if lineOf xp.1.1 z = xp.1.2 then S xp else 0

/-- The particle hits the position `z`: its line is `[z]_p`. -/
def HitsAt (z : ℤ × ℤ) (xp : Particle x d) : Prop := lineOf xp.1.1 z = xp.1.2

instance (z : ℤ × ℤ) : DecidablePred (HitsAt x d z) := fun _ => inferInstanceAs (Decidable (_ = _))

open scoped Classical in
/-- The ghost coefficient: `ghostCoef` at the current position with `del = -η'_j/ρ`,
`surv = q_j/ρ²`, `cre(p, ℓ) = -η'_j V(p)/ρ` and particle measure `ν(p)`; zero unless the choice
is admissible. -/
def chainGhostCoef (N j : ℕ) (s : ChainState x d Y d₀ u v r B)
    (c : (Particle x d → ℕ) × (Particle x d → ℕ)) : ℂ :=
  ghostCoef (HitsAt x d s.1.1) (fun xp : Particle x d => primeWeight q x d N xp.1.1)
      (-dampDefect q N j / pendingWeight q) ((1 - dampDefect q N j) / pendingWeight q ^ 2)
    (fun xp : Particle x d => -dampDefect q N j * primeMass x d xp.1.1 / pendingWeight q)
    B s.2.2 c

/-- The output of a ghost choice: delete `D` and create the batch. -/
def chainGhostOut (s : ChainState x d Y d₀ u v r B)
    (c : (Particle x d → ℕ) × (Particle x d → ℕ)) : ChainState x d Y d₀ u v r B :=
  (s.1, s.2.1, ghostOut (HitsAt x d s.1.1) B s.2.2 c)

/-- The ghost operation `𝒢_j`. -/
def chainGhost (N j : ℕ) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (multBox B ×ˢ multBox B) (chainGhostCoef q x d Y d₀ u v r B N j)
    (chainGhostOut x d Y d₀ u v r B)

/-- An edge choice: the source symmetrization, the stored groups, the target, a new label
`(prime, promoted?)` per group, and the target symmetrization. -/
abbrev EdgeChoice :=
  (Fin K → Equiv.Perm (Fin (padCount x + 1))) × Finset (Fin K) ×
    ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ × Bool) ×
    (Fin K → Equiv.Perm (Fin (padCount x + 1)))

/-- The edge choices: the new label of group `i` is a prime of `𝒫_i`. -/
def edgeChoices : Finset (EdgeChoice x d Y d₀ u v r) :=
  univ ×ˢ univ ×ˢ univ ×ˢ (Fintype.piFinset fun i => band x (d.a i) ×ˢ univ) ×ˢ univ

section Edge

variable {x d Y d₀ u v r B}

/-- The source lists reordered by the source symmetrization. -/
def edgeSrc (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    Lists K (padCount x) := fun i h => s.2.1.1 i (c.1 i h)

/-- The target lists: the copied pads and the new labels, reordered by `σ'`. -/
def edgeTgt (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    Lists K (padCount x) := fun i h =>
  let h' := c.2.2.2.2 i h
  if h' = Fin.last _ then (c.2.2.2.1 i).1 else edgeSrc s c i h'

/-- The particle promoted in group `i`: the new label with its line at the target. -/
def edgePromoted (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) : ℕ × ℕ :=
  ((c.2.2.2.1 i).1, lineOf (c.2.2.2.1 i).1 c.2.2.1.1)

/-- The particle stored from group `i`: the unshared source prime with its line at the
source. -/
def edgeStored (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) :
    ℕ × ℕ :=
  (edgeSrc s c i (Fin.last _), lineOf (edgeSrc s c i (Fin.last _)) s.1.1)

open scoped Classical in
/-- The memory after the edge: promoted particles removed, stored particles added. -/
def edgeMem (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    Particle x d → ℕ := fun xp =>
  s.2.2.1 xp - (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card +
    (c.2.1.filter fun i => edgeStored s c i = xp.1).card

/-- The fresh primes of the edge. -/
def edgeFresh (c : EdgeChoice x d Y d₀ u v r) : Finset ℕ :=
  (univ.filter fun i => (c.2.2.2.1 i).2 = false).image fun i => (c.2.2.2.1 i).1

/-- The pad product `D` of the edge. -/
def edgePad (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℕ :=
  ∏ i, ∏ h : Fin (padCount x), edgeSrc s c i h.castSucc

/-- The determinant `det(z, z')`. -/
def edgeDet (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℤ :=
  s.1.1.1 * c.2.2.1.1.2 - s.1.1.2 * c.2.2.1.1.1

end Edge

/-- An edge choice at `s` is admissible:
* the target lists are valid lists;
* the new labels avoid every source label (the cross-edge ban);
* the pad product lies in `[d₀, 2d₀)` and divides `det(z, z')`;
* both ends pass the good-state tests;
* every promoted particle is pending and hits the target, and every stored particle is a
  particle;
* the new memory respects the cap. -/
def EdgeValid (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : Prop :=
  edgeTgt s c ∈ lists x d (padCount x) ∧
    (∀ i i' h, (c.2.2.2.1 i).1 ≠ s.2.1.1 i' h) ∧
    d₀ ≤ (edgePad s c : ℝ) ∧ (edgePad s c : ℝ) < 2 * d₀ ∧ (edgePad s c : ℤ) ∣ edgeDet s c ∧
    (GoodFirst Y d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 ∧
      GoodSecond x d d₀ (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1) ∧
    (GoodFirst Y d₀ (tau r (complement c.2.2.1.1) / tau r c.2.2.1.1) (edgeTgt s c) ∧
      GoodSecond x d d₀ (tau r (complement c.2.2.1.1) / tau r c.2.2.1.1) (edgeTgt s c)) ∧
    (∀ i, (c.2.2.2.1 i).2 = true → ∃ xp : Particle x d, xp.1 = edgePromoted c i ∧
      1 ≤ s.2.2.1 xp) ∧
    (∀ i ∈ c.2.1, edgeStored s c i ∈ particles x d) ∧
    edgeMem s c ∈ memStates B

open scoped Classical in
/-- The edge coefficient:
`M!^{-2K} ρ^{hits(S, z)} ρ^{hits(S', z')} ∏_i w_i κ(t; b, a)`, where
* `w_i` is `S(x_i)/V(p_i)` for a promotion and `ν(p_i)` for a fresh prime;
* `κ(t; b, a) = (d₀/D) η(b/Y) η(a/Y) ψ(t/Y) {[t = b - a] - ∫_𝔐 e(θ(t - b + a))}` with
  `t = det/D`.

It is zero unless the choice is admissible. -/
def chainEdgeCoef (N : ℕ) (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℂ :=
  if EdgeValid x d Y d₀ u v r B s c then
    let D := edgePad s c
    let b := ∏ i, edgeSrc s c i (Fin.last _)
    let a := ∏ i, (c.2.2.2.1 i).1
    let t := edgeDet s c / D
    (((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
        pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
        (∏ i, if (c.2.2.2.1 i).2 then
          (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) /
            primeMass x d (c.2.2.2.1 i).1
        else primeWeight q x d N (c.2.2.2.1 i).1) *
        (d₀ / D) * dyadicBump (b / Y) * dyadicBump (a / Y) * plateau (t / Y) : ℝ) : ℂ) *
      ((if t = (b : ℤ) - a then 1 else 0) - arcIntegral A₀ x Y (t - b + a))
  else 0

open scoped Classical in
/-- The output of an edge choice. -/
def chainEdgeOut (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    ChainState x d Y d₀ u v r B :=
  if h : EdgeValid x d Y d₀ u v r B s c then
    (c.2.2.1, ⟨edgeTgt s c, h.1⟩, ⟨edgeMem s c, h.2.2.2.2.2.2.2.2.2⟩)
  else s

/-- The edge operation `ℰ`. -/
def chainEdge (N : ℕ) :
    (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ :=
  choiceOp (edgeChoices x d Y d₀ u v r) (chainEdgeCoef q A₀ x d Y d₀ u v r B N)
    (chainEdgeOut x d Y d₀ u v r B)

/-- `𝒢₀ ℰ 𝒢₁ ℰ ⋯ ℰ 𝒢_N` applied to `f`. -/
def chainProduct (N : ℕ) (f : ChainState x d Y d₀ u v r B → ℂ) :
    ChainState x d Y d₀ u v r B → ℂ :=
  (List.range N).foldr
    (fun j g => chainGhost q x d Y d₀ u v r B N j (chainEdge q A₀ x d Y d₀ u v r B N g))
    (chainGhost q x d Y d₀ u v r B N N f)

open scoped Classical in
/-- The initial vector: at `e₁`, with empty memory. -/
def chainInit (s : ChainState x d Y d₀ u v r B) : ℂ :=
  if s.1.1 = (1, 0) ∧ memSize s.2.2.1 = 0 then 1 else 0

/-- A ghost choice `(D, n)`: the deleted and the created multiplicities. -/
abbrev GhostChoice := (Particle x d → ℕ) × (Particle x d → ℕ)

/-- A history of `𝒢₀ ℰ 𝒢₁ ⋯ ℰ 𝒢_N`: a ghost choice at each visit and an edge choice at each
edge. -/
abbrev History (N : ℕ) := (Fin (N + 1) → GhostChoice x d) × (Fin N → EdgeChoice x d Y d₀ u v r)

/-- The histories whose choices are drawn from the choice sets of the operators. -/
def histories (N : ℕ) : Finset (History x d Y d₀ u v r N) :=
  Fintype.piFinset (fun _ => multBox B ×ˢ multBox B) ×ˢ
    Fintype.piFinset fun _ => edgeChoices x d Y d₀ u v r

variable {x d Y d₀ u v r B} in
/-- The state at visit `j` of the history `h` from `s`, before its ghost. -/
def chainVisit {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) :
    Fin (N + 1) → ChainState x d Y d₀ u v r B :=
  Fin.induction s fun j t =>
    chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B t (h.1 j.castSucc)) (h.2 j)

variable {x d Y d₀ u v r B} in
/-- The final state of the history `h` from `s`. -/
def chainEnd {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) :
    ChainState x d Y d₀ u v r B :=
  chainGhostOut x d Y d₀ u v r B (chainVisit s h (Fin.last N)) (h.1 (Fin.last N))

variable {x d Y d₀ u v r B} in
/-- The weight of the history `h` from `s`: the product of its ghost and edge
coefficients. -/
def chainWeight {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) : ℂ :=
  (∏ j : Fin (N + 1), chainGhostCoef q x d Y d₀ u v r B N j (chainVisit s h j) (h.1 j)) *
    ∏ j : Fin N, chainEdgeCoef q A₀ x d Y d₀ u v r B N
      (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc)) (h.2 j)

variable {x d Y d₀ u v r B} in
/-- The weight of the history `h` from `s` with the ghost indices shifted by `a` and the
defects of `M` edges: `chainWeight` is the case `a = 0`, `M = N`. The shift lets the
expansion peel off the first visit. -/
private def shiftWeight (M a : ℕ) {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (h : History x d Y d₀ u v r N) : ℂ :=
  (∏ j : Fin (N + 1), chainGhostCoef q x d Y d₀ u v r B M (j + a) (chainVisit s h j) (h.1 j)) *
    ∏ j : Fin N, chainEdgeCoef q A₀ x d Y d₀ u v r B M
      (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc)) (h.2 j)

variable {x d Y d₀ u v r B} in
/-- The visits of a history after its first edge are the visits of its tail from the state
after that edge. -/
private theorem chainVisit_cons_succ {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) (e : EdgeChoice x d Y d₀ u v r) (h : History x d Y d₀ u v r N)
    (j : Fin (N + 1)) :
    chainVisit (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) j.succ =
      chainVisit (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
    simp only [chainVisit] at ih ⊢
    rw [Fin.induction_succ, Fin.induction_succ, ← Fin.succ_castSucc, ih]
    simp

variable {x d Y d₀ u v r B} in
/-- The end of a history is the end of its tail from the state after its first edge. -/
private theorem chainEnd_cons {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) (e : EdgeChoice x d Y d₀ u v r) (h : History x d Y d₀ u v r N) :
    chainEnd (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) =
      chainEnd (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h := by
  rw [chainEnd, ← Fin.succ_last, chainVisit_cons_succ]
  rfl

variable {x d Y d₀ u v r B} in
/-- The weight of a history is its first ghost and edge coefficients times the weight of its
tail, with the ghost indices shifted by one. -/
private theorem shiftWeight_cons (M a : ℕ) {N : ℕ} (s : ChainState x d Y d₀ u v r B)
    (c : GhostChoice x d) (e : EdgeChoice x d Y d₀ u v r) (h : History x d Y d₀ u v r N) :
    shiftWeight q A₀ M a (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) =
      chainGhostCoef q x d Y d₀ u v r B M a s c *
        chainEdgeCoef q A₀ x d Y d₀ u v r B M (chainGhostOut x d Y d₀ u v r B s c) e *
        shiftWeight q A₀ M (1 + a)
          (chainEdgeOut x d Y d₀ u v r B (chainGhostOut x d Y d₀ u v r B s c) e) h := by
  -- split off the first factor of both products
  simp only [shiftWeight, Fin.prod_univ_succ (n := N + 1), Fin.prod_univ_succ (n := N),
    chainVisit_cons_succ, Fin.cons_succ, Fin.cons_zero, Fin.val_succ, Fin.val_zero,
    ← Fin.succ_castSucc, Fin.castSucc_zero, zero_add, add_assoc]
  have h0 : chainVisit (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) 0 = s := rfl
  rw [h0]
  ring

variable {x d Y d₀ u v r B} in
/-- A history with no edges is a single ghost choice. -/
private theorem sum_histories_zero (F : History x d Y d₀ u v r 0 → ℂ) :
    ∑ h ∈ histories x d Y d₀ u v r B 0, F h =
      ∑ c ∈ multBox B ×ˢ multBox B, F (fun _ => c, Fin.elim0) := by
  refine sum_nbij' (fun h => h.1 0) (fun c => (fun _ => c, Fin.elim0)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [histories, mem_product, Fintype.mem_piFinset] at hh ⊢
    exact hh.1 0
  · intro c hc
    simp only [histories, mem_product, Fintype.mem_piFinset] at hc ⊢
    exact ⟨fun _ => hc, fun i => i.elim0⟩
  · intro h _
    exact Prod.ext (funext fun k => by rw [Fin.fin_one_eq_zero k]) (Subsingleton.elim _ _)
  · intro c _
    rfl
  · intro h _
    congr 1
    exact Prod.ext (funext fun k => by rw [Fin.fin_one_eq_zero k]) (Subsingleton.elim _ _)

variable {x d Y d₀ u v r B} in
/-- A history with `N + 1` edges is a first ghost choice, a first edge choice, and a history
with `N` edges. -/
private theorem sum_histories_succ {N : ℕ} (F : History x d Y d₀ u v r (N + 1) → ℂ) :
    ∑ h ∈ histories x d Y d₀ u v r B (N + 1), F h =
      ∑ c ∈ multBox B ×ˢ multBox B, ∑ e ∈ edgeChoices x d Y d₀ u v r,
        ∑ h ∈ histories x d Y d₀ u v r B N, F (Fin.cons c h.1, Fin.cons e h.2) := by
  simp only [← sum_product']
  refine sum_nbij' (fun h => (h.1 0, h.2 0, Fin.tail h.1, Fin.tail h.2))
    (fun t => (Fin.cons t.1 t.2.2.1, Fin.cons t.2.1 t.2.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro h hh
    simp only [histories, mem_product, Fintype.mem_piFinset] at hh ⊢
    exact ⟨hh.1 0, hh.2 0, fun i => hh.1 _, fun i => hh.2 _⟩
  · intro t ht
    simp only [histories, mem_product, Fintype.mem_piFinset] at ht ⊢
    exact ⟨fun i => Fin.cases ht.1 ht.2.2.1 i, fun i => Fin.cases ht.2.1 ht.2.2.2 i⟩
  · intro h _
    simp
  · intro t _
    simp
  · intro h _
    simp

variable {x d Y d₀ u v r B} in
/-- The history expansion with shifted ghost indices: `𝒢_a ℰ 𝒢_{a+1} ⋯ ℰ 𝒢_{a+N} f (s)` is
`∑_h w_a(s, h) f(end(s, h))`, with the defects of `M` edges throughout. -/
private theorem foldr_eq_sum_history (M : ℕ) (f : ChainState x d Y d₀ u v r B → ℂ) (N : ℕ) :
    ∀ (a : ℕ) (s : ChainState x d Y d₀ u v r B),
      (List.range N).foldr (fun j g => chainGhost q x d Y d₀ u v r B M (j + a)
          (chainEdge q A₀ x d Y d₀ u v r B M g)) (chainGhost q x d Y d₀ u v r B M (N + a) f) s =
        ∑ h ∈ histories x d Y d₀ u v r B N, shiftWeight q A₀ M a s h * f (chainEnd s h) := by
  induction N with
  | zero =>
    intro a s
    rw [sum_histories_zero]
    simp only [List.range_zero, List.foldr_nil, zero_add, chainGhost, choiceOp, shiftWeight,
      Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.val_zero]
    rfl
  | succ N ih =>
    intro a s
    -- peel off `𝒢_a ℰ` and expand the rest from the state after the first edge
    rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, sum_histories_succ]
    simp only [Nat.succ_eq_add_one, add_assoc, zero_add]
    rw [funext (ih (1 + a))]
    simp only [chainGhost, chainEdge, choiceOp, shiftWeight_cons, chainEnd_cons, mul_sum, mul_assoc]

/-- The history expansion: `𝒢₀ ℰ 𝒢₁ ⋯ ℰ 𝒢_N f (s) = ∑_h w(s, h) f(end(s, h))`. -/
theorem chainProduct_eq_sum_history (N : ℕ) (f : ChainState x d Y d₀ u v r B → ℂ)
    (s : ChainState x d Y d₀ u v r B) :
    chainProduct q A₀ x d Y d₀ u v r B N f s =
      ∑ h ∈ histories x d Y d₀ u v r B N, chainWeight q A₀ s h * f (chainEnd s h) := by
  have h := foldr_eq_sum_history q A₀ N f N 0 s
  simp only [add_zero] at h
  exact h

/-- The birth addresses: the initial slots, the label of each group at each edge, and the
first `B` batch indices of each ghost. -/
abbrev BirthAddr (N : ℕ) :=
  (Fin K × Fin (padCount x + 1)) ⊕ (Fin N × Fin K) ⊕ (Fin (N + 1) × Fin B)

/-- The primes of a ghost batch, with multiplicity, in increasing order. -/
def batchPrimes (n : Particle x d → ℕ) : List ℕ :=
  (∑ xp : Particle x d, Multiset.replicate (n xp) xp.1.1).sort (· ≤ ·)

variable {x d Y d₀ u v r B} in
/-- The births of the history `h` from `s`: the prime born at each address, or `none` if the
address is not performed (a promoted label, or a batch index beyond the batch). -/
def births {N : ℕ} (s : ChainState x d Y d₀ u v r B) (h : History x d Y d₀ u v r N) :
    BirthAddr (K := K) x B N → Option ℕ
  | .inl (i, k) => some (s.2.1.1 i k)
  | .inr (.inl (j, i)) => if (h.2 j).2.2.2.1 i |>.2 then none else some ((h.2 j).2.2.2.1 i).1
  | .inr (.inr (j, k)) => (batchPrimes x d (h.1 j).2)[k.1]?

open scoped Classical in
/-- The history sum `∑_s μ(s) 𝐛(s) ∑_h w(s, h) 𝐛(end(s, h))` over the histories with distinct
births, with memory cap `B`; here `𝐛` is `chainInit`, the indicator of `e₁` with empty
memory. -/
def distinctSum (N : ℕ) : ℂ :=
  ∑ s, (chainMeasure q x d Y d₀ u v r B N s : ℂ) * chainInit x d Y d₀ u v r B s *
    ∑ h ∈ (histories x d Y d₀ u v r B N).filter (fun h => BirthsDistinct (births s h)),
      chainWeight q A₀ s h * chainInit x d Y d₀ u v r B (chainEnd s h)

end Chain

end Erdos408.OneSided
