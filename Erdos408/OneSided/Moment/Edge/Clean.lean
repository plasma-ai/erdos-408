module

public import Erdos408.OneSided.Moment.Edge.Core
public import Erdos408.OneSided.Moment.Phased.Edge
public import Erdos408.OneSided.Goodness.Symmetry
public import Erdos408.OneSided.Cauchy

/-!
# The clean signed edge

M6 of `blueprint/one_sided_type_ii.md` §5.5 and §16 (PD `mem:clean-bound`): the clean piece of
the edge, with no stored and no promoted groups, has norm at most `L^{-G-1/2}` for the chain
measure.

The reduction to the core kernel of `Moment/Edge/Core.lean` follows PD §4.

* `normLe_cleanOp_of_blocks`: split the clean choices by the two symmetrizations `σ, σ'`;
  their coefficients carry the average `M!^{-2K}`. For fixed `σ, σ'` the clean edge preserves the
  memory `S` and the shared pads `P`, and a source state of the block `(S, P)` is a position `z`
  and the last labels `b`, with measure `μ₀(S, P) ν(b)`; the targets are `(z', a)` with measure
  `μ₀(S, P) ν(a)`. So it suffices to bound each block kernel `cleanBlockKer` on `𝒵 × X(P)`.
* `wkerLe_cleanBlockKer`: in a block the coefficient is
  `M!^{-2K} (d₀/D) φ(z, b) ν(a) φ'(z', a) [ban] [D ∣ det] ψ(t/Y) {[t - b + a = 0] - ∫_𝔐}`,
  with endpoint multipliers `|φ|, |φ'| ≤ 1` that vanish unless the labels lie in `[Y, 4Y]` and
  the source passes test (i). The cross-edge ban is `[a_i ≠ b_i]` for every group: omitting it
  costs at most a coincidence `a_i = b_i`, whose weighted Schur sides are
  `16 (1 + 52 L^{3A₀}) K 4^K sup ν`. Without the ban, conjugation from `ν` to counting measure
  inserts `√(ν(b) ν(a)) ≤ 4^K/Y` (PD `mem:product-mass`), and the core kernel bound
  `exists_coreKer_bound` applies.
* `eventually_cleanOp_normLe`: for large `x` the resulting bound
  `4^K C₀ (1 + log 4Y)(L^{-A₀} + Y^{-0.1}) + 1024 K 4^K (1 + 52 L^{3A₀}) e^{-L^{a₋}}` is at most
  `L^{-G-1/2}`, since `A₀ = G + 1`, `log Y ≪_K L^{0.2}` and `Y ≥ e^{L^{0.1}}/4`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### Pads and last labels -/

section Lists

variable {J : ℕ}

/-- The lists with pads `P` (slots `0, …, J - 1`) and last labels `b`. -/
def joinList (P : Fin K → Fin J → ℕ) (b : Fin K → ℕ) : Lists K J :=
  fun i => Fin.snoc (α := fun _ => ℕ) (P i) (b i)

variable (x : ℝ) (d : Data K)

/-- The pad lists: `J` distinct primes of each band. -/
def padLists (J : ℕ) : Finset (Fin K → Fin J → ℕ) :=
  (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin J => band x (d.a i)).filter
    fun P => ∀ i, Function.Injective (P i)

/-- The last labels completing the pads `P` to lists: a prime of each band, not among the pads
of its group. -/
def lastSet (P : Fin K → Fin J → ℕ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun i => (band x (d.a i)).filter fun p => ∀ h, P i h ≠ p

omit d in
/-- The last label of `joinList P b` in group `i` is `b i`. -/
theorem joinList_last (P : Fin K → Fin J → ℕ) (b : Fin K → ℕ) (i : Fin K) :
    joinList P b i (Fin.last J) = b i := Fin.snoc_last (α := fun _ => ℕ) _ _

omit d in
/-- The pads of `joinList P b` are `P`. -/
theorem joinList_castSucc (P : Fin K → Fin J → ℕ) (b : Fin K → ℕ) (i : Fin K) (h : Fin J) :
    joinList P b i h.castSucc = P i h := Fin.snoc_castSucc (α := fun _ => ℕ) _ _ _

omit d in
/-- Two lists with the same pads differ only in the last slot. -/
theorem joinList_eq_ite (P : Fin K → Fin J → ℕ) (a b : Fin K → ℕ) (i : Fin K) (h : Fin (J + 1)) :
    joinList P a i h = if h = Fin.last J then a i else joinList P b i h := by
  induction h using Fin.lastCases with
  | last => simp [joinList_last]
  | cast h =>
    simp only [(Fin.castSucc_lt_last h).ne, ↓reduceIte, joinList_castSucc]

/-- Pads with a completing last label form a list. -/
theorem joinList_mem_lists {P : Fin K → Fin J → ℕ} {b : Fin K → ℕ} (hP : P ∈ padLists x d J)
    (hb : b ∈ lastSet x d P) : joinList P b ∈ lists x d J := by
  classical
  unfold padLists at hP
  unfold lastSet at hb
  rw [mem_filter, Fintype.mem_piFinset] at hP
  rw [Fintype.mem_piFinset] at hb
  refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun h => ?_,
    fun i => ?_⟩
  · induction h using Fin.lastCases with
    | last => rw [joinList_last]; exact (mem_filter.1 (hb i)).1
    | cast h => rw [joinList_castSucc]; exact Fintype.mem_piFinset.1 (hP.1 i) h
  · intro h h' hh
    induction h using Fin.lastCases with
    | last =>
      induction h' using Fin.lastCases with
      | last => rfl
      | cast h' =>
        rw [joinList_last, joinList_castSucc] at hh
        exact ((mem_filter.1 (hb i)).2 h' hh.symm).elim
    | cast h =>
      induction h' using Fin.lastCases with
      | last =>
        rw [joinList_last, joinList_castSucc] at hh
        exact ((mem_filter.1 (hb i)).2 h hh).elim
      | cast h' =>
        rw [joinList_castSucc, joinList_castSucc] at hh
        rw [hP.2 i hh]

/-- Reordering the slots keeps a list a list. -/
theorem permute_mem_lists {L : Lists K J} (hL : L ∈ lists x d J)
    (τ : Fin K → Equiv.Perm (Fin (J + 1))) : (fun i => L i ∘ τ i) ∈ lists x d J := by
  classical
  obtain ⟨hband, hinj⟩ := mem_filter.1 hL
  refine mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun h =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hband i) (τ i h), fun i =>
      (hinj i).comp (τ i).injective⟩

/-- **Splitting the lists**: a sum over lists is a sum over pads `P` and last labels `b`, of the
lists `joinList P b` reordered by `τ`. -/
theorem sum_lists_eq {M : Type*} [AddCommMonoid M] (τ : Fin K → Equiv.Perm (Fin (J + 1)))
    (F : Lists K J → M) :
    ∑ L ∈ lists x d J, F L =
      ∑ P ∈ padLists x d J, ∑ b ∈ lastSet x d P, F (fun i => joinList P b i ∘ τ i) := by
  classical
  rw [show (∑ P ∈ padLists x d J, ∑ b ∈ lastSet x d P, F (fun i => joinList P b i ∘ τ i)) =
      ∑ pb ∈ (padLists x d J).sigma (fun P => lastSet x d P),
        F (fun i => joinList pb.1 pb.2 i ∘ τ i) from
      (Finset.sum_sigma (padLists x d J) (fun P => lastSet x d P)
        (fun pb : (Σ _ : Fin K → Fin J → ℕ, Fin K → ℕ) =>
          F (fun i => joinList pb.1 pb.2 i ∘ τ i))).symm]
  refine sum_nbij' (fun L => ⟨fun i h => L i ((τ i).symm h.castSucc),
    fun i => L i ((τ i).symm (Fin.last J))⟩) (fun pb => fun i => joinList pb.1 pb.2 i ∘ τ i)
    ?_ ?_ ?_ ?_ ?_
  · intro L hL
    obtain ⟨hband, hinj⟩ := mem_filter.1 (mem_coe.1 hL)
    have hb : ∀ i h, L i h ∈ band x (d.a i) := fun i h =>
      Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hband i) h
    refine mem_coe.2 (mem_sigma.2 ⟨mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i =>
      Fintype.mem_piFinset.2 fun h => hb i _, fun i h h' hh => ?_⟩,
      Fintype.mem_piFinset.2 fun i => mem_filter.2 ⟨hb i _, fun h hh => ?_⟩⟩)
    · exact Fin.castSucc_injective _ ((τ i).symm.injective (hinj i hh))
    · exact (Fin.castSucc_lt_last h).ne ((τ i).symm.injective (hinj i hh))
  · intro pb hpb
    obtain ⟨hP, hb⟩ := mem_sigma.1 (mem_coe.1 hpb)
    exact mem_coe.2 (permute_mem_lists x d (joinList_mem_lists x d hP hb) τ)
  · intro L _
    funext i h
    simp only [Function.comp]
    -- `joinList` of the pads and last label of `L ∘ τ⁻¹` is `L ∘ τ⁻¹`
    have key : ∀ k, joinList (fun i h => L i ((τ i).symm h.castSucc))
        (fun i => L i ((τ i).symm (Fin.last J))) i k = L i ((τ i).symm k) := by
      intro k
      induction k using Fin.lastCases with
      | last => rw [joinList_last]
      | cast k => rw [joinList_castSucc]
    rw [key, Equiv.symm_apply_apply]
  · intro pb _
    ext i h
    · simp [joinList_castSucc]
    · simp [joinList_last]
  · intro L hL
    congr 1
    funext i h
    simp only [Function.comp]
    have key : ∀ k, joinList (fun i h => L i ((τ i).symm h.castSucc))
        (fun i => L i ((τ i).symm (Fin.last J))) i k = L i ((τ i).symm k) := by
      intro k
      induction k using Fin.lastCases with
      | last => rw [joinList_last]
      | cast k => rw [joinList_castSucc]
    rw [key, Equiv.symm_apply_apply]

omit d in
/-- The product of a weight over a reordered `joinList P b` is the pad product times the
product over the last labels. -/
theorem prod_joinList_permute (ν : ℕ → ℝ) (P : Fin K → Fin J → ℕ) (b : Fin K → ℕ)
    (τ : Fin K → Equiv.Perm (Fin (J + 1))) :
    ∏ i, ∏ h, ν ((fun i => joinList P b i ∘ τ i) i h) =
      (∏ i, ∏ h : Fin J, ν (P i h)) * ∏ i, ν (b i) := by
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  simp only [Function.comp]
  rw [Equiv.prod_comp (τ i) (fun h => ν (joinList P b i h)), Fin.prod_univ_castSucc]
  simp only [joinList_castSucc, joinList_last]

end Lists

/-! ### The clean edge and its blocks -/

section Blocks

variable (q A₀ x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B : ℕ)

/-- The clean edge choices: no stored and no promoted groups. -/
def cleanChoices : Finset (EdgeChoice x d Y d₀ u v r) :=
  (edgeChoices x d Y d₀ u v r).filter fun c =>
    c.2.1 = ∅ ∧ univ.filter (fun i => (c.2.2.2.1 i).2 = true) = ∅

/-- The measure `ν(b) = ∏_i ν(b_i)` of last labels. -/
def cleanLabelWeight (N : ℕ) (b : Fin K → ℕ) : ℝ := ∏ i, primeWeight q x d N (b i)

/-- The source lists of the block `(σ, P)` with last labels `b`: `joinList P b` reordered by
`σ⁻¹`, so that the source symmetrization `σ` brings back `joinList P b`. -/
def srcList (σ : Fin K → Equiv.Perm (Fin (padCount x + 1))) (P : Fin K → Fin (padCount x) → ℕ)
    (b : Fin K → ℕ) : Lists K (padCount x) :=
  fun i => joinList P b i ∘ (σ i).symm

open scoped Classical in
/-- The kernel of the clean edge in the block `(σ, σ', S, P)`, from `(z', a)` to `(z, b)`: the
edge coefficient at the source `(z, srcList σ P b, S)` for the choice of the target `z'`, the
fresh labels `a` and the symmetrizations. -/
def cleanBlockKer (N : ℕ) (σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1)))
    (S : MemState (Particle x d) B) (P : Fin K → Fin (padCount x) → ℕ)
    (p p' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ)) : ℂ :=
  if h : srcList x σ P p.2 ∈ lists x d (padCount x) then
    chainEdgeCoef q A₀ x d Y d₀ u v r B N (p.1, ⟨srcList x σ P p.2, h⟩, S)
      (σ, ∅, p'.1, fun i => (p'.2 i, false), σ')
  else 0

variable {q A₀ x d Y d₀ u v r B}

/-- The source of a block choice: the source symmetrization brings back `joinList P b`. -/
theorem edgeSrc_block {σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))}
    {S : MemState (Particle x d) B} {P : Fin K → Fin (padCount x) → ℕ} {b a : Fin K → ℕ}
    {z z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)}
    (h : srcList x σ P b ∈ lists x d (padCount x)) :
    edgeSrc (z, ⟨srcList x σ P b, h⟩, S) ((σ, ∅, z', fun i => (a i, false), σ') :
      EdgeChoice x d Y d₀ u v r) = joinList P b := by
  funext i k
  simp [edgeSrc, srcList]

/-- The target of a block choice is `joinList P a` reordered by `σ'`. -/
theorem edgeTgt_block {σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))}
    {S : MemState (Particle x d) B} {P : Fin K → Fin (padCount x) → ℕ} {b a : Fin K → ℕ}
    {z z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)}
    (h : srcList x σ P b ∈ lists x d (padCount x)) :
    edgeTgt (z, ⟨srcList x σ P b, h⟩, S) ((σ, ∅, z', fun i => (a i, false), σ') :
      EdgeChoice x d Y d₀ u v r) = fun i => joinList P a i ∘ σ' i := by
  funext i k
  simp only [edgeTgt, edgeSrc_block h, Function.comp]
  exact (joinList_eq_ite P a b i (σ' i k)).symm

/-- The pad product of a block choice is the product of the pads. -/
theorem edgePad_block {σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))}
    {S : MemState (Particle x d) B} {P : Fin K → Fin (padCount x) → ℕ} {b a : Fin K → ℕ}
    {z z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)}
    (h : srcList x σ P b ∈ lists x d (padCount x)) :
    edgePad (z, ⟨srcList x σ P b, h⟩, S) ((σ, ∅, z', fun i => (a i, false), σ') :
      EdgeChoice x d Y d₀ u v r) = ∏ i, ∏ k, P i k := by
  simp only [edgePad, edgeSrc_block h, joinList_castSucc]

/-- The memory is unchanged by a clean choice. -/
theorem edgeMem_block {σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))}
    {S : MemState (Particle x d) B} {P : Fin K → Fin (padCount x) → ℕ} {b a : Fin K → ℕ}
    {z z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)}
    (h : srcList x σ P b ∈ lists x d (padCount x)) :
    edgeMem (z, ⟨srcList x σ P b, h⟩, S) ((σ, ∅, z', fun i => (a i, false), σ') :
      EdgeChoice x d Y d₀ u v r) = S.1 := by
  funext xp
  simp [edgeMem]

/-- The pair test (i) and test (ii) at a position, for given lists. -/
def PosGood (x : ℝ) (d : Data K) (Y d₀ r : ℝ) (z : ℤ × ℤ) (L : Lists K (padCount x)) : Prop :=
  GoodFirst Y d₀ (tau r (complement z) / tau r z) L ∧
    GoodSecond x d d₀ (tau r (complement z) / tau r z) L

open scoped Classical in
/-- Test (ii) does not see the order. -/
theorem goodSecond_permute_iff {d₀ ρ : ℝ} {J : ℕ} (L : Lists K J)
    (τ : Fin K → Equiv.Perm (Fin (J + 1))) :
    GoodSecond x d d₀ ρ (fun i => L i ∘ τ i) ↔ GoodSecond x d d₀ ρ L := by
  unfold GoodSecond
  refine forall_congr' fun I => forall_congr' fun hI => ?_
  rw [filter_congr (p := fun T => ¬Separated x d d₀ I (I.max' hI) ρ (fun i => L i ∘ τ i) T)
    (q := fun T => ¬Separated x d d₀ I (I.max' hI) ρ L T)
    fun T _ => not_congr (separated_permuteLists_iff L τ T)]

/-- Goodness does not see the order. -/
theorem posGood_permute_iff {z : ℤ × ℤ} (L : Lists K (padCount x))
    (τ : Fin K → Equiv.Perm (Fin (padCount x + 1))) :
    PosGood x d Y d₀ r z (fun i => L i ∘ τ i) ↔ PosGood x d Y d₀ r z L := by
  unfold PosGood
  rw [show (fun i => L i ∘ τ i) = permuteLists L τ from rfl, goodFirst_permuteLists_iff,
    show permuteLists L τ = (fun i => L i ∘ τ i) from rfl, goodSecond_permute_iff]

/-- The source lists are `joinList P b` reordered by `σ⁻¹`. -/
theorem srcList_eq (σ : Fin K → Equiv.Perm (Fin (padCount x + 1))) (P : Fin K → Fin (padCount x) → ℕ)
    (b : Fin K → ℕ) : srcList x σ P b = fun i => joinList P b i ∘ (σ i).symm := rfl

/-- **The admissible block choices**: for completing labels `a, b`, a block choice is admissible
exactly when the fresh labels avoid the old last labels (the cross-edge ban), the pad product is
in `[d₀, 2d₀)` and divides `det(z, z')`, and both ends are good. -/
theorem edgeValid_block_iff (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))}
    {S : MemState (Particle x d) B} {P : Fin K → Fin (padCount x) → ℕ} {b a : Fin K → ℕ}
    (hP : P ∈ padLists x d (padCount x)) (hb : b ∈ lastSet x d P) (ha : a ∈ lastSet x d P)
    {z z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)}
    (h : srcList x σ P b ∈ lists x d (padCount x)) :
    EdgeValid x d Y d₀ u v r B (z, ⟨srcList x σ P b, h⟩, S)
      ((σ, ∅, z', fun i => (a i, false), σ') : EdgeChoice x d Y d₀ u v r) ↔
      (∀ i, a i ≠ b i) ∧ d₀ ≤ ((∏ i, ∏ k, P i k : ℕ) : ℝ) ∧
        ((∏ i, ∏ k, P i k : ℕ) : ℝ) < 2 * d₀ ∧
        ((∏ i, ∏ k, P i k : ℕ) : ℤ) ∣ zdet z.1 z'.1 ∧
        PosGood x d Y d₀ r z.1 (joinList P b) ∧ PosGood x d Y d₀ r z'.1 (joinList P a) := by
  have hjb := joinList_mem_lists x d hP hb
  have hja := joinList_mem_lists x d hP ha
  -- the entries of the source lists
  have hsrc : ∀ i k, srcList x σ P b i k ∈ band x (d.a i) := fun i k =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 h).1 i) k
  have haP : ∀ i k, P i k ≠ a i := fun i k =>
    (mem_filter.1 (Fintype.mem_piFinset.1 ha i)).2 k
  have hab : ∀ i, a i ∈ band x (d.a i) := fun i => (mem_filter.1 (Fintype.mem_piFinset.1 ha i)).1
  -- the ban is `a i ≠ b i`
  have hban : (∀ i i' k, a i ≠ srcList x σ P b i' k) ↔ ∀ i, a i ≠ b i := by
    constructor
    · intro hb' i
      have := hb' i i ((σ i) (Fin.last _))
      simpa [srcList, joinList_last] using this
    · intro hab' i i' k hk
      by_cases hii : i = i'
      · subst hii
        have hk' : a i = joinList P b i ((σ i).symm k) := hk
        generalize (σ i).symm k = m at hk'
        induction m using Fin.lastCases with
        | last => exact hab' i (hk'.trans (joinList_last P b i))
        | cast k' => exact haP i k' (hk'.trans (joinList_castSucc P b i k')).symm
      · exact (disjoint_left.1 (hdisj i i' hii) (hab i)) (hk ▸ hsrc i' k)
  have htgt := edgeTgt_block (a := a) (S := S) (z := z) (z' := z') (σ' := σ') h
  have hgs : PosGood x d Y d₀ r z.1 (srcList x σ P b) ↔ PosGood x d Y d₀ r z.1 (joinList P b) := by
    rw [srcList_eq]
    exact posGood_permute_iff _ _
  have hgt : PosGood x d Y d₀ r z'.1 (fun i => joinList P a i ∘ σ' i) ↔
      PosGood x d Y d₀ r z'.1 (joinList P a) := posGood_permute_iff _ _
  have hdet : edgeDet (z, ⟨srcList x σ P b, h⟩, S) ((σ, ∅, z', fun i => (a i, false), σ') :
      EdgeChoice x d Y d₀ u v r) = zdet z.1 z'.1 := rfl
  unfold EdgeValid
  rw [htgt, edgePad_block h, edgeMem_block h, hdet]
  constructor
  · rintro ⟨-, hban', h1, h2, h3, hgs', hgt', -⟩
    exact ⟨hban.1 hban', h1, h2, h3, hgs.1 hgs', hgt.1 hgt'⟩
  · rintro ⟨hban', h1, h2, h3, hgs', hgt'⟩
    exact ⟨permute_mem_lists x d hja σ', hban.2 hban', h1, h2, h3, hgs.2 hgs', hgt.2 hgt',
      fun i hi => absurd hi (by simp), fun i hi => absurd hi (Finset.notMem_empty i), S.2⟩

/-- The source lists of a block lie in `lists`. -/
theorem srcList_mem_lists {σ : Fin K → Equiv.Perm (Fin (padCount x + 1))}
    {P : Fin K → Fin (padCount x) → ℕ} {b : Fin K → ℕ} (hP : P ∈ padLists x d (padCount x))
    (hb : b ∈ lastSet x d P) : srcList x σ P b ∈ lists x d (padCount x) :=
  permute_mem_lists x d (joinList_mem_lists x d hP hb) fun i => (σ i).symm

variable (q A₀ Y d₀ u v r B) in
open scoped Classical in
/-- **The block coefficient**: for completing labels, the block kernel is
`M!^{-2K} ρ^{hits(z)} ρ^{hits(z')} ν(a) (d₀/D) η(b/Y) η(a/Y) ψ(t/Y) ([t - b + a = 0] - ∫_𝔐)`
on the admissible choices of `edgeValid_block_iff`, and zero otherwise. -/
theorem cleanBlockKer_eq (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (N : ℕ) (σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))) (S : MemState (Particle x d) B)
    {P : Fin K → Fin (padCount x) → ℕ} {b a : Fin K → ℕ}
    (hP : P ∈ padLists x d (padCount x)) (hb : b ∈ lastSet x d P) (ha : a ∈ lastSet x d P)
    (z z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) :
    cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P (z, b) (z', a) =
      if (∀ i, a i ≠ b i) ∧ d₀ ≤ ((∏ i, ∏ k, P i k : ℕ) : ℝ) ∧
          ((∏ i, ∏ k, P i k : ℕ) : ℝ) < 2 * d₀ ∧
          ((∏ i, ∏ k, P i k : ℕ) : ℤ) ∣ zdet z.1 z'.1 ∧
          PosGood x d Y d₀ r z.1 (joinList P b) ∧ PosGood x d Y d₀ r z'.1 (joinList P a) then
        (((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d z.1 S.1 * pendingWeight q ^ pendingHits x d z'.1 S.1 *
          cleanLabelWeight q x d N a * (d₀ / (∏ i, ∏ k, P i k : ℕ)) *
          dyadicBump ((∏ i, b i : ℕ) / Y) * dyadicBump ((∏ i, a i : ℕ) / Y) *
          plateau ((zdet z.1 z'.1 / (∏ i, ∏ k, P i k : ℕ) : ℤ) / Y) : ℝ) : ℂ) *
          ((if zdet z.1 z'.1 / (∏ i, ∏ k, P i k : ℕ) - (∏ i, b i : ℕ) + (∏ i, a i : ℕ) = 0
            then 1 else 0) -
            arcIntegral A₀ x Y (zdet z.1 z'.1 / (∏ i, ∏ k, P i k : ℕ) - (∏ i, b i : ℕ) +
              (∏ i, a i : ℕ)))
      else 0 := by
  have h := srcList_mem_lists (σ := σ) hP hb
  have hiff := edgeValid_block_iff (B := B) (S := S) (z := z) (z' := z') (σ' := σ') (Y := Y)
    (d₀ := d₀) (u := u) (v := v) (r := r) hdisj hP hb ha h
  unfold cleanBlockKer
  simp only [h, ↓reduceDIte]
  unfold chainEdgeCoef
  by_cases hv : (∀ i, a i ≠ b i) ∧ d₀ ≤ ((∏ i, ∏ k, P i k : ℕ) : ℝ) ∧
      ((∏ i, ∏ k, P i k : ℕ) : ℝ) < 2 * d₀ ∧ ((∏ i, ∏ k, P i k : ℕ) : ℤ) ∣ zdet z.1 z'.1 ∧
      PosGood x d Y d₀ r z.1 (joinList P b) ∧ PosGood x d Y d₀ r z'.1 (joinList P a)
  · have hv' := hiff.2 hv
    simp only [eq_true hv', eq_true hv, ↓reduceIte]
    simp only [edgeSrc_block h, edgePad_block h, edgeMem_block h, joinList_last,
      Bool.false_eq_true, ↓reduceIte]
    have ht : ∀ t b a : ℤ, (t = b - a) ↔ (t - b + a = 0) := fun t b a => by omega
    simp only [ht, cleanLabelWeight]
    rfl
  · have hv' : ¬ EdgeValid x d Y d₀ u v r B (z, ⟨srcList x σ P b, h⟩, S)
        ((σ, ∅, z', fun i => (a i, false), σ') : EdgeChoice x d Y d₀ u v r) := fun h' =>
      hv (hiff.1 h')
    simp only [hv', hv, ↓reduceIte]

/-- Minkowski for the weighted norm: `√(∑ μ |g + h|²) ≤ √(∑ μ |g|²) + √(∑ μ |h|²)`. -/
private theorem sqrt_wnormSq_add_le {ι : Type*} [Fintype ι] {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    (g h : ι → ℂ) : Real.sqrt (wnormSq μ (g + h)) ≤
      Real.sqrt (wnormSq μ g) + Real.sqrt (wnormSq μ h) := by
  have hg0 : 0 ≤ wnormSq μ g := sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hh0 : 0 ≤ wnormSq μ h := sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hS0 : 0 ≤ Real.sqrt (wnormSq μ g) + Real.sqrt (wnormSq μ h) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- `∑ μ |g| |h| ≤ ‖g‖ ‖h‖`
  have hcs : ∑ i, μ i * (‖g i‖ * ‖h i‖) ≤ Real.sqrt (wnormSq μ g) * Real.sqrt (wnormSq μ h) := by
    have hsq : ∀ (k : ι → ℂ), ∑ i, (Real.sqrt (μ i) * ‖k i‖) ^ 2 = wnormSq μ k := fun k => by
      unfold wnormSq
      exact sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt (hμ i)]
    calc ∑ i, μ i * (‖g i‖ * ‖h i‖) = ∑ i, (Real.sqrt (μ i) * ‖g i‖) * (Real.sqrt (μ i) * ‖h i‖) :=
          sum_congr rfl fun i _ => by
            rw [show Real.sqrt (μ i) * ‖g i‖ * (Real.sqrt (μ i) * ‖h i‖) =
              (Real.sqrt (μ i) * Real.sqrt (μ i)) * (‖g i‖ * ‖h i‖) by ring,
              Real.mul_self_sqrt (hμ i)]
      _ ≤ Real.sqrt (∑ i, (Real.sqrt (μ i) * ‖g i‖) ^ 2) *
            Real.sqrt (∑ i, (Real.sqrt (μ i) * ‖h i‖) ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = _ := by rw [hsq, hsq]
  have H : wnormSq μ (g + h) ≤ (Real.sqrt (wnormSq μ g) + Real.sqrt (wnormSq μ h)) ^ 2 :=
    calc wnormSq μ (g + h) ≤ ∑ i, μ i * (‖g i‖ + ‖h i‖) ^ 2 :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2) (hμ i)
      _ = wnormSq μ g + 2 * ∑ i, μ i * (‖g i‖ * ‖h i‖) + wnormSq μ h := by
          unfold wnormSq
          rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
          exact sum_congr rfl fun i _ => by ring
      _ ≤ wnormSq μ g + 2 * (Real.sqrt (wnormSq μ g) * Real.sqrt (wnormSq μ h)) + wnormSq μ h := by
          linarith
      _ = (Real.sqrt (wnormSq μ g) + Real.sqrt (wnormSq μ h)) ^ 2 := by
          rw [add_sq, Real.sq_sqrt hg0, Real.sq_sqrt hh0]
          ring
  calc Real.sqrt (wnormSq μ (g + h))
      ≤ Real.sqrt ((Real.sqrt (wnormSq μ g) + Real.sqrt (wnormSq μ h)) ^ 2) := Real.sqrt_le_sqrt H
    _ = _ := Real.sqrt_sq hS0

/-- Norm bounds add over a finite family (Minkowski). -/
private theorem normLe_finset_sum {ι κ γ : Type*} [Fintype ι] [Fintype κ] {μ : ι → ℝ}
    {ν : κ → ℝ} (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ j, 0 ≤ ν j) (s : Finset γ) {T : γ → (κ → ℂ) → ι → ℂ} {c : γ → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (hT : ∀ k ∈ s, NormLe μ ν (T k) (c k)) :
    NormLe μ ν (fun f i => ∑ k ∈ s, T k f i) (∑ k ∈ s, c k) := by
  classical
  intro f
  set F := Real.sqrt (wnormSq ν f) with hF
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  -- `‖T_k f‖ ≤ c_k ‖f‖`
  have hk : ∀ k ∈ s, Real.sqrt (wnormSq μ (T k f)) ≤ c k * F := fun k hk => by
    rw [hF, ← Real.sqrt_sq (hc k hk), ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hT k hk f)
  have hsum : Real.sqrt (wnormSq μ (fun i => ∑ k ∈ s, T k f i)) ≤ (∑ k ∈ s, c k) * F := by
    induction s using Finset.induction_on with
    | empty =>
      simp [wnormSq]
    | insert k s hks ih =>
      have e : (fun i => ∑ k' ∈ insert k s, T k' f i) = T k f + fun i => ∑ k' ∈ s, T k' f i := by
        funext i
        rw [sum_insert hks]
        rfl
      rw [e, sum_insert hks, add_mul]
      refine (sqrt_wnormSq_add_le hμ _ _).trans (add_le_add (hk k (mem_insert_self k s)) ?_)
      exact ih (fun k' hk' => hc k' (mem_insert_of_mem hk'))
        (fun k' hk' => hT k' (mem_insert_of_mem hk')) (fun k' hk' => hk k' (mem_insert_of_mem hk'))
  have h0 : 0 ≤ wnormSq μ (fun i => ∑ k ∈ s, T k f i) :=
    sum_nonneg fun i _ => mul_nonneg (hμ i) (sq_nonneg _)
  have hc0 : 0 ≤ ∑ k ∈ s, c k := sum_nonneg hc
  calc wnormSq μ (fun i => ∑ k ∈ s, T k f i) = Real.sqrt (wnormSq μ (fun i => ∑ k ∈ s, T k f i)) ^ 2 :=
        (Real.sq_sqrt h0).symm
    _ ≤ ((∑ k ∈ s, c k) * F) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsum 2
    _ = (∑ k ∈ s, c k) ^ 2 * wnormSq ν f := by
        rw [mul_pow, hF, Real.sq_sqrt (show 0 ≤ wnormSq ν f from
          sum_nonneg fun j _ => mul_nonneg (hν j) (sq_nonneg _))]

/-- **Splitting the chain states**: a sum over chain states is a sum over memories `S`, pads `P`,
positions `z` and completing labels `b`, of the states with lists `joinList P b` reordered by
`τ`. -/
theorem sum_chainState_split (τ : Fin K → Equiv.Perm (Fin (padCount x + 1)))
    (F : ChainState x d Y d₀ u v r B → ℝ) :
    ∑ s, F s = ∑ S : MemState (Particle x d) B, ∑ P ∈ padLists x d (padCount x),
      ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), ∑ b ∈ lastSet x d P,
        (if h : (fun i => joinList P b i ∘ τ i) ∈ lists x d (padCount x) then
          F (z, ⟨_, h⟩, S) else 0) := by
  classical
  set Fe : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → Lists K (padCount x) →
      MemState (Particle x d) B → ℝ := fun z L S =>
    if h : L ∈ lists x d (padCount x) then F (z, ⟨L, h⟩, S) else 0 with hFe
  have hsplit1 : ∑ s, F s = ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      ∑ L : ↥(lists x d (padCount x)), ∑ S : MemState (Particle x d) B, F (z, L, S) := by
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun z _ => Fintype.sum_prod_type _
  have hsplit2 : ∀ z S, ∑ L : ↥(lists x d (padCount x)), F (z, L, S) =
      ∑ L ∈ lists x d (padCount x), Fe z L S := by
    intro z S
    rw [← Finset.sum_coe_sort (lists x d (padCount x)) (fun L => Fe z L S)]
    refine sum_congr rfl fun L _ => ?_
    simp only [hFe, L.2, ↓reduceDIte]
  rw [hsplit1]
  calc ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), ∑ L : ↥(lists x d (padCount x)),
        ∑ S : MemState (Particle x d) B, F (z, L, S)
      = ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r), ∑ S : MemState (Particle x d) B,
          ∑ P ∈ padLists x d (padCount x), ∑ b ∈ lastSet x d P,
            Fe z (fun i => joinList P b i ∘ τ i) S := by
        refine sum_congr rfl fun z _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        rw [hsplit2, sum_lists_eq x d τ]
    _ = ∑ S : MemState (Particle x d) B, ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
          ∑ P ∈ padLists x d (padCount x), ∑ b ∈ lastSet x d P,
            Fe z (fun i => joinList P b i ∘ τ i) S := sum_comm
    _ = _ := sum_congr rfl fun S _ => sum_comm

/-- Last labels completing `P` to a list are completing labels. -/
theorem mem_lastSet_of_joinList_mem {P : Fin K → Fin (padCount x) → ℕ} {a : Fin K → ℕ}
    (h : joinList P a ∈ lists x d (padCount x)) : a ∈ lastSet x d P := by
  classical
  obtain ⟨hband, hinj⟩ := mem_filter.1 h
  refine Fintype.mem_piFinset.2 fun i => mem_filter.2 ⟨?_, fun k hk => ?_⟩
  · have := Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hband i) (Fin.last _)
    rwa [joinList_last] at this
  · have hk' : joinList P a i k.castSucc = joinList P a i (Fin.last _) := by
      rw [joinList_castSucc, joinList_last, hk]
    exact (Fin.castSucc_lt_last k).ne (hinj i hk')

/-- **The clean edge as an average over the symmetrizations**: the clean choices are the
symmetrizations `σ, σ'`, the target `z'` and the fresh labels `a`. -/
theorem choiceOp_cleanChoices_eq (N : ℕ) (f : ChainState x d Y d₀ u v r B → ℂ)
    (s : ChainState x d Y d₀ u v r B) :
    choiceOp (cleanChoices x d Y d₀ u v r) (chainEdgeCoef q A₀ x d Y d₀ u v r B N)
        (chainEdgeOut x d Y d₀ u v r B) f s =
      ∑ σσ' ∈ (univ : Finset ((Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
          (Fin K → Equiv.Perm (Fin (padCount x + 1))))),
        ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
          ∑ a ∈ Fintype.piFinset (fun i => band x (d.a i)),
            chainEdgeCoef q A₀ x d Y d₀ u v r B N s (σσ'.1, ∅, z', fun i => (a i, false), σσ'.2) *
              f (chainEdgeOut x d Y d₀ u v r B s (σσ'.1, ∅, z', fun i => (a i, false), σσ'.2)) := by
  classical
  unfold choiceOp
  simp only [← sum_product']
  refine sum_nbij' (fun c => ((c.1, c.2.2.2.2), (c.2.2.1, fun i => (c.2.2.2.1 i).1)))
    (fun t => (t.1.1, ∅, t.2.1, fun i => (t.2.2 i, false), t.1.2)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [cleanChoices, mem_filter] at hc
    obtain ⟨hc₁, -, -⟩ := hc
    simp only [edgeChoices, mem_product, mem_univ, true_and, Fintype.mem_piFinset] at hc₁
    simp only [mem_product, mem_univ, true_and, Fintype.mem_piFinset]
    exact fun i => (hc₁.1 i).1
  · intro t ht
    simp only [mem_product, mem_univ, true_and, Fintype.mem_piFinset] at ht
    rw [cleanChoices, mem_filter]
    refine ⟨?_, rfl, ?_⟩
    · simp only [edgeChoices, mem_product, mem_univ, true_and, Fintype.mem_piFinset, and_true]
      exact fun i => ht i
    · ext i
      simp
  · intro c hc
    rw [cleanChoices, mem_filter] at hc
    obtain ⟨-, hS, hI⟩ := hc
    have hfalse : ∀ i, (c.2.2.2.1 i).2 = false := by
      intro i
      by_contra h
      have : i ∈ univ.filter (fun i => (c.2.2.2.1 i).2 = true) := by simpa using h
      rw [hI] at this
      exact Finset.notMem_empty i this
    obtain ⟨σ, S₀, z', lab, σ'⟩ := c
    simp only at hS hfalse ⊢
    subst hS
    congr
    funext i
    exact Prod.ext rfl (hfalse i).symm
  · intro t _
    rfl
  · intro c hc
    rw [cleanChoices, mem_filter] at hc
    obtain ⟨-, hS, hI⟩ := hc
    have hfalse : ∀ i, (c.2.2.2.1 i).2 = false := by
      intro i
      by_contra h
      have : i ∈ univ.filter (fun i => (c.2.2.2.1 i).2 = true) := by simpa using h
      rw [hI] at this
      exact Finset.notMem_empty i this
    obtain ⟨σ, S₀, z', lab, σ'⟩ := c
    simp only at hS hfalse ⊢
    subst hS
    have : (fun i => ((lab i).1, false)) = lab := funext fun i => Prod.ext rfl (hfalse i).symm
    rw [this]

open scoped Classical in
/-- **The clean edge on a block**: at a source of the block `(S, P)`, the clean edge with fixed
symmetrizations is the block kernel applied to the targets `(z', a)` of the block. -/
theorem symEdge_block_eq (N : ℕ) (σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1)))
    (S : MemState (Particle x d) B) {P : Fin K → Fin (padCount x) → ℕ} {b : Fin K → ℕ}
    (hP : P ∈ padLists x d (padCount x)) (hb : b ∈ lastSet x d P)
    (z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) (f : ChainState x d Y d₀ u v r B → ℂ) :
    ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      ∑ a ∈ Fintype.piFinset (fun i => band x (d.a i)),
        chainEdgeCoef q A₀ x d Y d₀ u v r B N (z, ⟨srcList x σ P b, srcList_mem_lists hP hb⟩, S)
            (σ, ∅, z', fun i => (a i, false), σ') *
          f (chainEdgeOut x d Y d₀ u v r B (z, ⟨srcList x σ P b, srcList_mem_lists hP hb⟩, S)
            (σ, ∅, z', fun i => (a i, false), σ')) =
      ∑ p' ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ lastSet x d P,
        cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P (z, b) p' *
          (if h : (fun i => joinList P p'.2 i ∘ σ' i) ∈ lists x d (padCount x) then
            f (p'.1, ⟨_, h⟩, S) else 0) := by
  have hsrc := srcList_mem_lists (σ := σ) hP hb
  rw [sum_product]
  refine sum_congr rfl fun z' _ => ?_
  have hsub : lastSet x d P ⊆ Fintype.piFinset (fun i => band x (d.a i)) := fun a ha =>
    Fintype.mem_piFinset.2 fun i => (mem_filter.1 (Fintype.mem_piFinset.1 ha i)).1
  rw [← sum_subset hsub fun a _ ha => ?_]
  · refine sum_congr rfl fun a ha => ?_
    have hkblk : cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P (z, b) (z', a) =
        chainEdgeCoef q A₀ x d Y d₀ u v r B N (z, ⟨srcList x σ P b, hsrc⟩, S)
          (σ, ∅, z', fun i => (a i, false), σ') := by
      unfold cleanBlockKer
      simp only [hsrc, ↓reduceDIte]
    rw [hkblk]
    by_cases hv : EdgeValid x d Y d₀ u v r B (z, ⟨srcList x σ P b, hsrc⟩, S)
        ((σ, ∅, z', fun i => (a i, false), σ') : EdgeChoice x d Y d₀ u v r)
    · have htgt : (fun i => joinList P a i ∘ σ' i) ∈ lists x d (padCount x) :=
        edgeTgt_block (a := a) (S := S) (z := z) (z' := z') (σ' := σ') hsrc ▸ hv.1
      simp only [htgt, ↓reduceDIte]
      congr 2
      unfold chainEdgeOut
      simp only [hv, ↓reduceDIte]
      refine Prod.ext rfl (Prod.ext (Subtype.ext (edgeTgt_block hsrc)) (Subtype.ext ?_))
      exact edgeMem_block hsrc
    · have h0 : chainEdgeCoef q A₀ x d Y d₀ u v r B N (z, ⟨srcList x σ P b, hsrc⟩, S)
          (σ, ∅, z', fun i => (a i, false), σ') = 0 := by
        unfold chainEdgeCoef
        simp only [hv, ↓reduceIte]
      rw [h0, zero_mul, zero_mul]
  · -- a fresh label among the pads breaks the target list
    have hv : ¬ EdgeValid x d Y d₀ u v r B (z, ⟨srcList x σ P b, hsrc⟩, S)
        ((σ, ∅, z', fun i => (a i, false), σ') : EdgeChoice x d Y d₀ u v r) := by
      intro hv
      have h1 := hv.1
      rw [edgeTgt_block hsrc] at h1
      have h2 := permute_mem_lists x d h1 fun i => (σ' i).symm
      have e : (fun i => (joinList P a i ∘ σ' i) ∘ (σ' i).symm) = joinList P a := by
        funext i k
        simp
      rw [e] at h2
      exact ha (mem_lastSet_of_joinList_mem h2)
    unfold chainEdgeCoef
    simp only [hv, ↓reduceIte, zero_mul]

/-- **The block reduction**: if every block kernel has weighted norm at most `M!^{-2K} E` for the
label weights `ν`, then the clean edge has norm at most `E` for the chain measure. -/
theorem normLe_cleanOp_of_blocks (N : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hblk : ∀ (σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))) (S : MemState (Particle x d) B),
      ∀ P ∈ padLists x d (padCount x),
      WKerLe (univ ×ˢ lastSet x d P) (univ ×ˢ lastSet x d P)
        (fun p => cleanLabelWeight q x d N p.2) (fun p => cleanLabelWeight q x d N p.2)
        (cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P)
        ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * E)) :
    NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (choiceOp (cleanChoices x d Y d₀ u v r) (chainEdgeCoef q A₀ x d Y d₀ u v r B N)
        (chainEdgeOut x d Y d₀ u v r B)) E := by
  classical
  set Mf : ℝ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hMf
  have hMf0 : 0 ≤ Mf := by positivity
  have hμ : ∀ s : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
    fun s => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  -- the edge for fixed symmetrizations
  set T : (Fin K → Equiv.Perm (Fin (padCount x + 1))) →
      (Fin K → Equiv.Perm (Fin (padCount x + 1))) →
      (ChainState x d Y d₀ u v r B → ℂ) → ChainState x d Y d₀ u v r B → ℂ := fun σ σ' f s =>
    ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      ∑ a ∈ Fintype.piFinset (fun i => band x (d.a i)),
        chainEdgeCoef q A₀ x d Y d₀ u v r B N s (σ, ∅, z', fun i => (a i, false), σ') *
          f (chainEdgeOut x d Y d₀ u v r B s (σ, ∅, z', fun i => (a i, false), σ')) with hT
  -- the weight of a block state
  set μ₀ : MemState (Particle x d) B → (Fin K → Fin (padCount x) → ℕ) → ℝ := fun S P =>
    (∏ i, ∏ k, primeWeight q x d N (P i k)) *
      memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) S.1 with hμ₀
  have hμ₀0 : ∀ S P, 0 ≤ μ₀ S P := fun S P =>
    mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun k _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  have hμblk : ∀ (τ : Fin K → Equiv.Perm (Fin (padCount x + 1))) (z : ↥(rootPositions
      (d₀ * Y * d.Hm) d.Hn u v r)) (S : MemState (Particle x d) B) (P : Fin K → Fin (padCount x) → ℕ)
      (b : Fin K → ℕ) (h : (fun i => joinList P b i ∘ τ i) ∈ lists x d (padCount x)),
      chainMeasure q x d Y d₀ u v r B N (z, ⟨_, h⟩, S) = μ₀ S P * cleanLabelWeight q x d N b := by
    intro τ z S P b h
    unfold chainMeasure
    rw [prod_joinList_permute (fun p => primeWeight q x d N p) P b τ, hμ₀, cleanLabelWeight]
    ring
  have hTσ : ∀ σ σ', NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (fun s => chainMeasure q x d Y d₀ u v r B N s) (T σ σ') (Mf * E) := by
    intro σ σ' f
    -- the targets of a block
    set g : MemState (Particle x d) B → (Fin K → Fin (padCount x) → ℕ) →
        ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) → ℂ := fun S P p' =>
      if h : (fun i => joinList P p'.2 i ∘ σ' i) ∈ lists x d (padCount x) then
        f (p'.1, ⟨_, h⟩, S) else 0 with hg
    -- split the source states
    have hL : wnormSq (fun s => chainMeasure q x d Y d₀ u v r B N s) (T σ σ' f) =
        ∑ S : MemState (Particle x d) B, ∑ P ∈ padLists x d (padCount x), μ₀ S P *
          ∑ p ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ lastSet x d P,
            cleanLabelWeight q x d N p.2 *
              ‖∑ p' ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ
                lastSet x d P, cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P p p' * g S P p'‖ ^ 2 := by
      unfold wnormSq
      rw [sum_chainState_split (fun i => (σ i).symm)]
      refine sum_congr rfl fun S _ => sum_congr rfl fun P hP => ?_
      rw [sum_product, mul_sum]
      refine sum_congr rfl fun z _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun b hb => ?_
      have hsrc := srcList_mem_lists (σ := σ) hP hb
      have hsrc' : (fun i => joinList P b i ∘ (σ i).symm) ∈ lists x d (padCount x) := hsrc
      simp only [hsrc', ↓reduceDIte]
      rw [hμblk]
      have hTe : T σ σ' f (z, ⟨srcList x σ P b, hsrc⟩, S) = ∑ p' ∈ (univ : Finset
          ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ lastSet x d P,
          cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P (z, b) p' * g S P p' :=
        symEdge_block_eq N σ σ' S hP hb z f
      rw [show (z, (⟨fun i => joinList P b i ∘ (σ i).symm, hsrc⟩ : ↥(lists x d (padCount x))), S) =
        (z, ⟨srcList x σ P b, hsrc⟩, S) from rfl, hTe]
      ring
    -- split the target states
    have hR : wnormSq (fun s => chainMeasure q x d Y d₀ u v r B N s) f =
        ∑ S : MemState (Particle x d) B, ∑ P ∈ padLists x d (padCount x), μ₀ S P *
          ∑ p' ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ lastSet x d P,
            cleanLabelWeight q x d N p'.2 * ‖g S P p'‖ ^ 2 := by
      unfold wnormSq
      rw [sum_chainState_split σ']
      refine sum_congr rfl fun S _ => sum_congr rfl fun P hP => ?_
      rw [sum_product, mul_sum]
      refine sum_congr rfl fun z _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun a ha => ?_
      have htgt := permute_mem_lists x d (joinList_mem_lists x d hP ha) σ'
      simp only [htgt, ↓reduceDIte, hg]
      rw [hμblk]
      ring
    rw [hL, hR, mul_sum]
    refine sum_le_sum fun S _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun P hP => ?_
    have h := hblk σ σ' S P hP (g S P)
    calc μ₀ S P * ∑ p ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ
          lastSet x d P, cleanLabelWeight q x d N p.2 *
            ‖∑ p' ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ
              lastSet x d P, cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P p p' * g S P p'‖ ^ 2
        ≤ μ₀ S P * ((Mf * E) ^ 2 *
            ∑ p' ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ lastSet x d P,
              cleanLabelWeight q x d N p'.2 * ‖g S P p'‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h (hμ₀0 S P)
      _ = _ := by ring
  -- average over the symmetrizations
  have hsum := normLe_finset_sum hμ hμ (univ : Finset ((Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
      (Fin K → Equiv.Perm (Fin (padCount x + 1)))))
    (T := fun σσ' => T σσ'.1 σσ'.2) (c := fun _ => Mf * E) (fun _ _ => mul_nonneg hMf0 hE)
    (fun σσ' _ => hTσ σσ'.1 σσ'.2)
  have hcount : ∑ _σσ' ∈ (univ : Finset ((Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
      (Fin K → Equiv.Perm (Fin (padCount x + 1))))), Mf * E = E := by
    rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_pi, Fintype.card_perm,
      Fintype.card_fin, prod_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hMf]
    have h0 : (((padCount x + 1).factorial ^ K : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at h0 ⊢
    field_simp
  intro f
  have e : choiceOp (cleanChoices x d Y d₀ u v r) (chainEdgeCoef q A₀ x d Y d₀ u v r B N)
      (chainEdgeOut x d Y d₀ u v r B) f = fun s => ∑ σσ' ∈ (univ : Finset
        ((Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
          (Fin K → Equiv.Perm (Fin (padCount x + 1))))), T σσ'.1 σσ'.2 f s := by
    funext s
    exact choiceOp_cleanChoices_eq N f s
  rw [e]
  have := hsum f
  rwa [hcount] at this

end Blocks

/-- With baselines at least `1/2` at the band primes, the birth weights are nonnegative. -/
theorem primeWeight_nonneg_of_baseline {q x : ℝ} {d : Data K} {N : ℕ}
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (p : ℕ) : 0 ≤ primeWeight q x d N p := by
  have hV : 0 ≤ primeMass x d p :=
    sum_nonneg fun i _ => by
      split_ifs
      · exact sum_nonneg fun p _ => by positivity
      · exact le_rfl
  unfold primeWeight
  by_cases hp : p ∈ bandPrimes x d
  · have := hb p hp
    exact one_div_nonneg.2 (mul_nonneg (mul_nonneg hV (by positivity)) (by linarith))
  · have h0 : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_biUnion.2 ⟨i, mem_univ i, hpi⟩)
    rw [h0]
    simp

/-! ### The block bound -/

section Weights

variable {q x : ℝ} {d : Data K} {N : ℕ}

/-- At a prime of a band, `0 < ν(p) ≤ 4/p`. -/
theorem primeWeight_pos_le_of_mem
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hbase : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {i : Fin K} {p : ℕ}
    (hp : p ∈ band x (d.a i)) :
    0 < primeWeight q x d N p ∧ primeWeight q x d N p ≤ 4 * (1 / p) := by
  have hmem : p ∈ bandPrimes x d := mem_biUnion.2 ⟨i, mem_univ i, hp⟩
  have hV₁ : 1 / 2 ≤ primeMass x d p :=
    calc 1 / 2 ≤ harmonicMass (band x (d.a i)) := (hV i).1
      _ = if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0 := by simp [hp]
      _ ≤ primeMass x d p :=
          single_le_sum (f := fun i => if p ∈ band x (d.a i) then harmonicMass (band x (d.a i))
            else 0) (fun j _ => by
              split_ifs
              · exact sum_nonneg fun p _ => by positivity
              · exact le_rfl) (mem_univ i)
  have hb₁ := hbase p hmem
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hp).pos
  unfold primeWeight
  refine ⟨one_div_pos.2 (mul_pos (mul_pos (by linarith) (by positivity)) (by linarith)), ?_⟩
  calc 1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p)
      ≤ 1 / (1 / 2 * p * (1 / 2)) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul (mul_le_mul hV₁ (by linarith) hp0.le (by linarith)) hb₁ (by norm_num)
            (mul_nonneg (by linarith) (by linarith)))
    _ = 4 * (1 / p) := by field_simp; norm_num

/-- The birth weights of a band sum to at most `4`. -/
theorem sum_primeWeight_subset_band_le
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hbase : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (i : Fin K) {F : Finset ℕ}
    (hF : F ⊆ band x (d.a i)) : ∑ p ∈ F, primeWeight q x d N p ≤ 4 :=
  calc ∑ p ∈ F, primeWeight q x d N p ≤ ∑ p ∈ F, 4 * (1 / (p : ℝ)) :=
        sum_le_sum fun p hp => (primeWeight_pos_le_of_mem hV hbase (hF hp)).2
    _ ≤ ∑ p ∈ band x (d.a i), 4 * (1 / (p : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hF fun p _ _ => by positivity
    _ = 4 * harmonicMass (band x (d.a i)) := (mul_sum _ _ _).symm
    _ ≤ 4 := by linarith [(hV i).2]

/-- Completing labels have positive weight `ν(b) ≤ 4^K / ∏ b`. -/
theorem labelWeight_pos_le
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hbase : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {b : Fin K → ℕ}
    (hb : ∀ i, b i ∈ band x (d.a i)) :
    0 < cleanLabelWeight q x d N b ∧ cleanLabelWeight q x d N b ≤ 4 ^ K / ∏ i, (b i : ℝ) := by
  have hpos : ∀ i, (0 : ℝ) < b i := fun i => by exact_mod_cast (TypeII.band_prime (hb i)).pos
  refine ⟨prod_pos fun i _ => (primeWeight_pos_le_of_mem hV hbase (hb i)).1, ?_⟩
  calc cleanLabelWeight q x d N b ≤ ∏ i, 4 * (1 / (b i : ℝ)) :=
        prod_le_prod₀ (fun i _ => (primeWeight_pos_le_of_mem hV hbase (hb i)).1.le)
          fun i _ => (primeWeight_pos_le_of_mem hV hbase (hb i)).2
    _ = 4 ^ K / ∏ i, (b i : ℝ) := by
        rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_div_distrib,
          prod_const_one]
        ring

/-- **The coincidence mass**: the completing labels `a` agreeing with `b` in some group have
weight at most `K 4^K sup ν`, with `sup ν ≤ 4 e^{-L^{a₋}}`. -/
theorem sum_labelWeight_coinc_le {alo : ℝ}
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hbase : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)
    (hbig : ∀ i, ∀ p ∈ band x (d.a i), Real.exp (Real.log x ^ alo) ≤ p)
    {J : ℕ} (P : Fin K → Fin J → ℕ) (b : Fin K → ℕ) :
    ∑ a ∈ lastSet x d P, (if ∃ i, a i = b i then cleanLabelWeight q x d N a else 0) ≤
      K * 4 ^ K * (4 * Real.exp (-Real.log x ^ alo)) := by
  classical
  set νm := 4 * Real.exp (-Real.log x ^ alo) with hνm
  have hνm0 : 0 ≤ νm := by positivity
  set F : Fin K → Finset ℕ := fun i => (band x (d.a i)).filter fun p => ∀ h, P i h ≠ p with hF
  have hFsub : ∀ i, F i ⊆ band x (d.a i) := fun i => filter_subset _ _
  -- `ν(p) ≤ sup ν` on the bands
  have hνp : ∀ i, ∀ p ∈ band x (d.a i), primeWeight q x d N p ≤ νm := by
    intro i p hp
    have h1 := (primeWeight_pos_le_of_mem hV hbase hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hp).pos
    have h2 : 1 / (p : ℝ) ≤ Real.exp (-Real.log x ^ alo) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos _) (hbig i p hp)
    rw [hνm]
    linarith
  have hν0 : ∀ p, 0 ≤ primeWeight q x d N p := fun p =>
    primeWeight_nonneg_of_baseline hbase p
  -- one group at a time
  have key : ∀ i, ∑ a ∈ lastSet x d P, (if a i = b i then cleanLabelWeight q x d N a else 0) ≤
      4 ^ K * νm := by
    intro i
    set g : Fin K → ℕ → ℝ := fun j p =>
      if j = i then (if p = b i then primeWeight q x d N p else 0) else primeWeight q x d N p
      with hg
    have e : ∑ a ∈ lastSet x d P, (if a i = b i then cleanLabelWeight q x d N a else 0) =
        ∏ j, ∑ p ∈ F j, g j p := by
      rw [prod_univ_sum]
      refine sum_congr rfl fun a _ => ?_
      by_cases ha : a i = b i
      · simp only [ha, ↓reduceIte, cleanLabelWeight]
        refine prod_congr rfl fun j _ => ?_
        by_cases hj : j = i
        · subst hj
          simp [hg, ha]
        · simp [hg, hj]
      · simp only [ha, ↓reduceIte]
        symm
        refine prod_eq_zero (mem_univ i) ?_
        simp [hg, ha]
    rw [e, ← mul_prod_erase _ _ (mem_univ i)]
    have hci : ∑ p ∈ F i, g i p ≤ νm := by
      simp only [hg, ↓reduceIte]
      rw [sum_ite_eq']
      split_ifs with hbi
      · exact hνp i (b i) (hFsub i hbi)
      · exact hνm0
    have hcj : ∏ j ∈ univ.erase i, ∑ p ∈ F j, g j p ≤ 4 ^ K := by
      calc ∏ j ∈ univ.erase i, ∑ p ∈ F j, g j p ≤ ∏ _j ∈ univ.erase i, (4 : ℝ) := by
            refine prod_le_prod₀ (fun j _ => sum_nonneg fun p _ => ?_) fun j hj => ?_
            · simp only [hg]
              split_ifs <;> simp [hν0]
            · have hji : j ≠ i := ne_of_mem_erase hj
              simp only [hg, hji, ↓reduceIte]
              exact sum_primeWeight_subset_band_le hV hbase j (hFsub j)
        _ = 4 ^ (K - 1) := by rw [prod_const, card_erase_of_mem (mem_univ i), card_univ,
            Fintype.card_fin]
        _ ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) (Nat.sub_le K 1)
    have hci0 : 0 ≤ ∑ p ∈ F i, g i p := sum_nonneg fun p _ => by
      simp only [hg]
      split_ifs <;> simp [hν0]
    calc (∑ p ∈ F i, g i p) * ∏ j ∈ univ.erase i, ∑ p ∈ F j, g j p ≤ νm * 4 ^ K :=
          mul_le_mul hci hcj (prod_nonneg fun j _ => sum_nonneg fun p _ => by
            simp only [hg]
            split_ifs <;> simp [hν0]) hνm0
      _ = 4 ^ K * νm := by ring
  -- union over the groups
  calc ∑ a ∈ lastSet x d P, (if ∃ i, a i = b i then cleanLabelWeight q x d N a else 0)
      ≤ ∑ a ∈ lastSet x d P, ∑ i, (if a i = b i then cleanLabelWeight q x d N a else 0) := by
        refine sum_le_sum fun a _ => ?_
        split_ifs with h
        · obtain ⟨i, hi⟩ := h
          calc cleanLabelWeight q x d N a = if a i = b i then cleanLabelWeight q x d N a else 0 := by
                simp only [hi, ↓reduceIte]
            _ ≤ ∑ i, (if a i = b i then cleanLabelWeight q x d N a else 0) :=
                single_le_sum (f := fun i => if a i = b i then cleanLabelWeight q x d N a else 0)
                  (fun j _ => by split_ifs; exacts [prod_nonneg fun k _ => hν0 _, le_rfl])
                  (mem_univ i)
        · exact sum_nonneg fun i _ => by split_ifs; exacts [prod_nonneg fun k _ => hν0 _, le_rfl]
    _ = ∑ i, ∑ a ∈ lastSet x d P, (if a i = b i then cleanLabelWeight q x d N a else 0) := sum_comm
    _ ≤ ∑ _i : Fin K, 4 ^ K * νm := sum_le_sum fun i _ => key i
    _ = K * 4 ^ K * νm := by simp; ring

end Weights

/-- The label product is injective on completing labels, the bands being disjoint. -/
theorem injOn_labelProd {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {J : ℕ}
    (P : Fin K → Fin J → ℕ) :
    Set.InjOn (fun b : Fin K → ℕ => ((∏ i, b i : ℕ) : ℤ)) (lastSet x d P) := by
  intro b hb b' hb' he
  have he' : ∏ i, b i = ∏ i, b' i := by
    have : ((∏ i, b i : ℕ) : ℤ) = ((∏ i, b' i : ℕ) : ℤ) := he
    exact_mod_cast this
  have hbb : ∀ i, b i ∈ band x (d.a i) := fun i =>
    (mem_filter.1 (Fintype.mem_piFinset.1 (mem_coe.1 hb) i)).1
  have hbb' : ∀ i, b' i ∈ band x (d.a i) := fun i =>
    (mem_filter.1 (Fintype.mem_piFinset.1 (mem_coe.1 hb') i)).1
  funext i
  -- `b i` divides `∏ b'`, hence some `b' j`, and then `j = i`
  have hdvd : b i ∣ ∏ j, b' j := he' ▸ dvd_prod_of_mem _ (mem_univ i)
  obtain ⟨j, -, hj⟩ := (Nat.Prime.prime (TypeII.band_prime (hbb i))).dvd_finsetProd_iff _ |>.1 hdvd
  have heq : b i = b' j :=
    (Nat.prime_dvd_prime_iff_eq (TypeII.band_prime (hbb i)) (TypeII.band_prime (hbb' j))).1 hj
  by_cases hij : i = j
  · rw [heq, hij]
  · exact ((disjoint_left.1 (hdisj i j hij) (hbb i)) (heq ▸ hbb' j)).elim

/-- The pad product of a pad list is squarefree. -/
theorem squarefree_padProd {x : ℝ} {d : Data K}
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {J : ℕ}
    {P : Fin K → Fin J → ℕ} (hP : P ∈ padLists x d J) : Squarefree (∏ i, ∏ k, P i k) := by
  have hP' := mem_filter.1 hP
  have hband : ∀ i k, P i k ∈ band x (d.a i) := fun i k =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hP'.1 i) k
  rw [← prod_product' (f := fun i k => P i k)]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun ik _ jl _ hne => ?_)
    fun ik _ => (TypeII.band_prime (hband ik.1 ik.2)).prime.squarefree
  simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
  refine (Nat.coprime_primes (TypeII.band_prime (hband _ _)) (TypeII.band_prime (hband _ _))).2
    fun he => hne ?_
  by_cases hij : ik.1 = jl.1
  · have : ik.2 = jl.2 := by
      have := he
      rw [hij] at this
      exact hP'.2 jl.1 this
    exact Prod.ext hij this
  · exact ((disjoint_left.1 (hdisj _ _ hij) (hband ik.1 ik.2)) (he ▸ hband jl.1 jl.2)).elim

/-- Test (i) at the omission of the last slots gives the pad part `GoodPad`. -/
theorem goodPad_of_posGood {x : ℝ} {d : Data K} {Y d₀ r : ℝ}
    {P : Fin K → Fin (padCount x) → ℕ} {b : Fin K → ℕ} {z : ℤ × ℤ}
    (hD₁ : d₀ ≤ ((∏ i, ∏ k, P i k : ℕ) : ℝ)) (hD₂ : ((∏ i, ∏ k, P i k : ℕ) : ℝ) < 2 * d₀)
    (h : PosGood x d Y d₀ r z (joinList P b)) :
    GoodPad Y (∏ i, ∏ k, P i k) (posRatio r z) := by
  have homit : omitProd (joinList P b) (fun _ => Fin.last _) = ∏ i, ∏ k, P i k := by
    unfold omitProd
    refine prod_congr rfl fun i _ => ?_
    have hset : (univ : Finset (Fin (padCount x + 1))).erase (Fin.last _) =
        univ.map Fin.castSuccEmb := by
      ext k
      induction k using Fin.lastCases with
      | last => simp
      | cast k => simp [(Fin.castSucc_lt_last k).ne]
    rw [hset, prod_map]
    exact prod_congr rfl fun k _ => joinList_castSucc P b i k
  intro l hl hlY
  have := h.1 (fun _ => Fin.last _) (by rw [homit]; exact hD₁) (by rw [homit]; exact hD₂) l hl hlY
  rw [homit] at this
  exact this


/-- The bound of one clean block, up to the factor `M!^{-2K}`: the core term
`4^K C₀ (1 + log 4Y)(L^{-A₀} + Y^{-0.1})` and the coincidence term
`1024 K 4^K (1 + 52 L^{3A₀}) e^{-L^{a₋}}`. -/
def cleanBound (K : ℕ) (C₀ A₀ alo x Y : ℝ) : ℝ :=
  4 ^ K * C₀ * (1 + Real.log (4 * Y)) * ((Real.log x ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ))) +
    1024 * K * 4 ^ K * (1 + 52 * Real.log x ^ (3 * A₀)) * Real.exp (-Real.log x ^ alo)

open scoped Classical in
/-- **The clean block bound** in a block with pad product in `[d₀, 2d₀)` and size conditions at
`Y`: the block kernel has weighted norm at most `M!^{-2K} E`. -/
theorem wkerLe_cleanBlockKer_main {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcore : ∀ {κ : Type} (X : Finset κ) (β : κ → ℤ),
      Set.InjOn β X → ∀ (A₀ x Y d₀ U V u v r : ℝ) (D : ℕ),
      2 ≤ Real.log x ^ A₀ → 8 * (Real.log x ^ A₀) ^ 3 ≤ Y → 8 * latConst ≤ Y ^ (1 / 10 : ℝ) →
      0 < d₀ → d₀ ≤ D → (D : ℝ) < 2 * d₀ → Squarefree D → 0 < U → U ≤ u → u ≤ 16 * U →
      KerLe (rootPositions U V u v r ×ˢ X) (rootPositions U V u v r ×ˢ X)
        (fun q q' => if GoodPad Y D (posRatio r q.1) ∧ (D : ℤ) ∣ zdet q.1 q'.1 then
          (plateau ((zdet q.1 q'.1 / D : ℤ) / Y) : ℂ) *
            ((if zdet q.1 q'.1 / D - β q.2 + β q'.2 = 0 then 1 else 0) -
              arcIntegral A₀ x Y (zdet q.1 q'.1 / D - β q.2 + β q'.2))
          else 0)
        (C₀ * Y * (1 + Real.log (4 * Y)) * ((Real.log x ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ)))))
    {q A₀ alo x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ} (hq : 0 < q) (hq₁ : q < 1)
    (hL : 1 ≤ Real.log x) (hY : 1 ≤ Y) (hd₀ : 0 < d₀) (hHm : 0 < d.Hm)
    (hu : d₀ * Y * d.Hm ≤ u) (hu' : u ≤ 16 * (d₀ * Y * d.Hm))
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hbase : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)
    (hbig : ∀ i, ∀ p ∈ band x (d.a i), Real.exp (Real.log x ^ alo) ≤ p)
    {E : ℝ} (hE : 0 ≤ E) (hP2 : 2 ≤ Real.log x ^ A₀) (hY8 : 8 * (Real.log x ^ A₀) ^ 3 ≤ Y)
    (hYc : 8 * latConst ≤ Y ^ (1 / 10 : ℝ)) (hEb : cleanBound K C₀ A₀ alo x Y ≤ E)
    (σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))) (S : MemState (Particle x d) B)
    {P : Fin K → Fin (padCount x) → ℕ} (hP : P ∈ padLists x d (padCount x))
    (hD₁ : d₀ ≤ ((∏ i, ∏ k, P i k : ℕ) : ℝ)) (hD₂ : ((∏ i, ∏ k, P i k : ℕ) : ℝ) < 2 * d₀) :
    WKerLe (univ ×ˢ lastSet x d P) (univ ×ˢ lastSet x d P)
      (fun p => cleanLabelWeight q x d N p.2) (fun p => cleanLabelWeight q x d N p.2)
      (cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P)
      ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * E) := by
  classical
  set D : ℕ := ∏ i, ∏ k, P i k with hDdef
  set Mf : ℝ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hMf
  set X := lastSet x d P with hX
  set Zs : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) := univ with hZs
  set ν := cleanLabelWeight q x d N with hνdef
  set L := Real.log x with hLdef
  set Λ := 1 + Real.log (4 * Y) with hΛ
  set ε := (L ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ)) with hε
  set c₁ : ℝ := Mf * (d₀ / D) with hc₁
  have hD0 : (0 : ℝ) < D := hd₀.trans_le hD₁
  have hDpos : 0 < D := by exact_mod_cast hD0
  have hY0 : 0 < Y := by linarith
  have hMf0 : 0 ≤ Mf := by positivity
  have hdD : d₀ / D ≤ 1 := (div_le_one hD0).2 hD₁
  have hc₁0 : 0 ≤ c₁ := mul_nonneg hMf0 (div_nonneg hd₀.le hD0.le)
  have hc₁M : c₁ ≤ Mf := mul_le_of_le_one_right hMf0 hdD
  have hbX : ∀ b ∈ X, ∀ i, b i ∈ band x (d.a i) := fun b hb i =>
    (mem_filter.1 (Fintype.mem_piFinset.1 hb i)).1
  have hνpos : ∀ p ∈ Zs ×ˢ X, 0 < ν p.2 := fun p hp =>
    (labelWeight_pos_le hV hbase (hbX p.2 (mem_product.1 hp).2)).1
  have hν0 : ∀ p ∈ Zs ×ˢ X, 0 ≤ ν p.2 := fun p hp => (hνpos p hp).le
  have hρ0 : 0 ≤ pendingWeight q := (Real.rpow_pos_of_pos hq _).le
  have hρ1 : pendingWeight q ≤ 1 := Real.rpow_le_one hq.le hq₁.le (by norm_num)
  -- the core kernel on the block
  set β : (Fin K → ℕ) → ℤ := fun b => ((∏ i, b i : ℕ) : ℤ) with hβ
  set core : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) → ℂ := fun p p' =>
    if GoodPad Y D (posRatio r p.1.1) ∧ (D : ℤ) ∣ zdet p.1.1 p'.1.1 then
      (plateau ((zdet p.1.1 p'.1.1 / D : ℤ) / Y) : ℂ) *
        ((if zdet p.1.1 p'.1.1 / D - β p.2 + β p'.2 = 0 then 1 else 0) -
          arcIntegral A₀ x Y (zdet p.1.1 p'.1.1 / D - β p.2 + β p'.2))
    else 0 with hcore_def
  have hcoreK : KerLe (Zs ×ˢ X) (Zs ×ˢ X) core (C₀ * Y * Λ * ε) := by
    have h := hcore X β (injOn_labelProd hdisj P) A₀ x Y d₀ (d₀ * Y * d.Hm) d.Hn u v r D hP2 hY8
      hYc hd₀ hD₁ hD₂ (squarefree_padProd hdisj hP) (by positivity) hu hu'
    have hinj : Set.InjOn (fun p : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) =>
        (p.1.1, p.2)) (Zs ×ˢ X : Finset _) := fun p _ p' _ he => by
      simp only [Prod.mk.injEq] at he
      exact Prod.ext (Subtype.ext he.1) he.2
    have h' := h.comp_embed hinj hinj (fun p hp => mem_product.2 ⟨p.1.2, (mem_product.1 hp).2⟩)
      (fun p hp => mem_product.2 ⟨p.1.2, (mem_product.1 hp).2⟩)
    exact h'.congr fun p _ p' _ => rfl
  -- the endpoint multiplier
  set φ : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) → ℝ := fun p =>
    if PosGood x d Y d₀ r p.1.1 (joinList P p.2) then
      pendingWeight q ^ pendingHits x d p.1.1 S.1 * dyadicBump ((∏ i, p.2 i : ℕ) / Y)
    else 0 with hφ
  have hφ1 : ∀ p, |φ p| ≤ 1 := by
    intro p
    simp only [hφ]
    split_ifs
    · rw [abs_mul, abs_of_nonneg (pow_nonneg hρ0 _), abs_of_nonneg (dyadicBump_nonneg _)]
      exact (mul_le_mul (pow_le_one₀ hρ0 hρ1) (dyadicBump_le_one _) (dyadicBump_nonneg _)
        zero_le_one).trans_eq (one_mul 1)
    · simp
  have hφY : ∀ p, φ p ≠ 0 → Y < ∏ i, (p.2 i : ℝ) := by
    intro p hp
    have hη : dyadicBump ((∏ i, p.2 i : ℕ) / Y) ≠ 0 := by
      intro h0
      apply hp
      simp only [hφ, h0, mul_zero, ite_self]
    have := (lt_of_dyadicBump_ne_zero hη).1
    rw [lt_div_iff₀ hY0, one_mul] at this
    exact_mod_cast this
  -- the main kernel and its coincidence part
  set Km : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) → ℂ := fun p p' =>
    ((c₁ * φ p * ν p'.2 * φ p' : ℝ) : ℂ) * core p p' with hKm
  set Kc : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) → ℂ := fun p p' =>
    if ∃ i, p'.2 i = p.2 i then Km p p' else 0 with hKc
  have hsplit : ∀ p ∈ Zs ×ˢ X, ∀ p' ∈ Zs ×ˢ X,
      cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P p p' = Km p p' + (-1) * Kc p p' := by
    intro p hp p' hp'
    rw [cleanBlockKer_eq q A₀ Y d₀ u v r B hdisj N σ σ' S hP (mem_product.1 hp).2
      (mem_product.1 hp').2 p.1 p'.1]
    by_cases hcond : (∀ i, p'.2 i ≠ p.2 i) ∧ d₀ ≤ ((∏ i, ∏ k, P i k : ℕ) : ℝ) ∧
        ((∏ i, ∏ k, P i k : ℕ) : ℝ) < 2 * d₀ ∧ ((∏ i, ∏ k, P i k : ℕ) : ℤ) ∣ zdet p.1.1 p'.1.1 ∧
        PosGood x d Y d₀ r p.1.1 (joinList P p.2) ∧ PosGood x d Y d₀ r p'.1.1 (joinList P p'.2)
    · simp only [eq_true hcond, ↓reduceIte]
      have hco : ¬ ∃ i, p'.2 i = p.2 i := fun ⟨i, hi⟩ => hcond.1 i hi
      have hdvd : (D : ℤ) ∣ zdet p.1.1 p'.1.1 := hcond.2.2.2.1
      have hpad : GoodPad Y D (posRatio r p.1.1) := goodPad_of_posGood hD₁ hD₂ hcond.2.2.2.2.1
      simp only [hKc, hco, ↓reduceIte, mul_zero, add_zero, hKm, hcore_def, hφ, hdvd, hpad,
        hcond.2.2.2.2.1, hcond.2.2.2.2.2, and_self, hβ, hc₁, hνdef]
      simp only [hMf, hDdef]
      push_cast
      ring_nf
    · simp only [eq_false hcond, ↓reduceIte]
      by_cases hco : ∃ i, p'.2 i = p.2 i
      · simp only [hKc, hco, ↓reduceIte]
        ring
      · have hban : ∀ i, p'.2 i ≠ p.2 i := fun i hi => hco ⟨i, hi⟩
        simp only [hKc, hco, ↓reduceIte, mul_zero, add_zero]
        symm
        simp only [hKm]
        by_cases hgs : PosGood x d Y d₀ r p.1.1 (joinList P p.2)
        · by_cases hgt : PosGood x d Y d₀ r p'.1.1 (joinList P p'.2)
          · have hdvd : ¬ (D : ℤ) ∣ zdet p.1.1 p'.1.1 := fun h =>
              hcond ⟨hban, hD₁, hD₂, h, hgs, hgt⟩
            simp [hcore_def, hdvd]
          · simp [hφ, hgt]
        · simp [hφ, hgs]
  -- the main kernel after conjugation: `√(ν(b) ν(a)) ≤ 4^K/Y`
  set ψs : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ) → ℝ := fun p =>
    Real.sqrt (Y / 4 ^ K) * Real.sqrt (ν p.2) * φ p with hψs
  have hψs1 : ∀ p ∈ Zs ×ˢ X, ‖((ψs p : ℝ) : ℂ)‖ ≤ 1 := by
    intro p hp
    rw [Complex.norm_real, Real.norm_eq_abs, hψs]
    dsimp only
    by_cases h0 : φ p = 0
    · rw [h0, mul_zero, abs_zero]
      exact zero_le_one
    · have hYb := hφY p h0
      have hbp := hbX p.2 (mem_product.1 hp).2
      obtain ⟨hνp, hνle⟩ := labelWeight_pos_le hV hbase hbp
      have hprod : 0 < ∏ i, (p.2 i : ℝ) := hY0.trans hYb
      have h4 : (0 : ℝ) < 4 ^ K := by positivity
      have hprodle : Y / 4 ^ K * ν p.2 ≤ 1 := by
        calc Y / 4 ^ K * ν p.2 ≤ Y / 4 ^ K * (4 ^ K / ∏ i, (p.2 i : ℝ)) :=
              mul_le_mul_of_nonneg_left hνle (by positivity)
          _ = Y / ∏ i, (p.2 i : ℝ) := by field_simp
          _ ≤ 1 := (div_le_one hprod).2 hYb.le
      have hs : Real.sqrt (Y / 4 ^ K) * Real.sqrt (ν p.2) ≤ 1 := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_one.2 hprodle
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (Y / 4 ^ K) * Real.sqrt (ν p.2))]
      exact (mul_le_mul hs (hφ1 p) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hmain : KerLe (Zs ×ˢ X) (Zs ×ˢ X)
      (fun p p' => (Real.sqrt (ν p.2) : ℂ) * Km p p' / (Real.sqrt (ν p'.2) : ℂ))
      (c₁ * 4 ^ K * (C₀ * Λ * ε)) := by
    have h := ((hcoreK.mul_diag (φ := fun p => ((ψs p : ℝ) : ℂ))
      (φ' := fun p => ((ψs p : ℝ) : ℂ)) hψs1 hψs1).const_mul ((c₁ * 4 ^ K / Y : ℝ) : ℂ))
    have hnorm : ‖((c₁ * 4 ^ K / Y : ℝ) : ℂ)‖ * (C₀ * Y * Λ * ε) = c₁ * 4 ^ K * (C₀ * Λ * ε) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      field_simp
    rw [hnorm] at h
    refine h.congr fun p hp p' hp' => ?_
    have hνa : (0 : ℝ) < ν p'.2 := hνpos p' hp'
    have hsa : Real.sqrt (ν p'.2) ≠ 0 := (Real.sqrt_pos.2 hνa).ne'
    have hsa' : Real.sqrt (ν p'.2) * Real.sqrt (ν p'.2) = ν p'.2 := Real.mul_self_sqrt hνa.le
    have hY4 : Real.sqrt (Y / 4 ^ K) * Real.sqrt (Y / 4 ^ K) = Y / 4 ^ K :=
      Real.mul_self_sqrt (by positivity)
    have hreal : c₁ * 4 ^ K / Y * (ψs p * ψs p') =
        Real.sqrt (ν p.2) * (c₁ * φ p * ν p'.2 * φ p') / Real.sqrt (ν p'.2) := by
      have e1 : ψs p * ψs p' = (Real.sqrt (Y / 4 ^ K) * Real.sqrt (Y / 4 ^ K)) *
          (Real.sqrt (ν p.2) * Real.sqrt (ν p'.2) * φ p * φ p') := by
        simp only [hψs]
        ring
      have e2 : ν p'.2 / Real.sqrt (ν p'.2) = Real.sqrt (ν p'.2) := by
        rw [div_eq_iff hsa, hsa']
      rw [e1, hY4]
      have h4 : (4 : ℝ) ^ K ≠ 0 := by positivity
      calc c₁ * 4 ^ K / Y * (Y / 4 ^ K * (Real.sqrt (ν p.2) * Real.sqrt (ν p'.2) * φ p * φ p'))
          = c₁ * Real.sqrt (ν p.2) * φ p * φ p' * Real.sqrt (ν p'.2) := by
            field_simp
        _ = c₁ * Real.sqrt (ν p.2) * φ p * φ p' * (ν p'.2 / Real.sqrt (ν p'.2)) := by rw [e2]
        _ = _ := by ring
    have hL' : ((c₁ * 4 ^ K / Y : ℝ) : ℂ) * (((ψs p : ℝ) : ℂ) * core p p' * ((ψs p' : ℝ) : ℂ)) =
        ((c₁ * 4 ^ K / Y * (ψs p * ψs p') : ℝ) : ℂ) * core p p' := by
      push_cast
      ring
    have hR' : (Real.sqrt (ν p.2) : ℂ) * Km p p' / (Real.sqrt (ν p'.2) : ℂ) =
        ((Real.sqrt (ν p.2) * (c₁ * φ p * ν p'.2 * φ p') / Real.sqrt (ν p'.2) : ℝ) : ℂ) *
          core p p' := by
      simp only [hKm]
      push_cast
      ring
    show ((c₁ * 4 ^ K / Y : ℝ) : ℂ) * (((ψs p : ℝ) : ℂ) * core p p' * ((ψs p' : ℝ) : ℂ)) =
      (Real.sqrt (ν p.2) : ℂ) * Km p p' / (Real.sqrt (ν p'.2) : ℂ)
    rw [hL', hR', hreal]
  -- the coincidence part: the weighted Schur test
  set Rc : ℝ := 16 * (1 + 52 * L ^ (3 * A₀)) * (K * 4 ^ K * (4 * Real.exp (-L ^ alo))) with hRc
  have hRc0 : 0 ≤ Rc := by positivity
  have hLpos : 0 < L := by linarith
  have hU0 : 0 < d₀ * Y * d.Hm := by positivity
  -- `|Kc| ≤ [coincidence] c₁ ν(a) κ`
  have hKcle : ∀ p p', ‖Kc p p'‖ ≤ if ∃ i, p'.2 i = p.2 i then
      c₁ * ν p'.2 * crudeKernel A₀ x Y D (∏ i, p.2 i) (∏ i, p'.2 i) (zdet p.1.1 p'.1.1) else 0 := by
    intro p p'
    simp only [hKc]
    split_ifs with hco
    · simp only [hKm]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hν' : 0 ≤ ν p'.2 := prod_nonneg fun i _ => primeWeight_nonneg_of_baseline hbase _
      have h1 : |c₁ * φ p * ν p'.2 * φ p'| ≤ c₁ * ν p'.2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc₁0, abs_of_nonneg hν']
        have := hφ1 p
        have := hφ1 p'
        calc c₁ * |φ p| * ν p'.2 * |φ p'| = c₁ * ν p'.2 * (|φ p| * |φ p'|) := by ring
          _ ≤ c₁ * ν p'.2 * (1 * 1) := by gcongr
          _ = c₁ * ν p'.2 := by ring
      have h2 : ‖core p p'‖ ≤ crudeKernel A₀ x Y D (∏ i, p.2 i) (∏ i, p'.2 i) (zdet p.1.1 p'.1.1) := by
        simp only [hcore_def, crudeKernel]
        by_cases hc : GoodPad Y D (posRatio r p.1.1) ∧ (D : ℤ) ∣ zdet p.1.1 p'.1.1
        · simp only [hc.1, hc.2, and_self, ↓reduceIte, crudeTerm]
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (show 0 ≤ plateau _ from smoothTransition.nonneg _)]
          have ht : ∀ t b a : ℤ, (t - b + a = 0) ↔ (t = b - a) := fun t b a => by omega
          simp only [hβ, ht]
          exact le_rfl
        · simp only [hc, ↓reduceIte, norm_zero]
          split_ifs
          · exact crudeTerm_nonneg _ _ _ _ _ _
          · exact le_rfl
      calc |c₁ * φ p * ν p'.2 * φ p'| * ‖core p p'‖
          ≤ (c₁ * ν p'.2) * crudeKernel A₀ x Y D (∏ i, p.2 i) (∏ i, p'.2 i) (zdet p.1.1 p'.1.1) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [norm_zero]
  have hcrude0 : ∀ b a n, 0 ≤ crudeKernel A₀ x Y D b a n := fun b a n =>
    crudeKernel_nonneg _ _ _ _ _ _ _
  have hrow : ∀ p ∈ Zs ×ˢ X, ∑ p' ∈ Zs ×ˢ X, ‖Kc p p'‖ ≤ c₁ * Rc := by
    intro p hp
    calc ∑ p' ∈ Zs ×ˢ X, ‖Kc p p'‖
        ≤ ∑ p' ∈ Zs ×ˢ X, (if ∃ i, p'.2 i = p.2 i then
            c₁ * ν p'.2 * crudeKernel A₀ x Y D (∏ i, p.2 i) (∏ i, p'.2 i) (zdet p.1.1 p'.1.1)
            else 0) := sum_le_sum fun p' _ => hKcle p p'
      _ = c₁ * ∑ a ∈ X, (if ∃ i, a i = p.2 i then ν a else 0) *
            ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
              crudeKernel A₀ x Y D (∏ i, p.2 i) (∏ i, a i) (p.1.1.1 * z'.1.2 - p.1.1.2 * z'.1.1) := by
          rw [sum_product, sum_comm, mul_sum]
          refine sum_congr rfl fun a _ => ?_
          rw [hZs, mul_sum, mul_sum]
          refine sum_congr rfl fun z' _ => ?_
          split_ifs <;> simp [zdet]; ring
      _ ≤ c₁ * ∑ a ∈ X, (if ∃ i, a i = p.2 i then ν a else 0) * (16 * (1 + 52 * L ^ (3 * A₀))) := by
          gcongr with a ha
          · split_ifs
            · exact prod_nonneg fun i _ => primeWeight_nonneg_of_baseline hbase _
            · exact le_rfl
          · exact sum_crudeKernel_le A₀ hLpos hY hU0 p.1.2 hDpos _ _
      _ = c₁ * (16 * (1 + 52 * L ^ (3 * A₀)) *
            ∑ a ∈ X, (if ∃ i, a i = p.2 i then ν a else 0)) := by rw [← sum_mul]; ring
      _ ≤ c₁ * (16 * (1 + 52 * L ^ (3 * A₀)) * (K * 4 ^ K * (4 * Real.exp (-L ^ alo)))) := by
          gcongr
          exact sum_labelWeight_coinc_le hV hbase hbig P p.2
      _ = c₁ * Rc := by rw [hRc]
  have hcol : ∀ p' ∈ Zs ×ˢ X, ∑ p ∈ Zs ×ˢ X, ν p.2 * ‖Kc p p'‖ ≤ c₁ * Rc * ν p'.2 := by
    intro p' hp'
    have hν' : 0 ≤ ν p'.2 := hν0 p' hp'
    calc ∑ p ∈ Zs ×ˢ X, ν p.2 * ‖Kc p p'‖
        ≤ ∑ p ∈ Zs ×ˢ X, ν p.2 * (if ∃ i, p'.2 i = p.2 i then
            c₁ * ν p'.2 * crudeKernel A₀ x Y D (∏ i, p.2 i) (∏ i, p'.2 i) (zdet p.1.1 p'.1.1)
            else 0) := sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hKcle p p') (hν0 p hp)
      _ = c₁ * ν p'.2 * ∑ b ∈ X, (if ∃ i, b i = p'.2 i then ν b else 0) *
            ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
              crudeKernel A₀ x Y D (∏ i, b i) (∏ i, p'.2 i) (z.1.1 * p'.1.1.2 - z.1.2 * p'.1.1.1) := by
          rw [sum_product, sum_comm, mul_sum]
          refine sum_congr rfl fun b _ => ?_
          rw [hZs, mul_sum, mul_sum]
          refine sum_congr rfl fun z _ => ?_
          have hsymm : (∃ i, p'.2 i = b i) ↔ (∃ i, b i = p'.2 i) :=
            ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
          simp only [hsymm]
          split_ifs <;> simp [zdet]; ring
      _ ≤ c₁ * ν p'.2 * ∑ b ∈ X, (if ∃ i, b i = p'.2 i then ν b else 0) *
            (16 * (1 + 52 * L ^ (3 * A₀))) := by
          gcongr with b hb
          · split_ifs
            · exact prod_nonneg fun i _ => primeWeight_nonneg_of_baseline hbase _
            · exact le_rfl
          · exact sum_crudeKernel_le' A₀ hLpos hY hU0 p'.1.2 hDpos _ _
      _ = c₁ * ν p'.2 * (16 * (1 + 52 * L ^ (3 * A₀)) *
            ∑ b ∈ X, (if ∃ i, b i = p'.2 i then ν b else 0)) := by rw [← sum_mul]; ring
      _ ≤ c₁ * ν p'.2 * (16 * (1 + 52 * L ^ (3 * A₀)) * (K * 4 ^ K * (4 * Real.exp (-L ^ alo)))) := by
          gcongr
          exact sum_labelWeight_coinc_le hV hbase hbig P p'.2
      _ = c₁ * Rc * ν p'.2 := by rw [hRc]; ring
  have hcoW : WKerLe (Zs ×ˢ X) (Zs ×ˢ X) (fun p => ν p.2) (fun p => ν p.2) Kc
      (Real.sqrt ((c₁ * Rc) * (c₁ * Rc))) :=
    wkerLe_of_schur (S := Zs ×ˢ X) (S' := Zs ×ˢ X) (μ := fun p => ν p.2)
      (ν := fun p => ν p.2) (k := Kc) (R := c₁ * Rc) (C := c₁ * Rc)
      (mul_nonneg hc₁0 hRc0) (mul_nonneg hc₁0 hRc0) hν0 hrow hcol
  have hsq : Real.sqrt ((c₁ * Rc) * (c₁ * Rc)) = c₁ * Rc :=
    Real.sqrt_mul_self (mul_nonneg hc₁0 hRc0)
  have hcoK : KerLe (Zs ×ˢ X) (Zs ×ˢ X)
      (fun p p' => (Real.sqrt (ν p.2) : ℂ) * Kc p p' / (Real.sqrt (ν p'.2) : ℂ)) (c₁ * Rc) := by
    have h := kerLe_of_wkerLe (S := Zs ×ˢ X) (S' := Zs ×ˢ X) (μ := fun p => ν p.2)
      (ν := fun p => ν p.2) (k := Kc) hν0 hνpos hcoW
    rw [hsq] at h
    exact h
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ Real.log (4 * Y) := Real.log_nonneg (by linarith)
    rw [hΛ]
    linarith
  have hε0 : 0 ≤ ε := add_nonneg (inv_nonneg.2 (Real.rpow_nonneg hLpos.le _))
    (Real.rpow_nonneg hY0.le _)
  have hm0 : 0 ≤ c₁ * 4 ^ K * (C₀ * Λ * ε) :=
    mul_nonneg (mul_nonneg hc₁0 (by positivity)) (mul_nonneg (mul_nonneg hC₀.le hΛ0) hε0)
  -- the block kernel after conjugation
  have htot : KerLe (Zs ×ˢ X) (Zs ×ˢ X)
      (fun p p' => (Real.sqrt (ν p.2) : ℂ) *
        cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P p p' / (Real.sqrt (ν p'.2) : ℂ))
      (c₁ * 4 ^ K * (C₀ * Λ * ε) + ‖(-1 : ℂ)‖ * (c₁ * Rc)) := by
    refine (hmain.add (hcoK.const_mul (-1)) hm0
      (mul_nonneg (norm_nonneg _) (mul_nonneg hc₁0 hRc0))).congr fun p hp p' hp' => ?_
    rw [hsplit p hp p' hp']
    ring
  have hfin : c₁ * 4 ^ K * (C₀ * Λ * ε) + ‖(-1 : ℂ)‖ * (c₁ * Rc) ≤ Mf * E := by
    rw [norm_neg, norm_one, one_mul]
    have h1 : 4 ^ K * (C₀ * Λ * ε) + Rc ≤ cleanBound K C₀ A₀ alo x Y := by
      unfold cleanBound
      rw [hRc]
      have he : 0 ≤ (K : ℝ) * 4 ^ K * (1 + 52 * L ^ (3 * A₀)) * Real.exp (-L ^ alo) := by
        positivity
      nlinarith
    calc c₁ * 4 ^ K * (C₀ * Λ * ε) + c₁ * Rc = c₁ * (4 ^ K * (C₀ * Λ * ε) + Rc) := by ring
      _ ≤ c₁ * cleanBound K C₀ A₀ alo x Y := mul_le_mul_of_nonneg_left h1 hc₁0
      _ ≤ c₁ * E := mul_le_mul_of_nonneg_left hEb hc₁0
      _ ≤ Mf * E := mul_le_mul_of_nonneg_right hc₁M hE
  exact wkerLe_of_kerLe hν0 hνpos (htot.mono (add_nonneg hm0
    (mul_nonneg (norm_nonneg _) (mul_nonneg hc₁0 hRc0))) hfin)

open scoped Classical in
/-- **The clean block bound** (PD `mem:clean-kernel`, `mem:product-mass`). With the constant `C₀`
of `exists_coreKer_bound`, assume the bands are disjoint and of mass in `[1/2, 1]`, the baselines
are at least `1/2`, band primes exceed `e^{L^{a₋}}`, and every label product `b` with
`η(b/Y) ≠ 0` gives the size conditions of the core kernel and `cleanBound ≤ E`. Then every block
kernel has weighted norm at most `M!^{-2K} E`. -/
theorem wkerLe_cleanBlockKer {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcore : ∀ {κ : Type} (X : Finset κ) (β : κ → ℤ),
      Set.InjOn β X → ∀ (A₀ x Y d₀ U V u v r : ℝ) (D : ℕ),
      2 ≤ Real.log x ^ A₀ → 8 * (Real.log x ^ A₀) ^ 3 ≤ Y → 8 * latConst ≤ Y ^ (1 / 10 : ℝ) →
      0 < d₀ → d₀ ≤ D → (D : ℝ) < 2 * d₀ → Squarefree D → 0 < U → U ≤ u → u ≤ 16 * U →
      KerLe (rootPositions U V u v r ×ˢ X) (rootPositions U V u v r ×ˢ X)
        (fun q q' => if GoodPad Y D (posRatio r q.1) ∧ (D : ℤ) ∣ zdet q.1 q'.1 then
          (plateau ((zdet q.1 q'.1 / D : ℤ) / Y) : ℂ) *
            ((if zdet q.1 q'.1 / D - β q.2 + β q'.2 = 0 then 1 else 0) -
              arcIntegral A₀ x Y (zdet q.1 q'.1 / D - β q.2 + β q'.2))
          else 0)
        (C₀ * Y * (1 + Real.log (4 * Y)) * ((Real.log x ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ)))))
    {q A₀ alo x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ} (hq : 0 < q) (hq₁ : q < 1)
    (hL : 1 ≤ Real.log x) (hY : 1 ≤ Y) (hd₀ : 0 < d₀) (hHm : 0 < d.Hm)
    (hu : d₀ * Y * d.Hm ≤ u) (hu' : u ≤ 16 * (d₀ * Y * d.Hm))
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hbase : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)
    (hbig : ∀ i, ∀ p ∈ band x (d.a i), Real.exp (Real.log x ^ alo) ≤ p)
    {E : ℝ} (hE : 0 ≤ E)
    (hsize : ∀ b : Fin K → ℕ, (∀ i, b i ∈ band x (d.a i)) → dyadicBump ((∏ i, b i : ℕ) / Y) ≠ 0 →
      2 ≤ Real.log x ^ A₀ ∧ 8 * (Real.log x ^ A₀) ^ 3 ≤ Y ∧ 8 * latConst ≤ Y ^ (1 / 10 : ℝ) ∧
        cleanBound K C₀ A₀ alo x Y ≤ E)
    (σ σ' : Fin K → Equiv.Perm (Fin (padCount x + 1))) (S : MemState (Particle x d) B)
    {P : Fin K → Fin (padCount x) → ℕ} (hP : P ∈ padLists x d (padCount x)) :
    WKerLe (univ ×ˢ lastSet x d P) (univ ×ˢ lastSet x d P)
      (fun p => cleanLabelWeight q x d N p.2) (fun p => cleanLabelWeight q x d N p.2)
      (cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P)
      ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * E) := by
  classical
  set D : ℕ := ∏ i, ∏ k, P i k with hDdef
  set Mf : ℝ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hMf
  set X := lastSet x d P with hX
  set ν := cleanLabelWeight q x d N with hνdef
  have hbX : ∀ b ∈ X, ∀ i, b i ∈ band x (d.a i) := fun b hb i =>
    (mem_filter.1 (Fintype.mem_piFinset.1 hb i)).1
  have hνpos : ∀ p ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ X,
      0 < ν p.2 := fun p hp => (labelWeight_pos_le hV hbase (hbX p.2 (mem_product.1 hp).2)).1
  have hν0 : ∀ p ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ X,
      0 ≤ ν p.2 := fun p hp => (hνpos p hp).le
  have hMf0 : 0 ≤ Mf := by positivity
  -- the kernel formula on the index sets
  have hk : ∀ p ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ X,
      ∀ p' ∈ (univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ X,
      cleanBlockKer q A₀ x d Y d₀ u v r B N σ σ' S P p p' = _ := fun p hp p' hp' =>
    cleanBlockKer_eq q A₀ Y d₀ u v r B hdisj N σ σ' S hP (mem_product.1 hp).2
      (mem_product.1 hp').2 p.1 p'.1
  -- degenerate blocks
  by_cases hDr : d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2 * d₀
  swap
  · refine wkerLe_of_eq_zero hν0 fun p hp p' hp' => ?_
    rw [hk p hp p' hp']
    exact ite_eq_right_iff.2 fun h => (hDr ⟨h.2.1, h.2.2.1⟩).elim
  by_cases hη : ∃ b ∈ X, dyadicBump ((∏ i, b i : ℕ) / Y) ≠ 0
  swap
  · push Not at hη
    refine wkerLe_of_eq_zero hν0 fun p hp p' hp' => ?_
    rw [hk p hp p' hp']
    refine ite_eq_right_iff.2 fun _ => ?_
    rw [hη p.2 (mem_product.1 hp).2]
    simp
  obtain ⟨b₀, hb₀, hη₀⟩ := hη
  obtain ⟨hP2, hY8, hYc, hEb⟩ := hsize b₀ (hbX b₀ hb₀) hη₀
  exact wkerLe_cleanBlockKer_main hC₀ hcore hq hq₁ hL hY hd₀ hHm hu hu' hdisj hV hbase hbig hE hP2
    hY8 hYc hEb σ σ' S hP hDr.1 hDr.2

/-! ### Asymptotics -/

/-- The band facts used by the clean edge, for large `x`: `L ≥ 1`, disjoint bands of mass in
`[1/2, 1]`, baselines at least `1/2` for `N = 2R`, and band primes at least `e^{L^{a₋}}`. -/
theorem eventually_clean_facts {q C CX alo ahi g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x ∧ ∀ d : Data K, Admissible C CX alo ahi g x d →
      (∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) ∧
      (∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1) ∧
      (∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q (2 * momentPower x) p) ∧
      (∀ i, ∀ p ∈ band x (d.a i), Real.exp (Real.log x ^ alo) ≤ p) := by
  have hL := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_band_disjoint hg,
    eventually_harmonicMass_band halo.le, eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) 1,
    hL.eventually_ge_atTop 8] with x hL1 hdisj hV hbig hs8
  refine ⟨hL1, fun d hd => ⟨fun i j hij => ?_, fun i => hV _ (hd.window i).1, fun p hp => ?_,
    fun i p hp => ?_⟩⟩
  · -- bands at least `g` apart are disjoint
    rcases lt_or_gt_of_ne hij with h | h
    · exact hdisj _ _ (hd.gap i j h)
    · exact (hdisj _ _ (hd.gap j i h)).symm
  · -- `p ≥ 2N + 1` with `N = 2R`, so `b'_p ≥ 1/2`
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    have hLp := hbig (d.a i) (hd.window i).1 p hpi
    rw [Real.rpow_one] at hLp
    set t := Real.log x ^ (1 / 2 : ℝ) with ht
    have ht8 : 8 ≤ t := hs8
    have htt : t * t = Real.log x := by
      rw [ht, ← Real.rpow_add (by linarith)]
      norm_num
    have hR : (momentPower x : ℝ) < t / 2 + 1 := by
      unfold momentPower
      exact Nat.ceil_lt_add_one (by linarith)
    have h8 : 8 * t ≤ t * t := mul_le_mul_of_nonneg_right ht8 (by linarith)
    have hp' : ((2 * (2 * momentPower x) + 1 : ℕ) : ℝ) < p := by
      push_cast
      linarith
    have hNp : 2 * (2 * momentPower x) + 1 ≤ p := by exact_mod_cast hp'.le
    set N := 2 * momentPower x
    have hp1 : (0 : ℝ) < p + 1 := by positivity
    have hNp' : 2 * ((N : ℝ) + 1) ≤ p + 1 := by
      exact_mod_cast (show 2 * (N + 1) ≤ p + 1 by omega)
    have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
    have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 :=
      calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
            sum_le_sum fun j _ => by
              unfold dampDefect
              split_ifs <;> linarith [Real.sqrt_nonneg q]
        _ = (N : ℝ) + 1 := by simp
    have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 / 2 := by
      rw [inv_mul_le_iff₀ hp1]
      linarith
    unfold baseline
    linarith
  · -- `p ≥ exp(L^{a_i}) ≥ exp(L^{a₋})`
    exact (Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (hd.window i).1)).trans
      (exp_le_of_mem_band hp)

/-- `e^{W^a}` eventually exceeds `M W^B`, for `a > 0`. -/
private theorem eventually_mul_rpow_le_exp {a : ℝ} (ha : 0 < a) (B M : ℝ) :
    ∀ᶠ W : ℝ in atTop, M * W ^ B ≤ Real.exp (W ^ a) := by
  have hexp := (tendsto_exp_div_rpow_atTop (B / a)).comp (tendsto_rpow_atTop ha)
  filter_upwards [hexp.eventually_ge_atTop (max M 1), eventually_ge_atTop 1] with W hW hW1
  have hW0 : 0 < W := by linarith
  simp only [Function.comp] at hW
  rw [← Real.rpow_mul hW0.le, mul_div_cancel₀ _ ha.ne', le_div_iff₀ (by positivity)] at hW
  have hWB : 0 < W ^ B := by positivity
  calc M * W ^ B ≤ max M 1 * W ^ B := mul_le_mul_of_nonneg_right (le_max_left _ _) hWB.le
    _ ≤ Real.exp (W ^ a) := hW

/-- The size conditions of the clean edge, for large `x`: whenever a label product `b` has
`η(b/Y) ≠ 0`, the core kernel applies at `Y` and `cleanBound ≤ L^{-G-1/2}`. -/
theorem eventually_clean_size {C₀ C CX alo ahi Dstar g : ℝ} (hC₀ : 0 < C₀) (hC : 0 < C)
    (hD : 0 < Dstar) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ Y : ℝ, 1 ≤ Y →
      ∀ b : Fin K → ℕ, (∀ i, b i ∈ band x (d.a i)) → dyadicBump ((∏ i, b i : ℕ) / Y) ≠ 0 →
        2 ≤ Real.log x ^ arcExp Dstar C ∧ 8 * (Real.log x ^ arcExp Dstar C) ^ 3 ≤ Y ∧
          8 * latConst ≤ Y ^ (1 / 10 : ℝ) ∧
          cleanBound K C₀ (arcExp Dstar C) alo x Y ≤ Real.log x ^ (-(edgePrec Dstar C + 1 / 2)) := by
  set G := edgePrec Dstar C with hGdef
  set A₀ := arcExp Dstar C with hA₀def
  have hG0 : 0 < G := by
    rw [hGdef, edgePrec, momentPrec, squarePrec]
    linarith
  have hA₀ : A₀ = G + 1 := rfl
  have halo0 : 0 < alo := by linarith
  set M₁ : ℝ := 4 * 4 ^ K * C₀ * (3 + 2 * K) with hM₁
  set M₂ : ℝ := 2 * 1024 * 53 * K * 4 ^ K with hM₂
  have hW := Real.tendsto_log_atTop
  have hhalf := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 - ahi by linarith)).comp hW
  filter_upwards [hW.eventually_ge_atTop 2,
    hW.eventually (eventually_mul_rpow_le_exp halo0 (3 * A₀) 32),
    hW.eventually (eventually_mul_rpow_le_exp halo0 0 (4 * (8 * latConst) ^ 10)),
    hW.eventually (eventually_mul_rpow_le_exp halo0 (10 * A₀) 4),
    hW.eventually (eventually_mul_rpow_le_exp halo0 (3 * A₀ + G + 1 / 2) M₂),
    hhalf.eventually_ge_atTop M₁]
    with x hW2 hE2 hE3 hE4 hE6 hE5 d hd Y hY b hb hη
  set W := Real.log x with hWdef
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  -- the label product lies in `(Y, 4Y)`
  obtain ⟨hy1, hy4⟩ := lt_of_dyadicBump_ne_zero hη
  have hY0 : 0 < Y := by linarith
  rw [lt_div_iff₀ hY0, one_mul] at hy1
  rw [div_lt_iff₀ hY0] at hy4
  obtain ⟨hlo, hhi⟩ := labelProduct_bounds (a := d.a) hb
  have hprod : ((∏ i, b i : ℕ) : ℝ) = ∏ i, (b i : ℝ) := by push_cast; rfl
  rw [hprod] at hy1 hy4
  -- there is at least one band
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      simp at hy1
      linarith
    · exact h
  have hsum_lo : W ^ alo ≤ ∑ i, W ^ d.a i := by
    have i0 : Fin K := ⟨0, hK⟩
    calc W ^ alo ≤ W ^ d.a i0 := Real.rpow_le_rpow_of_exponent_le hW1 (hd.window i0).1
      _ ≤ ∑ i, W ^ d.a i := single_le_sum (f := fun i => W ^ d.a i)
          (fun i _ => Real.rpow_nonneg hW0.le _) (mem_univ i0)
  have hsum_hi : ∑ i, W ^ d.a i ≤ K * W ^ ahi := by
    calc ∑ i, W ^ d.a i ≤ ∑ _i : Fin K, W ^ ahi :=
          sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_le hW1 (hd.window i).2
      _ = K * W ^ ahi := by simp
  -- `Y ≥ e^{W^{a₋}}/4` and `log 4Y ≤ log 4 + 2K W^{a₊}`
  have hYlo : Real.exp (W ^ alo) ≤ 4 * Y := by
    have := (Real.exp_le_exp.2 hsum_lo).trans hlo
    linarith
  have hlogY : Real.log (4 * Y) ≤ 2 + 2 * K * W ^ ahi := by
    have h1 : 4 * Y ≤ 4 * Real.exp (2 * (K * W ^ ahi)) := by
      have := hhi.trans (Real.exp_le_exp.2 (by linarith : 2 * ∑ i, W ^ d.a i ≤ 2 * (K * W ^ ahi)))
      linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
    have : Real.log 4 ≤ 2 := by
      have e : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [e]
      linarith [Real.log_two_lt_d9]
    linarith
  have hWA : 1 ≤ W ^ A₀ := Real.one_le_rpow hW1 (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `L^{A₀} ≥ L ≥ 2`
    calc (2 : ℝ) ≤ W := hW2
      _ = W ^ (1 : ℝ) := (Real.rpow_one W).symm
      _ ≤ W ^ A₀ := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  · -- `8 L^{3A₀} ≤ e^{L^{a₋}}/4 ≤ Y`
    have : (W ^ A₀) ^ 3 = W ^ (3 * A₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
      ring_nf
    rw [this]
    linarith
  · -- `Y ≥ (8 c₀)^{10}`
    have h1 : (8 * latConst) ^ 10 ≤ Y := by
      have := hE3
      rw [Real.rpow_zero, mul_one] at this
      exact le_of_mul_le_mul_left (this.trans hYlo) (by norm_num : (0 : ℝ) < 4)
    calc 8 * latConst = ((8 * latConst) ^ (10 : ℝ)) ^ (1 / 10 : ℝ) := by
          rw [← Real.rpow_mul (by unfold latConst; norm_num)]
          norm_num
      _ ≤ Y ^ (1 / 10 : ℝ) := by
          refine Real.rpow_le_rpow (by unfold latConst; positivity) ?_ (by norm_num)
          rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          exact h1
  · -- the two terms of `cleanBound`
    have hY10 : Y ^ (-(1 / 10 : ℝ)) ≤ W ^ (-A₀) := by
      have h1 : W ^ (10 * A₀) ≤ Y := by linarith
      calc Y ^ (-(1 / 10 : ℝ)) ≤ (W ^ (10 * A₀)) ^ (-(1 / 10 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
        _ = W ^ (-A₀) := by
            rw [← Real.rpow_mul hW0.le]
            ring_nf
    have hinv : (W ^ A₀)⁻¹ = W ^ (-A₀) := (Real.rpow_neg hW0.le _).symm
    have hWahi : 1 ≤ W ^ ahi := Real.one_le_rpow hW1 (by linarith [(hd.window ⟨0, hK⟩).1,
      (hd.window ⟨0, hK⟩).2])
    -- first term: `4^K C₀ (3 + 2K) W^{a₊} 2 W^{-A₀} ≤ W^{-G-1/2}/2`
    have hT1 : 4 ^ K * C₀ * (1 + Real.log (4 * Y)) * ((W ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ))) ≤
        W ^ (-(G + 1 / 2)) / 2 := by
      have h1 : 1 + Real.log (4 * Y) ≤ (3 + 2 * K) * W ^ ahi := by nlinarith
      have h2 : (W ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ)) ≤ 2 * W ^ (-A₀) := by rw [hinv]; linarith
      have h1' : 0 ≤ 1 + Real.log (4 * Y) := by
        have : 0 ≤ Real.log (4 * Y) := Real.log_nonneg (by linarith)
        linarith
      have h3 : 4 ^ K * C₀ * (1 + Real.log (4 * Y)) * ((W ^ A₀)⁻¹ + Y ^ (-(1 / 10 : ℝ))) ≤
          4 ^ K * C₀ * ((3 + 2 * K) * W ^ ahi) * (2 * W ^ (-A₀)) := by
        gcongr
      have h4 : 4 ^ K * C₀ * ((3 + 2 * K) * W ^ ahi) * (2 * W ^ (-A₀)) =
          M₁ / 2 * (W ^ ahi * W ^ (-A₀)) := by rw [hM₁]; ring
      -- `W^{a₊ - A₀} = W^{-G-1/2} W^{a₊ - 1/2}` and `M₁ W^{a₊ - 1/2} ≤ 1`
      have h5 : W ^ ahi * W ^ (-A₀) = W ^ (-(G + 1 / 2)) * W ^ (-(1 / 2 - ahi)) := by
        rw [← Real.rpow_add hW0, ← Real.rpow_add hW0, hA₀]
        ring_nf
      have h6 : M₁ * W ^ (-(1 / 2 - ahi)) ≤ 1 := by
        rw [Real.rpow_neg hW0.le, ← div_eq_mul_inv, div_le_one (by positivity)]
        exact hE5
      have h7 : 0 ≤ W ^ (-(G + 1 / 2)) := by positivity
      calc _ ≤ _ := h3
        _ = M₁ / 2 * (W ^ ahi * W ^ (-A₀)) := h4
        _ = W ^ (-(G + 1 / 2)) * (M₁ * W ^ (-(1 / 2 - ahi))) / 2 := by rw [h5]; ring
        _ ≤ W ^ (-(G + 1 / 2)) * 1 / 2 := by gcongr
        _ = W ^ (-(G + 1 / 2)) / 2 := by ring
    -- second term: `1024 K 4^K (1 + 52 W^{3A₀}) e^{-W^{a₋}} ≤ W^{-G-1/2}/2`
    have hT2 : 1024 * K * 4 ^ K * (1 + 52 * W ^ (3 * A₀)) * Real.exp (-W ^ alo) ≤
        W ^ (-(G + 1 / 2)) / 2 := by
      have hW3 : 1 ≤ W ^ (3 * A₀) := Real.one_le_rpow hW1 (by linarith)
      have h1 : 1 + 52 * W ^ (3 * A₀) ≤ 53 * W ^ (3 * A₀) := by linarith
      have h2 : M₂ * W ^ (3 * A₀ + G + 1 / 2) ≤ Real.exp (W ^ alo) := hE6
      have h3 : W ^ (3 * A₀ + G + 1 / 2) = W ^ (3 * A₀) * W ^ (G + 1 / 2) := by
        rw [← Real.rpow_add hW0]
        ring_nf
      have h4 : W ^ (-(G + 1 / 2)) = (W ^ (G + 1 / 2))⁻¹ := Real.rpow_neg hW0.le _
      have hp : 0 < W ^ (G + 1 / 2) := by positivity
      rw [h3, hM₂] at h2
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      have h44 : (0 : ℝ) ≤ 4 ^ K := by positivity
      set X := 1024 * K * 4 ^ K * (1 + 52 * W ^ (3 * A₀)) with hX
      have key : 2 * X * W ^ (G + 1 / 2) ≤ Real.exp (W ^ alo) := by
        have : X ≤ 1024 * K * 4 ^ K * (53 * W ^ (3 * A₀)) := by
          rw [hX]
          gcongr
        calc 2 * X * W ^ (G + 1 / 2) ≤ 2 * (1024 * K * 4 ^ K * (53 * W ^ (3 * A₀))) *
              W ^ (G + 1 / 2) := by gcongr
          _ = 2 * 1024 * 53 * K * 4 ^ K * (W ^ (3 * A₀) * W ^ (G + 1 / 2)) := by ring
          _ ≤ _ := h2
      have hexp0 := Real.exp_pos (W ^ alo)
      rw [h4, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexp0]
      calc X = (W ^ (G + 1 / 2))⁻¹ / 2 * (2 * X * W ^ (G + 1 / 2)) := by field_simp
        _ ≤ (W ^ (G + 1 / 2))⁻¹ / 2 * Real.exp (W ^ alo) :=
          mul_le_mul_of_nonneg_left key (by positivity)
    unfold cleanBound
    linarith

/-! ### M6 -/

/-- **M6, the clean edge** (PD `mem:clean-bound`): for `B ≤ L³` and `N = 2R`, the clean edge has
norm at most `L^{-G-1/2}` for the chain measure, uniformly in the root box. -/
theorem eventually_cleanOp_normLe {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hC : 0 < C) (hD : 0 < Dstar) (_hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5)
    (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (choiceOp (cleanChoices x d (2 ^ j) (2 ^ k) u v r)
            (chainEdgeCoef q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N)
            (chainEdgeOut x d (2 ^ j) (2 ^ k) u v r B))
          (Real.log x ^ (-(edgePrec Dstar C + 1 / 2))) := by
  obtain ⟨C₀, hC₀, hcore⟩ := exists_coreKer_bound
  filter_upwards [eventually_clean_facts (K := K) (C := C) (CX := CX) (ahi := ahi) hq hq₁ halo hg,
    eventually_clean_size (K := K) (CX := CX) (g := g) hC₀ hC hD halo hahi,
    eventually_gt_atTop 0]
    with x ⟨hL, hfacts⟩ hsize hx d hd j k u v r hu hu' hv hv' hr hr' B N hB hN
  subst hN
  obtain ⟨hdisj, hV, hbase, hbig⟩ := hfacts d hd
  have hHm : 0 < d.Hm := (Real.rpow_pos_of_pos hx _).trans_le hd.Hm_ge
  refine normLe_cleanOp_of_blocks _ (Real.rpow_nonneg (by linarith) _)
    (primeWeight_nonneg_of_baseline hbase) fun σ σ' S P hP => ?_
  exact wkerLe_cleanBlockKer hC₀ hcore hq hq₁ hL (one_le_pow₀ (by norm_num)) (by positivity) hHm
    hu hu' hdisj hV hbase hbig (Real.rpow_nonneg (by linarith) _)
    (fun b hb hη => hsize d hd (2 ^ j) (one_le_pow₀ (by norm_num)) b hb hη) σ σ' S hP

end Erdos408.OneSided
