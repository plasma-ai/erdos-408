import Erdos408.OneSided.Moment.Chain
import Erdos408.OneSided.Moment.Edge.Anchor
import Erdos408.OneSided.Moment.Phased.Neighbor

/-!
# The rows of the dirty raw edges

The weighted row bounds of PD §4 "Dirty raw edges" for M7 (`eventually_edgeRaw_normLe` in
`Moment/Edge.lean`), with Schur weight one. The raw part of the edge piece `(S, I)` has
coefficients bounded by `rawAmp`: the admissibility and raw determinant indicator
`[det(z, z') = D (b - a)]` times `M!^{-2K} ρ^{hits} ρ^{hits'} ∏_i w_i`, where `w_i` is
`S(x_i)/V(a_i)` for a promotion and `ν(a_i)` for a fresh prime.

* `sum_rawAmp_le_of_empty`: with no promotions the row is at most `16 · 2^K`. For each source
  omission tuple, sample the fresh labels; the fixed determinant `D(b - a)` leaves at most `16`
  targets (`mem:neighbor`).
* `sum_rawAmp_le_of_nonempty`: with promotions `I ≠ ∅` and `i_* = max I`, the row is at most
  `16 (8 C_ρ)^K B / M^K + 16 (4B)^K e^{-L^{a_{i_*}}/4}`. Outside the exceptional fresh draws of
  the second good-state test, fix the promoted particle `(p_*, ℓ_*)` of group `i_*` (mass at most
  `B`); the anchor congruence (`anchor_unique`) leaves one omission tuple, which the source
  symmetrization weighs by `M^{-K}`, and one choice of the other promoted primes. The index
  damping `n ρ^{n-1} ≤ C_ρ` (`mem:index-damping`) absorbs the other promoted multiplicities. For
  the exceptional fresh draws, use the crude count `(2B)^{|I|}`.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

section Defs

variable (q x : ℝ) (d : Data K) (Y d₀ u v r : ℝ) (B N : ℕ)

variable {x d Y d₀ u v r B} in
/-- The weight product `∏_i w_i` of an edge choice: `S(x_i)/V(a_i)` for a promotion of the
particle `x_i` with prime `a_i`, and `ν(a_i)` for a fresh prime `a_i`. -/
def rawWeight (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℝ :=
  ∏ i, if (c.2.2.2.1 i).2 then
    (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (s.2.2.1 xp : ℝ) else 0) /
      primeMass x d (c.2.2.2.1 i).1
  else primeWeight q x d N (c.2.2.2.1 i).1

variable {x d Y d₀ u v r B} in
/-- The raw determinant equation `det(z, z') = D (b - a)` of an edge choice. -/
def RawDet (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : Prop :=
  edgeDet s c = (edgePad s c : ℤ) *
    (((∏ i, edgeSrc s c i (Fin.last _) : ℕ) : ℤ) - ((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℤ))

open scoped Classical in
variable {x d Y d₀ u v r B} in
/-- The bound for the raw coefficient: zero unless the choice is admissible and solves the raw
determinant equation, and otherwise `M!^{-2K} ρ^{hits(S, z)} ρ^{hits(S', z')} ∏_i w_i`. -/
def rawAmp (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℝ :=
  if EdgeValid x d Y d₀ u v r B s c ∧ RawDet s c then
    (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
      pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
      pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * rawWeight q N s c
  else 0

/-- The edge choices with stored groups `S` and promoted groups `I`. -/
def rawChoices (S I : Finset (Fin K)) : Finset (EdgeChoice x d Y d₀ u v r) :=
  (edgeChoices x d Y d₀ u v r).filter fun c =>
    c.2.1 = S ∧ univ.filter (fun i => (c.2.2.2.1 i).2 = true) = I

/-- The new labels with promoted groups `I`: a prime of each band, flagged exactly on `I`. -/
def labChoices (I : Finset (Fin K)) : Finset (Fin K → ℕ × Bool) :=
  (Fintype.piFinset fun i => band x (d.a i) ×ˢ (univ : Finset Bool)).filter fun lab =>
    univ.filter (fun i => (lab i).2 = true) = I

end Defs

/-- The fresh draw of the new labels outside `I`: the label for `i ∉ I`, and `1` for `i ∈ I`. -/
def freshOf (I : Finset (Fin K)) (lab : Fin K → ℕ × Bool) : Fin K → ℕ :=
  fun i => if i ∈ I then 1 else (lab i).1

/-- The other promoted primes `Z`: the label for `j ∈ I ∖ {i}`, and `1` otherwise. -/
def selOf (I : Finset (Fin K)) (i : Fin K) (lab : Fin K → ℕ × Bool) : Fin K → ℕ :=
  fun j => if j ∈ I.erase i then (lab j).1 else 1

/-- The omission tuple of a source symmetrization: the slot moved to the last place. -/
def omitOf {M : ℕ} (σ : Fin K → Equiv.Perm (Fin (M + 1))) : Fin K → Fin (M + 1) :=
  fun i => σ i (Fin.last M)

section Facts

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

variable (x d) in
/-- The multiplicity `S(y)` of the pair `y` in the memory `S` (zero unless `y` is a
particle). -/
def memAt (S : Particle x d → ℕ) (y : ℕ × ℕ) : ℕ :=
  ∑ xp : Particle x d, if xp.1 = y then S xp else 0

/-- A pair has the multiplicity of its particle, and none if it is not a particle. -/
theorem memAt_eq (S : Particle x d → ℕ) (y : ℕ × ℕ) :
    memAt x d S y = if h : y ∈ particles x d then S ⟨y, h⟩ else 0 := by
  unfold memAt
  split_ifs with h
  · refine (Fintype.sum_eq_single (f := fun xp : Particle x d => if xp.1 = y then S xp else 0)
      (⟨y, h⟩ : Particle x d) fun xp hne => ite_eq_right_iff.2 fun hxy =>
        absurd (Subtype.ext hxy) hne).trans ?_
    simp
  · exact sum_eq_zero fun xp _ => ite_eq_right_iff.2 fun hxy => absurd (hxy ▸ xp.2) h

/-- The real multiplicity sum of `rawWeight` is the multiplicity `memAt`. -/
theorem sum_ite_eq_memAt (S : Particle x d → ℕ) (y : ℕ × ℕ) :
    (∑ xp : Particle x d, if xp.1 = y then (S xp : ℝ) else 0) = memAt x d S y := by
  unfold memAt
  push_cast
  rfl

variable (x d) in
/-- The multiplicity `S(p, ·) = ∑_ℓ S(p, ℓ)` of the prime `p` in the memory `S`. -/
def rawMult (S : Particle x d → ℕ) (p : ℕ) : ℝ :=
  ∑ xp : Particle x d, if xp.1.1 = p then (S xp : ℝ) else 0

/-- The multiplicity of a prime is nonnegative. -/
theorem rawMult_nonneg (S : Particle x d → ℕ) (p : ℕ) : 0 ≤ rawMult x d S p :=
  sum_nonneg fun xp _ => by split_ifs <;> positivity

/-- The multiplicities of distinct primes sum to at most the size of the memory. -/
theorem sum_rawMult_le (S : Particle x d → ℕ) (T : Finset ℕ) :
    ∑ p ∈ T, rawMult x d S p ≤ memSize S := by
  classical
  unfold rawMult memSize
  rw [sum_comm, Nat.cast_sum]
  refine sum_le_sum fun xp _ => ?_
  rw [sum_ite_eq]
  split_ifs
  exacts [le_rfl, by positivity]

/-- The multiplicity of a pair is at most the multiplicity of its prime. -/
theorem memAt_le_rawMult (S : Particle x d → ℕ) (y : ℕ × ℕ) :
    (memAt x d S y : ℝ) ≤ rawMult x d S y.1 := by
  rw [← sum_ite_eq_memAt]
  refine sum_le_sum fun xp _ => ?_
  split_ifs with h₁ h₂ h₂
  · exact le_rfl
  · exact absurd (congrArg Prod.fst h₁) h₂
  · positivity
  · exact le_rfl

/-- The pad product is the omission product of the source lists for the omission tuple of the
source symmetrization. -/
theorem edgePad_eq_omitProd (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    edgePad s c = omitProd s.2.1.1 (omitOf c.1) := by
  unfold edgePad omitProd omitOf
  refine prod_congr rfl fun i _ => ?_
  -- reindex the slots by `σ_i`, and split off the last slot
  have hD : 0 < ∏ h, s.2.1.1 i h :=
    prod_pos fun h _ => (TypeII.band_prime (mem_band_of_mem_lists s.2.1.2 i h)).pos
  have h₁ := Fin.prod_univ_castSucc (fun h => edgeSrc s c i h)
  rw [show ∏ h, edgeSrc s c i h = ∏ h, s.2.1.1 i h from
    Equiv.prod_comp (c.1 i) (fun h => s.2.1.1 i h)] at h₁
  have h₂ := prod_erase_mul univ (fun h => s.2.1.1 i h) (mem_univ (c.1 i (Fin.last _)))
  have hl : 0 < s.2.1.1 i (c.1 i (Fin.last _)) :=
    (TypeII.band_prime (mem_band_of_mem_lists s.2.1.2 i _)).pos
  refine Nat.eq_of_mul_eq_mul_right hl ?_
  exact h₁.symm.trans h₂.symm

/-- The unshared source primes are the omitted labels. -/
theorem prod_edgeSrc_last (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    ∏ i, edgeSrc s c i (Fin.last _) = ∏ i, s.2.1.1 i (omitOf c.1 i) := rfl

/-- The product of the new labels splits into the anchor prime, the other promoted primes and
the fresh draw. -/
theorem prod_lab_eq {I : Finset (Fin K)} {i : Fin K} (hi : i ∈ I) (lab : Fin K → ℕ × Bool) :
    ∏ j, (lab j).1 = (lab i).1 * (∏ j, selOf I i lab j) * ∏ j, freshOf I lab j := by
  calc ∏ j, (lab j).1 = ∏ j, ((if j = i then (lab j).1 else 1) * selOf I i lab j *
        freshOf I lab j) := by
        refine prod_congr rfl fun j _ => ?_
        simp only [selOf, freshOf, mem_erase]
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · by_cases hjI : j ∈ I <;> simp [hj, hjI]
    _ = _ := by
        rw [prod_mul_distrib, prod_mul_distrib, prod_ite_eq']
        simp

end Facts

/-! ### Counting symmetrizations -/

/-- The permutations sending `a` to `b` number `n!/n`: `|{τ : τ a = b}| · n = n!`. -/
theorem card_perm_apply_eq {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    (univ.filter fun τ : Equiv.Perm α => τ a = b).card * Fintype.card α =
      (Fintype.card α).factorial := by
  -- every fiber has the size of the stabilizer
  have hfib : ∀ c, (univ.filter fun τ : Equiv.Perm α => τ a = c).card =
      (univ.filter fun τ : Equiv.Perm α => τ a = a).card := by
    intro c
    refine card_nbij' (fun τ => Equiv.swap a c * τ) (fun τ => Equiv.swap a c * τ) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hτ ⊢
      simp [Equiv.Perm.mul_apply, hτ]
    · intro τ hτ
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hτ ⊢
      simp [Equiv.Perm.mul_apply, hτ]
    · intro τ _
      simp [← mul_assoc]
    · intro τ _
      simp [← mul_assoc]
  have hsum := card_eq_sum_card_fiberwise (f := fun τ : Equiv.Perm α => τ a)
    (s := univ) (t := univ) (fun _ _ => mem_univ _)
  rw [card_univ, Fintype.card_perm] at hsum
  rw [hsum, hfib b]
  simp only [hfib, sum_const, card_univ, smul_eq_mul, mul_comm]

/-- The symmetrizations with a given omission tuple number `(M!/M)^K`. -/
theorem card_omitOf_eq {M : ℕ} (o : Fin K → Fin (M + 1)) :
    ((univ.filter fun σ : Fin K → Equiv.Perm (Fin (M + 1)) => omitOf σ = o).card : ℝ) =
      ((M + 1).factorial / (M + 1) : ℝ) ^ K := by
  have hset : (univ.filter fun σ : Fin K → Equiv.Perm (Fin (M + 1)) => omitOf σ = o) =
      Fintype.piFinset fun i => univ.filter fun τ : Equiv.Perm (Fin (M + 1)) =>
        τ (Fin.last M) = o i := by
    ext σ
    simp [omitOf, funext_iff]
  have hcard : ∀ i, ((univ.filter fun τ : Equiv.Perm (Fin (M + 1)) =>
      τ (Fin.last M) = o i).card : ℝ) = (M + 1).factorial / (M + 1) := by
    intro i
    have h := card_perm_apply_eq (Fin.last M) (o i)
    rw [Fintype.card_fin] at h
    rw [eq_div_iff (by positivity)]
    exact_mod_cast h
  rw [hset, Fintype.card_piFinset, Nat.cast_prod, prod_congr rfl fun i _ => hcard i, prod_const,
    card_univ, Fintype.card_fin]

/-! ### The choices of a dirty piece -/

section Choices

variable {x : ℝ} {d : Data K} {Y d₀ u v r : ℝ}

/-- A sum over the edge choices with stored groups `S` and promoted groups `I` is a sum over the
source symmetrization, the target, the new labels and the target symmetrization. -/
theorem sum_rawChoices (S I : Finset (Fin K)) (F : EdgeChoice x d Y d₀ u v r → ℝ) :
    ∑ c ∈ rawChoices x d Y d₀ u v r S I, F c =
      ∑ σ, ∑ z', ∑ lab ∈ labChoices x d I, ∑ σ', F (σ, S, z', lab, σ') := by
  rw [show (∑ σ, ∑ z', ∑ lab ∈ labChoices x d I, ∑ σ', F (σ, S, z', lab, σ')) =
      ∑ t ∈ (univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
        ((univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ
          (labChoices x d I ×ˢ (univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))))),
        F (t.1, S, t.2.1, t.2.2.1, t.2.2.2) by simp only [sum_product]]
  refine sum_nbij' (fun c => (c.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2))
    (fun t => (t.1, S, t.2.1, t.2.2.1, t.2.2.2)) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [rawChoices, edgeChoices, mem_filter, mem_product, mem_univ, true_and,
      and_true] at hc
    simp only [labChoices, mem_filter, mem_product, mem_univ, true_and, and_true]
    exact ⟨hc.1, hc.2.2⟩
  · intro t ht
    simp only [labChoices, mem_filter, mem_product, mem_univ, true_and, and_true] at ht
    simp only [rawChoices, edgeChoices, mem_filter, mem_product, mem_univ, true_and,
      and_true]
    exact ⟨ht.1, ht.2⟩
  · intro c hc
    rw [← (mem_filter.1 hc).2.1]
  · intro t _
    rfl
  · intro c hc
    rw [← (mem_filter.1 hc).2.1]

/-- The labels of an edge choice lie in the bands of their groups. -/
theorem mem_band_lab {c : EdgeChoice x d Y d₀ u v r} (hc : c ∈ edgeChoices x d Y d₀ u v r)
    (i : Fin K) : (c.2.2.2.1 i).1 ∈ band x (d.a i) := by
  simp only [edgeChoices, mem_product, Fintype.mem_piFinset, mem_univ, true_and,
    and_true] at hc
  exact hc i

/-- The labels of `labChoices` lie in the bands of their groups. -/
theorem mem_band_of_mem_labChoices {I : Finset (Fin K)} {lab : Fin K → ℕ × Bool}
    (hlab : lab ∈ labChoices x d I) (i : Fin K) : (lab i).1 ∈ band x (d.a i) :=
  (mem_product.1 (Fintype.mem_piFinset.1 (mem_filter.1 hlab).1 i)).1

/-- The labels of `labChoices` are flagged exactly on `I`. -/
theorem flag_iff_of_mem_labChoices {I : Finset (Fin K)} {lab : Fin K → ℕ × Bool}
    (hlab : lab ∈ labChoices x d I) (i : Fin K) : (lab i).2 = true ↔ i ∈ I := by
  rw [← (mem_filter.1 hlab).2, mem_filter]
  simp

end Choices

/-! ### Index damping -/

section Damping

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-- The damping constant `C_ρ = (1 - ρ)^{-2}` of `mem:index-damping`. -/
def dampConst (q : ℝ) : ℝ := 1 / (1 - pendingWeight q) ^ 2

/-- `ρ > 0`. -/
theorem pendingWeight_pos (hq : 0 < q) : 0 < pendingWeight q := Real.rpow_pos_of_pos hq _

/-- `ρ < 1`. -/
theorem pendingWeight_lt_one (hq : 0 < q) (hq₁ : q < 1) : pendingWeight q < 1 :=
  Real.rpow_lt_one hq.le hq₁ (by norm_num)

/-- `C_ρ ≥ 1`. -/
theorem one_le_dampConst (hq : 0 < q) (hq₁ : q < 1) : 1 ≤ dampConst q := by
  have h₀ := pendingWeight_pos hq
  have h₁ := pendingWeight_lt_one hq hq₁
  unfold dampConst
  rw [le_div_iff₀ (by nlinarith), one_mul]
  nlinarith

/-- **The index damping** (PD `mem:index-damping`): `n ρ^{n-1} ≤ C_ρ`. -/
theorem mul_pow_le_dampConst (hq : 0 < q) (hq₁ : q < 1) (n : ℕ) :
    (n : ℝ) * pendingWeight q ^ (n - 1) ≤ dampConst q := by
  have h₀ := pendingWeight_pos hq
  have h₁ := pendingWeight_lt_one hq hq₁
  rcases n with _ | n
  · simp only [Nat.cast_zero, zero_mul]
    exact zero_le_one.trans (one_le_dampConst hq hq₁)
  · have hsum := hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖pendingWeight q‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos h₀])
    have hle := le_hasSum hsum (n + 1) fun j _ => by positivity
    simp only [Nat.add_sub_cancel]
    unfold dampConst
    rw [pow_succ, ← mul_assoc, div_eq_mul_one_div] at hle
    exact le_of_mul_le_mul_right (by rwa [mul_comm (pendingWeight q)] at hle) h₀

/-- With disjoint bands, each particle is promoted by at most one group, so the memory after
the edge has `S'(x) ≥ S(x) - 1`. -/
theorem sub_one_le_edgeMem (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (xp : Particle x d) :
    s.2.2.1 xp - 1 ≤ edgeMem s c xp := by
  classical
  have hP : (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card ≤ 1 :=
    card_le_one.2 fun i hi j hj => by
      by_contra hij
      have hij' := congrArg Prod.fst ((mem_filter.1 hi).2.2.trans (mem_filter.1 hj).2.2.symm)
      change (c.2.2.2.1 i).1 = (c.2.2.2.1 j).1 at hij'
      exact disjoint_left.1 (hdisj i j hij) (mem_band_lab hc i) (hij' ▸ mem_band_lab hc j)
  unfold edgeMem
  omega

/-- **The damping of the other promotions**: with disjoint bands, for any set `J` of groups the
promoted multiplicities `S(x_i)` are absorbed by the outgoing pending damping:
`ρ^{hits(S', z')} ∏_{i ∈ J} S(x_i) ≤ C_ρ^{|J|}`. The promoted particles `x_i` hit `z'`, are
distinct, and `S'(x_i) ≥ S(x_i) - 1`. -/
theorem pow_hits_mul_prod_le (hq : 0 < q) (hq₁ : q < 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (J : Finset (Fin K)) :
    pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
        ∏ i ∈ J, (memAt x d s.2.2.1 (edgePromoted c i) : ℝ) ≤ dampConst q ^ J.card := by
  classical
  set S := s.2.2.1 with hS
  set S' := edgeMem s c with hS'
  set y : Fin K → ℕ × ℕ := fun i => edgePromoted c i with hy
  have h₀ := pendingWeight_pos hq
  have h₁ := pendingWeight_lt_one hq hq₁
  -- `S'(x_i) ≥ S(x_i) - 1`
  have hmem : ∀ i, memAt x d S (y i) - 1 ≤ memAt x d S' (y i) := by
    intro i
    rw [memAt_eq, memAt_eq]
    split_ifs
    · exact sub_one_le_edgeMem hdisj hc _
    · exact Nat.zero_le _
  -- the promoted particles are distinct and hit the target
  have hcard : ∀ xp : Particle x d, (J.filter fun i => y i = xp.1).card ≤ 1 := fun xp =>
    card_le_one.2 fun i hi j hj => by
      by_contra hij
      have hij' := congrArg Prod.fst ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm)
      change (c.2.2.2.1 i).1 = (c.2.2.2.1 j).1 at hij'
      exact disjoint_left.1 (hdisj i j hij) (mem_band_lab hc i) (hij' ▸ mem_band_lab hc j)
  have hhits : ∑ i ∈ J, memAt x d S' (y i) ≤ pendingHits x d c.2.2.1.1 S' := by
    unfold memAt pendingHits
    rw [sum_comm]
    refine sum_le_sum fun xp _ => ?_
    rw [← sum_filter, sum_const, smul_eq_mul]
    rcases Nat.eq_zero_or_pos (J.filter fun i => xp.1 = y i).card with h0 | hpos
    · rw [h0, zero_mul]
      exact Nat.zero_le _
    · obtain ⟨i, hi⟩ := card_pos.1 hpos
      have hxi := (mem_filter.1 hi).2
      have hline : lineOf xp.1.1 c.2.2.1.1 = xp.1.2 := by rw [hxi]; rfl
      rw [ite_eq_left_iff.2 (fun h => absurd hline h)]
      have : (J.filter fun i => xp.1 = y i).card ≤ 1 := by
        simpa only [eq_comm] using hcard xp
      calc (J.filter fun i => xp.1 = y i).card * S' xp ≤ 1 * S' xp :=
            Nat.mul_le_mul_right _ this
        _ = S' xp := one_mul _
  have hexp : ∑ i ∈ J, (memAt x d S (y i) - 1) ≤ pendingHits x d c.2.2.1.1 S' :=
    (sum_le_sum fun i _ => hmem i).trans hhits
  calc pendingWeight q ^ pendingHits x d c.2.2.1.1 S' * ∏ i ∈ J, (memAt x d S (y i) : ℝ)
      ≤ pendingWeight q ^ (∑ i ∈ J, (memAt x d S (y i) - 1)) *
          ∏ i ∈ J, (memAt x d S (y i) : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h₀.le h₁.le hexp)
          (prod_nonneg fun _ _ => by positivity)
    _ = ∏ i ∈ J, ((memAt x d S (y i) : ℝ) * pendingWeight q ^ (memAt x d S (y i) - 1)) := by
        rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
        exact prod_congr rfl fun i _ => mul_comm _ _
    _ ≤ ∏ _i ∈ J, dampConst q :=
        prod_le_prod₀ (fun i _ => by positivity) fun i _ => mul_pow_le_dampConst hq hq₁ _
    _ = dampConst q ^ J.card := prod_const _

end Damping

/-! ### Measure facts -/

section Measure

variable {q x : ℝ} {d : Data K} {N : ℕ}

/-- With disjoint bands, a prime of band `i` has `V(p) = V_i`. -/
theorem primeMass_eq_of_mem_band
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j))) {i : Fin K} {p : ℕ}
    (hp : p ∈ band x (d.a i)) : primeMass x d p = harmonicMass (band x (d.a i)) := by
  unfold primeMass
  rw [Fintype.sum_eq_single i fun j hji =>
    ite_eq_right_iff.2 fun hpj => absurd hp (disjoint_left.1 (hdisj j i hji) hpj)]
  exact ite_eq_left hp

/-- With nonnegative band masses and baselines at least `1/2`, the birth weights are
nonnegative; off the band primes `V(p) = 0`. -/
theorem primeWeight_nonneg_of (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (p : ℕ) :
    0 ≤ primeWeight q x d N p := by
  have hV0 : 0 ≤ primeMass x d p :=
    sum_nonneg fun i _ => by split_ifs; linarith [hV i]; exact le_rfl
  unfold primeWeight
  by_cases hp : p ∈ bandPrimes x d
  · have := hb p hp
    exact one_div_nonneg.2 (mul_nonneg (mul_nonneg hV0 (by positivity)) (by linarith))
  · have h0 : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_biUnion.2 ⟨i, mem_univ i, hpi⟩)
    rw [h0]
    simp

/-- At a prime of band `i`, `0 < ν(p) ≤ 2 μ_i(p)` with `μ_i(p) = 1/(p V_i)`
(`mem:measure-masses`). -/
theorem primeWeight_le_two
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {i : Fin K} {p : ℕ}
    (hp : p ∈ band x (d.a i)) :
    0 < primeWeight q x d N p ∧
      primeWeight q x d N p ≤ 2 * (1 / (p * harmonicMass (band x (d.a i)))) := by
  have hVi := hV i
  have hb₁ := hb p (mem_biUnion.2 ⟨i, mem_univ i, hp⟩)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hp).pos
  unfold primeWeight
  rw [primeMass_eq_of_mem_band hdisj hp]
  refine ⟨one_div_pos.2 (mul_pos (mul_pos (by linarith) (by positivity)) (by linarith)), ?_⟩
  rw [show 2 * (1 / (p * harmonicMass (band x (d.a i)))) =
    1 / (harmonicMass (band x (d.a i)) * p * (1 / 2)) by field_simp]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have : (p : ℝ) * (1 / 2) ≤ ((p : ℝ) + 1) * baseline q N p := by nlinarith
  calc harmonicMass (band x (d.a i)) * p * (1 / 2)
      = harmonicMass (band x (d.a i)) * ((p : ℝ) * (1 / 2)) := by ring
    _ ≤ harmonicMass (band x (d.a i)) * (((p : ℝ) + 1) * baseline q N p) :=
        mul_le_mul_of_nonneg_left this (by linarith)
    _ = _ := by ring

/-- The birth weights of a band sum to at most `2`. -/
theorem sum_primeWeight_band_le_two
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (i : Fin K) :
    ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 2 := by
  have hVi : 0 < harmonicMass (band x (d.a i)) := by linarith [hV i]
  calc ∑ p ∈ band x (d.a i), primeWeight q x d N p
      ≤ ∑ p ∈ band x (d.a i), 2 * (1 / (p * harmonicMass (band x (d.a i)))) :=
        sum_le_sum fun p hp => (primeWeight_le_two hdisj hV hb hp).2
    _ = 2 / harmonicMass (band x (d.a i)) * harmonicMass (band x (d.a i)) := by
        nth_rewrite 3 [harmonicMass]
        rw [mul_sum]
        refine sum_congr rfl fun p _ => ?_
        field_simp
    _ = 2 := by field_simp

/-- The fresh draws outside `I` have total birth weight at most `2^K`. -/
theorem sum_freshDraws_le
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (I : Finset (Fin K)) :
    ∑ T ∈ freshDraws x d I, ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i) ≤ 2 ^ K := by
  have hν := primeWeight_nonneg_of hV hb (q := q) (N := N)
  calc ∑ T ∈ freshDraws x d I, ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i)
      = ∑ T ∈ freshDraws x d I, ∏ i, if i ∈ I then 1 else primeWeight q x d N (T i) := by
        refine sum_congr rfl fun T _ => ?_
        rw [prod_filter]
        exact prod_congr rfl fun i _ => by split_ifs <;> rfl
    _ = ∏ i, ∑ t ∈ (if i ∈ I then {1} else band x (d.a i)),
          if i ∈ I then 1 else primeWeight q x d N t := by
        rw [freshDraws, prod_univ_sum]
    _ ≤ ∏ _i : Fin K, (2 : ℝ) := by
        refine prod_le_prod₀ (fun i _ => sum_nonneg fun t _ => ?_) fun i _ => ?_
        · split_ifs
          exacts [zero_le_one, hν _]
        split_ifs with hi
        · simp
        · exact sum_primeWeight_band_le_two hdisj hV hb i
    _ = 2 ^ K := by rw [prod_const, card_univ, Fintype.card_fin]

open scoped Classical in
/-- **The exceptional fresh draws** (PD `mem:measure-masses` and test (ii)): at a source passing
the second good-state test, the fresh draws outside `I ≠ ∅` failing the phase separation have
total birth weight at most `2^K exp(-L^{a_{i_*}}/4)`. -/
theorem sum_bad_le (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {d₀ rr : ℝ} {J : ℕ} {p : Lists K J}
    (hgood : GoodSecond x d d₀ rr p) {I : Finset (Fin K)} (hI : I.Nonempty) :
    ∑ T ∈ (freshDraws x d I).filter (fun T => ¬ Separated x d d₀ I (I.max' hI) rr p T),
        ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i) ≤
      2 ^ K * Real.exp (-Real.log x ^ d.a (I.max' hI) / 4) := by
  have hν := primeWeight_nonneg_of hV hb (q := q) (N := N)
  calc ∑ T ∈ (freshDraws x d I).filter (fun T => ¬ Separated x d d₀ I (I.max' hI) rr p T),
        ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i)
      ≤ ∑ T ∈ (freshDraws x d I).filter (fun T => ¬ Separated x d d₀ I (I.max' hI) rr p T),
          2 ^ K * freshWeight x d I T := by
        refine sum_le_sum fun T hT => ?_
        have hT' := Fintype.mem_piFinset.1 (mem_filter.1 hT).1
        unfold freshWeight
        calc ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i)
            ≤ ∏ i ∈ univ.filter (· ∉ I), 2 * (1 / ((T i : ℝ) * harmonicMass (band x (d.a i)))) :=
              prod_le_prod₀ (fun i _ => hν _) fun i hi => by
                have hTi := hT' i
                rw [ite_eq_right (mem_filter.1 hi).2] at hTi
                exact (primeWeight_le_two hdisj hV hb hTi).2
          _ = 2 ^ (univ.filter (· ∉ I)).card *
                ∏ i ∈ univ.filter (· ∉ I), 1 / ((T i : ℝ) * harmonicMass (band x (d.a i))) := by
              rw [prod_mul_distrib, prod_const]
          _ ≤ 2 ^ K *
                ∏ i ∈ univ.filter (· ∉ I), 1 / ((T i : ℝ) * harmonicMass (band x (d.a i))) := by
              refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ?_)
                (prod_nonneg fun i _ => one_div_nonneg.2 (mul_nonneg (by positivity)
                  (by linarith [hV i])))
              exact (card_filter_le _ _).trans (by rw [card_univ, Fintype.card_fin])
    _ = 2 ^ K * ∑ T ∈ (freshDraws x d I).filter
          (fun T => ¬ Separated x d d₀ I (I.max' hI) rr p T), freshWeight x d I T := by
        rw [mul_sum]
    _ ≤ 2 ^ K * Real.exp (-Real.log x ^ d.a (I.max' hI) / 4) :=
        mul_le_mul_of_nonneg_left (hgood I hI) (by positivity)

end Measure

/-! ### Summing the new labels -/

/-- **The label sum**: over the labels flagged on `I` whose fresh draw lies in `E`, a product of
nonnegative label weights `ω` sums to at most `Bm^{|I|} ∑_{T ∈ E} ∏_{i ∉ I} ω(T_i)`, if every
promoted group has `∑_{p ∈ 𝒫_i} ω(p, true) ≤ Bm`. -/
theorem sum_labChoices_le {x : ℝ} {d : Data K} (I : Finset (Fin K)) (E : Finset (Fin K → ℕ))
    {ω : ℕ × Bool → ℝ} (hω : ∀ l, 0 ≤ ω l) {Bm : ℝ}
    (hB : ∀ i ∈ I, ∑ p ∈ band x (d.a i), ω (p, true) ≤ Bm) :
    ∑ lab ∈ (labChoices x d I).filter (fun lab => freshOf I lab ∈ E), ∏ i, ω (lab i) ≤
      Bm ^ I.card * ∑ T ∈ E, ∏ i ∈ univ.filter (· ∉ I), ω (T i, false) := by
  classical
  rw [← sum_fiberwise_of_maps_to (g := freshOf I) (t := E) (fun lab hlab => (mem_filter.1 hlab).2),
    mul_sum]
  refine sum_le_sum fun T _ => ?_
  -- the label weights of the fiber as a product over the groups
  set g : Fin K → ℕ × Bool → ℝ := fun i l =>
    if i ∈ I then (if l.2 then ω l else 0) else (if l = (T i, false) then ω l else 0) with hg
  have hg0 : ∀ i l, 0 ≤ g i l := fun i l => by
    simp only [hg]
    split_ifs <;> first | exact hω _ | exact le_rfl
  calc ∑ lab ∈ ((labChoices x d I).filter fun lab => freshOf I lab ∈ E).filter
        (fun lab => freshOf I lab = T), ∏ i, ω (lab i)
      = ∑ lab ∈ ((labChoices x d I).filter fun lab => freshOf I lab ∈ E).filter
          (fun lab => freshOf I lab = T), ∏ i, g i (lab i) := by
        refine sum_congr rfl fun lab hlab => prod_congr rfl fun i _ => ?_
        obtain ⟨⟨hlab, -⟩, hT⟩ := mem_filter.1 hlab |>.imp_left mem_filter.1
        have hf := flag_iff_of_mem_labChoices hlab i
        simp only [hg]
        by_cases hi : i ∈ I
        · rw [ite_eq_left hi, ite_eq_left (hf.2 hi)]
        · rw [ite_eq_right hi]
          have hl : lab i = (T i, false) := by
            refine Prod.ext ?_ ?_
            · rw [← hT]
              simp [freshOf, hi]
            · simpa [hi] using hf
          rw [ite_eq_left hl]
    _ ≤ ∑ lab ∈ Fintype.piFinset (fun i => band x (d.a i) ×ˢ (univ : Finset Bool)),
          ∏ i, g i (lab i) :=
        sum_le_sum_of_subset_of_nonneg (fun lab hlab =>
          (mem_filter.1 (mem_filter.1 (mem_filter.1 hlab).1).1).1)
          fun lab _ _ => prod_nonneg fun i _ => hg0 i _
    _ = ∏ i, ∑ l ∈ band x (d.a i) ×ˢ (univ : Finset Bool), g i l := (prod_univ_sum _ _).symm
    _ ≤ ∏ i, if i ∈ I then Bm else ω (T i, false) := by
        refine prod_le_prod₀ (fun i _ => sum_nonneg fun l _ => hg0 i l) fun i _ => ?_
        by_cases hi : i ∈ I
        · rw [ite_eq_left hi]
          simp only [hg, ite_eq_left hi, sum_product, Fintype.sum_bool, ↓reduceIte,
            Bool.false_eq_true, add_zero]
          exact hB i hi
        · rw [ite_eq_right hi]
          simp only [hg, ite_eq_right hi]
          rw [sum_ite_eq']
          split_ifs
          exacts [le_rfl, hω _]
    _ = Bm ^ I.card * ∏ i ∈ univ.filter (· ∉ I), ω (T i, false) := by
        rw [prod_ite, prod_const, filter_mem_eq_inter, univ_inter]

/-! ### The crude row -/

section Crude

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

variable (q x d N) in
/-- The crude weight of a new label: `2 S(p, ·)` for a promotion of a particle with prime `p`,
and `ν(p)` for a fresh prime `p`. -/
def labWeight (S : Particle x d → ℕ) (l : ℕ × Bool) : ℝ :=
  if l.2 then 2 * rawMult x d S l.1 else primeWeight q x d N l.1

/-- The crude label weights are nonnegative. -/
theorem labWeight_nonneg (hν : ∀ p, 0 ≤ primeWeight q x d N p) (S : Particle x d → ℕ)
    (l : ℕ × Bool) : 0 ≤ labWeight q x d N S l := by
  unfold labWeight
  split_ifs
  exacts [mul_nonneg zero_le_two (rawMult_nonneg _ _), hν _]

/-- The determinant value `D (b - a)` of the raw equation, for the source symmetrization `σ` and
the new labels. -/
def rawN (s : ChainState x d Y d₀ u v r B) (σ : Fin K → Equiv.Perm (Fin (padCount x + 1)))
    (lab : Fin K → ℕ × Bool) : ℤ :=
  (omitProd s.2.1.1 (omitOf σ) : ℤ) *
    (((∏ i, s.2.1.1 i (omitOf σ i) : ℕ) : ℤ) - ((∏ i, (lab i).1 : ℕ) : ℤ))

/-- The raw determinant equation as an equation for the target. -/
theorem rawDet_iff (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    RawDet s c ↔ s.1.1.1 * c.2.2.1.1.2 - s.1.1.2 * c.2.2.1.1.1 = rawN s c.1 c.2.2.2.1 := by
  unfold RawDet rawN
  rw [edgePad_eq_omitProd, prod_edgeSrc_last]
  rfl

/-- **The crude coefficient bound**: `rawAmp ≤ M!^{-2K} ∏_i ω(a_i) [det(z, z') = D (b - a)]`.
The pending weights are at most one, and a promotion weight `S(x_i)/V(a_i)` is at most
`2 S(a_i, ·)`. -/
theorem rawAmp_le_crude (hq : 0 < q) (hq₁ : q < 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) :
    rawAmp q N s c ≤ (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
      (∏ i, labWeight q x d N s.2.2.1 (c.2.2.2.1 i)) *
      (if s.1.1.1 * c.2.2.1.1.2 - s.1.1.2 * c.2.2.1.1.1 = rawN s c.1 c.2.2.2.1 then 1 else 0) := by
  classical
  have hρ0 := (pendingWeight_pos hq).le
  have hρ1 := (pendingWeight_lt_one hq hq₁).le
  have hω0 : 0 ≤ ∏ i, labWeight q x d N s.2.2.1 (c.2.2.2.1 i) :=
    prod_nonneg fun i _ => labWeight_nonneg hν _ _
  unfold rawAmp
  split_ifs with hv hdet hdet
  · rw [mul_one]
    have hW : rawWeight q N s c ≤ ∏ i, labWeight q x d N s.2.2.1 (c.2.2.2.1 i) := by
      refine prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
      · split_ifs
        · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity)
            (by rw [primeMass_eq_of_mem_band hdisj (mem_band_lab hc i)]; linarith [hV i])
        · exact hν _
      · unfold labWeight
        split_ifs with hf
        · have hVi := hV i
          rw [primeMass_eq_of_mem_band hdisj (mem_band_lab hc i), sum_ite_eq_memAt,
            div_le_iff₀ (by linarith)]
          have h₁ := memAt_le_rawMult s.2.2.1 (edgePromoted c i)
          have h₂ := rawMult_nonneg s.2.2.1 (c.2.2.2.1 i).1
          change (memAt x d s.2.2.1 (edgePromoted c i) : ℝ) ≤ rawMult x d s.2.2.1 (c.2.2.2.1 i).1
            at h₁
          nlinarith
        · exact le_rfl
    have hW0 : 0 ≤ rawWeight q N s c := prod_nonneg fun i _ => by
      split_ifs
      · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity)
          (by rw [primeMass_eq_of_mem_band hdisj (mem_band_lab hc i)]; linarith [hV i])
      · exact hν _
    calc (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * rawWeight q N s c
        ≤ (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * 1 * 1 *
            ∏ i, labWeight q x d N s.2.2.1 (c.2.2.2.1 i) := by
          gcongr
          · exact pow_le_one₀ hρ0 hρ1
          · exact pow_le_one₀ hρ0 hρ1
      _ = _ := by ring
  · exact absurd ((rawDet_iff s c).1 hv.2) hdet
  · rw [mul_one]
    exact mul_nonneg (by positivity) hω0
  · rw [mul_zero]

/-- The targets with a given determinant against the source number at most `16`
(`mem:neighbor`). -/
theorem sum_target_le (hU : 0 < d₀ * Y * d.Hm) (s : ChainState x d Y d₀ u v r B) (n : ℤ) :
    ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      (if s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = n then (1 : ℝ) else 0) ≤ 16 := by
  rw [sum_coe_sort (rootPositions (d₀ * Y * d.Hm) d.Hn u v r)
    (fun z' => if s.1.1.1 * z'.2 - s.1.1.2 * z'.1 = n then (1 : ℝ) else 0), sum_boole]
  exact_mod_cast card_filter_det_le hU s.1.2 n

/-- The number of symmetrizations is `M!^K`. -/
theorem card_edgeSymm :
    (Fintype.card (Fin K → Equiv.Perm (Fin (padCount x + 1))) : ℝ) =
      (((padCount x + 1).factorial ^ K : ℕ) : ℝ) := by
  simp [Fintype.card_perm]

/-- **The crude row** (PD `mem:edge-crude`, restricted): for any set `E` of fresh draws, the raw
coefficients of the piece `(S, I)` whose fresh draw lies in `E` sum to at most
`16 (2B)^{|I|} ∑_{T ∈ E} ∏_{i ∉ I} ν(T_i)`. The symmetrizations cancel `M!^{-2K}`, each promoted
group carries `∑_p 2 S(p, ·) ≤ 2B`, and the targets number at most `16`. -/
theorem sum_rawAmp_fresh_le (hq : 0 < q) (hq₁ : q < 1) (hU : 0 < d₀ * Y * d.Hm)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (s : ChainState x d Y d₀ u v r B)
    (S I : Finset (Fin K)) (E : Finset (Fin K → ℕ)) :
    ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter (fun c => freshOf I c.2.2.2.1 ∈ E),
        rawAmp q N s c ≤
      16 * (2 * B) ^ I.card * ∑ T ∈ E, ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i) := by
  classical
  have hν := primeWeight_nonneg_of hV hb (q := q) (N := N)
  set r₀ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set ω := labWeight q x d N s.2.2.1 with hω
  set Wsum := ∑ T ∈ E, ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i) with hWsum
  have hr0 : 0 ≤ r₀ := by positivity
  have hω0 : ∀ l, 0 ≤ ω l := labWeight_nonneg hν _
  -- the label sum
  have hlab : ∑ lab ∈ (labChoices x d I).filter (fun lab => freshOf I lab ∈ E),
      ∏ i, ω (lab i) ≤ (2 * B) ^ I.card * Wsum := by
    refine sum_labChoices_le I E hω0 fun i _ => ?_
    simp only [hω, labWeight, ↓reduceIte, ← mul_sum]
    have h₁ := sum_rawMult_le s.2.2.1 (band x (d.a i))
    have h₂ : (memSize s.2.2.1 : ℝ) ≤ B := by exact_mod_cast mem_memStates.1 s.2.2.2
    linarith
  -- the inner sum over the target, the labels and `σ'`
  have hinner : ∀ σ, ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      ∑ lab ∈ labChoices x d I, ∑ _σ' : Fin K → Equiv.Perm (Fin (padCount x + 1)),
        (if freshOf I lab ∈ E then r₀ * (∏ i, ω (lab i)) *
          (if s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = rawN s σ lab then 1 else 0) else 0) ≤
      (((padCount x + 1).factorial ^ K : ℕ) : ℝ) * (r₀ * (16 * ((2 * B) ^ I.card * Wsum))) := by
    intro σ
    simp only [sum_const, card_univ, nsmul_eq_mul, card_edgeSymm, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [sum_comm]
    calc ∑ lab ∈ labChoices x d I, ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
          (if freshOf I lab ∈ E then r₀ * (∏ i, ω (lab i)) *
            (if s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = rawN s σ lab then 1 else 0) else 0)
        ≤ ∑ lab ∈ labChoices x d I, if freshOf I lab ∈ E then r₀ * (∏ i, ω (lab i)) * 16
            else 0 := by
          refine sum_le_sum fun lab _ => ?_
          split_ifs
          · rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left (sum_target_le hU s _)
              (mul_nonneg hr0 (prod_nonneg fun i _ => hω0 _))
          · simp
      _ = r₀ * 16 * ∑ lab ∈ (labChoices x d I).filter (fun lab => freshOf I lab ∈ E),
            ∏ i, ω (lab i) := by
          rw [sum_filter, mul_sum]
          exact sum_congr rfl fun lab _ => by split_ifs <;> ring
      _ ≤ r₀ * 16 * ((2 * B) ^ I.card * Wsum) := mul_le_mul_of_nonneg_left hlab (by positivity)
      _ = r₀ * (16 * ((2 * B) ^ I.card * Wsum)) := by ring
  calc ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter (fun c => freshOf I c.2.2.2.1 ∈ E),
        rawAmp q N s c
      = ∑ σ, ∑ z', ∑ lab ∈ labChoices x d I, ∑ σ',
          if freshOf I lab ∈ E then rawAmp q N s (σ, S, z', lab, σ') else 0 := by
        rw [sum_filter, sum_rawChoices]
    _ ≤ ∑ σ, ∑ z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
          ∑ lab ∈ labChoices x d I, ∑ _σ' : Fin K → Equiv.Perm (Fin (padCount x + 1)),
            (if freshOf I lab ∈ E then r₀ * (∏ i, ω (lab i)) *
              (if s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = rawN s σ lab then 1 else 0) else 0) := by
        refine sum_le_sum fun σ _ => sum_le_sum fun z' _ => sum_le_sum fun lab hlab =>
          sum_le_sum fun σ' _ => ?_
        by_cases hE : freshOf I lab ∈ E
        · simp only [hE, ↓reduceIte]
          refine rawAmp_le_crude hq hq₁ hdisj hV hν s ?_
          simp only [edgeChoices, mem_product, mem_univ, true_and, and_true]
          exact (mem_filter.1 hlab).1
        · simp only [hE, ↓reduceIte, le_refl]
    _ ≤ ∑ _σ : Fin K → Equiv.Perm (Fin (padCount x + 1)),
          (((padCount x + 1).factorial ^ K : ℕ) : ℝ) * (r₀ * (16 * ((2 * B) ^ I.card * Wsum))) :=
        sum_le_sum fun σ _ => hinner σ
    _ = 16 * (2 * B) ^ I.card * Wsum := by
        have hf : (((padCount x + 1).factorial ^ K : ℕ) : ℝ) ≠ 0 := by positivity
        rw [sum_const, card_univ, nsmul_eq_mul, card_edgeSymm, hr₀]
        field_simp

end Crude

/-! ### The anchored row -/

section Anchored

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The conditions on a raw dirty edge used by the anchor argument: the omission product lies in
`[d₀, 2d₀)`, the new labels avoid the source labels (the ban), and the target solves the raw
determinant equation. -/
def AnchorCond (s : ChainState x d Y d₀ u v r B)
    (σ : Fin K → Equiv.Perm (Fin (padCount x + 1)))
    (z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) (lab : Fin K → ℕ × Bool) : Prop :=
  d₀ ≤ (omitProd s.2.1.1 (omitOf σ) : ℝ) ∧ (omitProd s.2.1.1 (omitOf σ) : ℝ) < 2 * d₀ ∧
    (∀ i i' h, (lab i).1 ≠ s.2.1.1 i' h) ∧
    s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = rawN s σ lab

/-- An admissible raw edge satisfies the anchor conditions. -/
theorem anchorCond_of_valid {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h : EdgeValid x d Y d₀ u v r B s c ∧ RawDet s c) : AnchorCond s c.1 c.2.2.1 c.2.2.2.1 := by
  obtain ⟨hv, hdet⟩ := h
  obtain ⟨-, hban, hD₁, hD₂, -⟩ := hv
  rw [edgePad_eq_omitProd] at hD₁ hD₂
  exact ⟨hD₁, hD₂, hban, (rawDet_iff s c).1 hdet⟩

open scoped Classical in
/-- **The anchored coefficient bound**: on the piece `(S, I)` with `I ≠ ∅` and `i_* = max I`,
`rawAmp ≤ M!^{-2K} (2 C_ρ)^K S(x_{i_*}) ∏_{i ∉ I} ν(a_i) [admissible, raw]`. The weight of the
anchor promotion is kept; the other promotions are absorbed by the index damping
(`pow_hits_mul_prod_le`), and `1/V ≤ 2`. -/
theorem rawAmp_le_anchor (hq : 0 < q) (hq₁ : q < 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) {S I : Finset (Fin K)} (hI : I.Nonempty)
    {c : EdgeChoice x d Y d₀ u v r} (hc : c ∈ rawChoices x d Y d₀ u v r S I) :
    rawAmp q N s c ≤ (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 * (2 * dampConst q) ^ K *
      (memAt x d s.2.2.1 (edgePromoted c (I.max' hI)) : ℝ) *
      (∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (c.2.2.2.1 i).1) *
      (if EdgeValid x d Y d₀ u v r B s c ∧ RawDet s c then 1 else 0) := by
  classical
  obtain ⟨hc, -, hflag⟩ := mem_filter.1 hc
  set i₀ := I.max' hI with hi₀
  have hi₀I : i₀ ∈ I := I.max'_mem hI
  have hρ0 := (pendingWeight_pos hq).le
  have hρ1 := (pendingWeight_lt_one hq hq₁).le
  have hdC := one_le_dampConst hq hq₁
  have hVa : ∀ i, 1 / 2 ≤ primeMass x d (c.2.2.2.1 i).1 := fun i => by
    rw [primeMass_eq_of_mem_band hdisj (mem_band_lab hc i)]
    exact hV i
  set m : Fin K → ℝ := fun i => (memAt x d s.2.2.1 (edgePromoted c i) : ℝ) with hm
  set F := ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (c.2.2.2.1 i).1 with hF
  have hF0 : 0 ≤ F := prod_nonneg fun i _ => hν _
  have hm0 : ∀ i, 0 ≤ m i := fun i => Nat.cast_nonneg _
  unfold rawAmp
  split_ifs with h
  · rw [mul_one]
    -- the weight splits into the promotions and the fresh primes
    have hW : rawWeight q N s c ≤ 2 ^ K * (m i₀ * ∏ i ∈ I.erase i₀, m i) * F := by
      have hsplit : rawWeight q N s c = (∏ i ∈ I, m i / primeMass x d (c.2.2.2.1 i).1) * F := by
        unfold rawWeight
        rw [prod_ite, hflag]
        congr 1
        · exact prod_congr rfl fun i _ => by rw [sum_ite_eq_memAt]
        · rw [hF]
          refine prod_congr (filter_congr fun i _ => ?_) fun i _ => rfl
          rw [← hflag, mem_filter]
          simp
      rw [hsplit]
      refine mul_le_mul_of_nonneg_right ?_ hF0
      calc ∏ i ∈ I, m i / primeMass x d (c.2.2.2.1 i).1 ≤ ∏ i ∈ I, 2 * m i :=
            prod_le_prod₀ (fun i _ => div_nonneg (hm0 i) (by linarith [hVa i])) fun i _ => by
              rw [div_le_iff₀ (by linarith [hVa i])]
              nlinarith [hVa i, hm0 i]
        _ = 2 ^ I.card * ∏ i ∈ I, m i := by rw [prod_mul_distrib, prod_const]
        _ ≤ 2 ^ K * ∏ i ∈ I, m i := by
            refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ?_)
              (prod_nonneg fun i _ => hm0 i)
            exact (card_le_univ I).trans (by rw [Fintype.card_fin])
        _ = 2 ^ K * (m i₀ * ∏ i ∈ I.erase i₀, m i) := by rw [mul_prod_erase I m hi₀I]
    -- the damping absorbs the other promotions
    have hdamp := pow_hits_mul_prod_le hq hq₁ hdisj (s := s) hc (I.erase i₀)
    have hdamp' : pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
        ∏ i ∈ I.erase i₀, m i ≤ dampConst q ^ K :=
      hdamp.trans (pow_le_pow_right₀ hdC ((card_le_univ _).trans (by rw [Fintype.card_fin])))
    have hW0 : 0 ≤ rawWeight q N s c := prod_nonneg fun i _ => by
      split_ifs
      · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity)
          (by linarith [hVa i])
      · exact hν _
    set r₀ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
    have hr0 : 0 ≤ r₀ := by positivity
    set ρh := pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) with hρh
    have hρh0 : 0 ≤ ρh := pow_nonneg hρ0 _
    calc r₀ * pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 * ρh * rawWeight q N s c
        ≤ r₀ * 1 * ρh * (2 ^ K * (m i₀ * ∏ i ∈ I.erase i₀, m i) * F) := by
          gcongr
          exact pow_le_one₀ hρ0 hρ1
      _ = r₀ * 2 ^ K * m i₀ * F * (ρh * ∏ i ∈ I.erase i₀, m i) := by ring
      _ ≤ r₀ * 2 ^ K * m i₀ * F * dampConst q ^ K :=
          mul_le_mul_of_nonneg_left hdamp' (by have := hm0 i₀; positivity)
      _ = r₀ * (2 * dampConst q) ^ K * m i₀ * F := by ring
  · rw [mul_zero]

open scoped Classical in
/-- **The anchor count**: at a source in the box, for a fresh draw `T` passing the phase
separation and a pending particle `(p_*, ℓ_*)`, the triples `(σ, z', a)` of the piece with
promoted groups `I ∋ i_*` whose fresh draw is `T`, whose anchor promotion is `(p_*, ℓ_*)`
and which satisfy the anchor conditions number at most `16 (M!/M)^K`: the omission tuple and
the other promoted primes are unique (`anchor_unique`), and then at most `16` targets solve
the determinant equation. -/
theorem card_anchor_le (hU : 0 < d₀ * Y * d.Hm) (hu : 0 < u)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (s : ChainState x d Y d₀ u v r B) {I : Finset (Fin K)} (hI : I.Nonempty) {T : Fin K → ℕ}
    (hsep : Separated x d d₀ I (I.max' hI) (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 T)
    (xp : Particle x d) :
    ((((univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
        ((univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ labChoices x d I)).filter
        fun t : (Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
            ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ × Bool) =>
          freshOf I t.2.2 = T ∧
          xp.1 = ((t.2.2 (I.max' hI)).1, lineOf (t.2.2 (I.max' hI)).1 t.2.1.1) ∧
          AnchorCond s t.1 t.2.1 t.2.2).card : ℝ) ≤
      16 * (((padCount x + 1).factorial / (padCount x + 1) : ℝ)) ^ K := by
  classical
  set i₀ := I.max' hI with hi₀
  have hi₀I : i₀ ∈ I := I.max'_mem hI
  set F := ((univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
      ((univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ labChoices x d I)).filter
      fun t : (Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
          ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ × Bool) =>
        freshOf I t.2.2 = T ∧
        xp.1 = ((t.2.2 i₀).1, lineOf (t.2.2 i₀).1 t.2.1.1) ∧ AnchorCond s t.1 t.2.1 t.2.2
    with hFdef
  rcases F.eq_empty_or_nonempty with hF | ⟨t₀, ht₀⟩
  · rw [hF, card_empty, Nat.cast_zero]
    positivity
  have hprime : ∀ i h, (s.2.1.1 i h).Prime := fun i h =>
    TypeII.band_prime (mem_band_of_mem_lists s.2.1.2 i h)
  -- the data of a triple of `F`, in the form of `anchor_unique`
  have hdata : ∀ t ∈ F, t.2.2 ∈ labChoices x d I ∧ freshOf I t.2.2 = T ∧
      xp.1.1 = (t.2.2 i₀).1 ∧ lineOf xp.1.1 t.2.1.1 = xp.1.2 ∧ AnchorCond s t.1 t.2.1 t.2.2 := by
    intro t ht
    obtain ⟨hmem, hT, hxp, hcond⟩ := mem_filter.1 ht
    refine ⟨(mem_product.1 (mem_product.1 hmem).2).2, hT, congrArg Prod.fst hxp, ?_, hcond⟩
    rw [hxp]
  have hsel : ∀ t ∈ F, selOf I i₀ t.2.2 ∈ selections x d I i₀ := by
    intro t ht
    refine Fintype.mem_piFinset.2 fun j => ?_
    unfold selOf
    split_ifs with hj
    · exact mem_band_of_mem_labChoices (hdata t ht).1 j
    · exact mem_singleton_self 1
  have hselban : ∀ t ∈ F, ∀ j i h, selOf I i₀ t.2.2 j ≠ s.2.1.1 i h := by
    intro t ht j i h
    unfold selOf
    split_ifs
    · exact (hdata t ht).2.2.2.2.2.2.1 j i h
    · exact (hprime i h).one_lt.ne
  have hdet : ∀ t ∈ F, s.1.1.1 * t.2.1.1.2 - s.1.1.2 * t.2.1.1.1 =
      (omitProd s.2.1.1 (omitOf t.1) : ℤ) * ((∏ i, s.2.1.1 i (omitOf t.1 i) : ℕ) -
        (xp.1.1 * (∏ j, selOf I i₀ t.2.2 j) * ∏ j, T j : ℕ)) := by
    intro t ht
    obtain ⟨-, hT, hp, -, hcond⟩ := hdata t ht
    rw [hcond.2.2.2, rawN, prod_lab_eq hi₀I, hT, hp]
  -- every triple of `F` has the omission tuple and the labels of `t₀`
  have huniq : ∀ t ∈ F, omitOf t.1 = omitOf t₀.1 ∧ t.2.2 = t₀.2.2 := by
    intro t ht
    obtain ⟨hlab, hT, hp, hline, hcond⟩ := hdata t ht
    obtain ⟨hlab₀, hT₀, hp₀, hline₀, hcond₀⟩ := hdata t₀ ht₀
    have hps : xp.1.1 ∈ band x (d.a i₀) := hp ▸ mem_band_of_mem_labChoices hlab i₀
    obtain ⟨ho, hZ⟩ := anchor_unique hU hu hdisj s.2.1.2 s.1.2 hI hsep hps
      (fun i h => hp ▸ hcond.2.2.1 i₀ i h) (hsel t ht) (hsel t₀ ht₀) (hselban t ht)
      (hselban t₀ ht₀) hcond.1 hcond.2.1 hcond₀.1 hcond₀.2.1 t.2.1.2 t₀.2.1.2
      (hline.trans hline₀.symm) (hdet t ht) (hdet t₀ ht₀)
    refine ⟨ho, funext fun j => Prod.ext ?_ ?_⟩
    · by_cases hj : j = i₀
      · rw [hj, ← hp, ← hp₀]
      · by_cases hjI : j ∈ I
        · have := congrFun hZ j
          simp only [selOf, mem_erase, hj, ne_eq, not_false_eq_true, hjI, and_self,
            ↓reduceIte] at this
          exact this
        · have := congrFun (hT.trans hT₀.symm) j
          simp only [freshOf, hjI, ↓reduceIte] at this
          exact this
    · rw [Bool.eq_iff_iff, flag_iff_of_mem_labChoices hlab, flag_iff_of_mem_labChoices hlab₀]
  -- so `F` lies in a product of `(M!/M)^K` symmetrizations, `16` targets and one label
  have hsub : F ⊆ (univ.filter fun σ : Fin K → Equiv.Perm (Fin (padCount x + 1)) =>
      omitOf σ = omitOf t₀.1) ×ˢ ((univ.filter
        fun z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) =>
          s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = rawN s t₀.1 t₀.2.2) ×ˢ {t₀.2.2}) := by
    intro t ht
    obtain ⟨ho, hl⟩ := huniq t ht
    have hcond := (hdata t ht).2.2.2.2
    refine mem_product.2 ⟨mem_filter.2 ⟨mem_univ _, ho⟩, mem_product.2 ⟨mem_filter.2
      ⟨mem_univ _, ?_⟩, mem_singleton.2 hl⟩⟩
    rw [hcond.2.2.2]
    unfold rawN
    rw [ho, hl]
  have hz : ((univ.filter fun z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) =>
      s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = rawN s t₀.1 t₀.2.2).card : ℝ) ≤ 16 := by
    rw [natCast_card_filter]
    exact sum_target_le hU s _
  calc (F.card : ℝ) ≤ ((univ.filter fun σ : Fin K → Equiv.Perm (Fin (padCount x + 1)) =>
        omitOf σ = omitOf t₀.1).card : ℝ) *
        (((univ.filter fun z' : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) =>
          s.1.1.1 * z'.1.2 - s.1.1.2 * z'.1.1 = rawN s t₀.1 t₀.2.2).card : ℝ) * 1) := by
        have := card_le_card hsub
        rw [card_product, card_product, card_singleton] at this
        exact_mod_cast this
    _ ≤ (((padCount x + 1).factorial / (padCount x + 1) : ℝ)) ^ K * (16 * 1) := by
        rw [card_omitOf_eq]
        gcongr
    _ = 16 * (((padCount x + 1).factorial / (padCount x + 1) : ℝ)) ^ K := by ring

open scoped Classical in
/-- **The anchored triple sum**: over the triples `(σ, z', a)` of the piece with promoted groups
`I ≠ ∅` whose fresh draw passes the phase separation, the anchor weight
`S(x_{i_*}) ∏_{i ∉ I} ν(a_i) [anchor conditions]` sums to at most `B · 16 (M!/M)^K · 2^K`. Fix the
anchor particle (total mass `B`) and the fresh draw (total weight `2^K`), and count the rest by
`card_anchor_le`. -/
theorem sum_anchor_le (hU : 0 < d₀ * Y * d.Hm) (hu : 0 < u)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (s : ChainState x d Y d₀ u v r B)
    {I : Finset (Fin K)} (hI : I.Nonempty) :
    ∑ t ∈ (univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
        ((univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ labChoices x d I),
      (if freshOf I t.2.2 ∈ (freshDraws x d I).filter (fun T => Separated x d d₀ I (I.max' hI)
          (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 T) then
        (memAt x d s.2.2.1 ((t.2.2 (I.max' hI)).1, lineOf (t.2.2 (I.max' hI)).1 t.2.1.1) : ℝ) *
          (∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (t.2.2 i).1) *
          (if AnchorCond s t.1 t.2.1 t.2.2 then 1 else 0)
      else 0) ≤
      B * (16 * (((padCount x + 1).factorial / (padCount x + 1) : ℝ)) ^ K * 2 ^ K) := by
  classical
  have hν := primeWeight_nonneg_of hV hb (q := q) (N := N)
  set i₀ := I.max' hI with hi₀
  set G := (freshDraws x d I).filter (fun T => Separated x d d₀ I i₀
    (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 T) with hG
  set Ω := (univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
    ((univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ labChoices x d I) with hΩ
  set C₀ := 16 * (((padCount x + 1).factorial / (padCount x + 1) : ℝ)) ^ K with hC₀
  have hC0 : 0 ≤ C₀ := by positivity
  set νF : (Fin K → ℕ) → ℝ := fun T => ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (T i)
    with hνF
  have hνF0 : ∀ T, 0 ≤ νF T := fun T => prod_nonneg fun i _ => hν _
  set P : Particle x d → (Fin K → Equiv.Perm (Fin (padCount x + 1))) ×
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) × (Fin K → ℕ × Bool) → Prop :=
    fun xp t => freshOf I t.2.2 ∈ G ∧
    xp.1 = ((t.2.2 i₀).1, lineOf (t.2.2 i₀).1 t.2.1.1) ∧ AnchorCond s t.1 t.2.1 t.2.2 with hP
  -- for a fixed anchor particle, the fresh draws and the count
  have hxp : ∀ xp : Particle x d, ∑ t ∈ Ω, (if P xp t then νF (freshOf I t.2.2) else 0) ≤
      C₀ * 2 ^ K := by
    intro xp
    rw [← sum_filter, ← sum_fiberwise_of_maps_to (g := fun t => freshOf I t.2.2) (t := G)
      (fun t ht => (mem_filter.1 ht).2.1)]
    calc ∑ T ∈ G, ∑ t ∈ (Ω.filter (P xp)).filter (fun t => freshOf I t.2.2 = T),
          νF (freshOf I t.2.2)
        = ∑ T ∈ G, ((Ω.filter (P xp)).filter (fun t => freshOf I t.2.2 = T)).card * νF T := by
          refine sum_congr rfl fun T _ => ?_
          rw [sum_congr rfl (g := fun _ => νF T) fun t ht => by rw [(mem_filter.1 ht).2],
            sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ G, C₀ * νF T := by
          refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_right ?_ (hνF0 T)
          refine le_trans ?_ (card_anchor_le hU hu hdisj s hI (mem_filter.1 hT).2 xp)
          refine Nat.cast_le.2 (card_le_card fun t ht => ?_)
          obtain ⟨ht, hTt⟩ := mem_filter.1 ht
          obtain ⟨htΩ, -, h₁, h₂⟩ := mem_filter.1 ht
          exact mem_filter.2 ⟨htΩ, hTt, h₁, h₂⟩
      _ = C₀ * ∑ T ∈ G, νF T := (mul_sum _ _ _).symm
      _ ≤ C₀ * 2 ^ K := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun T _ _ => hνF0 T).trans
            (sum_freshDraws_le hdisj hV hb I)
  calc ∑ t ∈ Ω, (if freshOf I t.2.2 ∈ G then
        (memAt x d s.2.2.1 ((t.2.2 i₀).1, lineOf (t.2.2 i₀).1 t.2.1.1) : ℝ) *
          (∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (t.2.2 i).1) *
          (if AnchorCond s t.1 t.2.1 t.2.2 then 1 else 0) else 0)
      = ∑ t ∈ Ω, ∑ xp : Particle x d, (s.2.2.1 xp : ℝ) *
          (if P xp t then νF (freshOf I t.2.2) else 0) := by
        refine sum_congr rfl fun t _ => ?_
        rw [← sum_ite_eq_memAt]
        -- `∏_{i ∉ I} ν(a_i)` is the weight of the fresh draw
        have hνt : ∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (t.2.2 i).1 =
            νF (freshOf I t.2.2) :=
          prod_congr rfl fun i hi => by
            simp only [freshOf, (mem_filter.1 hi).2, ↓reduceIte]
        rw [hνt, sum_mul, sum_mul]
        by_cases hG' : freshOf I t.2.2 ∈ G
        · rw [ite_eq_left hG']
          refine sum_congr rfl fun xp _ => ?_
          simp only [hP, hG', true_and]
          by_cases h₁ : xp.1 = ((t.2.2 i₀).1, lineOf (t.2.2 i₀).1 t.2.1.1) <;>
            by_cases h₂ : AnchorCond s t.1 t.2.1 t.2.2 <;> simp [h₁, h₂]
        · rw [ite_eq_right hG']
          refine (sum_eq_zero fun xp _ => ?_).symm
          simp [hP, hG']
    _ = ∑ xp : Particle x d, (s.2.2.1 xp : ℝ) *
          ∑ t ∈ Ω, (if P xp t then νF (freshOf I t.2.2) else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun xp _ => (mul_sum _ _ _).symm
    _ ≤ ∑ xp : Particle x d, (s.2.2.1 xp : ℝ) * (C₀ * 2 ^ K) :=
        sum_le_sum fun xp _ => mul_le_mul_of_nonneg_left (hxp xp) (Nat.cast_nonneg _)
    _ = (memSize s.2.2.1 : ℝ) * (C₀ * 2 ^ K) := by
        rw [← sum_mul, memSize, Nat.cast_sum]
    _ ≤ B * (C₀ * 2 ^ K) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast mem_memStates.1 s.2.2.2

open scoped Classical in
/-- **The anchored row** (PD §4, dirty raw edges, `I ≠ ∅`): the raw coefficients of the piece
`(S, I)` whose fresh draw passes the phase separation sum to at most `16 (4 C_ρ)^K B / M^K`. -/
theorem sum_rawAmp_good_le (hq : 0 < q) (hq₁ : q < 1) (hU : 0 < d₀ * Y * d.Hm) (hu : 0 < u)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (s : ChainState x d Y d₀ u v r B)
    (S : Finset (Fin K)) {I : Finset (Fin K)} (hI : I.Nonempty) :
    ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter (fun c => freshOf I c.2.2.2.1 ∈
        (freshDraws x d I).filter (fun T => Separated x d d₀ I (I.max' hI)
          (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 T)), rawAmp q N s c ≤
      16 * (4 * dampConst q) ^ K * B / ((padCount x + 1 : ℕ) : ℝ) ^ K := by
  classical
  have hν := primeWeight_nonneg_of hV hb (q := q) (N := N)
  set i₀ := I.max' hI with hi₀
  set G := (freshDraws x d I).filter (fun T => Separated x d d₀ I i₀
    (tau r (complement s.1.1) / tau r s.1.1) s.2.1.1 T) with hG
  set r₀ := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 with hr₀
  set κ := r₀ * (2 * dampConst q) ^ K with hκ
  have hκ0 : 0 ≤ κ := by have := one_le_dampConst hq hq₁; positivity
  set H : (Fin K → Equiv.Perm (Fin (padCount x + 1))) →
      ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → (Fin K → ℕ × Bool) → ℝ :=
    fun σ z' lab => if freshOf I lab ∈ G then
      (memAt x d s.2.2.1 ((lab i₀).1, lineOf (lab i₀).1 z'.1) : ℝ) *
        (∏ i ∈ univ.filter (· ∉ I), primeWeight q x d N (lab i).1) *
        (if AnchorCond s σ z' lab then 1 else 0) else 0 with hH
  have hA := sum_anchor_le hU hu hdisj hV hb s hI (q := q) (N := N)
  calc ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter (fun c => freshOf I c.2.2.2.1 ∈ G),
        rawAmp q N s c
      ≤ ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter (fun c => freshOf I c.2.2.2.1 ∈ G),
          κ * H c.1 c.2.2.1 c.2.2.2.1 := by
        refine sum_le_sum fun c hc => ?_
        obtain ⟨hc, hcG⟩ := mem_filter.1 hc
        refine (rawAmp_le_anchor hq hq₁ hdisj hV hν s hI hc).trans ?_
        simp only [hH, hcG, ↓reduceIte, hκ]
        have hm := (Nat.cast_nonneg (α := ℝ) (memAt x d s.2.2.1 (edgePromoted c i₀)))
        have hF := prod_nonneg fun i (_ : i ∈ univ.filter (· ∉ I)) => hν (c.2.2.2.1 i).1
        split_ifs with h₁ h₂ h₂
        · exact le_of_eq (by simp only [edgePromoted]; ring)
        · exact absurd (anchorCond_of_valid h₁) h₂
        · rw [mul_zero]
          exact mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hm hF) zero_le_one)
        · simp
    _ = ∑ σ, ∑ z', ∑ lab ∈ labChoices x d I,
          ∑ _σ' : Fin K → Equiv.Perm (Fin (padCount x + 1)), κ * H σ z' lab := by
        rw [sum_filter, sum_rawChoices]
        refine sum_congr rfl fun σ _ => sum_congr rfl fun z' _ => sum_congr rfl fun lab _ =>
          sum_congr rfl fun σ' _ => ?_
        by_cases hG' : freshOf I lab ∈ G
        · rw [ite_eq_left hG']
        · rw [ite_eq_right hG']
          simp [hH, hG']
    _ = (((padCount x + 1).factorial ^ K : ℕ) : ℝ) * κ *
          ∑ t ∈ (univ : Finset (Fin K → Equiv.Perm (Fin (padCount x + 1)))) ×ˢ
            ((univ : Finset ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)) ×ˢ labChoices x d I),
            H t.1 t.2.1 t.2.2 := by
        simp only [sum_const, card_univ, nsmul_eq_mul, card_edgeSymm, sum_product, mul_sum]
        refine sum_congr rfl fun σ _ => sum_congr rfl fun z' _ => sum_congr rfl fun lab _ => ?_
        ring
    _ ≤ (((padCount x + 1).factorial ^ K : ℕ) : ℝ) * κ *
          (B * (16 * (((padCount x + 1).factorial / (padCount x + 1) : ℝ)) ^ K * 2 ^ K)) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = 16 * (4 * dampConst q) ^ K * B / ((padCount x + 1 : ℕ) : ℝ) ^ K := by
        have hf : ((padCount x + 1).factorial : ℝ) ≠ 0 := by positivity
        have hM : ((padCount x : ℝ) + 1) ≠ 0 := by positivity
        rw [hκ, hr₀, div_pow, show (4 * dampConst q) ^ K = 2 ^ K * (2 * dampConst q) ^ K by
          rw [← mul_pow]; ring]
        push_cast
        field_simp

end Anchored

/-! ### The rows -/

section Rows

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The fresh draw of an edge choice of the piece `(S, I)` is a fresh draw outside `I`. -/
theorem freshOf_mem_freshDraws {S I : Finset (Fin K)} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ rawChoices x d Y d₀ u v r S I) : freshOf I c.2.2.2.1 ∈ freshDraws x d I := by
  refine Fintype.mem_piFinset.2 fun i => ?_
  unfold freshOf
  split_ifs
  · exact mem_singleton_self 1
  · exact mem_band_lab (mem_filter.1 hc).1 i

/-- **The row without promotions** (PD §4, dirty raw edges, `I = ∅`): the raw coefficients of
the piece `(S, ∅)` sum to at most `16 · 2^K`, independently of `B`. -/
theorem sum_rawAmp_le_of_empty (hq : 0 < q) (hq₁ : q < 1) (hU : 0 < d₀ * Y * d.Hm)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (s : ChainState x d Y d₀ u v r B)
    (S : Finset (Fin K)) :
    ∑ c ∈ rawChoices x d Y d₀ u v r S ∅, rawAmp q N s c ≤ 16 * 2 ^ K := by
  have h := sum_rawAmp_fresh_le hq hq₁ hU hdisj hV hb s S ∅ (freshDraws x d ∅)
  rw [filter_true_of_mem fun c hc => freshOf_mem_freshDraws hc, card_empty, pow_zero,
    mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (sum_freshDraws_le hdisj hV hb ∅) (by norm_num))

/-- The raw coefficients are nonnegative. -/
theorem rawAmp_nonneg (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) : 0 ≤ rawAmp q N s c := by
  have hρ0 := (pendingWeight_pos hq).le
  unfold rawAmp
  split_ifs
  · refine mul_nonneg (by positivity) (prod_nonneg fun i _ => ?_)
    split_ifs
    · exact div_nonneg (sum_nonneg fun xp _ => by split_ifs <;> positivity)
        (by rw [primeMass_eq_of_mem_band hdisj (mem_band_lab hc i)]; linarith [hV i])
    · exact hν _
  · exact le_rfl

/-- **The row with promotions** (PD `mem:epsilon`, `I ≠ ∅`): the raw coefficients of the piece
`(S, I)` sum to at most `16 (4 C_ρ)^K B / M^K + 16 (2B + 1)^K 2^K exp(-L^{a_{i_*}}/4)`. At a
source failing the second good-state test the row vanishes; otherwise split the fresh draws by
the phase separation (`sum_rawAmp_good_le`, `sum_rawAmp_fresh_le` and `sum_bad_le`). -/
theorem sum_rawAmp_le_of_nonempty (hq : 0 < q) (hq₁ : q < 1) (hU : 0 < d₀ * Y * d.Hm)
    (hu : 0 < u) (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (s : ChainState x d Y d₀ u v r B)
    (S : Finset (Fin K)) {I : Finset (Fin K)} (hI : I.Nonempty) :
    ∑ c ∈ rawChoices x d Y d₀ u v r S I, rawAmp q N s c ≤
      16 * (4 * dampConst q) ^ K * B / ((padCount x + 1 : ℕ) : ℝ) ^ K +
        16 * (2 * B + 1) ^ K * (2 ^ K * Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)) := by
  classical
  have hν := primeWeight_nonneg_of hV hb (q := q) (N := N)
  have hdC := one_le_dampConst hq hq₁
  have hR0 : 0 ≤ 16 * (4 * dampConst q) ^ K * B / ((padCount x + 1 : ℕ) : ℝ) ^ K +
      16 * (2 * B + 1) ^ K * (2 ^ K * Real.exp (-Real.log x ^ d.a (I.max' hI) / 4)) := by
    positivity
  set rr := tau r (complement s.1.1) / tau r s.1.1 with hrr
  by_cases hgood : GoodSecond x d d₀ rr s.2.1.1
  · set G := (freshDraws x d I).filter (fun T => Separated x d d₀ I (I.max' hI) rr s.2.1.1 T)
      with hG
    set Bad := (freshDraws x d I).filter (fun T => ¬ Separated x d d₀ I (I.max' hI) rr s.2.1.1 T)
      with hBad
    rw [← sum_filter_add_sum_filter_not _ (fun c => freshOf I c.2.2.2.1 ∈ G)]
    refine add_le_add (sum_rawAmp_good_le hq hq₁ hU hu hdisj hV hb s S hI) ?_
    have hset : (rawChoices x d Y d₀ u v r S I).filter (fun c => ¬ freshOf I c.2.2.2.1 ∈ G) =
        (rawChoices x d Y d₀ u v r S I).filter (fun c => freshOf I c.2.2.2.1 ∈ Bad) :=
      filter_congr fun c hc => by
        simp only [hG, hBad, mem_filter, freshOf_mem_freshDraws hc, true_and]
    rw [hset]
    refine (sum_rawAmp_fresh_le hq hq₁ hU hdisj hV hb s S I Bad).trans ?_
    have hpow : (2 * (B : ℝ)) ^ I.card ≤ (2 * B + 1) ^ K :=
      (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)])
          ((card_le_univ I).trans (by rw [Fintype.card_fin])))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num))
      (sum_bad_le hdisj hV hb hgood hI)
      (sum_nonneg fun T _ => prod_nonneg fun i _ => hν _) (by positivity)
  · -- a source failing the second good-state test has no admissible edge
    refine le_trans (le_of_eq (sum_eq_zero fun c _ => ?_)) hR0
    unfold rawAmp
    exact ite_eq_right fun h => absurd h.1.2.2.2.2.2.1.2 hgood

end Rows

end Erdos408.OneSided
