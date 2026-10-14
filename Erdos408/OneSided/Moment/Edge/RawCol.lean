import Erdos408.OneSided.Moment.Edge.RawRow

/-!
# The columns of the dirty raw edges by reversal

PD §4 "Dirty raw edges": reversal exchanges the stored groups `S` and the promoted groups `I`
(`mem:edge-factorial`), changes only bounded `V_i` factors, and retains both good-state tests
and the ban. So the weighted column of the piece `(S, I)` at an output `s'` is at most `2^K μ(s')`
times the row of the piece `(I, S)` at `s'`.

* `revChoice`: the reversed choice of an edge `s → s'`. Its source symmetrization is `σ'^{-1}`,
  its stored groups are the promoted groups, its target is the source position, its new labels
  are the unshared source primes `b_i` (promoted exactly on `S`), and its target symmetrization
  is `σ^{-1}`.
* `edgeValid_revChoice`, `chainEdgeOut_revChoice`: the reversed choice is admissible and leads
  back to `s`; it solves the reversed raw determinant equation.
* `measure_mul_rawAmp_le`: the adjoint calculation `μ(s) rawAmp(s, c) ≤ 2^K μ(s') rawAmp(s',
  c^rev)`.
* `sum_col_rawAmp_le`: the column bound.
-/

noncomputable section

namespace Erdos408.OneSided

open Finset Real

variable {K : ℕ}

section Reversal

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The reversed edge choice: the source symmetrization `σ'^{-1}`, the promoted groups as
stored groups, the source position as target, the unshared source primes as new labels
(promoted exactly on the stored groups), and the target symmetrization `σ^{-1}`. -/
def revChoice (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) :
    EdgeChoice x d Y d₀ u v r :=
  (fun i => (c.2.2.2.2 i).symm, univ.filter (fun i => (c.2.2.2.1 i).2 = true), s.1,
    fun i => (edgeSrc s c i (Fin.last _), decide (i ∈ c.2.1)), fun i => (c.1 i).symm)

/-- The output of an admissible edge choice. -/
private theorem chainEdgeOut_of_valid' {s : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (hv : EdgeValid x d Y d₀ u v r B s c) :
    chainEdgeOut x d Y d₀ u v r B s c =
      (c.2.2.1, ⟨edgeTgt s c, hv.1⟩, ⟨edgeMem s c, hv.2.2.2.2.2.2.2.2.2⟩) := by
  unfold chainEdgeOut
  rw [dite_eq_left hv]

/-- The target lists after undoing `σ'`: the new label in the last slot, and the source lists
reordered by `σ` elsewhere. -/
private theorem edgeTgt_symm' (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r)
    (i : Fin K) (h : Fin (padCount x + 1)) :
    edgeTgt s c i ((c.2.2.2.2 i).symm h) =
      if h = Fin.last _ then (c.2.2.2.1 i).1 else edgeSrc s c i h := by
  simp only [edgeTgt, Equiv.apply_symm_apply]

/-- The source lists of the reversed choice: the target lists reordered by `σ'^{-1}`, which
are the source lists reordered by `σ` with the new label in the last slot. -/
theorem edgeSrc_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₂ : s'.2.1.1 = edgeTgt s c) (i : Fin K) (h : Fin (padCount x + 1)) :
    edgeSrc s' (revChoice s c) i h =
      if h = Fin.last _ then (c.2.2.2.1 i).1 else edgeSrc s c i h := by
  change s'.2.1.1 i ((c.2.2.2.2 i).symm h) = _
  rw [h₂, edgeTgt_symm']

/-- The target lists of the reversed choice are the source lists. -/
theorem edgeTgt_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₂ : s'.2.1.1 = edgeTgt s c) : edgeTgt s' (revChoice s c) = s.2.1.1 := by
  funext i h
  change (if (c.1 i).symm h = Fin.last _ then edgeSrc s c i (Fin.last _)
    else edgeSrc s' (revChoice s c) i ((c.1 i).symm h)) = _
  rw [edgeSrc_revChoice h₂]
  split_ifs with hh
  · change s.2.1.1 i (c.1 i (Fin.last _)) = _
    rw [← hh, Equiv.apply_symm_apply]
  · change s.2.1.1 i (c.1 i ((c.1 i).symm h)) = _
    rw [Equiv.apply_symm_apply]

/-- The reversed choice has the same pad product. -/
theorem edgePad_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₂ : s'.2.1.1 = edgeTgt s c) : edgePad s' (revChoice s c) = edgePad s c := by
  unfold edgePad
  simp only [edgeSrc_revChoice h₂, Fin.castSucc_ne_last, ↓reduceIte]

/-- The unshared source primes of the reversed choice are the new labels. -/
theorem prod_edgeSrc_revChoice {s s' : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (h₂ : s'.2.1.1 = edgeTgt s c) :
    ∏ i, edgeSrc s' (revChoice s c) i (Fin.last _) = ∏ i, (c.2.2.2.1 i).1 := by
  simp only [edgeSrc_revChoice h₂, ↓reduceIte]

/-- The reversed determinant is the negated determinant. -/
theorem edgeDet_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₁ : s'.1 = c.2.2.1) : edgeDet s' (revChoice s c) = -edgeDet s c := by
  unfold edgeDet
  change s'.1.1.1 * s.1.1.2 - s'.1.1.2 * s.1.1.1 = _
  rw [h₁]
  ring

/-- The particle promoted by the reversed choice is the particle stored by the edge. -/
theorem edgePromoted_revChoice (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) :
    edgePromoted (revChoice s c) i = edgeStored s c i := rfl

/-- The particle stored by the reversed choice is the particle promoted by the edge. -/
theorem edgeStored_revChoice {s s' : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c)
    (i : Fin K) : edgeStored s' (revChoice s c) i = edgePromoted c i := by
  unfold edgeStored edgePromoted
  rw [edgeSrc_revChoice h₂, ite_eq_left rfl, h₁]

/-- The unshared source prime of each group lies in its band. -/
private theorem mem_band_edgeSrc' (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) (i : Fin K) (h : Fin (padCount x + 1)) :
    edgeSrc s c i h ∈ band x (d.a i) :=
  mem_band_of_mem_lists s.2.1.2 i _

/-- With disjoint bands, each particle is promoted by at most one group. -/
private theorem card_promoted_le_one'
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {c : EdgeChoice x d Y d₀ u v r} (hc : c ∈ edgeChoices x d Y d₀ u v r) (xp : Particle x d) :
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card ≤ 1 :=
  card_le_one.2 fun i hi j hj => by
    by_contra hij
    have hij' := congrArg Prod.fst ((mem_filter.1 hi).2.2.trans (mem_filter.1 hj).2.2.symm)
    change (c.2.2.2.1 i).1 = (c.2.2.2.1 j).1 at hij'
    exact disjoint_left.1 (hdisj i j hij) (mem_band_lab hc i) (hij' ▸ mem_band_lab hc j)

/-- With disjoint bands, each particle is stored by at most one group. -/
private theorem card_stored_le_one'
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) (xp : Particle x d) :
    (c.2.1.filter fun i => edgeStored s c i = xp.1).card ≤ 1 :=
  card_le_one.2 fun i hi j hj => by
    by_contra hij
    have hij' := congrArg Prod.fst ((mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm)
    change edgeSrc s c i (Fin.last _) = edgeSrc s c j (Fin.last _) at hij'
    exact disjoint_left.1 (hdisj i j hij) (mem_band_edgeSrc' s c i _)
      (hij' ▸ mem_band_edgeSrc' s c j _)

/-- With disjoint bands, an admissible edge promotes each particle at most as often as it is
pending. -/
private theorem card_promoted_le'
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (xp : Particle x d) :
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card ≤ s.2.2.1 xp := by
  classical
  rcases Nat.eq_zero_or_pos
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · obtain ⟨i, hi⟩ := card_pos.1 hpos
    obtain ⟨hf, he⟩ := (mem_filter.1 hi).2
    obtain ⟨yp, hyp, hS1⟩ := hv.2.2.2.2.2.2.2.1 i hf
    have hyx : yp = xp := Subtype.ext (hyp.trans he)
    rw [← hyx]
    exact (card_promoted_le_one' hdisj hc yp).trans hS1

/-- The memory after the reversed choice is the source memory: the reversed edge stores the
promoted particles back and promotes the stored particles. -/
theorem edgeMem_revChoice (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h₃ : s'.2.2.1 = edgeMem s c) :
    edgeMem s' (revChoice s c) = s.2.2.1 := by
  classical
  funext xp
  have hP := card_promoted_le' hdisj hc hv xp
  -- the reversed promotions are the stored groups, and the reversed stores the promotions
  have hQ : (univ.filter fun i => ((revChoice s c).2.2.2.1 i).2 ∧
      edgePromoted (revChoice s c) i = xp.1).card =
        (c.2.1.filter fun i => edgeStored s c i = xp.1).card := by
    congr 1
    ext i
    rw [mem_filter, mem_filter, edgePromoted_revChoice]
    simp only [mem_univ, true_and]
    change (decide (i ∈ c.2.1) = true ∧ _) ↔ _
    rw [decide_eq_true_iff]
  have hP' : ((revChoice s c).2.1.filter fun i => edgeStored s' (revChoice s c) i = xp.1).card =
      (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card := by
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, edgeStored_revChoice h₁ h₂]
    change (i ∈ univ.filter (fun i => (c.2.2.2.1 i).2 = true) ∧ _) ↔ _
    rw [mem_filter]
    simp only [mem_univ, true_and]
  unfold edgeMem
  rw [hQ, hP', h₃]
  unfold edgeMem
  omega

/-- **The reversed choice is admissible**: its target lists are the source lists, the ban
holds since the source lists are distinct and the new labels avoid them, the pad product is
the same, both good-state tests swap, the stored particles are pending after the edge, and the
promoted particles are particles. -/
theorem edgeValid_revChoice
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h₃ : s'.2.2.1 = edgeMem s c) :
    EdgeValid x d Y d₀ u v r B s' (revChoice s c) := by
  classical
  obtain ⟨-, hban, hD₁, hD₂, hdvd, hgood, hgood', hprom, hstore, -⟩ := id hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [edgeTgt_revChoice h₂]
    exact s.2.1.2
  · -- the ban: `b_i` is no target label
    intro i i' h
    change edgeSrc s c i (Fin.last _) ≠ s'.2.1.1 i' h
    rw [h₂]
    unfold edgeTgt
    dsimp only
    split_ifs with hh
    · exact (hban i' i _).symm
    · intro heq
      change s.2.1.1 i (c.1 i (Fin.last _)) = s.2.1.1 i' (c.1 i' (c.2.2.2.2 i' h)) at heq
      have hii : i = i' := by
        by_contra hii
        exact disjoint_left.1 (hdisj i i' hii) (mem_band_of_mem_lists s.2.1.2 i _)
          (heq ▸ mem_band_of_mem_lists s.2.1.2 i' _)
      subst hii
      exact hh ((c.1 i).injective (injective_of_mem_lists s.2.1.2 i heq)).symm
  · rw [edgePad_revChoice h₂]
    exact hD₁
  · rw [edgePad_revChoice h₂]
    exact hD₂
  · rw [edgePad_revChoice h₂, edgeDet_revChoice h₁]
    exact dvd_neg.2 hdvd
  · rw [h₁, h₂]
    exact hgood'
  · rw [edgeTgt_revChoice h₂]
    exact hgood
  · -- the stored particles are pending after the edge
    intro i hi
    have hiS : i ∈ c.2.1 := by simpa [revChoice] using hi
    refine ⟨⟨edgeStored s c i, hstore i hiS⟩, rfl, ?_⟩
    rw [h₃]
    unfold edgeMem
    have : 1 ≤ (c.2.1.filter fun j =>
        edgeStored s c j = (⟨edgeStored s c i, hstore i hiS⟩ : Particle x d).1).card :=
      card_pos.2 ⟨i, mem_filter.2 ⟨hiS, rfl⟩⟩
    omega
  · -- the promoted particles are particles
    intro i hi
    have hiI : (c.2.2.2.1 i).2 = true := (mem_filter.1 hi).2
    obtain ⟨xp, hxp, -⟩ := hprom i hiI
    rw [edgeStored_revChoice h₁ h₂, ← hxp]
    exact xp.2
  · rw [edgeMem_revChoice hdisj hc hv h₁ h₂ h₃]
    exact s.2.2.2

/-- The reversed choice leads back to the source. -/
theorem chainEdgeOut_revChoice
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c)
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h₃ : s'.2.2.1 = edgeMem s c) :
    chainEdgeOut x d Y d₀ u v r B s' (revChoice s c) = s := by
  rw [chainEdgeOut_of_valid' (edgeValid_revChoice hdisj hc hv h₁ h₂ h₃)]
  refine Prod.ext rfl (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · exact edgeTgt_revChoice h₂
  · exact edgeMem_revChoice hdisj hc hv h₁ h₂ h₃

/-- The reversed choice solves the reversed raw determinant equation. -/
theorem rawDet_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₁ : s'.1 = c.2.2.1) (h₂ : s'.2.1.1 = edgeTgt s c) (h : RawDet s c) :
    RawDet s' (revChoice s c) := by
  unfold RawDet at h ⊢
  rw [edgeDet_revChoice h₁, edgePad_revChoice h₂, prod_edgeSrc_revChoice h₂]
  change -edgeDet s c = (edgePad s c : ℤ) * (((∏ i, (c.2.2.2.1 i).1 : ℕ) : ℤ) -
    ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) : ℤ))
  linear_combination -h

/-- Reversal exchanges the stored and the promoted groups. -/
theorem revChoice_mem_rawChoices {s : ChainState x d Y d₀ u v r B}
    {c : EdgeChoice x d Y d₀ u v r} {S I : Finset (Fin K)}
    (hc : c ∈ rawChoices x d Y d₀ u v r S I) :
    revChoice s c ∈ rawChoices x d Y d₀ u v r I S := by
  obtain ⟨-, hS, hI⟩ := mem_filter.1 hc
  refine mem_filter.2 ⟨?_, hI, ?_⟩
  · simp only [edgeChoices, mem_product, mem_univ, true_and, and_true]
    exact Fintype.mem_piFinset.2 fun i => mem_product.2
      ⟨mem_band_edgeSrc' s c i _, mem_univ _⟩
  · ext i
    rw [mem_filter, ← hS]
    simp only [mem_univ, true_and]
    change decide (i ∈ c.2.1) = true ↔ _
    rw [decide_eq_true_iff]

/-! ### The adjoint calculation -/

/-- The per-particle identity behind the memory weight: if `S' = S - P + Q` with `P, Q ≤ 1`
and `P ≤ S`, then `y^S/S! · S^P · y^Q = y^{S'}/S'! · y^P · S'^Q`. -/
private theorem pow_div_factorial_mul_eq' {a P Q : ℕ} (y : ℝ) (hP : P ≤ 1) (hQ : Q ≤ 1)
    (hPa : P ≤ a) :
    y ^ a / (a.factorial : ℝ) * (a : ℝ) ^ P * y ^ Q =
      y ^ (a - P + Q) / ((a - P + Q).factorial : ℝ) * y ^ P * ((a - P + Q : ℕ) : ℝ) ^ Q := by
  interval_cases P <;> interval_cases Q
  · simp
  · rw [Nat.sub_zero, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.add_zero]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring

/-- **The memory weight under an edge**: removing `P ≤ 1` and adding `Q ≤ 1` particles at each
point, `w(S) ∏ S^P ∏ ν^Q = w(S') ∏ ν^P ∏ S'^Q` for `S' = S - P + Q`. -/
private theorem memWeight_mul_eq' {X : Type*} [Fintype X] [DecidableEq X] (ν : X → ℝ)
    (S P Q : X → ℕ) (hP : ∀ x, P x ≤ 1) (hQ : ∀ x, Q x ≤ 1) (hPS : ∀ x, P x ≤ S x) :
    memWeight ν S * (∏ x, (S x : ℝ) ^ P x) * ∏ x, ν x ^ Q x =
      memWeight ν (fun x => S x - P x + Q x) * (∏ x, ν x ^ P x) *
        ∏ x, ((S x - P x + Q x : ℕ) : ℝ) ^ Q x := by
  unfold memWeight
  simp only [← prod_mul_distrib]
  exact prod_congr rfl fun x _ => pow_div_factorial_mul_eq' (ν x) (hP x) (hQ x) (hPS x)

/-- A product over the points `y` of `f(y)` to the number of indices `i ∈ F` with `g(i) = y` is
the product over `i ∈ F` of `f` over the fiber of `g(i)`. -/
private theorem prod_pow_card_filter' {α ι M : Type*} [DecidableEq α] [CommMonoid M]
    {T : Finset α} (F : Finset ι) (g : ι → α) (f : ↥T → M) :
    ∏ y : ↥T, f y ^ (F.filter fun i => g i = y.1).card =
      ∏ i ∈ F, ∏ y : ↥T with y.1 = g i, f y := by
  calc ∏ y : ↥T, f y ^ (F.filter fun i => g i = y.1).card
      = ∏ y : ↥T, ∏ i ∈ F, if g i = y.1 then f y else 1 :=
        prod_congr rfl fun y _ => by rw [← prod_const, prod_filter]
    _ = ∏ i ∈ F, ∏ y : ↥T, if g i = y.1 then f y else 1 := prod_comm
    _ = ∏ i ∈ F, ∏ y : ↥T with y.1 = g i, f y :=
        prod_congr rfl fun i _ => by
          rw [prod_filter]
          exact prod_congr rfl fun y _ => by simp only [eq_comm]

/-- The fiber of a point of a subtype is a singleton. -/
private theorem filter_val_eq' {α : Type*} [DecidableEq α] {T : Finset α} {y : α} (z : ↥T)
    (hz : z.1 = y) : (univ.filter fun w : ↥T => w.1 = y) = {z} := by
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_singleton, ← hz, Subtype.ext_iff]

/-- **The list weights under an edge**: `∏ f(act) ∏_i f(a_i) = ∏ f(act') ∏_i f(b_i)`, since the
source and target lists share their pads and differ by `b_i ↔ a_i`. -/
private theorem prod_edgeTgt_mul' (f : ℕ → ℝ) (s : ChainState x d Y d₀ u v r B)
    (c : EdgeChoice x d Y d₀ u v r) :
    (∏ i, ∏ h, f (s.2.1.1 i h)) * ∏ i, f (c.2.2.2.1 i).1 =
      (∏ i, ∏ h, f (edgeTgt s c i h)) * ∏ i, f (edgeSrc s c i (Fin.last _)) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  have h₁ : ∏ h, f (s.2.1.1 i h) =
      (∏ h : Fin (padCount x), f (edgeSrc s c i h.castSucc)) * f (edgeSrc s c i (Fin.last _)) := by
    rw [← Fin.prod_univ_castSucc (fun h => f (edgeSrc s c i h))]
    exact (Equiv.prod_comp (c.1 i) (fun h => f (s.2.1.1 i h))).symm
  have h₂ : ∏ h, f (edgeTgt s c i h) =
      (∏ h : Fin (padCount x), f (edgeSrc s c i h.castSucc)) * f (c.2.2.2.1 i).1 := by
    rw [← Equiv.prod_comp (c.2.2.2.2 i).symm, Fin.prod_univ_castSucc]
    simp only [edgeTgt_symm', Fin.castSucc_ne_last, ↓reduceIte]
  rw [h₁, h₂]
  ring

/-- **The adjoint calculation** (PD `mem:edge-factorial`): for an admissible edge `s → s'`,
`μ(s) ∏_i w_i ≤ 2^K μ(s') ∏_i w_i^{rev}`, where the reversed weights are `S'(y_i)/V(b_i)` for a
stored particle `y_i` and `ν(b_i)` otherwise. Removing a promoted particle `x_i` from `S` trades
its weight `S(x_i)` for `ν(a_i)`, which cancels the target label and leaves `1/V(a_i) ≤ 2`;
storing `b_i` trades the source label `ν(b_i)` for the multiplicity `S'(y_i) ≤ S'(y_i)/V(b_i)`. -/
theorem measure_mul_rawWeight_le
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p)
    {s : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (hv : EdgeValid x d Y d₀ u v r B s c) :
    (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
        rawWeight q N s c ≤
      2 ^ K * ((∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
        ∏ i, if i ∈ c.2.1 then
          (memAt x d (edgeMem s c) (edgeStored s c i) : ℝ) /
            primeMass x d (edgeSrc s c i (Fin.last _))
        else primeWeight q x d N (edgeSrc s c i (Fin.last _))) := by
  classical
  set ν := primeWeight q x d N with hνdef
  set S := s.2.2.1 with hS
  set S' := edgeMem s c with hS'
  set P : Particle x d → ℕ := fun xp =>
    (univ.filter fun i => (c.2.2.2.1 i).2 ∧ edgePromoted c i = xp.1).card with hPdef
  set Q : Particle x d → ℕ := fun xp =>
    (c.2.1.filter fun i => edgeStored s c i = xp.1).card with hQdef
  have hprom := hv.2.2.2.2.2.2.2.1
  have hstore := hv.2.2.2.2.2.2.2.2.1
  have hVa : ∀ i, 1 / 2 ≤ primeMass x d (c.2.2.2.1 i).1 := fun i => by
    rw [primeMass_eq_of_mem_band hdisj (mem_band_lab hc i)]
    exact (hV i).1
  have hVb : ∀ i, 1 / 2 ≤ primeMass x d (edgeSrc s c i (Fin.last _)) ∧
      primeMass x d (edgeSrc s c i (Fin.last _)) ≤ 1 := fun i => by
    rw [primeMass_eq_of_mem_band hdisj (mem_band_edgeSrc' s c i _)]
    exact hV i
  -- each particle is promoted and stored at most once, and only if pending
  have hP1 : ∀ xp, P xp ≤ 1 := card_promoted_le_one' hdisj hc
  have hQ1 : ∀ xp, Q xp ≤ 1 := card_stored_le_one' hdisj s c
  have hPS : ∀ xp, P xp ≤ S xp := card_promoted_le' hdisj hc hv
  -- the products over the particles as products over the groups
  have hfibP : ∀ f : Particle x d → ℝ, ∏ xp, f xp ^ P xp =
      ∏ i, if (c.2.2.2.1 i).2 = true then
        ∏ xp : Particle x d with xp.1 = edgePromoted c i, f xp else 1 := by
    intro f
    have hP' : ∀ xp, P xp = ((univ.filter fun i => (c.2.2.2.1 i).2 = true).filter
        fun i => edgePromoted c i = xp.1).card := fun xp => by rw [filter_filter]
    rw [prod_congr rfl fun xp _ => by rw [hP' xp], prod_pow_card_filter', prod_filter]
  have hii : ∏ xp, (S xp : ℝ) ^ P xp = ∏ i, if (c.2.2.2.1 i).2 = true then
      (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (S xp : ℝ) else 0) else 1 := by
    rw [hfibP]
    refine prod_congr rfl fun i _ => ?_
    split_ifs with hf
    · obtain ⟨yp, hyp, -⟩ := hprom i hf
      rw [filter_val_eq' yp hyp, prod_singleton, ← sum_filter, filter_val_eq' yp hyp,
        sum_singleton]
    · rfl
  have hiii : ∏ xp : Particle x d, ν xp.1.1 ^ P xp =
      ∏ i, if (c.2.2.2.1 i).2 = true then ν (c.2.2.2.1 i).1 else 1 := by
    rw [hfibP]
    refine prod_congr rfl fun i _ => ?_
    split_ifs with hf
    · obtain ⟨yp, hyp, -⟩ := hprom i hf
      rw [filter_val_eq' yp hyp, prod_singleton, hyp]
      rfl
    · rfl
  have hiv : ∏ xp : Particle x d, ν xp.1.1 ^ Q xp =
      ∏ i, if i ∈ c.2.1 then ν (edgeSrc s c i (Fin.last _)) else 1 := by
    rw [prod_pow_card_filter', prod_ite_mem, univ_inter]
    refine prod_congr rfl fun i hi => ?_
    rw [filter_val_eq' ⟨_, hstore i hi⟩ rfl, prod_singleton]
    rfl
  have hv' : ∏ xp : Particle x d, ((S' xp : ℕ) : ℝ) ^ Q xp =
      ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ) else 1 := by
    rw [prod_pow_card_filter', prod_ite_mem, univ_inter]
    refine prod_congr rfl fun i hi => ?_
    rw [filter_val_eq' ⟨_, hstore i hi⟩ rfl, prod_singleton, memAt_eq, dite_eq_left (hstore i hi)]
  -- the memory weights
  have hmw := memWeight_mul_eq' (fun xp : Particle x d => ν xp.1.1) S P Q hP1 hQ1 hPS
  change memWeight _ S * _ * _ = memWeight _ S' * _ * ∏ xp, ((S' xp : ℕ) : ℝ) ^ Q xp at hmw
  set A := ∏ i, if (c.2.2.2.1 i).2 = true then
      (∑ xp : Particle x d, if xp.1 = edgePromoted c i then (S xp : ℝ) else 0) else 1 with hAdef
  set T := ∏ i, if i ∈ c.2.1 then ν (edgeSrc s c i (Fin.last _)) else 1 with hTdef
  set Bν := ∏ i, if (c.2.2.2.1 i).2 = true then ν (c.2.2.2.1 i).1 else 1 with hBdef
  set Mm := ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ) else 1 with hMdef
  set mW := memWeight (fun xp : Particle x d => ν xp.1.1) S with hmW
  set mW' := memWeight (fun xp : Particle x d => ν xp.1.1) S' with hmW'
  have hmW'0 : 0 ≤ mW' := memWeight_nonneg (fun xp => hν _) _
  have hA : mW * A * T = mW' * Bν * Mm := by rw [← hii, ← hiv, hmw, hiii, hv']
  -- the per-group rearrangements
  set E := ∏ i, if (c.2.2.2.1 i).2 = true then (primeMass x d (c.2.2.2.1 i).1)⁻¹
    else ν (c.2.2.2.1 i).1 with hEdef
  set G := ∏ i, if (c.2.2.2.1 i).2 = true then (primeMass x d (c.2.2.2.1 i).1)⁻¹ else 1
    with hGdef
  set Na := ∏ i, ν (c.2.2.2.1 i).1 with hNa
  set Nb := ∏ i, ν (edgeSrc s c i (Fin.last _)) with hNb
  set Cm := ∏ i, if i ∈ c.2.1 then (memAt x d S' (edgeStored s c i) : ℝ)
    else ν (edgeSrc s c i (Fin.last _)) with hCm
  set Wr := ∏ i, if i ∈ c.2.1 then
      (memAt x d S' (edgeStored s c i) : ℝ) / primeMass x d (edgeSrc s c i (Fin.last _))
    else ν (edgeSrc s c i (Fin.last _)) with hWr
  set Two := ∏ i, if (c.2.2.2.1 i).2 = true then (2 : ℝ) else 1 with hTwo
  have hW : rawWeight q N s c = A * E := by
    rw [hAdef, hEdef, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [div_eq_mul_inv]
    · rw [one_mul]
  have hBE : Bν * E = Na * G := by
    rw [hBdef, hEdef, hNa, hGdef, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    split_ifs
    · rfl
    · rw [one_mul, mul_one]
  have hNbM : Nb * Mm = Cm * T := by
    rw [hNb, hMdef, hCm, hTdef, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    split_ifs
    · rw [mul_comm]
    · rfl
  have hG : G ≤ Two := by
    rw [hGdef, hTwo]
    refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · split_ifs
      exacts [inv_nonneg.2 (by linarith [hVa i]), zero_le_one]
    · split_ifs
      · have := hVa i
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      · exact le_rfl
  have hTwoK : Two ≤ 2 ^ K := by
    calc Two ≤ ∏ _i : Fin K, (2 : ℝ) :=
          prod_le_prod₀ (fun i _ => by split_ifs <;> norm_num) fun i _ => by
            split_ifs <;> norm_num
      _ = 2 ^ K := by rw [prod_const, card_univ, Fintype.card_fin]
  have hCmWr : Cm ≤ Wr := by
    refine prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
    · split_ifs
      exacts [Nat.cast_nonneg _, hν _]
    · split_ifs
      · obtain ⟨h₁, h₂⟩ := hVb i
        rw [le_div_iff₀ (by linarith)]
        exact mul_le_of_le_one_right (Nat.cast_nonneg _) h₂
      · exact le_rfl
  have hT : 0 < T := prod_pos fun i _ => by
    split_ifs
    exacts [hνpos i _ (mem_band_edgeSrc' s c i _), zero_lt_one]
  have hΛ0 : 0 ≤ ∏ i, ∏ h, ν (s.2.1.1 i h) := prod_nonneg fun i _ => prod_nonneg fun h _ => hν _
  have hΛ'0 : 0 ≤ ∏ i, ∏ h, ν (edgeTgt s c i h) :=
    prod_nonneg fun i _ => prod_nonneg fun h _ => hν _
  have hE0 : 0 ≤ E := prod_nonneg fun i _ => by
    split_ifs
    exacts [inv_nonneg.2 (by linarith [hVa i]), hν _]
  have hCm0 : 0 ≤ Cm := prod_nonneg fun i _ => by
    split_ifs
    exacts [Nat.cast_nonneg _, hν _]
  have hΛ := prod_edgeTgt_mul' ν s c
  rw [← hNa, ← hNb] at hΛ
  rw [hW]
  have hmain : (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW * (A * E) ≤
      (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * (Cm * Two) := by
    refine le_of_mul_le_mul_right ?_ hT
    calc (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW * (A * E) * T
        = (∏ i, ∏ h, ν (s.2.1.1 i h)) * E * (mW * A * T) := by ring
      _ = (∏ i, ∏ h, ν (s.2.1.1 i h)) * E * (mW' * Bν * Mm) := by rw [hA]
      _ = (∏ i, ∏ h, ν (s.2.1.1 i h)) * mW' * Mm * (Bν * E) := by ring
      _ = ((∏ i, ∏ h, ν (s.2.1.1 i h)) * Na) * mW' * G * Mm := by rw [hBE]; ring
      _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * G * (Nb * Mm) := by rw [hΛ]; ring
      _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Cm * T * G := by rw [hNbM]; ring
      _ ≤ (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Cm * T * Two :=
          mul_le_mul_of_nonneg_left hG
            (mul_nonneg (mul_nonneg (mul_nonneg hΛ'0 hmW'0) hCm0) hT.le)
      _ = (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * (Cm * Two) * T := by ring
  refine hmain.trans ?_
  calc (∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * (Cm * Two)
      = Two * ((∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Cm) := by ring
    _ ≤ 2 ^ K * ((∏ i, ∏ h, ν (edgeTgt s c i h)) * mW' * Wr) := by
        gcongr

end Reversal

/-! ### The column bound -/

section Column

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The output of an admissible edge choice. -/
private theorem out_eq {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hv : EdgeValid x d Y d₀ u v r B s c) (hs' : chainEdgeOut x d Y d₀ u v r B s c = s') :
    s'.1 = c.2.2.1 ∧ s'.2.1.1 = edgeTgt s c ∧ s'.2.2.1 = edgeMem s c := by
  rw [← hs', chainEdgeOut_of_valid' hv]
  exact ⟨rfl, rfl, rfl⟩

/-- The weight product of the reversed choice. -/
theorem rawWeight_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (h₃ : s'.2.2.1 = edgeMem s c) :
    rawWeight q N s' (revChoice s c) = ∏ i, if i ∈ c.2.1 then
      (memAt x d (edgeMem s c) (edgeStored s c i) : ℝ) /
        primeMass x d (edgeSrc s c i (Fin.last _))
    else primeWeight q x d N (edgeSrc s c i (Fin.last _)) := by
  unfold rawWeight
  refine prod_congr rfl fun i _ => ?_
  change (if decide (i ∈ c.2.1) = true then _ else _) = _
  rw [edgePromoted_revChoice, sum_ite_eq_memAt, h₃]
  simp only [decide_eq_true_eq]
  rfl

/-- **The adjoint calculation for the raw coefficients**: for an admissible raw edge `s → s'`,
`μ(s) rawAmp(s, c) ≤ 2^K μ(s') rawAmp(s', c^rev)`. The pending factors swap, and
`measure_mul_rawWeight_le` compares the rest. -/
theorem measure_mul_rawAmp_le (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p) (hq : 0 < q)
    {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) (h : EdgeValid x d Y d₀ u v r B s c ∧ RawDet s c)
    (hs' : chainEdgeOut x d Y d₀ u v r B s c = s') :
    chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c ≤
      2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' * rawAmp q N s' (revChoice s c)) := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := out_eq h.1 hs'
  have hv' := edgeValid_revChoice hdisj hc h.1 h₁ h₂ h₃
  have hdet' := rawDet_revChoice h₁ h₂ h.2
  have hmem := edgeMem_revChoice hdisj hc h.1 h₁ h₂ h₃
  have hadj := measure_mul_rawWeight_le hdisj hV hν hνpos hc h.1
  rw [← rawWeight_revChoice (q := q) (N := N) h₃] at hadj
  unfold rawAmp chainMeasure
  rw [ite_eq_left h, ite_eq_left ⟨hv', hdet'⟩, hmem, h₁, h₂, h₃]
  change _ ≤ _ * ((∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
    memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
      ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
        pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 * rawWeight q N s' (revChoice s c)))
  have hρ0 := (pendingWeight_pos hq).le
  have hk : 0 ≤ (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
      pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
      pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 := by positivity
  calc (∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
        memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
        ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * rawWeight q N s c)
      = ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
          pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1) *
          ((∏ i, ∏ h, primeWeight q x d N (s.2.1.1 i h)) *
            memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) s.2.2.1 *
            rawWeight q N s c) := by ring
    _ ≤ ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
          pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) *
          pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1) *
          (2 ^ K * ((∏ i, ∏ h, primeWeight q x d N (edgeTgt s c i h)) *
            memWeight (fun xp : Particle x d => primeWeight q x d N xp.1.1) (edgeMem s c) *
            rawWeight q N s' (revChoice s c))) := mul_le_mul_of_nonneg_left hadj hk
    _ = _ := by ring

/-- An admissible raw edge of the piece `(S, I)` reaching `s'` is recovered from `s'` and its
reversed choice. -/
theorem eq_of_revChoice {s s' : ChainState x d Y d₀ u v r B} {c : EdgeChoice x d Y d₀ u v r}
    {S I : Finset (Fin K)} (hc : c ∈ rawChoices x d Y d₀ u v r S I)
    (hv : EdgeValid x d Y d₀ u v r B s c) (hs' : chainEdgeOut x d Y d₀ u v r B s c = s') :
    c = (fun i => ((revChoice s c).2.2.2.2 i).symm, S, s'.1,
      fun i => (s'.2.1.1 i ((revChoice s c).1 i (Fin.last _)), decide (i ∈ I)),
      fun i => ((revChoice s c).1 i).symm) := by
  obtain ⟨h₁, h₂, -⟩ := out_eq hv hs'
  obtain ⟨-, hS, hI⟩ := mem_filter.1 hc
  refine Prod.ext (funext fun i => ?_) (Prod.ext hS (Prod.ext h₁.symm
    (Prod.ext (funext fun i => ?_) (funext fun i => ?_))))
  · exact (Equiv.symm_symm _).symm
  · change c.2.2.2.1 i = (s'.2.1.1 i ((c.2.2.2.2 i).symm (Fin.last _)), decide (i ∈ I))
    rw [h₂, edgeTgt_symm', ite_eq_left rfl]
    refine Prod.ext rfl ?_
    change (c.2.2.2.1 i).2 = decide (i ∈ I)
    rw [← hI]
    cases hf : (c.2.2.2.1 i).2 <;> simp [hf]
  · exact (Equiv.symm_symm _).symm

open scoped Classical in
/-- **The column bound by reversal** (PD §4, dirty raw edges): the measure-weighted raw
coefficients of the piece `(S, I)` reaching `s'` sum to at most `2^K μ(s')` times the row of
the piece `(I, S)` at `s'`. Each admissible raw edge reaching `s'` is determined by its
reversed choice, which lies in the piece `(I, S)` (`eq_of_revChoice`). -/
theorem sum_col_rawAmp_le (hq : 0 < q)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (S I : Finset (Fin K))
    (s' : ChainState x d Y d₀ u v r B) :
    ∑ s, ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter
        (fun c => chainEdgeOut x d Y d₀ u v r B s c = s'),
      chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c ≤
      2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
        ∑ c' ∈ rawChoices x d Y d₀ u v r I S, rawAmp q N s' c') := by
  classical
  have hV' : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hV i).1
  have hν := primeWeight_nonneg_of hV' hb (q := q) (N := N)
  have hνpos : ∀ i, ∀ p ∈ band x (d.a i), 0 < primeWeight q x d N p := fun i p hp =>
    (primeWeight_le_two hdisj hV' hb hp).1
  have hμ0 : ∀ t : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N t :=
    fun t => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  set X := ((univ : Finset (ChainState x d Y d₀ u v r B)) ×ˢ
    rawChoices x d Y d₀ u v r S I).filter fun p =>
      chainEdgeOut x d Y d₀ u v r B p.1 p.2 = s' ∧ EdgeValid x d Y d₀ u v r B p.1 p.2 ∧
        RawDet p.1 p.2 with hX
  have hrc : ∀ p ∈ X, p.2 ∈ rawChoices x d Y d₀ u v r S I := fun p hp =>
    (mem_product.1 (mem_filter.1 hp).1).2
  -- only the admissible raw edges contribute
  have hLHS : ∑ s, ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter
      (fun c => chainEdgeOut x d Y d₀ u v r B s c = s'),
        chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c =
      ∑ p ∈ X, chainMeasure q x d Y d₀ u v r B N p.1 * rawAmp q N p.1 p.2 := by
    rw [hX, sum_filter, sum_product]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_filter]
    refine sum_congr rfl fun c _ => ?_
    by_cases hout : chainEdgeOut x d Y d₀ u v r B t c = s'
    · by_cases hvd : EdgeValid x d Y d₀ u v r B t c ∧ RawDet t c
      · rw [ite_eq_left hout, ite_eq_left ⟨hout, hvd⟩]
      · rw [ite_eq_left hout, ite_eq_right fun h => hvd h.2]
        unfold rawAmp
        rw [ite_eq_right hvd, mul_zero]
    · rw [ite_eq_right hout, ite_eq_right fun h => hout h.1]
  -- the reversal is injective on the admissible raw edges reaching `s'`
  have hinj : Set.InjOn (fun p : ChainState x d Y d₀ u v r B × EdgeChoice x d Y d₀ u v r =>
      revChoice p.1 p.2) X := by
    intro p hp p' hp' heq
    obtain ⟨hout, hv, -⟩ := (mem_filter.1 hp).2
    obtain ⟨hout', hv', -⟩ := (mem_filter.1 hp').2
    have hc := (mem_filter.1 (hrc p hp)).1
    have hc' := (mem_filter.1 (hrc p' hp')).1
    simp only at heq
    obtain ⟨h₁, h₂, h₃⟩ := out_eq hv hout
    obtain ⟨h₁', h₂', h₃'⟩ := out_eq hv' hout'
    have hs : p.1 = p'.1 := by
      rw [← chainEdgeOut_revChoice hdisj hc hv h₁ h₂ h₃,
        ← chainEdgeOut_revChoice hdisj hc' hv' h₁' h₂' h₃', heq]
    have hcc : p.2 = p'.2 := by
      rw [eq_of_revChoice (hrc p hp) hv hout, eq_of_revChoice (hrc p' hp') hv' hout', heq]
    exact Prod.ext hs hcc
  rw [hLHS]
  calc ∑ p ∈ X, chainMeasure q x d Y d₀ u v r B N p.1 * rawAmp q N p.1 p.2
      ≤ ∑ p ∈ X, 2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
          rawAmp q N s' (revChoice p.1 p.2)) := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨hout, hvd⟩ := (mem_filter.1 hp).2
        exact measure_mul_rawAmp_le hdisj hV hν hνpos hq (mem_filter.1 (hrc p hp)).1 hvd hout
    _ ≤ ∑ c' ∈ rawChoices x d Y d₀ u v r I S,
          2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' * rawAmp q N s' c') := by
        refine sum_le_sum_of_injOn (fun p => revChoice p.1 p.2) hinj (fun c' hc' => ?_)
          (fun p _ => le_rfl) fun c' hc' _ => ?_
        · obtain ⟨p, hp, rfl⟩ := mem_image.1 hc'
          exact revChoice_mem_rawChoices (hrc p hp)
        · exact mul_nonneg (by positivity) (mul_nonneg (hμ0 s')
            (rawAmp_nonneg hq hdisj hV' hν s' (mem_filter.1 hc').1))
    _ = 2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
          ∑ c' ∈ rawChoices x d Y d₀ u v r I S, rawAmp q N s' c') := by
        rw [← mul_sum, ← mul_sum]

end Column

end Erdos408.OneSided
