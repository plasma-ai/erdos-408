module

public import Erdos408.OneSided.Lift

/-!
# Slot symmetry of the lift

The slot symmetrization `𝒮` of `Lift.lean` averages over the orders of the lists. It fixes
every vector that does not see that order (`blueprint/one_sided_type_ii.md` §14).

* `permuteLists p σ` reorders the list of each group `i` by `σ i`. The list product is
  unchanged, and the omission products are permuted as a family over the omissions, so
  `endVec` and `IsGood` do not see the order.
* The reorderings of a state are states, and they are `((J + 1)!)^K` distinct states,
  because the lists have distinct entries. So each row of `𝒮` sums to one, and `𝒮` is
  symmetric.
* `sum_symOp_mul`, `sum_mul_symOp_mulVec`: `𝒮` fixes a `SlotInvariant` vector, acting from
  either side.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset
open scoped Matrix

variable {K : ℕ}

/-! ### Reordered lists -/

/-- The lists `p` with the list of each group `i` reordered by `σ i`. -/
def permuteLists {J : ℕ} (p : Lists K J) (σ : Fin K → Equiv.Perm (Fin (J + 1))) :
    Lists K J :=
  fun i => p i ∘ σ i

/-- Reordering by `σ` and then by `σ⁻¹` gives back the lists. -/
theorem permuteLists_inv {J : ℕ} (p : Lists K J) (σ : Fin K → Equiv.Perm (Fin (J + 1))) :
    permuteLists (permuteLists p σ) σ⁻¹ = p := by
  funext i h
  simp [permuteLists]

/-- The list product does not see the order. -/
theorem listProd_permuteLists {J : ℕ} (p : Lists K J)
    (σ : Fin K → Equiv.Perm (Fin (J + 1))) : listProd (permuteLists p σ) = listProd p :=
  prod_congr rfl fun i _ => Equiv.prod_comp (σ i) (p i)

/-- Omitting the slots `o` of the reordered lists omits the slots `σ ∘ o` of `p`. -/
theorem omitProd_permuteLists {J : ℕ} (p : Lists K J) (σ : Fin K → Equiv.Perm (Fin (J + 1)))
    (o : Fin K → Fin (J + 1)) :
    omitProd (permuteLists p σ) o = omitProd p fun i => σ i (o i) :=
  prod_congr rfl fun i _ =>
    prod_equiv (σ i) (by simp [(σ i).injective.ne_iff]) fun _ _ => rfl

/-! ### Goodness does not see the order -/

/-- Test (i) survives a reordering: the omission `o` of the reordered lists is the omission
`σ ∘ o` of `p`. -/
theorem GoodFirst.permuteLists {Y d₀ r : ℝ} {J : ℕ} {p : Lists K J}
    (h : GoodFirst Y d₀ r p) (σ : Fin K → Equiv.Perm (Fin (J + 1))) :
    GoodFirst Y d₀ r (permuteLists p σ) := by
  intro o h₁ h₂ l hl₁ hl₂
  rw [omitProd_permuteLists] at h₁ h₂ ⊢
  exact h _ h₁ h₂ l hl₁ hl₂

/-- Test (i) does not see the order. -/
theorem goodFirst_permuteLists_iff {Y d₀ r : ℝ} {J : ℕ} (p : Lists K J)
    (σ : Fin K → Equiv.Perm (Fin (J + 1))) :
    GoodFirst Y d₀ r (permuteLists p σ) ↔ GoodFirst Y d₀ r p :=
  ⟨fun h => permuteLists_inv p σ ▸ h.permuteLists σ⁻¹, fun h => h.permuteLists σ⟩

/-- The separation survives a reordering, as test (i) does. -/
theorem Separated.permuteLists {x : ℝ} {d : Data K} {d₀ : ℝ} {I : Finset (Fin K)} {i : Fin K}
    {J : ℕ} {r : ℝ} {p : Lists K J} {T : Fin K → ℕ} (h : Separated x d d₀ I i r p T)
    (σ : Fin K → Equiv.Perm (Fin (J + 1))) : Separated x d d₀ I i r (permuteLists p σ) T := by
  intro o o' Z hZ Z' hZ' h₁ h₂ h₁' h₂' hne
  simp only [omitProd_permuteLists] at h₁ h₂ h₁' h₂' hne ⊢
  exact h _ _ Z hZ Z' hZ' h₁ h₂ h₁' h₂' hne

/-- The separation does not see the order. -/
theorem separated_permuteLists_iff {x : ℝ} {d : Data K} {d₀ : ℝ} {I : Finset (Fin K)}
    {i : Fin K} {J : ℕ} {r : ℝ} (p : Lists K J) (σ : Fin K → Equiv.Perm (Fin (J + 1)))
    (T : Fin K → ℕ) :
    Separated x d d₀ I i r (permuteLists p σ) T ↔ Separated x d d₀ I i r p T :=
  ⟨fun h => permuteLists_inv p σ ▸ h.permuteLists σ⁻¹, fun h => h.permuteLists σ⟩

/-- Goodness does not see the order. -/
theorem isGood_permuteLists_iff {x : ℝ} {d : Data K} {Y d₀ : ℝ} {J : ℕ} (P : ℕ × ℕ)
    (p : Lists K J) (σ : Fin K → Equiv.Perm (Fin (J + 1))) :
    IsGood x d Y d₀ P (permuteLists p σ) ↔ IsGood x d Y d₀ P p := by
  classical
  unfold IsGood GoodSecond
  rw [goodFirst_permuteLists_iff]
  refine and_congr Iff.rfl (forall_congr' fun I => forall_congr' fun hI => ?_)
  rw [filter_congr (p := fun T => ¬Separated x d d₀ I (I.max' hI) (rootRatio P)
    (permuteLists p σ) T) (q := fun T => ¬Separated x d d₀ I (I.max' hI) (rootRatio P) p T)
    fun T _ => not_congr (separated_permuteLists_iff p σ T)]

/-! ### Reordered states -/

variable {x : ℝ} {d : Data K} {Y d₀ : ℝ}

/-- A state's lists have distinct entries in each group. -/
theorem injective_state_lists (s : State x d Y d₀) (i : Fin K) : Function.Injective (s.1.2 i) :=
  (mem_filter.1 (mem_product.1 (mem_filter.1 s.2).1).2).2 i

/-- Reordering the lists of a state gives a state. -/
theorem mem_states_permuteLists (s : State x d Y d₀)
    (σ : Fin K → Equiv.Perm (Fin (padCount x + 1))) :
    (s.1.1, permuteLists s.1.2 σ) ∈ states x d Y d₀ := by
  obtain ⟨hs, hdiv⟩ := mem_filter.1 s.2
  obtain ⟨hP, hl⟩ := mem_product.1 hs
  obtain ⟨hband, hinj⟩ := mem_filter.1 hl
  refine mem_filter.2 ⟨mem_product.2 ⟨hP, mem_filter.2 ⟨?_, fun i =>
    (hinj i).comp (σ i).injective⟩⟩, fun i h => hdiv i (σ i h)⟩
  simp only [Fintype.mem_piFinset] at hband ⊢
  exact fun i h => hband i (σ i h)

/-- The reorderings of `s` are the `((J + 1)!)^K` states `s ∘ σ`: they are distinct, since
the lists have distinct entries. -/
theorem card_filter_reorders (s : State x d Y d₀)
    [DecidablePred fun s' : State x d Y d₀ => s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i] :
    (univ.filter fun s' : State x d Y d₀ => s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i).card =
      (padCount x + 1).factorial ^ K := by
  classical
  -- the reorderings are the injective image of the tuples of permutations
  set φ : (Fin K → Equiv.Perm (Fin (padCount x + 1))) → State x d Y d₀ :=
    fun σ => ⟨(s.1.1, permuteLists s.1.2 σ), mem_states_permuteLists s σ⟩ with hφ
  have hinj : Function.Injective φ := by
    intro σ τ h
    funext i
    refine Equiv.ext fun h' => ?_
    have hh := congrArg (fun s' : State x d Y d₀ => s'.1.2 i h') h
    exact injective_state_lists s i hh
  have himage : (univ.filter fun s' : State x d Y d₀ => s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i) =
      univ.image φ := by
    ext s'
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨h₁, σ, hσ⟩
      exact ⟨σ, Subtype.ext (Prod.ext h₁ (funext fun i => (hσ i).symm))⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨rfl, σ, fun _ => rfl⟩
  rw [himage, card_image_of_injective _ hinj, card_univ]
  simp [Fintype.card_perm]

/-! ### The symmetrization -/

/-- Each row of `𝒮` sums to one. -/
theorem sum_symOp (s : State x d Y d₀) : ∑ s', symOp x d Y d₀ s s' = 1 := by
  unfold symOp
  rw [sum_ite, sum_const_zero, add_zero, sum_const, card_filter_reorders, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (pow_ne_zero _ (Nat.factorial_ne_zero _)))

/-- `𝒮` is symmetric: reordering by `σ` is undone by `σ⁻¹`. -/
theorem symOp_comm (s s' : State x d Y d₀) : symOp x d Y d₀ s s' = symOp x d Y d₀ s' s := by
  -- `s'` reorders `s` exactly when `s` reorders `s'`
  have hsymm : ∀ s s' : State x d Y d₀, (s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i) →
      s'.1.1 = s.1.1 ∧
        ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s.1.2 i = s'.1.2 i ∘ σ i := by
    rintro s s' ⟨h₁, σ, hσ⟩
    refine ⟨h₁.symm, σ⁻¹, fun i => ?_⟩
    rw [hσ i]
    funext h
    simp
  unfold symOp
  split_ifs with h h' h''
  · rfl
  · exact absurd (hsymm s s' h) h'
  · exact absurd (hsymm s' s h'') h
  · rfl

/-- A vector on states is slot invariant when it does not see the order of the lists. -/
def SlotInvariant (v : State x d Y d₀ → ℂ) : Prop :=
  ∀ (s s' : State x d Y d₀) (σ : Fin K → Equiv.Perm (Fin (padCount x + 1))),
    s.1.1 = s'.1.1 → (∀ i, s'.1.2 i = s.1.2 i ∘ σ i) → v s' = v s

/-- The endpoint vector is slot invariant, because the list product is. -/
theorem slotInvariant_endVec : SlotInvariant (endVec x d Y d₀) := by
  intro s s' σ h₁ hσ
  have hp : s'.1.2 = permuteLists s.1.2 σ := funext hσ
  rw [endVec, endVec, hp, listProd_permuteLists, ← h₁]

/-- `𝒮` fixes a slot-invariant vector: `𝒮 v = v`. -/
theorem sum_symOp_mul {v : State x d Y d₀ → ℂ} (hv : SlotInvariant v) (s : State x d Y d₀) :
    ∑ s', symOp x d Y d₀ s s' * v s' = v s := by
  calc ∑ s', symOp x d Y d₀ s s' * v s' = ∑ s', symOp x d Y d₀ s s' * v s := by
        refine sum_congr rfl fun s' _ => ?_
        unfold symOp
        split_ifs with h
        · obtain ⟨h₁, σ, hσ⟩ := h
          rw [hv s s' σ h₁ hσ]
        · rw [zero_mul, zero_mul]
    _ = v s := by rw [← sum_mul, sum_symOp, one_mul]

/-- `𝒮` fixes a slot-invariant vector acting from the left: `⟨u, 𝒮 w⟩ = ⟨u, w⟩` without the
conjugation, by the symmetry of `𝒮`. -/
theorem sum_mul_symOp_mulVec {u : State x d Y d₀ → ℂ} (hu : SlotInvariant u)
    (w : State x d Y d₀ → ℂ) :
    ∑ s, u s * (symOp x d Y d₀ *ᵥ w) s = ∑ s, u s * w s := by
  simp only [Matrix.mulVec, dotProduct, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s' _ => ?_
  calc ∑ s, u s * (symOp x d Y d₀ s s' * w s')
      = (∑ s, symOp x d Y d₀ s' s * u s) * w s' := by
        rw [sum_mul]
        refine sum_congr rfl fun s _ => ?_
        rw [symOp_comm]
        ring
    _ = u s' * w s' := by rw [sum_symOp_mul hu]

end Erdos408.OneSided
