module

public import Erdos408.OneSided.Lift

/-!
# Position models

The lift of PD §3.2 over an abstract set of positions (`blueprint/one_sided_type_ii.md` §11).
A position model has:

* a finite type of positions;
* a determinant `det : Pos → Pos → ℤ`;
* a divisibility predicate `FirstDvd p P` ("`p` divides the first coordinate of `P`");
* a ratio `ratio P` (the `r_P` of the good-state tests).

The row operation, the symmetrization, the good-state projection, the operator `𝒜` and the
moment at a base position are defined once, for every model. Two instances matter:

* `physModel`: the primitive positions of `Ω`, with `p ∣ P₁` and `r_P`. Its operators are
  those of `Lift.lean` (`detMoment_eq_sum_moment`).
* `rootModel`: at a real root `ϱ = (u, v, r)` and lines `ℓ`, the primitive `z ∈ ℤ²` with
  `g(ϱ) z ∈ Ω`. Here `p ∣ (gz)₁` is replaced by `[z]_p = ℓ_p`, and `r_{gz}` by
  `τ(w_z)/τ(z)`, where `τ(z) = z₁ + r z₂` and `w_z` is a complement of `z`. PD Lemma 3.4
  compares the physical moment with the average of root moments over independent uniform
  lines.

The good-state tests are invariant under adding an integer to the ratio, so models are
compared with ratios modulo `ℤ`.
-/

@[expose] public section

noncomputable section

namespace Erdos408.OneSided

open Finset Real
open scoped Matrix

variable {K : ℕ}

/-- A position model: finitely many positions, with a determinant, divisibility of the first
coordinate, and the ratio used by the good-state tests. -/
structure PosModel where
  /-- The positions. -/
  Pos : Type
  [instFintype : Fintype Pos]
  [instDecEq : DecidableEq Pos]
  /-- The determinant of two positions. -/
  det : Pos → Pos → ℤ
  /-- `p` divides the first coordinate of the position. -/
  FirstDvd : ℕ → Pos → Prop
  /-- The ratio `r_P`. -/
  ratio : Pos → ℝ

attribute [instance] PosModel.instFintype PosModel.instDecEq

namespace PosModel

variable (M : PosModel)

open scoped Classical in
/-- The states: a position and lists whose labels all divide its first coordinate. -/
def states (x : ℝ) (d : Data K) : Finset (M.Pos × Lists K (padCount x)) :=
  (univ ×ˢ lists x d (padCount x)).filter fun s => ∀ i h, M.FirstDvd (s.2 i h) s.1

/-- The state space of the model. -/
abbrev State (x : ℝ) (d : Data K) := ↥(M.states x d)

open scoped Classical in
/-- `ω(P)`: the number of band primes dividing the first coordinate. -/
def bandCount (x : ℝ) (d : Data K) (P : M.Pos) : ℕ :=
  ∑ i, ((band x (d.a i)).filter fun p => M.FirstDvd p P).card

open scoped Classical in
/-- The row operation `𝒯` of PD §3.2 over the model; see `Erdos408.OneSided.rowOp`. -/
def rowOp (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    Matrix (M.State x d) (M.State x d) ℂ := fun s s' =>
  if (∀ i (h : Fin (padCount x)), s'.1.2 i h.castSucc = s.1.2 i h.castSucc) ∧
      (∀ i i' h', s'.1.2 i (Fin.last _) ≠ s.1.2 i' h') ∧
      d₀ ≤ (padProd s.1.2 : ℝ) ∧ (padProd s.1.2 : ℝ) < 2 * d₀ ∧
      (padProd s.1.2 : ℤ) ∣ M.det s.1.1 s'.1.1 then
    (((d.bandMass x)⁻¹ * (d₀ / padProd s.1.2) * dyadicBump (lastProd s.1.2 / Y) *
        dyadicBump (lastProd s'.1.2 / Y) *
        plateau ((M.det s.1.1 s'.1.1 / padProd s.1.2 : ℤ) / Y) *
        q ^ (((M.bandCount x d s.1.1 : ℝ) - K * (padCount x + 1)) / 2 +
          ((M.bandCount x d s'.1.1 : ℝ) - K * (padCount x + 1)) / 2) : ℝ) : ℂ) *
      ((if M.det s.1.1 s'.1.1 / padProd s.1.2 = (lastProd s.1.2 : ℤ) - lastProd s'.1.2 then 1
          else 0) -
        arcIntegral A₀ x Y
          (M.det s.1.1 s'.1.1 / padProd s.1.2 - lastProd s.1.2 + lastProd s'.1.2))
  else 0

open scoped Classical in
/-- The slot symmetrization `𝒮` over the model. -/
def symOp (x : ℝ) (d : Data K) : Matrix (M.State x d) (M.State x d) ℂ := fun s s' =>
  if s.1.1 = s'.1.1 ∧
      ∃ σ : Fin K → Equiv.Perm (Fin (padCount x + 1)), ∀ i, s'.1.2 i = s.1.2 i ∘ σ i then
    (((padCount x + 1).factorial ^ K : ℕ) : ℂ)⁻¹
  else 0

open scoped Classical in
/-- The projection `𝒢` onto states passing both good-state tests at the model's ratio. -/
def goodOp (x : ℝ) (d : Data K) (Y d₀ : ℝ) : Matrix (M.State x d) (M.State x d) ℂ :=
  Matrix.diagonal fun s =>
    if GoodFirst Y d₀ (M.ratio s.1.1) s.1.2 ∧ GoodSecond x d d₀ (M.ratio s.1.1) s.1.2 then 1
    else 0

/-- The operator `𝒜 = 𝒢 𝒮 𝒯 𝒮 𝒢` over the model. -/
def edgeOp (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) : Matrix (M.State x d) (M.State x d) ℂ :=
  M.goodOp x d Y d₀ * M.symOp x d * M.rowOp q A₀ x d Y d₀ * M.symOp x d * M.goodOp x d Y d₀

open scoped Classical in
/-- The moment `⟨u_{P₀}, (𝒜𝒜^*)^R u_{P₀}⟩` at the base position `P₀`. -/
def moment (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) (P₀ : M.Pos) : ℂ :=
  (stateMass x d : ℂ) * ∑ s : M.State x d, ∑ s' : M.State x d,
    if s.1.1 = P₀ ∧ s'.1.1 = P₀ then
      ((M.edgeOp q A₀ x d Y d₀ * (M.edgeOp q A₀ x d Y d₀)ᴴ) ^ momentPower x) s s'
    else 0

end PosModel

/-! ### Reindexing along an equivalence of states -/

section Reindex

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Products of matrices agreeing along an equivalence of indices agree along it. -/
private theorem mul_apply_equiv_of_apply (σ : α ≃ β) {A B : Matrix α α ℂ}
    {A' B' : Matrix β β ℂ} (hA : ∀ i j, A' (σ i) (σ j) = A i j)
    (hB : ∀ i j, B' (σ i) (σ j) = B i j) (i j : α) :
    (A' * B') (σ i) (σ j) = (A * B) i j := by
  simp only [Matrix.mul_apply]
  exact (Fintype.sum_equiv σ _ _ fun k => by rw [hA, hB]).symm

/-- `𝒢 𝒮 𝒯 𝒮 𝒢` agrees along an equivalence of indices when `𝒢`, `𝒮` and `𝒯` do. -/
private theorem edge_apply_equiv_of_apply (σ : α ≃ β) {G S T : Matrix α α ℂ}
    {G' S' T' : Matrix β β ℂ} (hG : ∀ i j, G' (σ i) (σ j) = G i j)
    (hS : ∀ i j, S' (σ i) (σ j) = S i j) (hT : ∀ i j, T' (σ i) (σ j) = T i j) (i j : α) :
    (G' * S' * T' * S' * G') (σ i) (σ j) = (G * S * T * S * G) i j :=
  mul_apply_equiv_of_apply σ (mul_apply_equiv_of_apply σ
    (mul_apply_equiv_of_apply σ (mul_apply_equiv_of_apply σ hG hS) hT) hS) hG i j

/-- `(𝒜𝒜^*)^R` agrees along an equivalence of indices when `𝒜` does. -/
private theorem momentPow_apply_equiv_of_apply [DecidableEq α] [DecidableEq β] (σ : α ≃ β)
    {A : Matrix α α ℂ} {A' : Matrix β β ℂ} (hA : ∀ i j, A' (σ i) (σ j) = A i j) (R : ℕ) (i j : α) :
    ((A' * A'ᴴ) ^ R) (σ i) (σ j) = ((A * Aᴴ) ^ R) i j := by
  -- `𝒜𝒜^*` agrees
  have hAA : ∀ i j, (A' * A'ᴴ) (σ i) (σ j) = (A * Aᴴ) i j :=
    mul_apply_equiv_of_apply σ hA fun i j => by simp [Matrix.conjTranspose_apply, hA]
  induction R generalizing i j with
  | zero => simp [Matrix.one_apply, σ.injective.eq_iff]
  | succ R ih =>
    rw [pow_succ, pow_succ]
    exact mul_apply_equiv_of_apply σ ih hAA i j

end Reindex

/-! ### Integer shifts of the ratio -/

/-- The circle distance is invariant under adding an integer. -/
theorem circleDist_add_intCast (t : ℝ) (n : ℤ) : circleDist (t + n) = circleDist t := by
  simp [circleDist, round_add_intCast]

/-- `‖c (r + k)‖ = ‖c r‖` for integers `c` and `k`. -/
theorem circleDist_intCast_mul_add_intCast (c k : ℤ) (r : ℝ) :
    circleDist (c * (r + k)) = circleDist (c * r) := by
  rw [mul_add, ← Int.cast_mul, circleDist_add_intCast]

/-- Test (i) is invariant under adding an integer to the ratio. -/
theorem goodFirst_add_intCast (Y d₀ : ℝ) {J : ℕ} (r : ℝ) (k : ℤ) (p : Lists K J) :
    GoodFirst Y d₀ (r + k) p ↔ GoodFirst Y d₀ r p := by
  have h (l D : ℕ) : circleDist (l * D * (r + k)) = circleDist (l * D * r) := by
    exact_mod_cast circleDist_intCast_mul_add_intCast (l * D) k r
  simp only [GoodFirst, h]

/-- The separation in test (ii) is invariant under adding an integer to the ratio. -/
theorem separated_add_intCast (x : ℝ) (d : Data K) (d₀ : ℝ) (I : Finset (Fin K)) (i : Fin K)
    {J : ℕ} (r : ℝ) (k : ℤ) (p : Lists K J) (T : Fin K → ℕ) :
    Separated x d d₀ I i (r + k) p T ↔ Separated x d d₀ I i r p T := by
  have h (A B C : ℕ) :
      circleDist (((A : ℝ) - B) * C * (r + k)) = circleDist (((A : ℝ) - B) * C * r) := by
    exact_mod_cast circleDist_intCast_mul_add_intCast ((A - B) * C) k r
  simp only [Separated, h]

open scoped Classical in
/-- Test (ii) is invariant under adding an integer to the ratio. -/
theorem goodSecond_add_intCast (x : ℝ) (d : Data K) (d₀ : ℝ) {J : ℕ} (r : ℝ) (k : ℤ)
    (p : Lists K J) : GoodSecond x d d₀ (r + k) p ↔ GoodSecond x d d₀ r p := by
  simp only [GoodSecond]
  refine forall_congr' fun I => forall_congr' fun hI => ?_
  rw [filter_congr fun T _ => not_congr (separated_add_intCast x d d₀ I _ r k p T)]

/-! ### The moments over base positions -/

/-- The sum of the moments over the base positions pairs the states at a common position. -/
theorem PosModel.sum_moment (M : PosModel) (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    ∑ P₀, M.moment q A₀ x d Y d₀ P₀ = (stateMass x d : ℂ) * ∑ s : M.State x d, ∑ s',
      if s.1.1 = s'.1.1 then
        ((M.edgeOp q A₀ x d Y d₀ * (M.edgeOp q A₀ x d Y d₀)ᴴ) ^ momentPower x) s s'
      else 0 := by
  simp only [PosModel.moment, ← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun s' _ => ?_
  -- only the common position contributes
  by_cases h : s.1.1 = s'.1.1
  · simp [h]
  · simp only [h, ite_false]
    exact sum_eq_zero fun P₀ _ => ite_eq_right_iff.2 fun hP => (h (hP.1.trans hP.2.symm)).elim

/-! ### Isomorphisms of models -/

/-- The band elements are prime. -/
theorem prime_of_mem_band {x a : ℝ} {p : ℕ} (hp : p ∈ band x a) : p.Prime :=
  (mem_filter.1 hp).2

/-- The labels of a list are prime. -/
theorem prime_of_mem_lists {x : ℝ} {d : Data K} {J : ℕ} {p : Lists K J} (hp : p ∈ lists x d J)
    (i : Fin K) (h : Fin (J + 1)) : (p i h).Prime := by
  classical
  exact prime_of_mem_band (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1
    (mem_filter.1 hp).1 i) h)

/-- An isomorphism of position models: a bijection of positions preserving the determinant,
divisibility by primes, and the ratio modulo `ℤ`. -/
structure PosModel.Iso (M N : PosModel) where
  /-- The bijection of positions. -/
  toEquiv : M.Pos ≃ N.Pos
  det_eq : ∀ P Q, N.det (toEquiv P) (toEquiv Q) = M.det P Q
  firstDvd_iff : ∀ p, p.Prime → ∀ P, N.FirstDvd p (toEquiv P) ↔ M.FirstDvd p P
  ratio_sub : ∀ P, ∃ k : ℤ, N.ratio (toEquiv P) - M.ratio P = k

namespace PosModel.Iso

variable {M N : PosModel} (e : M.Iso N)

/-- The states correspond under an isomorphism: map the position, keep the lists. -/
def stateEquiv (x : ℝ) (d : Data K) : M.State x d ≃ N.State x d where
  toFun s := ⟨(e.toEquiv s.1.1, s.1.2), by
    have hs := s.2
    simp only [PosModel.states, mem_filter, mem_product, mem_univ, true_and] at hs ⊢
    exact ⟨hs.1, fun i h => (e.firstDvd_iff _ (prime_of_mem_lists hs.1 i h) _).2 (hs.2 i h)⟩⟩
  invFun s := ⟨(e.toEquiv.symm s.1.1, s.1.2), by
    have hs := s.2
    simp only [PosModel.states, mem_filter, mem_product, mem_univ, true_and] at hs ⊢
    refine ⟨hs.1, fun i h => (e.firstDvd_iff _ (prime_of_mem_lists hs.1 i h) _).1 ?_⟩
    rw [e.toEquiv.apply_symm_apply]
    exact hs.2 i h⟩
  left_inv s := Subtype.ext (Prod.ext (e.toEquiv.symm_apply_apply _) rfl)
  right_inv s := Subtype.ext (Prod.ext (e.toEquiv.apply_symm_apply _) rfl)

open scoped Classical in
/-- An isomorphism preserves `ω`. -/
theorem bandCount_toEquiv (x : ℝ) (d : Data K) (P : M.Pos) :
    N.bandCount x d (e.toEquiv P) = M.bandCount x d P := by
  refine sum_congr rfl fun i _ => ?_
  rw [filter_congr fun p hp => e.firstDvd_iff p (prime_of_mem_band hp) P]

/-- An isomorphism preserves the row operation. -/
theorem rowOp_stateEquiv (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) (s s' : M.State x d) :
    N.rowOp q A₀ x d Y d₀ (e.stateEquiv x d s) (e.stateEquiv x d s') =
      M.rowOp q A₀ x d Y d₀ s s' := by
  simp only [PosModel.rowOp, stateEquiv, Equiv.coe_fn_mk, e.det_eq, e.bandCount_toEquiv]

/-- An isomorphism preserves the slot symmetrization. -/
theorem symOp_stateEquiv (x : ℝ) (d : Data K) (s s' : M.State x d) :
    N.symOp x d (e.stateEquiv x d s) (e.stateEquiv x d s') = M.symOp x d s s' := by
  simp only [PosModel.symOp, stateEquiv, Equiv.coe_fn_mk, e.toEquiv.apply_eq_iff_eq]

open scoped Classical in
/-- An isomorphism preserves the good-state projection, as the tests are invariant under
integer shifts of the ratio. -/
theorem goodOp_stateEquiv (x : ℝ) (d : Data K) (Y d₀ : ℝ) (s s' : M.State x d) :
    N.goodOp x d Y d₀ (e.stateEquiv x d s) (e.stateEquiv x d s') = M.goodOp x d Y d₀ s s' := by
  obtain ⟨k, hk⟩ := e.ratio_sub s.1.1
  have hr : N.ratio (e.toEquiv s.1.1) = M.ratio s.1.1 + k := by linarith
  simp only [PosModel.goodOp, Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]
  refine if_congr Iff.rfl (if_congr ?_ rfl rfl) rfl
  simp only [stateEquiv, Equiv.coe_fn_mk, hr, goodFirst_add_intCast, goodSecond_add_intCast]

/-- An isomorphism preserves `𝒜`. -/
theorem edgeOp_stateEquiv (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) (s s' : M.State x d) :
    N.edgeOp q A₀ x d Y d₀ (e.stateEquiv x d s) (e.stateEquiv x d s') =
      M.edgeOp q A₀ x d Y d₀ s s' :=
  edge_apply_equiv_of_apply _ (e.goodOp_stateEquiv x d Y d₀) (e.symOp_stateEquiv x d)
    (e.rowOp_stateEquiv q A₀ x d Y d₀) s s'

end PosModel.Iso

/-- Isomorphic models have equal moments at corresponding base positions. -/
theorem PosModel.Iso.moment_eq {M N : PosModel} (e : M.Iso N) (q A₀ x : ℝ) (d : Data K)
    (Y d₀ : ℝ) (P₀ : M.Pos) :
    N.moment q A₀ x d Y d₀ (e.toEquiv P₀) = M.moment q A₀ x d Y d₀ P₀ := by
  rw [PosModel.moment, PosModel.moment, ← (e.stateEquiv x d).sum_comp]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [← (e.stateEquiv x d).sum_comp]
  refine sum_congr rfl fun s' _ => ?_
  -- the states and `(𝒜𝒜^*)^R` correspond
  rw [momentPow_apply_equiv_of_apply _ (e.edgeOp_stateEquiv q A₀ x d Y d₀)]
  simp only [stateEquiv, Equiv.coe_fn_mk, e.toEquiv.apply_eq_iff_eq]

/-! ### The physical model -/

/-- The physical model: the primitive positions of `Ω`, with `p ∣ P₁` and the ratio `r_P`. -/
def physModel (d : Data K) (Y d₀ : ℝ) : PosModel where
  Pos := ↥(positions d Y d₀)
  det P Q := det P.1 Q.1
  FirstDvd p P := p ∣ P.1.1
  ratio P := rootRatio P.1

open scoped Classical in
/-- The physical states are the states of the physical model. -/
def physStateEquiv (x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    State x d Y d₀ ≃ (physModel d Y d₀).State x d where
  toFun s := ⟨(⟨s.1.1, (mem_product.1 (mem_filter.1 s.2).1).1⟩, s.1.2),
    mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, (mem_product.1 (mem_filter.1 s.2).1).2⟩,
      (mem_filter.1 s.2).2⟩⟩
  invFun s := ⟨(s.1.1.1, s.1.2),
    mem_filter.2 ⟨mem_product.2 ⟨s.1.1.2, (mem_product.1 (mem_filter.1 s.2).1).2⟩,
      (mem_filter.1 s.2).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `ω` in the physical model is `ω` of the first coordinate. -/
theorem physModel_bandCount (x : ℝ) (d : Data K) (Y d₀ : ℝ) (P : (physModel d Y d₀).Pos) :
    (physModel d Y d₀).bandCount x d P = bandCount x d P.1.1 := by
  simp only [PosModel.bandCount, bandCount, primeCount, physModel]
  refine sum_congr rfl fun i _ => ?_
  exact congrArg card (filter_congr_decidable _ _ _)

/-- The physical model's `𝒜` is the physical `𝒜`. -/
theorem physModel_edgeOp_physStateEquiv (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ)
    (s s' : State x d Y d₀) :
    (physModel d Y d₀).edgeOp q A₀ x d Y d₀ (physStateEquiv x d Y d₀ s)
      (physStateEquiv x d Y d₀ s') = edgeOp q A₀ x d Y d₀ s s' := by
  refine edge_apply_equiv_of_apply _ (fun s s' => ?_) (fun s s' => ?_) (fun s s' => ?_) s s'
  · -- `𝒢`: the tests are at `r_P`
    simp only [PosModel.goodOp, goodOp, Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]
    classical
    exact if_congr Iff.rfl (if_congr Iff.rfl rfl rfl) rfl
  · -- `𝒮`
    exact if_congr (and_congr Subtype.ext_iff Iff.rfl) rfl rfl
  · -- `𝒯`
    simp only [PosModel.rowOp, rowOp, physModel_bandCount]
    rfl

/-- The determinant moment of `Lift.lean` is the sum of the physical moments over the base
positions. -/
theorem detMoment_eq_sum_moment (q A₀ x : ℝ) (d : Data K) (Y d₀ : ℝ) :
    detMoment q A₀ x d Y d₀ = ∑ P₀, (physModel d Y d₀).moment q A₀ x d Y d₀ P₀ := by
  rw [PosModel.sum_moment, detMoment, ← (physStateEquiv x d Y d₀).sum_comp]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [← (physStateEquiv x d Y d₀).sum_comp]
  refine sum_congr rfl fun s' _ => ?_
  -- the states and `(𝒜𝒜^*)^R` correspond
  rw [momentPow_apply_equiv_of_apply _ (physModel_edgeOp_physStateEquiv q A₀ x d Y d₀)]
  exact if_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩ rfl rfl

/-! ### The model at a real root -/

/-- `τ(z) = z₁ + r z₂`. -/
def tau (r : ℝ) (z : ℤ × ℤ) : ℝ := z.1 + r * z.2

/-- A complement of `z`, from Bézout: `det(z, w_z) = gcd(z₁, z₂)`. -/
def complement (z : ℤ × ℤ) : ℤ × ℤ := (-Int.gcdB z.1 z.2, Int.gcdA z.1 z.2)

/-- The projective line `[z]_p ∈ {0, …, p}`: `z₂ / z₁` if `p ∤ z₁`, and `p` otherwise. -/
def lineOf (p : ℕ) (z : ℤ × ℤ) : ℕ :=
  if (z.1 : ZMod p) = 0 then p else ((z.2 : ZMod p) * (z.1 : ZMod p)⁻¹).val

/-- A bound for the positions at a root: every `z` with `g(ϱ) z ∈ Ω` has
`|z₁|, |z₂| ≤ 2 (16U + 2V + 1)²`. -/
def rootBound (U V : ℝ) : ℕ := ⌈2 * (16 * U + 2 * V + 1) ^ 2⌉₊

/-- The primitive `z` with `g(ϱ) z ∈ Ω`, where `g(ϱ) = (u, ur; v, vr + 1/u)`, so that
`(g z)₁ = u τ(z)` and `(g z)₂ = v τ(z) + z₂/u`. -/
def rootPositions (U V u v r : ℝ) : Finset (ℤ × ℤ) :=
  ((Icc (-(rootBound U V : ℤ)) (rootBound U V)) ×ˢ
      (Icc (-(rootBound U V : ℤ)) (rootBound U V))).filter fun z =>
    Int.gcd z.1 z.2 = 1 ∧ U ≤ u * tau r z ∧ u * tau r z ≤ 16 * U ∧
      V ≤ v * tau r z + z.2 / u ∧ v * tau r z + z.2 / u ≤ 2 * V

/-- The model at the real root `ϱ = (u, v, r)` with lines `ℓ`: positions `z` with
`g(ϱ) z ∈ Ω`, divisibility `[z]_p = ℓ_p`, and ratio `τ(w_z)/τ(z)`. -/
def rootModel (d : Data K) (Y d₀ u v r : ℝ) (ℓ : ℕ → ℕ) : PosModel where
  Pos := ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r)
  det z z' := z.1.1 * z'.1.2 - z.1.2 * z'.1.1
  FirstDvd p z := lineOf p z.1 = ℓ p
  ratio z := tau r (complement z.1) / tau r z.1

end Erdos408.OneSided
