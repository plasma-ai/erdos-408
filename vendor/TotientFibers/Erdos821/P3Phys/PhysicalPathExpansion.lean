import Erdos821.S2Phys.PhysicalPathExpansion

/-! Identification of the literal root-moment path expansion with
`closedPhysicalExpression`, and the proof of `PhysicalPathExpansionTask`. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Phys

open Erdos821.Blueprint.Graph
open Erdos821.S2Core
open Erdos821.S2Phys

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Orientation of edge `i` in a path whose first edge has orientation `f`. -/
def orient (f : Bool) {n : ℕ} (i : Fin n) : Bool := cond f (edgeForward i) (!edgeForward i)

/-- Vertex `j` of the physical path started at position `x` with first orientation `f`. -/
def vtx {A : Model F P J m} {n : ℕ} (f : Bool) (x : ℤ) (Q : ResiduePath A n)
    (j : Fin (n + 1)) : A.State :=
  (x + cond f (Q.offset j) (-Q.offset j), Q.labels j)

/-- The edge record of edge `i`. -/
def edgeOf {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n) (i : Fin n) : PathEdge A :=
  ⟨Q.sourcePerm i, Q.targetPerm i, Q.pattern i, Q.free i⟩

theorem pathDataHead_residuePathToPathData (A : Model F P J m) (n : ℕ)
    (Q : ResiduePath A n) :
    pathDataHead A n (residuePathToPathData A n Q) = Q.labels 0 := by
  cases n <;> rfl

theorem offset_succ_eq_step_sub_tail {A : Model F P J m} {n : ℕ}
    (Q : ResiduePath A (n + 1)) (j : Fin (n + 1)) :
    Q.offset j.succ = Q.step 0 - (residuePathTail Q).offset j := by
  simp only [ResiduePath.offset]
  rw [Fin.sum_univ_succ]
  have h : ∀ e : Fin n,
      (if e.succ.val < j.succ.val then Q.step e.succ else 0) =
        -(if e.val < j.val then (residuePathTail Q).step e else 0) := by
    intro e
    rw [residuePath_step_succ_eq_neg_tail]
    simp only [Fin.val_succ, Nat.add_lt_add_iff_right]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun e _ => h e), Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]

theorem pathEdgeDelta_head {A : Model F P J m} {n : ℕ} (Q : ResiduePath A (n + 1))
    (f : Bool) (x : ℤ) :
    pathEdgeDelta A f (x, Q.labels 0) (edgeOf Q 0) = cond f (Q.step 0) (-Q.step 0) := by
  cases f <;> simp [pathEdgeDelta, pathEdgeSource, edgeOf, ResiduePath.step,
    ResiduePath.source, edgeForward, edgeDelta]

theorem orient_zero (f : Bool) (n : ℕ) : orient f (0 : Fin (n + 1)) = f := by
  cases f <;> simp [orient, edgeForward]

theorem orient_succ (f : Bool) {n : ℕ} (i : Fin n) : orient f i.succ = orient (!f) i := by
  have h := edgeForward_succ_flip i
  have h2 : edgeForward i.castSucc = edgeForward i := by simp [edgeForward]
  cases f <;> simp [orient, h, h2]

theorem vtx_zero {A : Model F P J m} {n : ℕ} (f : Bool) (x : ℤ) (Q : ResiduePath A n) :
    vtx f x Q 0 = (x, Q.labels 0) := by
  cases f <;> simp [vtx, ResiduePath.offset_zero]

theorem vtx_tail {A : Model F P J m} {n : ℕ} (f : Bool) (x : ℤ)
    (Q : ResiduePath A (n + 1)) (j : Fin (n + 1)) :
    vtx (!f) (x + cond f (Q.step 0) (-Q.step 0)) (residuePathTail Q) j = vtx f x Q j.succ := by
  have h := offset_succ_eq_step_sub_tail Q j
  apply Prod.ext
  · cases f <;> simp [vtx, h] <;> ring
  · rfl

theorem kernelProduct_succ_unfold (A : Model F P J m) (n : ℕ) (Q : ResiduePath A (n + 1))
    (f : Bool) (x : ℤ) :
    pathDataKernelProduct A f (n + 1) (residuePathToPathData A (n + 1) Q) (x, Q.labels 0) =
      pathEdgeTerm A f (x, Q.labels 0)
          (x + pathEdgeDelta A f (x, Q.labels 0) (edgeOf Q 0), (residuePathTail Q).labels 0)
          (edgeOf Q 0) *
        pathDataKernelProduct A (!f) n (residuePathToPathData A n (residuePathTail Q))
          (x + pathEdgeDelta A f (x, Q.labels 0) (edgeOf Q 0), (residuePathTail Q).labels 0) := by
  rw [← pathDataHead_residuePathToPathData A n (residuePathTail Q)]
  simp only [residuePathToPathData, pathDataKernelProduct]
  rw [if_pos trivial]
  rfl

theorem kernelProduct_eq_prod (A : Model F P J m) :
    ∀ (n : ℕ) (Q : ResiduePath A n) (f : Bool) (x : ℤ),
      pathDataKernelProduct A f n (residuePathToPathData A n Q) (x, Q.labels 0) =
        ∏ i : Fin n, pathEdgeTerm A (orient f i) (vtx f x Q i.castSucc) (vtx f x Q i.succ)
          (edgeOf Q i)
  | 0, Q, f, x => by simp [pathDataKernelProduct]
  | n + 1, Q, f, x => by
      have ih := kernelProduct_eq_prod A n (residuePathTail Q) (!f)
        (x + cond f (Q.step 0) (-Q.step 0))
      rw [kernelProduct_succ_unfold, pathEdgeDelta_head]
      have hmid : ((x + cond f (Q.step 0) (-Q.step 0), (residuePathTail Q).labels 0) : A.State) =
          vtx f x Q (0 : Fin (n + 1)).succ := by
        rw [← vtx_tail, vtx_zero]
      rw [ih, Fin.prod_univ_succ, hmid, orient_zero, Fin.castSucc_zero, vtx_zero]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [orient_succ, vtx_tail, vtx_tail, Fin.succ_castSucc]
      rfl

theorem endState_eq_vtx (A : Model F P J m) :
    ∀ (n : ℕ) (Q : ResiduePath A n) (f : Bool) (x : ℤ),
      pathDataEndState A f n (residuePathToPathData A n Q) (x, Q.labels 0) =
        vtx f x Q (Fin.last n)
  | 0, Q, f, x => by
      rw [Fin.last_zero, vtx_zero]
      rfl
  | n + 1, Q, f, x => by
      have ih := endState_eq_vtx A n (residuePathTail Q) (!f)
        (x + cond f (Q.step 0) (-Q.step 0))
      have hu : pathDataEndState A f (n + 1) (residuePathToPathData A (n + 1) Q)
            (x, Q.labels 0) =
          pathDataEndState A (!f) n (residuePathToPathData A n (residuePathTail Q))
            (x + pathEdgeDelta A f (x, Q.labels 0) (edgeOf Q 0),
              (residuePathTail Q).labels 0) := by
        rw [← pathDataHead_residuePathToPathData A n (residuePathTail Q)]
        rfl
      rw [hu, pathEdgeDelta_head, ih, vtx_tail, Fin.succ_last]

/-! ### Termwise identification with the closed physical expression -/

/-- The physical condition at vertex `j` of the path started at `z`. -/
def vertexPhysical {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n) (z : ℤ)
    (j : Fin (n + 1)) : Prop :=
  P.physical (J + F.ell) (z + Q.offset j) (Q.labels j)

/-- Compatibility and ban condition of edge `i`. -/
def edgeAdmissible {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n) (i : Fin n) : Prop :=
  (A.pattern (Q.pattern i)).compatible (Q.source i) (Q.target i) ∧
    (A.pattern (Q.pattern i)).ban (Q.source i) (Q.target i) (Q.free i)

theorem physical_act_iff (M : ℕ) (x : ℤ) (π : P.Permutations M) (a : P.Labels M) :
    P.physical M x (P.act π a) ↔ P.physical M x a := by
  unfold PrimeGroups.physical PrimeGroups.act
  constructor
  · intro h g
    refine ⟨(Equiv.injective_comp (π g) (a g)).mp (h g).1, fun i => ?_⟩
    simpa using (h g).2 ((π g).symm i)
  · intro h g
    exact ⟨(h g).1.comp (π g).injective, fun i => (h g).2 (π g i)⟩

theorem pathEdgeTerm_vtx (A : Model F P J m) {n : ℕ} (Q : ResiduePath A n) (z : ℤ)
    (i : Fin n) :
    pathEdgeTerm A (orient true i) (vtx true z Q i.castSucc) (vtx true z Q i.succ)
        (edgeOf Q i) =
      if vertexPhysical Q z i.castSucc ∧ vertexPhysical Q z i.succ ∧ edgeAdmissible Q i then
        ((A.damping (z + Q.offset i.castSucc) * A.damping (z + Q.offset i.succ) : ℝ) : ℂ) *
          Q.edgeCoefficient 0 i
      else 0 := by
  have hstep : (vtx true z Q i.succ).1 = (vtx true z Q i.castSucc).1 +
      pathEdgeDelta A (orient true i) (vtx true z Q i.castSucc) (edgeOf Q i) := by
    show z + Q.offset i.succ = z + Q.offset i.castSucc + Q.step i
    rw [offset_step]
    ring
  have hvalid : pathEdgeValid A (orient true i) (vtx true z Q i.castSucc)
      (vtx true z Q i.succ) (edgeOf Q i) ↔
      vertexPhysical Q z i.castSucc ∧ vertexPhysical Q z i.succ ∧ edgeAdmissible Q i := by
    simp only [pathEdgeValid, ← hstep, and_true]
    exact and_congr (physical_act_iff _ _ _ _) (and_congr (physical_act_iff _ _ _ _) Iff.rfl)
  unfold pathEdgeTerm
  by_cases h : vertexPhysical Q z i.castSucc ∧ vertexPhysical Q z i.succ ∧ edgeAdmissible Q i
  · rw [if_pos (hvalid.mpr h), if_pos h]
    simp only [ResiduePath.edgeCoefficient, orient, Bool.cond_true, phase, zero_mul,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    by_cases hf : edgeForward i <;>
      simp [hf, pathEdgeSource, pathEdgeTarget, edgeOf, vtx, ResiduePath.source,
        ResiduePath.target] <;> ring
  · rw [if_neg (mt hvalid.mp h), if_neg h]

theorem prod_pathEdgeTerm_vtx (A : Model F P J m) {n : ℕ} (Q : ResiduePath A n) (z : ℤ) :
    ∏ i : Fin n, pathEdgeTerm A (orient true i) (vtx true z Q i.castSucc)
        (vtx true z Q i.succ) (edgeOf Q i) =
      if ∀ i : Fin n, vertexPhysical Q z i.castSucc ∧ vertexPhysical Q z i.succ ∧
          edgeAdmissible Q i then
        ((∏ i : Fin n, A.damping (z + Q.offset i.castSucc) *
            A.damping (z + Q.offset i.succ) : ℝ) : ℂ) * ∏ i : Fin n, Q.edgeCoefficient 0 i
      else 0 := by
  simp_rw [pathEdgeTerm_vtx]
  by_cases h : ∀ i : Fin n, vertexPhysical Q z i.castSucc ∧ vertexPhysical Q z i.succ ∧
      edgeAdmissible Q i
  · rw [if_pos h, Finset.prod_congr rfl (fun i _ => if_pos (h i)), Finset.prod_mul_distrib,
      Complex.ofReal_prod]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem active_card_eq {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n) (j : Fin (n + 1))
    (hinj : ∀ g, Function.Injective (Q.labels j g)) :
    (Q.active j).card = (J + F.ell) * P.count := by
  unfold ResiduePath.active
  rw [Finset.card_biUnion]
  · have hc : ∀ g : P.Group,
        (Finset.univ.image (fun h => (Q.labels j g h).val)).card = J + F.ell := by
      intro g
      have hi : Function.Injective (fun h => (Q.labels j g h).val) :=
        fun a b hab => hinj g (Subtype.ext hab)
      rw [Finset.card_image_of_injective _ hi]
      simp
    simp [hc, PrimeGroups.Group, Nat.mul_comm]
  · intro g _ h _ hgh
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hp'
    exact hgh (prime_group_eq (Q.labels j h b) (Q.labels j g a) hb).symm

theorem omega_eq_card (x : ℤ) :
    P.omega x = (P.allPrimes.filter (fun p : ℕ => (p : ℤ) ∣ x)).card := by
  unfold PrimeGroups.omega PrimeGroups.omegaGroup PrimeGroups.allPrimes
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro g _ h _ hgh
  exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) (P.disjoint g h hgh)

theorem active_dvd {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n) (z : ℤ)
    (j : Fin (n + 1)) (hV : vertexPhysical Q z j) {p : ℕ} (hp : p ∈ Q.active j) :
    (p : ℤ) ∣ z + Q.offset j := by
  unfold ResiduePath.active at hp
  obtain ⟨g, _, hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hp
  exact (hV g).2 h

/-- Number of unmarked group primes dividing the position of vertex `j`. -/
def extraCount {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n) (z : ℤ)
    (j : Fin (n + 1)) : ℕ :=
  ((P.allPrimes.filter (fun p : ℕ => (p : ℤ) ∣ z + Q.offset j)).filter
    (fun p => p ∉ Q.active j)).card

theorem damping_eq_sqrt_pow (A : Model F P J m) {n : ℕ} (Q : ResiduePath A n) (z : ℤ)
    (j : Fin (n + 1)) (hV : vertexPhysical Q z j) :
    A.damping (z + Q.offset j) = Real.sqrt F.q ^ extraCount Q z j := by
  have hcard : (P.omega (z + Q.offset j) : ℝ) - (J + F.ell) * P.count =
      extraCount Q z j := by
    rw [omega_eq_card]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := P.allPrimes.filter (fun p : ℕ => (p : ℤ) ∣ z + Q.offset j))
      (fun p => p ∈ Q.active j)
    have hact : (P.allPrimes.filter (fun p : ℕ => (p : ℤ) ∣ z + Q.offset j)).filter
        (fun p => p ∈ Q.active j) = Q.active j := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact h.2
      · intro hp
        exact ⟨⟨Q.active_subset j hp, active_dvd Q z j hV hp⟩, hp⟩
    rw [hact, active_card_eq Q j (fun g => (hV g).1)] at hsplit
    unfold extraCount
    rw [← hsplit]
    push_cast
    ring
  unfold Model.damping
  rw [hcard, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul F.q_pos.le]
  ring_nf

theorem vertexFactor_eq {A : Model F P J m} {n : ℕ} (Q : ResiduePath A n) (z : ℤ)
    (j : Fin (n + 1)) (hV : vertexPhysical Q z j) (c : ℝ) :
    ∏ p ∈ P.allPrimes, (if p ∈ Q.active j then (if (p : ℤ) ∣ z + Q.offset j then 1 else 0)
      else if (p : ℤ) ∣ z + Q.offset j then c else 1) = c ^ extraCount Q z j := by
  unfold extraCount
  rw [← Finset.prod_const, Finset.prod_filter, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _
  by_cases ha : p ∈ Q.active j
  · simp [ha, active_dvd Q z j hV ha]
  · by_cases hd : (p : ℤ) ∣ z + Q.offset j <;> simp [ha, hd]

theorem damping_prod_eq_pathFactor (A : Model F P J m) {n : ℕ} (Q : ResiduePath A (n + 1))
    (z : ℤ) (hV : ∀ j, vertexPhysical Q z j) :
    ∏ i : Fin (n + 1), A.damping (z + Q.offset i.castSucc) * A.damping (z + Q.offset i.succ) =
      P.pathFactor (n + 1) (visitQ F.q (n + 1)) Q.offset Q.active z := by
  let a : Fin (n + 2) → ℝ := fun j => A.damping (z + Q.offset j)
  have h1 : ∏ i : Fin (n + 1), a i.castSucc =
      ∏ j : Fin (n + 2), a j ^ (if j = Fin.last (n + 1) then 0 else 1) := by
    rw [Fin.prod_univ_castSucc (fun j => a j ^ (if j = Fin.last (n + 1) then 0 else 1))]
    simp [Fin.castSucc_lt_last, ne_of_lt]
  have h2 : ∏ i : Fin (n + 1), a i.succ =
      ∏ j : Fin (n + 2), a j ^ (if j = 0 then 0 else 1) := by
    rw [Fin.prod_univ_succ (fun j => a j ^ (if j = 0 then 0 else 1))]
    simp
  rw [Finset.prod_mul_distrib]
  change (∏ i : Fin (n + 1), a i.castSucc) * (∏ i : Fin (n + 1), a i.succ) = _
  rw [h1, h2, ← Finset.prod_mul_distrib]
  unfold PrimeGroups.pathFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [vertexFactor_eq Q z j (hV j)]
  change A.damping (z + Q.offset j) ^ _ * A.damping (z + Q.offset j) ^ _ = _
  rw [damping_eq_sqrt_pow A Q z j (hV j)]
  unfold visitQ
  by_cases h0 : j = 0
  · subst h0
    have hl : (0 : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [hl]
  · by_cases hl : j = Fin.last (n + 1)
    · subst hl
      simp [h0]
    · have hv : ¬ (j.val = 0 ∨ j.val = n + 1) := by
        rintro (h | h)
        · exact h0 (Fin.ext h)
        · exact hl (Fin.ext h)
      rw [if_neg hv, if_neg h0, if_neg hl]
      simp only [pow_one]
      rw [← mul_pow, Real.mul_self_sqrt F.q_pos.le]

theorem term_eq_succ (A : Model F P J m) {n : ℕ} (Q : ResiduePath A (n + 1)) (z : ℤ) :
    (A.stateMass (z, Q.labels 0) : ℂ) *
      (if (vtx true z Q (Fin.last (n + 1))).1 = z then
        ∏ i : Fin (n + 1), pathEdgeTerm A (orient true i) (vtx true z Q i.castSucc)
          (vtx true z Q i.succ) (edgeOf Q i)
      else 0) =
    if Q.Valid ∧ Q.offset (Fin.last (n + 1)) = 0 then
      (P.markMass (J + F.ell) : ℂ) * (∏ i, Q.edgeCoefficient 0 i) *
        (P.pathFactor (n + 1) (visitQ F.q (n + 1)) Q.offset Q.active z : ℂ)
    else 0 := by
  have hend : (vtx true z Q (Fin.last (n + 1))).1 = z ↔ Q.offset (Fin.last (n + 1)) = 0 := by
    show z + Q.offset _ = z ↔ _
    omega
  rw [prod_pathEdgeTerm_vtx]
  by_cases ho : Q.offset (Fin.last (n + 1)) = 0
  swap
  · rw [if_neg (mt hend.mp ho), if_neg (fun h => ho h.2), mul_zero]
  rw [if_pos (hend.mpr ho)]
  have hcover : (∀ i : Fin (n + 1), vertexPhysical Q z i.castSucc ∧
      vertexPhysical Q z i.succ) → ∀ j, vertexPhysical Q z j := by
    intro h j
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact (h i).1
    · rw [← Fin.succ_last]
      exact (h (Fin.last n)).2
  by_cases hV : ∀ j, vertexPhysical Q z j
  · have hmass : A.stateMass (z, Q.labels 0) = P.markMass (J + F.ell) := by
      unfold Model.stateMass
      rw [if_pos]
      simpa [vertexPhysical, ResiduePath.offset_zero] using hV 0
    have hvalid : Q.Valid ↔ ∀ i, edgeAdmissible Q i := by
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨fun j g => (hV j g).1, h⟩
    by_cases hE : ∀ i, edgeAdmissible Q i
    · rw [if_pos (fun i => ⟨hV _, hV _, hE i⟩), if_pos ⟨hvalid.mpr hE, ho⟩, hmass,
        damping_prod_eq_pathFactor A Q z hV]
      ring
    · rw [if_neg (fun h => hE (fun i => (h i).2.2)), if_neg (fun h => hE (hvalid.mp h.1)),
        mul_zero]
  · rw [if_neg (fun h => hV (hcover (fun i => ⟨(h i).1, (h i).2.1⟩))), mul_zero]
    by_cases hQ : Q.Valid
    · rw [if_pos ⟨hQ, ho⟩]
      obtain ⟨j, hj⟩ := not_forall.mp hV
      have hex : ∃ g h, ¬ ((Q.labels j g h).val : ℤ) ∣ z + Q.offset j := by
        by_contra hc
        push_neg at hc
        exact hj (fun g => ⟨hQ.1 j g, hc g⟩)
      obtain ⟨g, h, hnd⟩ := hex
      have hzero : P.pathFactor (n + 1) (visitQ F.q (n + 1)) Q.offset Q.active z = 0 := by
        unfold PrimeGroups.pathFactor
        apply Finset.prod_eq_zero (i := (Q.labels j g h).val)
        · exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, (Q.labels j g h).property⟩
        · apply Finset.prod_eq_zero (i := j) (Finset.mem_univ _)
          have hmem : (Q.labels j g h).val ∈ Q.active j :=
            Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _,
              Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩⟩
          rw [if_pos hmem, if_neg hnd]
      rw [hzero]
      simp
    · rw [if_neg (fun h => hQ h.1)]

theorem term_eq (A : Model F P J m) {n : ℕ} (hn : 0 < n) (Q : ResiduePath A n) (z : ℤ) :
    (A.stateMass (z, pathDataHead A n (residuePathToPathData A n Q)) : ℂ) *
      (if (pathDataEndState A true n (residuePathToPathData A n Q)
            (z, pathDataHead A n (residuePathToPathData A n Q))).1 = z then
        pathDataKernelProduct A true n (residuePathToPathData A n Q)
          (z, pathDataHead A n (residuePathToPathData A n Q))
      else 0) =
    if Q.Valid ∧ Q.offset (Fin.last n) = 0 then
      (P.markMass (J + F.ell) : ℂ) * (∏ i, Q.edgeCoefficient 0 i) *
        (P.pathFactor n (visitQ F.q n) Q.offset Q.active z : ℂ)
    else 0 := by
  rw [pathDataHead_residuePathToPathData, endState_eq_vtx, kernelProduct_eq_prod]
  cases n with
  | zero => omega
  | succ n => exact term_eq_succ A Q z

theorem rootMoment_complex_eq (A : Model F P J m) (r : ℕ) (hr : 0 < r) (z : ℤ) :
    (∑ a : A.Labels, ∑ b : A.Labels, (A.stateMass (z, a) : ℂ) *
      kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) r (z, a) (z, b)) =
      closedPhysicalExpression A (2 * r) z := by
  have hkp : ∀ s t : A.State,
      kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) r s t =
        ∑ d : PathData A (2 * r), pathDataKernelTerm A true (2 * r) d s t :=
    pairedKernelPower_eq_pathData A r
  simp_rw [hkp]
  calc
    _ = ∑ a : A.Labels, ∑ d : PathData A (2 * r), ∑ b : A.Labels,
          (A.stateMass (z, a) : ℂ) * pathDataKernelTerm A true (2 * r) d (z, a) (z, b) := by
        apply Finset.sum_congr rfl
        intro a _
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ d : PathData A (2 * r), ∑ a : A.Labels, ∑ b : A.Labels,
          (A.stateMass (z, a) : ℂ) * pathDataKernelTerm A true (2 * r) d (z, a) (z, b) :=
        Finset.sum_comm
    _ = ∑ d : PathData A (2 * r), ∑ a : A.Labels, (A.stateMass (z, a) : ℂ) *
          ∑ b : A.Labels, pathDataKernelTerm A true (2 * r) d (z, a) (z, b) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ d : PathData A (2 * r),
          (A.stateMass (z, pathDataHead A (2 * r) d) : ℂ) *
            (if (pathDataEndState A true (2 * r) d (z, pathDataHead A (2 * r) d)).1 = z then
              pathDataKernelProduct A true (2 * r) d (z, pathDataHead A (2 * r) d)
            else 0) := by
        apply Finset.sum_congr rfl
        intro d _
        exact pathDataKernelTerm_sum_over_both_labels A true (2 * r) d z
    _ = ∑ Q : ResiduePath A (2 * r),
          (A.stateMass (z, pathDataHead A (2 * r) (residuePathToPathData A (2 * r) Q)) : ℂ) *
            (if (pathDataEndState A true (2 * r) (residuePathToPathData A (2 * r) Q)
                  (z, pathDataHead A (2 * r) (residuePathToPathData A (2 * r) Q))).1 = z then
              pathDataKernelProduct A true (2 * r) (residuePathToPathData A (2 * r) Q)
                (z, pathDataHead A (2 * r) (residuePathToPathData A (2 * r) Q))
            else 0) :=
        (Equiv.sum_comp (pathDataEquivResiduePath A (2 * r)).symm
          (fun d => (A.stateMass (z, pathDataHead A (2 * r) d) : ℂ) *
            (if (pathDataEndState A true (2 * r) d (z, pathDataHead A (2 * r) d)).1 = z then
              pathDataKernelProduct A true (2 * r) d (z, pathDataHead A (2 * r) d)
            else 0))).symm
    _ = closedPhysicalExpression A (2 * r) z := by
        unfold closedPhysicalExpression
        apply Finset.sum_congr rfl
        intro Q _
        exact term_eq A (by omega) Q z

end Erdos821.P3Phys

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

theorem PhysicalPathExpansionTask_proof : PhysicalPathExpansionTask := by
  intro F P J m r A hr z
  unfold Model.rootMoment
  rw [Erdos821.P3Phys.rootMoment_complex_eq A r hr z]

example : PhysicalPathExpansionTask := PhysicalPathExpansionTask_proof


end Erdos821.S2Core
