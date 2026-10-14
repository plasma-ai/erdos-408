import Erdos821.S2.PhysicalPathTask
import Erdos821.S2.PhysicalCompatibility

/-! Finite physical path expansion for the literal root moment. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Phys

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem offset_step {A : Model F P J m} {n : ℕ}
    (Q : ResiduePath A n) (i : Fin n) :
    Q.offset i.succ = Q.offset i.castSucc + Q.step i := by
  classical
  simp only [ResiduePath.offset, ResiduePath.step]
  have hsum :
      (∑ e : Fin n, if e.val < i.succ.val then Q.step e else 0) =
        (∑ e : Fin n, if e.val < i.castSucc.val then Q.step e else 0) + Q.step i := by
    have hsplit (e : Fin n) :
        (if e.val < i.succ.val then Q.step e else 0) =
          (if e.val < i.castSucc.val then Q.step e else 0) +
            (if e = i then Q.step e else 0) := by
      have hs : i.succ.val = i.val + 1 := by simp
      have hc : i.castSucc.val = i.val := by simp
      rw [hs, hc]
      by_cases heq : e = i
      · subst e
        simp
      · by_cases hlt : e.val < i.val
        · have hlt' : e.val < i.val + 1 := by omega
          simp [hlt, hlt', heq]
        · have hnot : ¬ e.val < i.val + 1 := by omega
          simp [hlt, heq, hnot]
    calc
      _ = ∑ e : Fin n,
          ((if e.val < i.castSucc.val then Q.step e else 0) +
            (if e = i then Q.step e else 0)) := by
            apply Finset.sum_congr rfl
            intro e he
            exact hsplit e
      _ = (∑ e : Fin n, if e.val < i.castSucc.val then Q.step e else 0) +
          ∑ e : Fin n, if e = i then Q.step e else 0 := Finset.sum_add_distrib
      _ = _ := by simp
  exact hsum

theorem edgeForward_succ_flip {n : ℕ} (i : Fin n) :
    edgeForward i.succ = !(edgeForward i.castSucc) := by
  unfold edgeForward
  simp only [Fin.val_succ, Fin.val_castSucc]
  have hmod : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hmod with h | h <;> simp [h, Nat.add_mod]

theorem residuePath_step_sum_eq_head_add_tail {A : Model F P J m} {n : ℕ}
    (Q : ResiduePath A (n + 1)) :
    (∑ i : Fin (n + 1), Q.step i) =
      Q.step 0 + ∑ i : Fin n, Q.step i.succ := by
  simpa using (Fin.sum_univ_succ Q.step)

def oneStepDisplacements (A : Model F P J m) : Finset ℤ :=
  Finset.univ.image fun c : Fin A.patternCount × (A.Labels × P.Aux J) =>
    A.k * ((A.pattern c.1).D c.2.1 c.2.2 : ℤ)

def stepRadius (A : Model F P J m) : ℕ :=
  (oneStepDisplacements A).sup Int.natAbs

theorem displacement_mem_oneStepDisplacements (A : Model F P J m)
    (v : Fin A.patternCount) (a : A.Labels) (u : P.Aux J) :
    A.k * ((A.pattern v).D a u : ℤ) ∈ oneStepDisplacements A := by
  apply Finset.mem_image.mpr
  exact ⟨(v, (a, u)), Finset.mem_univ _, rfl⟩

theorem physicalKernel_false_zero_of_not_oneStepDisplacement
    (A : Model F P J m) (s t : A.State)
    (h : t.1 - s.1 ∉ oneStepDisplacements A) :
    A.physicalKernel false s t = 0 := by
  classical
  have hraw (π τ : P.Permutations (J + F.ell)) :
      A.physicalRaw false (s.1, P.act π s.2) (t.1, P.act τ t.2) = 0 := by
    unfold Model.physicalRaw
    by_cases hphys : P.physical (J + F.ell) s.1 (P.act π s.2) ∧
        P.physical (J + F.ell) t.1 (P.act τ t.2)
    · rw [if_pos hphys]
      apply Finset.sum_eq_zero
      intro v hv
      apply Finset.sum_eq_zero
      intro u hu
      by_cases hcond : (A.pattern v).compatible (P.act π s.2) (P.act τ t.2) ∧
          (A.pattern v).ban (P.act π s.2) (P.act τ t.2) u ∧
          t.1 = s.1 + A.k * ((A.pattern v).D (P.act π s.2) u : ℤ)
      · have hmem : t.1 - s.1 ∈ oneStepDisplacements A := by
          apply Finset.mem_image.mpr
          refine ⟨(v, (P.act π s.2, u)), Finset.mem_univ _, ?_⟩
          rw [hcond.2.2]
          ring
        exact False.elim (h hmem)
      · simp [hcond]
    · simp [hphys]
  simp [Model.physicalKernel, hraw]

theorem stepRadius_mem (A : Model F P J m) {d : ℤ}
    (hd : d ∈ oneStepDisplacements A) : Int.natAbs d ≤ stepRadius A := by
  exact Finset.le_sup (s := oneStepDisplacements A) (f := Int.natAbs) (b := d) hd

theorem physicalKernel_false_zero_of_stepRadius_lt
    (A : Model F P J m) (s t : A.State)
    (h : stepRadius A < Int.natAbs (t.1 - s.1)) :
    A.physicalKernel false s t = 0 := by
  apply physicalKernel_false_zero_of_not_oneStepDisplacement A s t
  intro hmem
  have hbound := stepRadius_mem A hmem
  omega

theorem physicalKernel_false_time_bound (A : Model F P J m) (s t : A.State)
    (h : A.physicalKernel false s t ≠ 0) :
    Int.natAbs (t.1 - s.1) ≤ stepRadius A := by
  by_contra hbound
  have hz := physicalKernel_false_zero_of_stepRadius_lt A s t (by omega)
  exact h hz

def pairedKernel (A : Model F P J m) : A.State → A.State → ℂ :=
  kernelComp (A.physicalKernel false) A.adjointKernel

def pairRadius (A : Model F P J m) : ℕ := 2 * stepRadius A

def pairNeighbors (A : Model F P J m) (s : A.State) : Finset A.State :=
  (Finset.Icc (s.1 - (pairRadius A : ℤ)) (s.1 + (pairRadius A : ℤ))).product Finset.univ

theorem pairedKernel_zero_of_pairRadius_lt (A : Model F P J m)
    (s t : A.State) (h : pairRadius A < Int.natAbs (t.1 - s.1)) :
    pairedKernel A s t = 0 := by
  classical
  unfold pairedKernel kernelComp
  have hzero : (fun z : A.State =>
      A.physicalKernel false s z * A.adjointKernel z t) = 0 := by
    funext z
    change A.physicalKernel false s z * A.adjointKernel z t = 0
    by_cases hs : A.physicalKernel false s z = 0
    · simp [hs]
    · by_cases ht : A.physicalKernel false t z = 0
      · simp [Model.adjointKernel, ht]
      · have hsNat := physicalKernel_false_time_bound A s z hs
        have htNat := physicalKernel_false_time_bound A t z ht
        have hsCast : (Int.natAbs (z.1 - s.1) : ℤ) ≤ (stepRadius A : ℤ) := by
          exact_mod_cast hsNat
        have htCast : (Int.natAbs (z.1 - t.1) : ℤ) ≤ (stepRadius A : ℤ) := by
          exact_mod_cast htNat
        have hsAbs : |z.1 - s.1| ≤ (stepRadius A : ℤ) := by
          simpa only [Int.natCast_natAbs] using hsCast
        have htAbs : |z.1 - t.1| ≤ (stepRadius A : ℤ) := by
          simpa only [Int.natCast_natAbs] using htCast
        have htAbs' : |t.1 - z.1| ≤ (stepRadius A : ℤ) := by
          simpa only [abs_sub_comm] using htAbs
        have htriangle : |t.1 - s.1| ≤ (pairRadius A : ℤ) := by
          calc
            |t.1 - s.1| = |(t.1 - z.1) + (z.1 - s.1)| := by congr 1 <;> ring
            _ ≤ |t.1 - z.1| + |z.1 - s.1| := abs_add_le _ _
            _ ≤ (stepRadius A : ℤ) + (stepRadius A : ℤ) := add_le_add htAbs' hsAbs
            _ = (pairRadius A : ℤ) := by simp [pairRadius, Nat.cast_mul]; ring
        have hnat : Int.natAbs (t.1 - s.1) ≤ pairRadius A := by
          have hcast : (Int.natAbs (t.1 - s.1) : ℤ) ≤ (pairRadius A : ℤ) := by
            simpa only [Int.natCast_natAbs] using htriangle
          exact_mod_cast hcast
        omega
  rw [hzero]
  exact tsum_zero

theorem pairedKernel_zero_of_not_pairNeighbor (A : Model F P J m)
    (s t : A.State) (h : t ∉ pairNeighbors A s) : pairedKernel A s t = 0 := by
  have hnot : ¬ |t.1 - s.1| ≤ (pairRadius A : ℤ) := by
    intro hc
    apply h
    have hc' := abs_le.mp hc
    change t ∈ (Finset.Icc (s.1 - (pairRadius A : ℤ))
      (s.1 + (pairRadius A : ℤ))).product Finset.univ
    apply Finset.mem_product.mpr
    constructor
    · simp only [Finset.mem_Icc]
      constructor <;> omega
    · exact Finset.mem_univ _
  have hcast : ¬ (Int.natAbs (t.1 - s.1) : ℤ) ≤ (pairRadius A : ℤ) := by
    simpa only [Int.natCast_natAbs] using hnot
  have hgt : pairRadius A < Int.natAbs (t.1 - s.1) := by omega
  exact pairedKernel_zero_of_pairRadius_lt A s t hgt

theorem pairedKernel_comp_eq_sum_pairNeighbors (A : Model F P J m)
    (H : A.State → A.State → ℂ) (s t : A.State) :
    kernelComp (pairedKernel A) H s t =
      ∑ z ∈ pairNeighbors A s, pairedKernel A s z * H z t := by
  unfold kernelComp
  apply tsum_eq_sum
  intro z hz
  simp [pairedKernel_zero_of_not_pairNeighbor A s z hz]

def pathRadius (A : Model F P J m) (n : ℕ) : ℕ := n * pairRadius A

def pathWindow (A : Model F P J m) (root : ℤ) (n : ℕ) : Finset A.State :=
  (Finset.Icc (root - (pathRadius A n : ℤ)) (root + (pathRadius A n : ℤ))).product
    Finset.univ

theorem pairNeighbors_time_bound (A : Model F P J m) (s t : A.State)
    (ht : t ∈ pairNeighbors A s) : |t.1 - s.1| ≤ (pairRadius A : ℤ) := by
  have ht' := Finset.mem_product.mp ht
  have ht'' := Finset.mem_Icc.mp ht'.1
  apply abs_le.mpr
  constructor <;> omega

theorem mem_pathWindow_of_time_bound (A : Model F P J m) (root : ℤ) (n : ℕ)
    (s : A.State) (hs : |s.1 - root| ≤ (pathRadius A n : ℤ)) :
    s ∈ pathWindow A root n := by
  have hs' := abs_le.mp hs
  apply Finset.mem_product.mpr
  constructor
  · simp only [Finset.mem_Icc]
    constructor <;> omega
  · exact Finset.mem_univ _

theorem pairNeighbor_close_trans (A : Model F P J m) (root : ℤ) (k : ℕ)
    (s t : A.State) (ht : t ∈ pairNeighbors A s)
    (hs : |s.1 - root| ≤ (pathRadius A k : ℤ)) :
    |t.1 - root| ≤ (pathRadius A (k + 1) : ℤ) := by
  have ht' := pairNeighbors_time_bound A s t ht
  have hradius : pathRadius A (k + 1) = pathRadius A k + pairRadius A := by
    simp [pathRadius, Nat.succ_mul]
  calc
    |t.1 - root| = |(t.1 - s.1) + (s.1 - root)| := by congr 1 <;> ring
    _ ≤ |t.1 - s.1| + |s.1 - root| := abs_add_le _ _
    _ ≤ (pairRadius A : ℤ) + (pathRadius A k : ℤ) := add_le_add ht' hs
    _ = (pathRadius A (k + 1) : ℤ) := by rw [hradius, Nat.cast_add]; ring

theorem pairNeighbors_subset_pathWindow (A : Model F P J m) (root : ℤ)
    (R k : ℕ) (hk : k + 1 ≤ R) (s : A.State)
    (hs : |s.1 - root| ≤ (pathRadius A k : ℤ)) :
    pairNeighbors A s ⊆ pathWindow A root R := by
  intro t ht
  apply mem_pathWindow_of_time_bound
  calc
    |t.1 - root| ≤ (pathRadius A (k + 1) : ℤ) := pairNeighbor_close_trans A root k s t ht hs
    _ ≤ (pathRadius A R : ℤ) := by
      have h := Nat.mul_le_mul_right (pairRadius A) hk
      exact_mod_cast h

private def finiteKernelPower {α : Type*} (K : α → α → ℂ) (S : Finset α) :
    ℕ → α → α → ℂ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, b => ∑ z ∈ S, K a z * finiteKernelPower K S n z b

theorem pairedKernelPower_eq_finiteWindow (A : Model F P J m) (root : ℤ)
    (R n k : ℕ) (hk : k + n ≤ R) (a b : A.State)
    (ha : |a.1 - root| ≤ (pathRadius A k : ℤ)) :
    kernelPower (pairedKernel A) n a b =
      finiteKernelPower (pairedKernel A) (pathWindow A root R) n a b := by
  classical
  induction n generalizing k a with
  | zero => rfl
  | succ n ih =>
      change kernelComp (pairedKernel A) (kernelPower (pairedKernel A) n) a b = _
      have hk1 : k + 1 ≤ R := by omega
      have hsubset : pairNeighbors A a ⊆ pathWindow A root R :=
        pairNeighbors_subset_pathWindow A root R k hk1 a ha
      calc
        kernelComp (pairedKernel A) (kernelPower (pairedKernel A) n) a b =
            ∑ z ∈ pairNeighbors A a,
              pairedKernel A a z * kernelPower (pairedKernel A) n z b :=
          pairedKernel_comp_eq_sum_pairNeighbors A (kernelPower (pairedKernel A) n) a b
        _ = ∑ z ∈ pairNeighbors A a,
              pairedKernel A a z * finiteKernelPower (pairedKernel A)
                (pathWindow A root R) n z b := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [ih (k + 1) (by omega) z (pairNeighbor_close_trans A root k a z hz ha)]
        _ = ∑ z ∈ pathWindow A root R,
              pairedKernel A a z * finiteKernelPower (pairedKernel A)
                (pathWindow A root R) n z b := by
          apply Finset.sum_subset hsubset
          intro z hz hznot
          simp [pairedKernel_zero_of_not_pairNeighbor A a z hznot]
        _ = finiteKernelPower (pairedKernel A) (pathWindow A root R) (n + 1) a b := rfl

structure PathEdge (A : Model F P J m) where
  sourcePerm : P.Permutations (J + F.ell)
  targetPerm : P.Permutations (J + F.ell)
  pattern : Fin A.patternCount
  free : P.Aux J

noncomputable instance pathEdgeFintype (A : Model F P J m) : Fintype (PathEdge A) := by
  classical
  exact Fintype.ofEquiv
    (P.Permutations (J + F.ell) × P.Permutations (J + F.ell) ×
      Fin A.patternCount × P.Aux J)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun e => (e.sourcePerm, e.targetPerm, e.pattern, e.free)
      left_inv := by intro x; rcases x with ⟨a, b, c, d⟩; rfl
      right_inv := by intro e; cases e; rfl }

def pathEdgeEquivProduct (A : Model F P J m) :
    PathEdge A ≃ P.Permutations (J + F.ell) × P.Permutations (J + F.ell) ×
      Fin A.patternCount × P.Aux J where
  toFun e := (e.sourcePerm, e.targetPerm, e.pattern, e.free)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv e := by cases e; rfl
  right_inv x := by rcases x with ⟨a, b, c, d⟩; rfl

theorem pathEdge_sum_eq_product (A : Model F P J m) (f : PathEdge A → ℂ) :
    (∑ e : PathEdge A, f e) =
      ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
        ∑ v : Fin A.patternCount, ∑ u : P.Aux J, f ⟨π, τ, v, u⟩ := by
  classical
  rw [show (∑ e : PathEdge A, f e) =
      ∑ x : P.Permutations (J + F.ell) × P.Permutations (J + F.ell) ×
        Fin A.patternCount × P.Aux J, f ((pathEdgeEquivProduct A).symm x) by
        exact (Equiv.sum_comp (pathEdgeEquivProduct A).symm f).symm]
  simp only [Fintype.sum_prod_type]
  rfl

def pathEdgeSource (A : Model F P J m) (s : A.State) (e : PathEdge A) : A.Labels :=
  P.act e.sourcePerm s.2

def pathEdgeTarget (A : Model F P J m) (t : A.State) (e : PathEdge A) : A.Labels :=
  P.act e.targetPerm t.2

def pathEdgeDelta (A : Model F P J m) (forward : Bool) (s : A.State) (e : PathEdge A) : ℤ :=
  edgeDelta A (A.pattern e.pattern) forward (pathEdgeSource A s e) e.free

def pathEdgeValid (A : Model F P J m) (forward : Bool) (s t : A.State)
    (e : PathEdge A) : Prop :=
  P.physical (J + F.ell) s.1 (pathEdgeSource A s e) ∧
  P.physical (J + F.ell) t.1 (pathEdgeTarget A t e) ∧
  (A.pattern e.pattern).compatible (pathEdgeSource A s e) (pathEdgeTarget A t e) ∧
  (A.pattern e.pattern).ban (pathEdgeSource A s e) (pathEdgeTarget A t e) e.free ∧
  t.1 = s.1 + pathEdgeDelta A forward s e

def pathEdgeCoefficient (A : Model F P J m) (forward : Bool) (s t : A.State)
    (e : PathEdge A) : ℂ :=
  let ν := A.pattern e.pattern
  let a := pathEdgeSource A s e
  let b := pathEdgeTarget A t e
  let uBig : P.BigAux J := fun g => e.free g.val
  let D := ν.D a e.free
  let z := ν.coefficient (P.restrictBig a) (P.restrictBig b) uBig *
    imaginaryPower D A.zeta
  let zr := star (ν.coefficient (P.restrictBig b) (P.restrictBig a) uBig *
    imaginaryPower D A.zeta)
  ((edgeSymmetryFactor P (J + F.ell) * ν.auxMass e.free * ν.physicalTargetMass : ℝ) : ℂ) *
    (if forward then z else zr)

def pathEdgeTerm (A : Model F P J m) (forward : Bool) (s t : A.State)
    (e : PathEdge A) : ℂ :=
  if pathEdgeValid A forward s t e then
    ((edgeSymmetryFactor P (J + F.ell) * (A.pattern e.pattern).auxMass e.free *
      (A.pattern e.pattern).physicalTargetMass * A.damping s.1 * A.damping t.1 : ℝ) : ℂ) *
      (if forward then
        (A.pattern e.pattern).coefficient
          (P.restrictBig (pathEdgeSource A s e)) (P.restrictBig (pathEdgeTarget A t e))
          (fun g => e.free g.val) *
            imaginaryPower ((A.pattern e.pattern).D (pathEdgeSource A s e) e.free) A.zeta
       else
        star ((A.pattern e.pattern).coefficient
          (P.restrictBig (pathEdgeTarget A t e)) (P.restrictBig (pathEdgeSource A s e))
          (fun g => e.free g.val) *
            imaginaryPower ((A.pattern e.pattern).D (pathEdgeSource A s e) e.free) A.zeta))
  else 0

def pathEdgeSwapEquiv (A : Model F P J m) : PathEdge A ≃ PathEdge A where
  toFun e := ⟨e.targetPerm, e.sourcePerm, e.pattern, e.free⟩
  invFun e := ⟨e.targetPerm, e.sourcePerm, e.pattern, e.free⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

theorem pathEdgeValid_swap (A : Model F P J m) (s t : A.State) (e : PathEdge A) :
    pathEdgeValid A true t s ((pathEdgeSwapEquiv A) e) ↔
      pathEdgeValid A false s t e := by
  classical
  let ν := A.pattern e.pattern
  let a := pathEdgeSource A s e
  let b := pathEdgeTarget A t e
  constructor
  · intro h
    change P.physical (J + F.ell) t.1 b ∧ P.physical (J + F.ell) s.1 a ∧
      ν.compatible b a ∧ ν.ban b a e.free ∧
      s.1 = t.1 + A.k * (ν.D b e.free : ℤ) at h
    have hcomp : ν.compatible a b := by
      intro g i hi
      exact (h.2.2.1 g i hi).symm
    have hban : ν.ban a b e.free := by
      intro g i hi j
      exact ⟨(h.2.2.2.1 g i hi j).2, (h.2.2.2.1 g i hi j).1⟩
    have hD := compatible_D_eq ν a b e.free hcomp
    refine ⟨h.2.1, h.1, hcomp, hban, ?_⟩
    rw [← hD] at h
    change t.1 = s.1 + -(A.k * (ν.D a e.free : ℤ))
    omega
  · intro h
    change P.physical (J + F.ell) s.1 a ∧ P.physical (J + F.ell) t.1 b ∧
      ν.compatible a b ∧ ν.ban a b e.free ∧
      t.1 = s.1 + -(A.k * (ν.D a e.free : ℤ)) at h
    have hcomp : ν.compatible b a := by
      intro g i hi
      exact (h.2.2.1 g i hi).symm
    have hban : ν.ban b a e.free := by
      intro g i hi j
      exact ⟨(h.2.2.2.1 g i hi j).2, (h.2.2.2.1 g i hi j).1⟩
    have hD := compatible_D_eq ν b a e.free hcomp
    refine ⟨h.2.1, h.1, hcomp, hban, ?_⟩
    change s.1 = t.1 + A.k * (ν.D b e.free : ℤ)
    rw [hD]
    omega

theorem pathEdgeTerm_swap (A : Model F P J m) (s t : A.State) (e : PathEdge A) :
    star (pathEdgeTerm A true t s ((pathEdgeSwapEquiv A) e)) =
      pathEdgeTerm A false s t e := by
  classical
  let ν := A.pattern e.pattern
  let a := pathEdgeSource A s e
  let b := pathEdgeTarget A t e
  have hvalid := pathEdgeValid_swap A s t e
  by_cases hv : pathEdgeValid A false s t e
  · have hcomp : ν.compatible a b := by exact hv.2.2.1
    have hD := compatible_D_eq ν a b e.free hcomp
    have hD' :
        (A.pattern e.pattern).D (P.act e.sourcePerm s.2) e.free =
          (A.pattern e.pattern).D (P.act e.targetPerm t.2) e.free := by
      simpa [ν, a, b, pathEdgeSource, pathEdgeTarget] using hD
    simp only [pathEdgeTerm, if_pos (hvalid.mpr hv), if_pos hv]
    simp [pathEdgeSource, pathEdgeTarget, pathEdgeSwapEquiv,
      star_mul, Complex.conj_ofReal]
    rw [hD']
    ring
  · have hneg : ¬ pathEdgeValid A true t s ((pathEdgeSwapEquiv A) e) := by
      intro hh
      exact hv (hvalid.mp hh)
    simp [pathEdgeTerm, hv, hneg]

theorem edgeSymmetryFactor_complex (M : ℕ) :
    (((Fintype.card (P.Permutations M) : ℂ) ^ (2 : ℕ))⁻¹) =
      (edgeSymmetryFactor P M : ℂ) := by
  classical
  have hcard : (Fintype.card (P.Permutations M) : ℝ) ≠ 0 := by
    have hp : Fintype.card (P.Permutations M) ≠ 0 :=
      Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card (P.Permutations M))
    exact_mod_cast hp
  simp [edgeSymmetryFactor, Complex.ofReal_inv, Complex.ofReal_pow, hcard]

theorem physicalKernel_false_eq_pathEdge_sum (A : Model F P J m)
    (s t : A.State) :
    A.physicalKernel false s t = ∑ e : PathEdge A, pathEdgeTerm A true s t e := by
  classical
  have hraw (π τ : P.Permutations (J + F.ell)) :
      (edgeSymmetryFactor P (J + F.ell) : ℂ) *
        A.physicalRaw false (s.1, P.act π s.2) (t.1, P.act τ t.2) =
      ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
        pathEdgeTerm A true s t ⟨π, τ, v, u⟩ := by
    unfold Model.physicalRaw
    by_cases hphys : P.physical (J + F.ell) s.1 (P.act π s.2) ∧
        P.physical (J + F.ell) t.1 (P.act τ t.2)
    · rw [if_pos hphys]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hcond : (A.pattern v).compatible (P.act π s.2) (P.act τ t.2) ∧
          (A.pattern v).ban (P.act π s.2) (P.act τ t.2) u ∧
          t.1 = s.1 + A.k * ((A.pattern v).D (P.act π s.2) u : ℤ)
      · have htarget : P.physical (J + F.ell)
            (s.1 + A.k * ((A.pattern v).D (P.act π s.2) u : ℤ)) (P.act τ t.2) := by
          rw [← hcond.2.2]
          exact hphys.2
        rw [hcond.2.2]
        simp [pathEdgeTerm, pathEdgeValid, pathEdgeSource, pathEdgeTarget,
          pathEdgeDelta, edgeDelta, hphys.1, htarget, hcond, Complex.ofReal_mul]
        ring
      · simp [pathEdgeTerm, pathEdgeValid, pathEdgeSource, pathEdgeTarget,
          pathEdgeDelta, edgeDelta, hphys, hcond]
    · have hvalid (v : Fin A.patternCount) (u : P.Aux J) :
          ¬ pathEdgeValid A true s t ⟨π, τ, v, u⟩ := by
        intro hv
        exact hphys ⟨hv.1, hv.2.1⟩
      simp [hphys, pathEdgeTerm, hvalid]
  calc
    A.physicalKernel false s t =
        ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
          (edgeSymmetryFactor P (J + F.ell) : ℂ) *
            A.physicalRaw false (s.1, P.act π s.2) (t.1, P.act τ t.2) := by
          unfold Model.physicalKernel
          rw [edgeSymmetryFactor_complex]
          simp only [Finset.mul_sum]
    _ = ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
          ∑ v : Fin A.patternCount, ∑ u : P.Aux J,
            pathEdgeTerm A true s t ⟨π, τ, v, u⟩ := by
          apply Finset.sum_congr rfl
          intro π hπ
          apply Finset.sum_congr rfl
          intro τ hτ
          exact hraw π τ
    _ = ∑ e : PathEdge A, pathEdgeTerm A true s t e := by
          symm
          exact pathEdge_sum_eq_product A (pathEdgeTerm A true s t)

theorem adjointKernel_eq_pathEdge_sum (A : Model F P J m) (s t : A.State) :
    A.adjointKernel s t = ∑ e : PathEdge A, pathEdgeTerm A false s t e := by
  classical
  rw [Model.adjointKernel, physicalKernel_false_eq_pathEdge_sum A t s, star_sum]
  calc
    (∑ e : PathEdge A, star (pathEdgeTerm A true t s e)) =
        ∑ e : PathEdge A,
          star (pathEdgeTerm A true t s ((pathEdgeSwapEquiv A) e)) := by
      exact (Equiv.sum_comp (pathEdgeSwapEquiv A)
        (fun e => star (pathEdgeTerm A true t s e))).symm
    _ = ∑ e : PathEdge A, pathEdgeTerm A false s t e := by
      apply Finset.sum_congr rfl
      intro e he
      exact pathEdgeTerm_swap A s t e

theorem physicalAdjointComp_eq_sum_pairNeighbors (A : Model F P J m)
    (s t : A.State) :
    pairedKernel A s t =
      ∑ z ∈ pairNeighbors A s,
        A.physicalKernel false s z * A.adjointKernel z t := by
  classical
  unfold pairedKernel kernelComp
  apply tsum_eq_sum
  intro z hz
  have hnot : ¬ |z.1 - s.1| ≤ (pairRadius A : ℤ) := by
    intro hc
    apply hz
    have hc' := abs_le.mp hc
    change z ∈ (Finset.Icc (s.1 - (pairRadius A : ℤ))
      (s.1 + (pairRadius A : ℤ))).product Finset.univ
    apply Finset.mem_product.mpr
    constructor
    · simp only [Finset.mem_Icc]
      constructor <;> omega
    · exact Finset.mem_univ _
  have hcast : ¬ (Int.natAbs (z.1 - s.1) : ℤ) ≤ (pairRadius A : ℤ) := by
    simpa only [Int.natCast_natAbs] using hnot
  have hgt : pairRadius A < Int.natAbs (z.1 - s.1) := by omega
  have hstep : stepRadius A < Int.natAbs (z.1 - s.1) := by
    unfold pairRadius at hgt
    omega
  simp [physicalKernel_false_zero_of_stepRadius_lt A s z hstep]

theorem pathEdgeDelta_forward_bound (A : Model F P J m) (s : A.State)
    (e : PathEdge A) : Int.natAbs (pathEdgeDelta A true s e) ≤ stepRadius A := by
  have h := stepRadius_mem A
    (displacement_mem_oneStepDisplacements A e.pattern (pathEdgeSource A s e) e.free)
  simpa [pathEdgeDelta, pathEdgeSource, edgeDelta] using h

theorem pathEdgeDelta_bound (A : Model F P J m) (forward : Bool)
    (s : A.State) (e : PathEdge A) :
    Int.natAbs (pathEdgeDelta A forward s e) ≤ stepRadius A := by
  cases forward
  · have h := pathEdgeDelta_forward_bound A s e
    simpa [pathEdgeDelta, edgeDelta] using h
  · exact pathEdgeDelta_forward_bound A s e

theorem pathEdgeNextPosition_mem_pairNeighbors (A : Model F P J m)
    (s : A.State) (e : PathEdge A) :
    s.1 + pathEdgeDelta A true s e ∈
      Finset.Icc (s.1 - (pairRadius A : ℤ)) (s.1 + (pairRadius A : ℤ)) := by
  have hbound : Int.natAbs ((s.1 + pathEdgeDelta A true s e) - s.1) ≤ pairRadius A := by
    have hstep := pathEdgeDelta_forward_bound A s e
    have hle : stepRadius A ≤ pairRadius A := by unfold pairRadius; omega
    have hcast : (Int.natAbs ((s.1 + pathEdgeDelta A true s e) - s.1) : ℤ) ≤
        (pairRadius A : ℤ) := by
      have heq : (s.1 + pathEdgeDelta A true s e) - s.1 = pathEdgeDelta A true s e := by omega
      rw [heq]
      exact_mod_cast hstep.trans hle
    exact_mod_cast hcast
  have habs : |(s.1 + pathEdgeDelta A true s e) - s.1| ≤ (pairRadius A : ℤ) := by
    have hc : (Int.natAbs ((s.1 + pathEdgeDelta A true s e) - s.1) : ℤ) ≤
        (pairRadius A : ℤ) := by exact_mod_cast hbound
    simpa only [Int.natCast_natAbs] using hc
  have habs' := abs_le.mp habs
  simp only [Finset.mem_Icc]
  constructor <;> omega

theorem pathEdgeTerm_forward_zero_of_pos_ne (A : Model F P J m) (s z : A.State)
    (e : PathEdge A)
    (h : z.1 ≠ s.1 + pathEdgeDelta A true s e) :
    pathEdgeTerm A true s z e = 0 := by
  have hv : ¬ pathEdgeValid A true s z e := by
    intro hv
    exact h hv.2.2.2.2
  simp [pathEdgeTerm, hv]

theorem pathEdgeTerm_zero_of_pos_ne (A : Model F P J m) (forward : Bool)
    (s z : A.State) (e : PathEdge A)
    (h : z.1 ≠ s.1 + pathEdgeDelta A forward s e) :
    pathEdgeTerm A forward s z e = 0 := by
  have hv : ¬ pathEdgeValid A forward s z e := by
    intro hv
    exact h hv.2.2.2.2
  simp [pathEdgeTerm, hv]

theorem pathEdgePairNextPosition_mem_pairNeighbors (A : Model F P J m)
    (s : A.State) (a : A.Labels) (e₀ e₁ : PathEdge A) :
    (s.1 + pathEdgeDelta A true s e₀ +
      pathEdgeDelta A false (s.1 + pathEdgeDelta A true s e₀, a) e₁) ∈
      Finset.Icc (s.1 - (pairRadius A : ℤ)) (s.1 + (pairRadius A : ℤ)) := by
  let mid : A.State := (s.1 + pathEdgeDelta A true s e₀, a)
  let δ₀ := pathEdgeDelta A true s e₀
  let δ₁ := pathEdgeDelta A false mid e₁
  have h₀nat := pathEdgeDelta_bound A true s e₀
  have h₁nat := pathEdgeDelta_bound A false mid e₁
  have h₀cast : (Int.natAbs δ₀ : ℤ) ≤ (stepRadius A : ℤ) := by
    exact_mod_cast h₀nat
  have h₁cast : (Int.natAbs δ₁ : ℤ) ≤ (stepRadius A : ℤ) := by
    exact_mod_cast h₁nat
  have h₀ : |δ₀| ≤ (stepRadius A : ℤ) := by
    simpa only [Int.natCast_natAbs] using h₀cast
  have h₁ : |δ₁| ≤ (stepRadius A : ℤ) := by
    simpa only [Int.natCast_natAbs] using h₁cast
  have hpos : s.1 + δ₀ + δ₁ - s.1 = δ₀ + δ₁ := by ring
  have hbound : |(s.1 + δ₀ + δ₁) - s.1| ≤ (pairRadius A : ℤ) := by
    rw [hpos]
    calc
      |δ₀ + δ₁| ≤ |δ₀| + |δ₁| := abs_add_le _ _
      _ ≤ (stepRadius A : ℤ) + (stepRadius A : ℤ) := add_le_add h₀ h₁
      _ = (pairRadius A : ℤ) := by simp [pairRadius, Nat.cast_mul]; ring
  have hbounds := abs_le.mp hbound
  change s.1 + δ₀ + δ₁ ∈
    Finset.Icc (s.1 - (pairRadius A : ℤ)) (s.1 + (pairRadius A : ℤ))
  simp only [Finset.mem_Icc]
  constructor <;> omega

theorem pairNeighbors_sum_at_position (A : Model F P J m) (s : A.State)
    (p : ℤ) (hp : p ∈ Finset.Icc (s.1 - (pairRadius A : ℤ))
      (s.1 + (pairRadius A : ℤ))) (f : A.State → ℂ) :
    (∑ z ∈ pairNeighbors A s, if z.1 = p then f z else 0) =
      ∑ a : A.Labels, f (p, a) := by
  classical
  change (∑ z ∈ (Finset.Icc (s.1 - (pairRadius A : ℤ))
      (s.1 + (pairRadius A : ℤ)) ×ˢ Finset.univ),
        if z.1 = p then f z else 0) = _
  rw [Finset.sum_product, Finset.sum_comm]
  simp [hp]

def twoEdgeTerm (A : Model F P J m) (s t : A.State)
    (e₀ e₁ : PathEdge A) (a : A.Labels) : ℂ :=
  let mid : A.State := (s.1 + pathEdgeDelta A true s e₀, a)
  pathEdgeTerm A true s mid e₀ * pathEdgeTerm A false mid t e₁

theorem pairedKernel_eq_twoEdgeSum (A : Model F P J m) (s t : A.State) :
    pairedKernel A s t =
      ∑ e₀ : PathEdge A, ∑ a : A.Labels, ∑ e₁ : PathEdge A,
        twoEdgeTerm A s t e₀ e₁ a := by
  classical
  calc
    pairedKernel A s t =
        ∑ z ∈ pairNeighbors A s,
          A.physicalKernel false s z * A.adjointKernel z t :=
      physicalAdjointComp_eq_sum_pairNeighbors A s t
    _ = ∑ z ∈ pairNeighbors A s,
          (∑ e₀ : PathEdge A, pathEdgeTerm A true s z e₀) *
            (∑ e₁ : PathEdge A, pathEdgeTerm A false z t e₁) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [physicalKernel_false_eq_pathEdge_sum, adjointKernel_eq_pathEdge_sum]
    _ = ∑ e₀ : PathEdge A, ∑ z ∈ pairNeighbors A s,
          ∑ e₁ : PathEdge A,
            pathEdgeTerm A true s z e₀ * pathEdgeTerm A false z t e₁ := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ e₀ : PathEdge A, ∑ a : A.Labels, ∑ e₁ : PathEdge A,
          twoEdgeTerm A s t e₀ e₁ a := by
          apply Finset.sum_congr rfl
          intro e₀ he₀
          let p : ℤ := s.1 + pathEdgeDelta A true s e₀
          have hp : p ∈ Finset.Icc (s.1 - (pairRadius A : ℤ))
              (s.1 + (pairRadius A : ℤ)) := by
            exact pathEdgeNextPosition_mem_pairNeighbors A s e₀
          have hcollapse :
              (∑ z ∈ pairNeighbors A s,
                ∑ e₁ : PathEdge A,
                  pathEdgeTerm A true s z e₀ * pathEdgeTerm A false z t e₁) =
              ∑ z ∈ pairNeighbors A s,
                if z.1 = p then
                  ∑ e₁ : PathEdge A,
                    pathEdgeTerm A true s z e₀ * pathEdgeTerm A false z t e₁
                else 0 := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hzp : z.1 = p
            · simp [hzp]
            · have hzero : pathEdgeTerm A true s z e₀ = 0 := by
                apply pathEdgeTerm_forward_zero_of_pos_ne
                simpa [p] using hzp
              simp [hzp, hzero]
          calc
            _ = ∑ z ∈ pairNeighbors A s,
                  if z.1 = p then
                    ∑ e₁ : PathEdge A,
                      pathEdgeTerm A true s z e₀ * pathEdgeTerm A false z t e₁
                  else 0 := hcollapse
            _ = ∑ a : A.Labels, ∑ e₁ : PathEdge A,
                  twoEdgeTerm A s t e₀ e₁ a := by
                  rw [pairNeighbors_sum_at_position A s p hp]
                  apply Finset.sum_congr rfl
                  intro a ha
                  simp [twoEdgeTerm, p]

def PathData (A : Model F P J m) : ℕ → Type
  | 0 => A.Labels
  | n + 1 => A.Labels × (PathEdge A × PathData A n)

noncomputable instance pathDataFintype (A : Model F P J m) (n : ℕ) : Fintype (PathData A n) := by
  classical
  haveI (g : P.Group) : Fintype (P.Prime g) :=
    Fintype.ofFinset (P.primes g) (by intro p; rfl)
  induction n with
  | zero => change Fintype A.Labels; infer_instance
  | succ n ih => change Fintype (A.Labels × (PathEdge A × PathData A n)); infer_instance

def pathDataToResiduePath (A : Model F P J m) :
    (n : ℕ) → PathData A n → ResiduePath A n
  | 0, a => ⟨fun _ => a, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩
  | n + 1, d =>
      let Q := pathDataToResiduePath A n d.2.2
      ⟨Fin.cases d.1 Q.labels,
       Fin.cases d.2.1.sourcePerm Q.sourcePerm,
       Fin.cases d.2.1.targetPerm Q.targetPerm,
       Fin.cases d.2.1.pattern Q.pattern,
       Fin.cases d.2.1.free Q.free⟩

def residuePathTail {A : Model F P J m} {n : ℕ}
    (Q : ResiduePath A (n + 1)) : ResiduePath A n :=
  ⟨fun i => Q.labels i.succ, fun i => Q.sourcePerm i.succ,
    fun i => Q.targetPerm i.succ, fun i => Q.pattern i.succ, fun i => Q.free i.succ⟩

theorem residuePath_step_succ_eq_neg_tail {A : Model F P J m} {n : ℕ}
    (Q : ResiduePath A (n + 1)) (i : Fin n) :
    Q.step i.succ = -(residuePathTail Q).step i := by
  simp [ResiduePath.step, ResiduePath.source, residuePathTail,
    edgeForward, edgeDelta]
  have hmod : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hmod with h | h <;> simp [h, Nat.add_mod]

def residuePathToPathData (A : Model F P J m) :
    (n : ℕ) → ResiduePath A n → PathData A n
  | 0, Q => Q.labels 0
  | n + 1, Q =>
      (Q.labels 0,
        (⟨Q.sourcePerm 0, Q.targetPerm 0, Q.pattern 0, Q.free 0⟩,
          residuePathToPathData A n (residuePathTail Q)))

theorem residuePath_ext {A : Model F P J m} {n : ℕ}
    {Q R : ResiduePath A n}
    (hlabels : Q.labels = R.labels)
    (hsource : Q.sourcePerm = R.sourcePerm)
    (htarget : Q.targetPerm = R.targetPerm)
    (hpattern : Q.pattern = R.pattern) (hfree : Q.free = R.free) : Q = R := by
  cases Q
  cases R
  simp_all

theorem residuePathTail_pathDataToResiduePath (A : Model F P J m) (n : ℕ)
    (d : PathData A (n + 1)) :
    residuePathTail (pathDataToResiduePath A (n + 1) d) =
      pathDataToResiduePath A n d.2.2 := by
  rcases d with ⟨a, ⟨e, tail⟩⟩
  cases e
  apply residuePath_ext <;> funext i <;> simp [pathDataToResiduePath, residuePathTail]

def pathDataEquivResiduePath (A : Model F P J m) (n : ℕ) :
    PathData A n ≃ ResiduePath A n where
  toFun := pathDataToResiduePath A n
  invFun := residuePathToPathData A n
  left_inv := by
    induction n with
    | zero => intro d; rfl
    | succ n ih =>
        intro d
        rcases d with ⟨a, ⟨e, tail⟩⟩
        change residuePathToPathData A (n + 1)
            (pathDataToResiduePath A (n + 1) (a, (e, tail))) = (a, (e, tail))
        rw [residuePathToPathData]
        rw [residuePathTail_pathDataToResiduePath A n (a, (e, tail))]
        exact congrArg (fun x => (a, (e, x))) (ih tail)
  right_inv := by
    induction n with
    | zero =>
        intro Q
        cases Q with
        | mk labels sourcePerm targetPerm pattern free =>
          apply residuePath_ext
          · funext i
            fin_cases i
            rfl
          · funext i
            exact Fin.elim0 i
          · funext i
            exact Fin.elim0 i
          · funext i
            exact Fin.elim0 i
          · funext i
            exact Fin.elim0 i
    | succ n ih =>
        intro Q
        cases Q with
        | mk labels sourcePerm targetPerm pattern free =>
          have hlabels :
              Fin.cases (labels 0) (fun i => labels i.succ) = labels := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hsource :
              Fin.cases (sourcePerm 0) (fun i => sourcePerm i.succ) = sourcePerm := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have htarget :
              Fin.cases (targetPerm 0) (fun i => targetPerm i.succ) = targetPerm := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hpattern :
              Fin.cases (pattern 0) (fun i => pattern i.succ) = pattern := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          have hfree :
              Fin.cases (free 0) (fun i => free i.succ) = free := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          let tail : ResiduePath A n := residuePathTail
            ⟨labels, sourcePerm, targetPerm, pattern, free⟩
          have htail := ih tail
          dsimp [residuePathToPathData, pathDataToResiduePath]
          rw [htail]
          apply residuePath_ext
          · simpa [tail, residuePathTail] using hlabels
          · simpa [tail, residuePathTail] using hsource
          · simpa [tail, residuePathTail] using htarget
          · simpa [tail, residuePathTail] using hpattern
          · simpa [tail, residuePathTail] using hfree

def pathDataHead (A : Model F P J m) :
    (n : ℕ) → PathData A n → A.Labels
  | 0, a => a
  | n + 1, d => d.1

def pathDataPairEquiv (A : Model F P J m) (n : ℕ) :
    PathData A (n + 2) ≃
      A.Labels × (PathEdge A × (A.Labels × (PathEdge A × PathData A n))) where
  toFun d := d
  invFun d := d
  left_inv d := rfl
  right_inv d := rfl

theorem pathData_sum_pairEquiv (A : Model F P J m) (n : ℕ)
    (f : PathData A (n + 2) → ℂ) :
    (∑ d : PathData A (n + 2), f d) =
      ∑ a₀ : A.Labels, ∑ e₀ : PathEdge A, ∑ a₁ : A.Labels,
        ∑ e₁ : PathEdge A, ∑ tail : PathData A n,
          f (a₀, (e₀, (a₁, (e₁, tail)))) := by
  classical
  rw [show (∑ d : PathData A (n + 2), f d) =
      ∑ x : A.Labels × (PathEdge A × (A.Labels × (PathEdge A × PathData A n))),
        f ((pathDataPairEquiv A n).symm x) by
        exact (Equiv.sum_comp (pathDataPairEquiv A n).symm f).symm]
  simp only [Fintype.sum_prod_type]
  rfl

def pathDataKernelTerm (A : Model F P J m) :
    (forward : Bool) → (n : ℕ) → PathData A n → A.State → A.State → ℂ
  | _, 0, a, s, t => if s = t ∧ a = s.2 then 1 else 0
  | forward, n + 1, d, s, t =>
      if d.1 = s.2 then
        let e := d.2.1
        let tail := d.2.2
        let mid : A.State :=
          (s.1 + pathEdgeDelta A forward s e, pathDataHead A n tail)
        pathEdgeTerm A forward s mid e * pathDataKernelTerm A (!forward) n tail mid t
      else 0

def pathDataEndState (A : Model F P J m) :
    (forward : Bool) → (n : ℕ) → PathData A n → A.State → A.State
  | _, 0, _, s => s
  | forward, n + 1, d, s =>
      let e := d.2.1
      let tail := d.2.2
      let mid : A.State :=
        (s.1 + pathEdgeDelta A forward s e, pathDataHead A n tail)
      pathDataEndState A (!forward) n tail mid

def pathDataDisplacement (A : Model F P J m) :
    (forward : Bool) → (n : ℕ) → PathData A n → ℤ
  | _, 0, _ => 0
  | forward, n + 1, d =>
      pathEdgeDelta A forward (0, d.1) d.2.1 +
        pathDataDisplacement A (!forward) n d.2.2

theorem pathDataEndState_fst_eq_add_displacement (A : Model F P J m)
    (forward : Bool) (n : ℕ) (d : PathData A n) (s : A.State)
    (hhead : pathDataHead A n d = s.2) :
    (pathDataEndState A forward n d s).1 =
      s.1 + pathDataDisplacement A forward n d := by
  induction n generalizing forward s with
  | zero => simp [pathDataHead, pathDataEndState, pathDataDisplacement] at hhead ⊢
  | succ n ih =>
      rcases d with ⟨a, ⟨e, tail⟩⟩
      have hhead' : a = s.2 := by simpa [pathDataHead] using hhead
      let mid : A.State := (s.1 + pathEdgeDelta A forward s e,
        pathDataHead A n tail)
      have htail : pathDataHead A n tail = mid.2 := rfl
      have hI := ih (!forward) tail mid htail
      have hdelta : pathEdgeDelta A forward s e =
          pathEdgeDelta A forward (0, a) e := by
        simp [pathEdgeDelta, pathEdgeSource, hhead']
      change (pathDataEndState A (!forward) n tail mid).1 = _
      rw [hI]
      simp [pathDataDisplacement, mid, hdelta]
      ring

def pathDataKernelProduct (A : Model F P J m) :
    (forward : Bool) → (n : ℕ) → PathData A n → A.State → ℂ
  | _, 0, _, _ => 1
  | forward, n + 1, d, s =>
      if d.1 = s.2 then
        let e := d.2.1
        let tail := d.2.2
        let mid : A.State :=
          (s.1 + pathEdgeDelta A forward s e, pathDataHead A n tail)
        pathEdgeTerm A forward s mid e * pathDataKernelProduct A (!forward) n tail mid
      else 0

theorem pathDataKernelTerm_eq_endpoint_indicator (A : Model F P J m)
    (forward : Bool) (n : ℕ) (d : PathData A n) (s t : A.State) :
    pathDataKernelTerm A forward n d s t =
      if pathDataHead A n d = s.2 ∧ pathDataEndState A forward n d s = t then
        pathDataKernelProduct A forward n d s
      else 0 := by
  induction n generalizing forward s t with
  | zero =>
      by_cases hst : s = t
      · by_cases hhead : d = s.2
        · simp [pathDataKernelTerm, pathDataHead, pathDataEndState,
            pathDataKernelProduct, hst, hhead, and_comm]
          rfl
        · simp [pathDataKernelTerm, pathDataHead, pathDataEndState,
            pathDataKernelProduct, hst, hhead, and_comm]
          rfl
      · simp [pathDataKernelTerm, pathDataHead, pathDataEndState,
          pathDataKernelProduct, hst, and_comm]
  | succ n ih =>
      rcases d with ⟨a, ⟨e, tail⟩⟩
      by_cases h : a = s.2
      · simp [pathDataKernelTerm, pathDataHead, pathDataEndState,
          pathDataKernelProduct, h, ih]
      · simp [pathDataKernelTerm, pathDataHead, pathDataEndState,
          pathDataKernelProduct, h]

theorem pathDataKernelTerm_sum_over_terminal_label (A : Model F P J m)
    (forward : Bool) (n : ℕ) (d : PathData A n) (s : A.State) (z : ℤ) :
    (∑ b : A.Labels, pathDataKernelTerm A forward n d s (z, b)) =
      if pathDataHead A n d = s.2 ∧ (pathDataEndState A forward n d s).1 = z then
        pathDataKernelProduct A forward n d s
      else 0 := by
  classical
  simp_rw [pathDataKernelTerm_eq_endpoint_indicator]
  let e := pathDataEndState A forward n d s
  let K := pathDataKernelProduct A forward n d s
  by_cases hh : pathDataHead A n d = s.2
  · by_cases hp : e.1 = z
    · have hfun : (fun b : A.Labels => if e = (z, b) then K else 0) =
          (fun b => if e.2 = b then K else 0) := by
        funext b
        by_cases hEq : e = (z, b)
        · have hlabel := congrArg Prod.snd hEq
          simp [hEq, hlabel]
        · have hlabel : e.2 ≠ b := by
            intro h
            exact hEq (Prod.ext hp h)
          simp [hEq, hlabel]
      have hsum : (∑ b : A.Labels, if e = (z, b) then K else 0) = K := by
        rw [show (∑ b : A.Labels, if e = (z, b) then K else 0) =
            ∑ b : A.Labels, (fun b : A.Labels => if e = (z, b) then K else 0) b by rfl]
        rw [hfun]
        exact Fintype.sum_ite_eq e.2 (fun _ => K)
      simpa [hh, hp, e, K] using hsum
    · have hsum : (∑ b : A.Labels, if e = (z, b) then K else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hEq : e ≠ (z, b) := by
          intro h
          exact hp (congrArg Prod.fst h)
        simp [hEq]
      simpa [hh, hp, e, K] using hsum
  · simp [hh, e, K]

theorem pathDataKernelTerm_sum_over_both_labels (A : Model F P J m)
    (forward : Bool) (n : ℕ) (d : PathData A n) (z : ℤ) :
    (∑ a : A.Labels, (A.stateMass (z, a) : ℂ) *
      ∑ b : A.Labels, pathDataKernelTerm A forward n d (z, a) (z, b)) =
      (A.stateMass (z, pathDataHead A n d) : ℂ) *
        (if (pathDataEndState A forward n d (z, pathDataHead A n d)).1 = z then
          pathDataKernelProduct A forward n d (z, pathDataHead A n d)
        else 0) := by
  classical
  simp_rw [pathDataKernelTerm_sum_over_terminal_label]
  rw [Fintype.sum_eq_single (pathDataHead A n d)
    (fun a ha => by simp [Ne.symm ha])]
  simp

theorem pairNeighbors_sum_at_state (A : Model F P J m) (s : A.State)
    (p : ℤ) (a : A.Labels)
    (hp : p ∈ Finset.Icc (s.1 - (pairRadius A : ℤ))
      (s.1 + (pairRadius A : ℤ))) (f : A.State → ℂ) :
    (∑ z ∈ pairNeighbors A s, if z = (p, a) then f z else 0) = f (p, a) := by
  classical
  calc
    (∑ z ∈ pairNeighbors A s, if z = (p, a) then f z else 0) =
        ∑ z ∈ pairNeighbors A s,
          if z.1 = p then (if z.2 = a then f z else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hpz : z.1 = p
          · have hz' : z = (p, z.2) := by ext <;> simp [hpz]
            rw [hz']
            simp
          · have hneq : z ≠ (p, a) := by
              intro heq
              exact hpz (congrArg Prod.fst heq)
            simp [hpz, hneq]
    _ = ∑ b : A.Labels, if b = a then f (p, b) else 0 :=
          pairNeighbors_sum_at_position A s p hp
            (fun z => if z.2 = a then f z else 0)
    _ = f (p, a) := by simp

theorem pairNeighbors_sum_comm (A : Model F P J m) (s : A.State)
    (β : Type*) [Fintype β] (f : A.State → β → ℂ) :
    (∑ u ∈ pairNeighbors A s, ∑ b : β, f u b) =
      ∑ b : β, ∑ u ∈ pairNeighbors A s, f u b := by
  classical
  change (∑ u ∈ pairNeighbors A s, ∑ b ∈ (Finset.univ : Finset β), f u b) =
    ∑ b ∈ (Finset.univ : Finset β), ∑ u ∈ pairNeighbors A s, f u b
  rw [Finset.sum_comm]

theorem pairNeighbors_sum_comm4 (A : Model F P J m) (s : A.State)
    (β γ δ ε : Type*) [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (f : A.State → β → γ → δ → ε → ℂ) :
    (∑ u ∈ pairNeighbors A s, ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ e : ε,
      f u b c d e) =
      ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ e : ε,
        ∑ u ∈ pairNeighbors A s, f u b c d e := by
  classical
  calc
    _ = ∑ b : β, ∑ u ∈ pairNeighbors A s, ∑ c : γ, ∑ d : δ, ∑ e : ε,
          f u b c d e :=
          pairNeighbors_sum_comm A s β (fun u b =>
            ∑ c : γ, ∑ d : δ, ∑ e : ε, f u b c d e)
    _ = ∑ b : β, ∑ c : γ, ∑ u ∈ pairNeighbors A s, ∑ d : δ, ∑ e : ε,
          f u b c d e := by
          apply Finset.sum_congr rfl
          intro b hb
          exact pairNeighbors_sum_comm A s γ (fun u c =>
            ∑ d : δ, ∑ e : ε, f u b c d e)
    _ = ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ u ∈ pairNeighbors A s, ∑ e : ε,
          f u b c d e := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          exact pairNeighbors_sum_comm A s δ (fun u d =>
            ∑ e : ε, f u b c d e)
    _ = ∑ b : β, ∑ c : γ, ∑ d : δ, ∑ e : ε,
          ∑ u ∈ pairNeighbors A s, f u b c d e := by
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro d hd
          exact pairNeighbors_sum_comm A s ε (fun u e => f u b c d e)

theorem pathDataKernelTerm_pair_unfold (A : Model F P J m) (n : ℕ)
    (d : PathData A (n + 2)) (s t : A.State) :
    pathDataKernelTerm A true (n + 2) d s t =
      if d.1 = s.2 then
        let e₀ := d.2.1
        let after₀ := d.2.2
        let a₁ := after₀.1
        let e₁ := after₀.2.1
        let tail := after₀.2.2
        let mid : A.State := (s.1 + pathEdgeDelta A true s e₀, a₁)
        let next : A.State := (mid.1 + pathEdgeDelta A false mid e₁,
          pathDataHead A n tail)
        pathEdgeTerm A true s mid e₀ *
          (if a₁ = mid.2 then
            pathEdgeTerm A false mid next e₁ * pathDataKernelTerm A true n tail next t
          else 0)
      else 0 := by
  rcases d with ⟨a₀, ⟨e₀, ⟨a₁, ⟨e₁, tail⟩⟩⟩⟩
  rfl

theorem pathDataKernelTerm_zero_of_head_ne (A : Model F P J m)
    (forward : Bool) (n : ℕ) (d : PathData A n) (s t : A.State)
    (h : pathDataHead A n d ≠ s.2) : pathDataKernelTerm A forward n d s t = 0 := by
  cases n with
  | zero =>
      change d ≠ s.2 at h
      simp [pathDataKernelTerm, h]
  | succ n =>
      change d.1 ≠ s.2 at h
      simp [pathDataKernelTerm, h]

theorem secondEdge_pathData_sum_over_state (A : Model F P J m)
    (s : A.State) (e₀ : PathEdge A) (a : A.Labels) (e₁ : PathEdge A)
    (n : ℕ) (d : PathData A n) (t : A.State) :
    (∑ u ∈ pairNeighbors A s,
      pathEdgeTerm A false
          (s.1 + pathEdgeDelta A true s e₀, a) u e₁ *
        pathDataKernelTerm A true n d u t) =
      pathEdgeTerm A false
          (s.1 + pathEdgeDelta A true s e₀, a)
          (s.1 + pathEdgeDelta A true s e₀ +
            pathEdgeDelta A false (s.1 + pathEdgeDelta A true s e₀, a) e₁,
            pathDataHead A n d) e₁ *
        pathDataKernelTerm A true n d
          (s.1 + pathEdgeDelta A true s e₀ +
            pathEdgeDelta A false (s.1 + pathEdgeDelta A true s e₀, a) e₁,
            pathDataHead A n d) t := by
  classical
  let mid : A.State := (s.1 + pathEdgeDelta A true s e₀, a)
  let q := mid.1 + pathEdgeDelta A false mid e₁
  let u₀ : A.State := (q, pathDataHead A n d)
  have hq : q ∈ Finset.Icc (s.1 - (pairRadius A : ℤ))
      (s.1 + (pairRadius A : ℤ)) := by
    simpa [q, mid] using pathEdgePairNextPosition_mem_pairNeighbors A s a e₀ e₁
  let f : A.State → ℂ := fun u =>
    pathEdgeTerm A false mid u e₁ * pathDataKernelTerm A true n d u t
  have hcollapse : ∀ u : A.State, f u = if u = u₀ then f u else 0 := by
    intro u
    by_cases heq : u = u₀
    · simp [heq]
    · have hnot : ¬ (u.1 = q ∧ u.2 = pathDataHead A n d) := by
        intro hpair
        exact heq (Prod.ext hpair.1 hpair.2)
      rcases not_and_or.mp hnot with hpos | hlabel
      · have hzero : pathEdgeTerm A false mid u e₁ = 0 := by
          apply pathEdgeTerm_zero_of_pos_ne
          simpa [q, mid] using hpos
        simp [f, hzero]
      · have hzero : pathDataKernelTerm A true n d u t = 0 :=
          pathDataKernelTerm_zero_of_head_ne A true n d u t (Ne.symm hlabel)
        simp [f, hzero]
  calc
    _ = ∑ u ∈ pairNeighbors A s, if u = u₀ then f u else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hcollapse u
    _ = f u₀ := pairNeighbors_sum_at_state A s q
          (pathDataHead A n d) hq f
    _ = _ := by simp [f, u₀, q, mid]

theorem pathData_pairTerm_sum (A : Model F P J m) (n : ℕ)
    (s t : A.State) :
    (∑ d : PathData A (n + 2), pathDataKernelTerm A true (n + 2) d s t) =
      ∑ e₀ : PathEdge A, ∑ a₁ : A.Labels, ∑ e₁ : PathEdge A,
        ∑ tail : PathData A n,
          let next : A.State :=
            (s.1 + pathEdgeDelta A true s e₀ +
              pathEdgeDelta A false (s.1 + pathEdgeDelta A true s e₀, a₁) e₁,
              pathDataHead A n tail)
          twoEdgeTerm A s next e₀ e₁ a₁ *
            pathDataKernelTerm A true n tail next t := by
  classical
  rw [pathData_sum_pairEquiv]
  rw [Fintype.sum_eq_single s.2 (by
    intro a₀ ha₀
    simp [pathDataKernelTerm, pathDataHead, ha₀])]
  simp [pathDataKernelTerm, pathDataHead, twoEdgeTerm, mul_assoc]

theorem pairedKernel_pathData_sum_step (A : Model F P J m) (n : ℕ)
    (s t : A.State) :
    (∑ u ∈ pairNeighbors A s,
      pairedKernel A s u *
        ∑ tail : PathData A n, pathDataKernelTerm A true n tail u t) =
      ∑ d : PathData A (n + 2), pathDataKernelTerm A true (n + 2) d s t := by
  classical
  calc
    _ = ∑ u ∈ pairNeighbors A s,
          (∑ e₀ : PathEdge A, ∑ a₁ : A.Labels, ∑ e₁ : PathEdge A,
            twoEdgeTerm A s u e₀ e₁ a₁) *
            ∑ tail : PathData A n, pathDataKernelTerm A true n tail u t := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [pairedKernel_eq_twoEdgeSum]
    _ = ∑ e₀ : PathEdge A, ∑ a₁ : A.Labels, ∑ e₁ : PathEdge A,
          ∑ tail : PathData A n, ∑ u ∈ pairNeighbors A s,
            pathEdgeTerm A true s
                (s.1 + pathEdgeDelta A true s e₀, a₁) e₀ *
              (pathEdgeTerm A false
                  (s.1 + pathEdgeDelta A true s e₀, a₁) u e₁ *
                pathDataKernelTerm A true n tail u t) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum, twoEdgeTerm, mul_assoc]
          rw [pairNeighbors_sum_comm4]
    _ = ∑ e₀ : PathEdge A, ∑ a₁ : A.Labels, ∑ e₁ : PathEdge A,
          ∑ tail : PathData A n,
            twoEdgeTerm A s
                (s.1 + pathEdgeDelta A true s e₀ +
                  pathEdgeDelta A false (s.1 + pathEdgeDelta A true s e₀, a₁) e₁,
                  pathDataHead A n tail) e₀ e₁ a₁ *
              pathDataKernelTerm A true n tail
                (s.1 + pathEdgeDelta A true s e₀ +
                  pathEdgeDelta A false (s.1 + pathEdgeDelta A true s e₀, a₁) e₁,
                  pathDataHead A n tail) t := by
          apply Finset.sum_congr rfl
          intro e₀ he₀
          apply Finset.sum_congr rfl
          intro a₁ ha₁
          apply Finset.sum_congr rfl
          intro e₁ he₁
          apply Finset.sum_congr rfl
          intro tail htail
          rw [← Finset.mul_sum, secondEdge_pathData_sum_over_state]
          simp [twoEdgeTerm, mul_assoc]
    _ = ∑ d : PathData A (n + 2), pathDataKernelTerm A true (n + 2) d s t := by
          symm
          exact pathData_pairTerm_sum A n s t

theorem pairedKernelPower_eq_pathData (A : Model F P J m) (r : ℕ) :
    ∀ s t : A.State,
      kernelPower (pairedKernel A) r s t =
        ∑ d : PathData A (2 * r), pathDataKernelTerm A true (2 * r) d s t := by
  induction r with
  | zero =>
      intro s t
      letI : Decidable (s = t) := Classical.propDecidable _
      simp only [kernelPower, Nat.mul_zero]
      change (if s = t then (1 : ℂ) else 0) =
        ∑ d : A.Labels, pathDataKernelTerm A true 0 d s t
      by_cases h : s = t
      · subst t
        simp only [pathDataKernelTerm, PathData, true_and]
        rw [Fintype.sum_ite_eq']
        simp
      · simp [kernelPower, pathDataKernelTerm, h]
  | succ r ih =>
      intro s t
      change kernelComp (pairedKernel A) (kernelPower (pairedKernel A) r) s t = _
      calc
        kernelComp (pairedKernel A) (kernelPower (pairedKernel A) r) s t =
            ∑ u ∈ pairNeighbors A s,
              pairedKernel A s u * kernelPower (pairedKernel A) r u t :=
          pairedKernel_comp_eq_sum_pairNeighbors A
            (kernelPower (pairedKernel A) r) s t
        _ = ∑ u ∈ pairNeighbors A s,
              pairedKernel A s u *
                ∑ tail : PathData A (2 * r),
                  pathDataKernelTerm A true (2 * r) tail u t := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [ih u t]
        _ = ∑ d : PathData A (2 * r + 2),
              pathDataKernelTerm A true (2 * r + 2) d s t :=
              pairedKernel_pathData_sum_step A (2 * r) s t
        _ = ∑ d : PathData A (2 * (r + 1)),
              pathDataKernelTerm A true (2 * (r + 1)) d s t := by
              simpa [Nat.mul_succ]

theorem pairedKernelPower_eq_residuePath (A : Model F P J m) (r : ℕ)
    (s t : A.State) :
    kernelPower (pairedKernel A) r s t =
      ∑ Q : ResiduePath A (2 * r),
        pathDataKernelTerm A true (2 * r)
          ((pathDataEquivResiduePath A (2 * r)).symm Q) s t := by
  rw [pairedKernelPower_eq_pathData A r s t]
  exact (Equiv.sum_comp (pathDataEquivResiduePath A (2 * r)).symm
    (fun d => pathDataKernelTerm A true (2 * r) d s t)).symm

end Erdos821.S2Phys

