import Erdos821.S2.EdgeTasks
import Erdos821.S2.CountableSchur
import Erdos821.S2.MemoryIndices
import Erdos821.S2.PhysicalCompatibility
import Erdos821.Leaves
import Erdos821.P3Edge.RowBound
import Erdos821.P3Edge.ColumnBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false


noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Rare

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Raw absolute row cost after fixing both endpoint permutations, a pattern,
and an auxiliary tuple, before the endpoint symmetry average. -/
def fixedContextRowCost (A : Model F P J m) (r : MemoryParameters F) (n : ℕ)
    (theta : ℝ) (i : Fin n) (v : Fin A.patternCount) (u : P.Aux J)
    (s : P.MemoryState (J + F.ell)) (π τ : P.Permutations (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell))) : ℝ :=
  ∑ tr : TransferChoice s, ∑ t ∈ S,
    if edgeChoiceValid A .all i s t (π, τ, v, u, tr) then
      ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, tr)‖ *
        P.memoryWeight r.v t
    else 0

def fixedContextColumnCost (A : Model F P J m) (r : MemoryParameters F)
    (n : ℕ) (theta : ℝ) (i : Fin n) (v : Fin A.patternCount) (u : P.Aux J)
    (t : P.MemoryState (J + F.ell)) (π τ : P.Permutations (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell))) : ℝ :=
  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
      ∑ s ∈ S, Erdos821.P3Edge.colSourceMapSum F r n theta i A t π τ v u B A_retr s

/-- The local row estimate from the absolute-edge proof remains valid for a
fixed pair of endpoint permutations, pattern, and auxiliary tuple. -/
theorem fixedContextRowCost_le (A : Model F P J m) (r : MemoryParameters F)
    (n : ℕ) (theta : ℝ) (i : Fin n) (v : Fin A.patternCount)
    (u : P.Aux J) (s : P.MemoryState (J + F.ell))
    (π τ : P.Permutations (J + F.ell)) (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVpos : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val,
      tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    fixedContextRowCost A r n theta i v u s π τ S ≤
      Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u * P.memoryWeight r.v s *
        ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup) := by
  classical
  let ss := permuteActive π s
  let delta := edgeDelta A (A.pattern v) (edgeForward i) ss.2.1 u
  let labelCost (tr : TransferChoice ss) : ℝ :=
    ∑ b : P.Labels (J + F.ell),
      (∏ g : P.BigGroup,
        if Erdos821.P3Edge.bigGroupValid (A.pattern v) delta g
            (ss.2.1 g.val) (ss.2.2 g) (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val) then
          Erdos821.P3Edge.bigGroupWeight F r n (A.pattern v) delta g
            (ss.2.1 g.val) (ss.2.2 g) (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val)
        else 0) *
      (∏ g : P.SmallGroup,
        if b g.val ∈ Erdos821.P3Edge.smallPrefixFibre J F.ell
            (translateSmallResidues delta ss.1 g)
            (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
          Erdos821.P3Edge.smallGroupWeight F J g
            (translateSmallResidues delta ss.1 g)
        else 0)
  let labelCostS (tr : TransferChoice s) : ℝ :=
    ∑ b : P.Labels (J + F.ell),
      (∏ g : P.BigGroup,
        if Erdos821.P3Edge.bigGroupValid (A.pattern v) delta g
            (ss.2.1 g.val) (s.2.2 g) (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val) then
          Erdos821.P3Edge.bigGroupWeight F r n (A.pattern v) delta g
            (ss.2.1 g.val) (s.2.2 g) (tr.1 g) (tr.2.1 g) (tr.2.2 g) (b g.val)
        else 0) *
      (∏ g : P.SmallGroup,
        if b g.val ∈ Erdos821.P3Edge.smallPrefixFibre J F.ell
            (translateSmallResidues delta s.1 g)
            (fun j => ss.2.1 g.val (Fin.castAdd F.ell j)) then
          Erdos821.P3Edge.smallGroupWeight F J g
            (translateSmallResidues delta s.1 g)
        else 0)
  let pref : ℝ := Erdos821.P3Edge.patternSup A v *
    (A.pattern v).auxMass u * P.memoryWeight r.v s
  have hTransfer := Erdos821.P3Edge.sum_transfer_labels_le F r n Cprom Csmall0
    hCsmall0Pos hCprom hCsmall0 hVlo htilted htiltedSum (A.pattern v) delta ss
  have hT : (∑ tr : TransferChoice ss, labelCost tr) ≤
      (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
          Fintype.card P.SmallGroup := by
    simpa [labelCost] using hTransfer
  have hcostEq (tr : TransferChoice s) : labelCost tr = labelCostS tr := by
    simp [labelCost, labelCostS, ss, permuteActive]
  have hTarget (tr : TransferChoice ss) :
      (∑ t ∈ S,
        if edgeChoiceValid A .all i s t (π, τ, v, u, tr) then
          ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, tr)‖ *
            P.memoryWeight r.v t else 0) ≤ pref * labelCost tr := by
    have h := Erdos821.P3Edge.sum_target_for_choice_le r n theta i A s
      (π, τ, v, u, tr) S hVpos htilted
    have hpermA (g : P.BigGroup) :
        (permuteActive π s).2.1 g.val = ss.2.1 g.val := rfl
    have hpermMem (g : P.BigGroup) :
        (permuteActive π s).2.2 g = ss.2.2 g := rfl
    have hS : (∑ t ∈ S,
        if edgeChoiceValid A .all i s t (π, τ, v, u, tr) then
          ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, tr)‖ *
            P.memoryWeight r.v t else 0) ≤ pref * labelCostS tr := by
      simpa [pref, labelCostS, delta, hpermA, hpermMem] using h
    calc
      _ ≤ pref * labelCostS tr := hS
      _ = pref * labelCost tr := by rw [hcostEq tr]
  have haux : 0 ≤ (A.pattern v).auxMass u := by
    unfold Pattern.auxMass
    apply Finset.prod_nonneg
    intro g hg
    apply Finset.prod_nonneg
    intro j hj
    exact (Erdos821.P3Edge.mu_pos_of_V_pos g (hVpos g) (u g j)).le
  have hpref : 0 ≤ pref := by
    dsimp [pref]
    exact mul_nonneg (mul_nonneg
      (Erdos821.P3Edge.patternSup_nonneg A v) haux)
      (Erdos821.P3Edge.memoryWeight_pos r s).le
  calc
    _ = ∑ tr : TransferChoice s, ∑ t ∈ S,
        if edgeChoiceValid A .all i s t (π, τ, v, u, tr) then
            ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, tr)‖ *
            P.memoryWeight r.v t else 0 := rfl
    _ ≤ ∑ tr : TransferChoice ss, pref * labelCost tr :=
      Finset.sum_le_sum (fun tr _ => hTarget tr)
    _ = pref * ∑ tr : TransferChoice s, labelCost tr :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ pref * ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^
        Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
          Fintype.card P.SmallGroup) := mul_le_mul_of_nonneg_left hT hpref

/-- Fixed-permutation column bound from the reversed retrieval factorization. -/
theorem fixedContextColumnCost_le (A : Model F P J m) (r : MemoryParameters F)
    (n : ℕ) (theta : ℝ) (i : Fin n) (v : Fin A.patternCount) (u : P.Aux J)
    (t : P.MemoryState (J + F.ell)) (π τ : P.Permutations (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVhi : ∀ g : P.Group, P.V g ≤ F.vMax)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val,
      tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    fixedContextColumnCost A r n theta i v u t π τ S ≤
      Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
        P.memoryMass F J n t * P.memoryWeight r.v t *
        ((Erdos821.P3Edge.colRevConst F m) ^ Fintype.card P.BigGroup *
          (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup) := by
  classical
  let MW : ℝ := P.memoryMass F J n t * P.memoryWeight r.v t *
    (Erdos821.P3Edge.colRevConst F m ^ Fintype.card P.BigGroup)
  let smallC : ℝ :=
    (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^ Fintype.card P.SmallGroup
  let bigC : ℝ := (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^
    Fintype.card P.BigGroup
  let pref : ℝ := Erdos821.P3Edge.patternSup A v *
    (A.pattern v).auxMass u * MW
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g =>
    lt_of_lt_of_le F.vMin_pos (hVlo g)
  have hAux : 0 ≤ (A.pattern v).auxMass u := by
    unfold Pattern.auxMass
    apply Finset.prod_nonneg
    intro g hg
    apply Finset.prod_nonneg
    intro j hj
    exact (Erdos821.P3Edge.mu_pos_of_V_pos g (hVpos g) (u g j)).le
  have hMW : 0 ≤ MW := by
    dsimp [MW]
    exact mul_nonneg
      (mul_nonneg
        (Erdos821.P3Edge.memoryMass_nonneg F J n hVpos htilted t)
        (Erdos821.P3Edge.memoryWeight_pos r t).le)
      (pow_nonneg (Erdos821.P3Edge.colRevConst_pos F m).le _)
  have hPref : 0 ≤ pref := by
    dsimp [pref]
    exact mul_nonneg (mul_nonneg
      (Erdos821.P3Edge.patternSup_nonneg A v) hAux) hMW
  have hLabels := Erdos821.P3Edge.sum_colLabelTerm_le F r n Cprom Csmall0
    hCsmall0Pos hCprom hCsmall0 hVlo htilted htiltedSum (A.pattern v)
    (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
    (permuteActive τ t)
  have hBA : fixedContextColumnCost A r n theta i v u t π τ S ≤ pref * (bigC * smallC) := by
    unfold fixedContextColumnCost
    calc
      _ ≤ ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
          ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
            (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u * MW) *
              ∑ a : P.Labels (J + F.ell),
                Erdos821.P3Edge.colLabelTerm F r n (A.pattern v)
                  (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                  (permuteActive τ t) A_retr B a := by
            apply Finset.sum_le_sum
            intro B hB
            apply Finset.sum_le_sum
            intro A_retr hA
            have h := Erdos821.P3Edge.sum_source_colSourceMapSum_le F r n theta i A
              hVlo hVhi htilted π τ v u B A_retr t S
            simpa [MW, mul_assoc, mul_left_comm, mul_comm] using h
      _ = pref *
          ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
            ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
              ∑ a : P.Labels (J + F.ell),
                Erdos821.P3Edge.colLabelTerm F r n (A.pattern v)
                  (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                  (permuteActive τ t) A_retr B a := by
            change (∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  pref * ∑ a : P.Labels (J + F.ell),
                    Erdos821.P3Edge.colLabelTerm F r n (A.pattern v)
                      (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                      (permuteActive τ t) A_retr B a) = _
            calc
              _ = ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    pref * ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      ∑ a : P.Labels (J + F.ell),
                        Erdos821.P3Edge.colLabelTerm F r n (A.pattern v)
                          (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                          (permuteActive τ t) A_retr B a := by
                      apply Finset.sum_congr rfl
                      intro B hB
                      rw [← Finset.mul_sum]
              _ = pref *
                    ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                        ∑ a : P.Labels (J + F.ell),
                          Erdos821.P3Edge.colLabelTerm F r n (A.pattern v)
                            (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                            (permuteActive τ t) A_retr B a := by
                      rw [← Finset.mul_sum]
              _ = _ := rfl
      _ ≤ pref * (bigC * smallC) := by
          have hLabels' :
              (∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ a : P.Labels (J + F.ell),
                    Erdos821.P3Edge.colLabelTerm F r n (A.pattern v)
                      (-edgeDelta A (A.pattern v) (edgeForward i) (permuteActive τ t).2.1 u)
                      (permuteActive τ t) A_retr B a) ≤ bigC * smallC := by
            simpa [bigC, smallC] using hLabels
          exact mul_le_mul_of_nonneg_left hLabels' hPref
  simpa [MW, bigC, smallC, pref, mul_assoc, mul_left_comm, mul_comm] using hBA

/-- Coordinate projection cannot increase a finite-support operator bound. -/
theorem normBound_projectKernel {α : Type*} (mass : α → ℝ) (K : α → α → ℂ)
    (keep : α → Prop) (C : ℝ) (hmass : ∀ a, 0 ≤ mass a) (hC : 0 ≤ C)
    (hK : NormBound mass K C) :
    NormBound mass (projectKernel keep K) C := by
  classical
  intro s t f g
  let f' : α → ℂ := fun a => if keep a then f a else 0
  let g' : α → ℂ := fun b => if keep b then g b else 0
  have hEq :
      (∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) *
        projectKernel keep K a b * g b) =
      ∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f' a) * K a b * g' b := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hka : keep a
    · by_cases hkb : keep b <;> simp [projectKernel, f', g', hka, hkb]
    · simp [projectKernel, f', g', hka]
  have hf :
      (∑ a ∈ s, mass a * ‖f' a‖ ^ 2) ≤ ∑ a ∈ s, mass a * ‖f a‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro a ha
    by_cases hk : keep a
    · simp [f', hk]
    · simp [f', hk]
      exact mul_nonneg (hmass a) (sq_nonneg (‖f a‖))
  have hg :
      (∑ b ∈ t, mass b * ‖g' b‖ ^ 2) ≤ ∑ b ∈ t, mass b * ‖g b‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro b hb
    by_cases hk : keep b
    · simp [g', hk]
    · simp [g', hk]
      exact mul_nonneg (hmass b) (sq_nonneg (‖g b‖))
  have htest := hK s t f' g'
  calc
    _ = ‖∑ a ∈ s, ∑ b ∈ t,
        (mass a : ℂ) * star (f' a) * K a b * g' b‖ := by rw [hEq]
    _ ≤ C * Real.sqrt (∑ a ∈ s, mass a * ‖f' a‖ ^ 2) *
          Real.sqrt (∑ b ∈ t, mass b * ‖g' b‖ ^ 2) := htest
    _ ≤ C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
          Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2) := by
      have hrf := Real.sqrt_le_sqrt hf
      have hrg := Real.sqrt_le_sqrt hg
      calc
        _ ≤ C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
              Real.sqrt (∑ b ∈ t, mass b * ‖g' b‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrf hC) (Real.sqrt_nonneg _)
        _ ≤ C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
              Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hrg
            (mul_nonneg hC (Real.sqrt_nonneg _))

/-- A product of distinct primes records its selected index set. -/
theorem primeProduct_factorization_at {α : Type*} [DecidableEq α]
    (p : α → ℕ) (hp : ∀ a, Nat.Prime (p a)) (hinj : Function.Injective p)
    (S : Finset α) (a : α) :
    (S.prod p).factorization (p a) = if a ∈ S then 1 else 0 := by
  classical
  rw [Nat.factorization_prod (fun i hi => (hp i).ne_zero)]
  simp_rw [(hp _).factorization]
  simp [Finsupp.single_apply, hinj.eq_iff]

/-- Prime-product equality forces equality of the selected sets. -/
theorem primeProduct_injective {α : Type*} [DecidableEq α]
    (p : α → ℕ) (hp : ∀ a, Nat.Prime (p a)) (hinj : Function.Injective p)
    {S T : Finset α} (h : S.prod p = T.prod p) : S = T := by
  classical
  apply Finset.ext
  intro a
  have h' := congrArg (fun n : ℕ => n.factorization (p a)) h
  rw [primeProduct_factorization_at p hp hinj S a,
      primeProduct_factorization_at p hp hinj T a] at h'
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;> simp_all

abbrev SmallSlot (P : PrimeGroups) (M : ℕ) := Σ g : P.SmallGroup, Fin M

def smallSlotPrime {P : PrimeGroups} {M : ℕ} (a : P.Labels M)
    (z : SmallSlot P M) : ℕ := (a z.1.val z.2).val

/-- Physical small labels are globally distinct across groups and slots. -/
theorem smallSlotPrime_injective (P : PrimeGroups) {M : ℕ}
    (y : P.SmallResidues) (a : P.Labels M) (hphys : P.smallPhysical y a) :
    Function.Injective (smallSlotPrime a) := by
  classical
  intro z w h
  rcases z with ⟨g, i⟩
  rcases w with ⟨hgroup, j⟩
  have hval : (a g.val i).val = (a hgroup.val j).val := by
    simpa [smallSlotPrime] using h
  have hgroups : g.val = hgroup.val := by
    by_contra hne
    have hd := Finset.disjoint_left.mp (P.disjoint g.val hgroup.val hne)
    have hmem : (a g.val i).val ∈ P.primes hgroup.val := by
      rw [hval]
      exact (a hgroup.val j).property
    exact hd (a g.val i).property hmem
  have hg : g = hgroup := Subtype.ext hgroups
  subst hgroup
  have hidx : i = j := (hphys g).1 (Subtype.ext hval)
  subst j
  rfl

def omittedSlots {P : PrimeGroups} {M : ℕ}
    (O : ∀ g : P.SmallGroup, Finset (Fin M)) : Finset (SmallSlot P M) :=
  Finset.sigma Finset.univ O

def omittedPrimeProduct {P : PrimeGroups} {M : ℕ} (a : P.Labels M)
    (O : ∀ g : P.SmallGroup, Finset (Fin M)) : ℕ :=
  (omittedSlots O).prod (smallSlotPrime a)

/-- The product of omitted small labels uniquely determines every omitted slot. -/
theorem omittedPrimeProduct_injective {P : PrimeGroups} {M : ℕ}
    (y : P.SmallResidues) (a : P.Labels M) (hphys : P.smallPhysical y a)
    {O O' : ∀ g : P.SmallGroup, Finset (Fin M)}
    (hprod : omittedPrimeProduct a O = omittedPrimeProduct a O') : O = O' := by
  classical
  have hslots : omittedSlots O = omittedSlots O' :=
    primeProduct_injective (smallSlotPrime a)
      (fun z => P.prime z.1.val (a z.1.val z.2).val (a z.1.val z.2).property)
      (smallSlotPrime_injective P y a hphys) hprod
  funext g
  apply Finset.ext
  intro i
  have hmem := congrArg (fun S : Finset (SmallSlot P M) => (⟨g, i⟩ : SmallSlot P M) ∈ S) hslots
  simpa [omittedSlots, Finset.mem_sigma] using hmem

abbrev OmissionChoices (P : PrimeGroups) (M ell : ℕ) :=
  ∀ g : P.SmallGroup, {S : Finset (Fin M) // S.card = ell}

/-- The number of independent omitted ell-subsets in the small groups. -/
theorem omissionChoices_card (P : PrimeGroups) (M ell : ℕ) :
    Fintype.card (OmissionChoices P M ell) =
      Nat.choose M ell ^ P.smallGroups.card := by
  classical
  have hsmall : Fintype.card P.SmallGroup = P.smallGroups.card := by
    simpa [PrimeGroups.SmallGroup, PrimeGroups.smallGroups] using
      (Fintype.card_subtype (fun g : P.Group => P.big g = false))
  simp [OmissionChoices, Fintype.card_pi, Fintype.card_finset_len, hsmall]

def omissionTail (J ell : ℕ) : Finset (Fin (J + ell)) :=
  Finset.univ.image (Fin.natAdd J)

theorem omissionTail_card (J ell : ℕ) : (omissionTail J ell).card = ell := by
  classical
  have hinj : Function.Injective (Fin.natAdd J : Fin ell → Fin (J + ell)) := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simp only [Fin.natAdd] at hval
    omega
  rw [omissionTail, Finset.card_image_of_injective _ hinj]
  simp

def omissionSlotsFromPerm {J ell : ℕ} (π : Equiv.Perm (Fin (J + ell))) :
    Finset (Fin (J + ell)) := (omissionTail J ell).image π

theorem omissionSlotsFromPerm_card {J ell : ℕ}
    (π : Equiv.Perm (Fin (J + ell))) : (omissionSlotsFromPerm π).card = ell := by
  classical
  rw [omissionSlotsFromPerm, Finset.card_image_of_injective _ π.injective,
    omissionTail_card]

/-- Extend an equivalence between equal-size finite subsets to a permutation. -/
noncomputable def permMapFinset {α : Type*} [Fintype α] [DecidableEq α]
    (S T : Finset α) (h : S.card = T.card) : Equiv.Perm α :=
  (S.equivOfCardEq h).extendSubtype

theorem permMapFinset_image {α : Type*} [Fintype α] [DecidableEq α]
    (S T : Finset α) (h : S.card = T.card) : S.image (permMapFinset S T h) = T := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Equiv.extendSubtype_mem (S.equivOfCardEq h) y hy
  · rw [Finset.card_image_of_injective _ (permMapFinset S T h).injective, h]

abbrev OmissionPermutationFiber {J ell : ℕ} (O : Finset (Fin (J + ell))) :=
  {π : Equiv.Perm (Fin (J + ell)) // omissionSlotsFromPerm π = O}

/-- Every ell-subset is reached by the same number of permutations. -/
noncomputable def omissionFiberEquiv {J ell : ℕ}
    (O O' : Finset (Fin (J + ell))) (h : O.card = O'.card) :
    OmissionPermutationFiber O ≃ OmissionPermutationFiber O' := by
  classical
  let σ := permMapFinset O O' h
  have hσ : O.image σ = O' := permMapFinset_image O O' h
  have hσsymm : O'.image σ.symm = O := by
    rw [← hσ, Finset.image_image]
    simp
  refine
    { toFun := fun π => ⟨π.1.trans σ, ?_⟩
      invFun := fun π => ⟨π.1.trans σ.symm, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change (omissionTail J ell).image (π.1.trans σ) = O'
    have himage :
        (omissionTail J ell).image (π.1.trans σ) =
          ((omissionTail J ell).image π.1).image σ := by
      ext x
      simp
    have hπ : (omissionTail J ell).image π.1 = O := by
      simpa [omissionSlotsFromPerm] using π.2
    rw [himage, hπ, hσ]
  · change (omissionTail J ell).image (π.1.trans σ.symm) = O
    have himage :
        (omissionTail J ell).image (π.1.trans σ.symm) =
          ((omissionTail J ell).image π.1).image σ.symm := by
      ext x
      simp
    have hπ : (omissionTail J ell).image π.1 = O' := by
      simpa [omissionSlotsFromPerm] using π.2
    rw [himage, hπ, hσsymm]
  · intro π
    apply Subtype.ext
    ext x
    simp [Equiv.trans_apply]
  · intro π
    apply Subtype.ext
    ext x
    simp [Equiv.trans_apply]

def omissionOfPerm (P : PrimeGroups) (J ell : ℕ)
    (π : P.Permutations (J + ell)) : OmissionChoices P (J + ell) ell :=
  fun g => ⟨omissionSlotsFromPerm (π g.val), omissionSlotsFromPerm_card (π g.val)⟩

abbrev OmissionAssignmentFiber (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell) :=
  {π : P.Permutations (J + ell) // omissionOfPerm P J ell π = O}

/-- Permutations on the small groups alone. -/
abbrev SmallPermutations (P : PrimeGroups) (M : ℕ) :=
  P.SmallGroup → Equiv.Perm (Fin M)

def omissionOfSmallPerm (P : PrimeGroups) (J ell : ℕ)
    (π : SmallPermutations P (J + ell)) : OmissionChoices P (J + ell) ell :=
  fun g => ⟨omissionSlotsFromPerm (π g), omissionSlotsFromPerm_card (π g)⟩

abbrev OmissionSmallFiber (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell) :=
  {π : SmallPermutations P (J + ell) // omissionOfSmallPerm P J ell π = O}

noncomputable def omissionAlignment (P : PrimeGroups) (J ell : ℕ)
    (O O' : OmissionChoices P (J + ell) ell) : P.Permutations (J + ell) := by
  classical
  exact fun g => if hg : P.big g = false then
    permMapFinset (O ⟨g, hg⟩).val (O' ⟨g, hg⟩).val (by
      rw [(O ⟨g, hg⟩).property, (O' ⟨g, hg⟩).property])
    else Equiv.refl _

theorem omissionAlignment_map (P : PrimeGroups) (J ell : ℕ)
    (O O' : OmissionChoices P (J + ell) ell) (g : P.SmallGroup) :
    (O g).val.image (omissionAlignment P J ell O O' g.val) = (O' g).val := by
  classical
  unfold omissionAlignment
  simp only [dif_pos g.property]
  exact permMapFinset_image (O g).val (O' g).val (by
    rw [(O g).property, (O' g).property])

theorem omissionAlignment_symm_map (P : PrimeGroups) (J ell : ℕ)
    (O O' : OmissionChoices P (J + ell) ell) (g : P.SmallGroup) :
    (O' g).val.image (omissionAlignment P J ell O O' g.val).symm = (O g).val := by
  rw [← omissionAlignment_map P J ell O O' g, Finset.image_image]
  simp

/-- The small-group permutation fibers over omissions all have the same size. -/
noncomputable def omissionSmallFiberEquiv (P : PrimeGroups) (J ell : ℕ)
    (O O' : OmissionChoices P (J + ell) ell) :
    OmissionSmallFiber P J ell O ≃ OmissionSmallFiber P J ell O' := by
  classical
  let σ : SmallPermutations P (J + ell) :=
    fun g => omissionAlignment P J ell O O' g.val
  let σi : SmallPermutations P (J + ell) := fun g => (σ g).symm
  refine
    { toFun := fun π => ⟨fun g => (π.1 g).trans (σ g), ?_⟩
      invFun := fun π => ⟨fun g => (π.1 g).trans (σi g), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · funext g
    apply Subtype.ext
    have hπ : (omissionTail J ell).image (π.1 g) = (O g).val := by
      simpa [omissionOfSmallPerm, omissionSlotsFromPerm] using
        congrArg (fun Q : OmissionChoices P (J + ell) ell => (Q g).val) π.2
    have himage :
        (omissionTail J ell).image ((π.1 g).trans (σ g)) =
          ((omissionTail J ell).image (π.1 g)).image (σ g) := by
      ext x
      simp
    calc
      _ = ((omissionTail J ell).image (π.1 g)).image (σ g) := himage
      _ = (O g).val.image (σ g) := by rw [hπ]
      _ = (O' g).val := omissionAlignment_map P J ell O O' g
  · funext g
    apply Subtype.ext
    have hπ : (omissionTail J ell).image (π.1 g) = (O' g).val := by
      simpa [omissionOfSmallPerm, omissionSlotsFromPerm] using
        congrArg (fun Q : OmissionChoices P (J + ell) ell => (Q g).val) π.2
    have himage :
        (omissionTail J ell).image ((π.1 g).trans (σi g)) =
          ((omissionTail J ell).image (π.1 g)).image (σi g) := by
      ext x
      simp
    calc
      _ = ((omissionTail J ell).image (π.1 g)).image (σi g) := himage
      _ = (O' g).val.image (σi g) := by rw [hπ]
      _ = (O g).val := omissionAlignment_symm_map P J ell O O' g
  · intro π
    apply Subtype.ext
    funext g
    ext i
    simp [σi]
  · intro π
    apply Subtype.ext
    funext g
    ext i
    simp [σi]

noncomputable def omissionSmallFiberSigmaEquiv (P : PrimeGroups) (J ell : ℕ) :
    (Σ O : OmissionChoices P (J + ell) ell, OmissionSmallFiber P J ell O) ≃
      SmallPermutations P (J + ell) where
  toFun x := x.2.1
  invFun π := ⟨omissionOfSmallPerm P J ell π, ⟨π, rfl⟩⟩
  left_inv := by
    rintro ⟨O, ⟨π, hπ⟩⟩
    dsimp
    cases hπ
    rfl
  right_inv := by
    intro π
    rfl

theorem omissionSmallFiber_card_total (P : PrimeGroups) (J ell : ℕ) :
    Fintype.card (SmallPermutations P (J + ell)) =
      Fintype.card (OmissionChoices P (J + ell) ell) *
        Fintype.card (OmissionSmallFiber P J ell
          (omissionOfSmallPerm P J ell (fun _ => Equiv.refl _))) := by
  classical
  let O₀ := omissionOfSmallPerm P J ell (fun _ => Equiv.refl _)
  have hfib (O : OmissionChoices P (J + ell) ell) :
      Fintype.card (OmissionSmallFiber P J ell O) =
        Fintype.card (OmissionSmallFiber P J ell O₀) :=
    Fintype.card_congr (omissionSmallFiberEquiv P J ell O O₀)
  have hcard := Fintype.card_congr (omissionSmallFiberSigmaEquiv P J ell)
  rw [Fintype.card_sigma] at hcard
  calc
    Fintype.card (SmallPermutations P (J + ell)) =
        ∑ O : OmissionChoices P (J + ell) ell,
          Fintype.card (OmissionSmallFiber P J ell O) := hcard.symm
    _ = Fintype.card (OmissionChoices P (J + ell) ell) *
        Fintype.card (OmissionSmallFiber P J ell O₀) := by
      rw [show (∑ O : OmissionChoices P (J + ell) ell,
          Fintype.card (OmissionSmallFiber P J ell O)) =
        ∑ O : OmissionChoices P (J + ell) ell,
          Fintype.card (OmissionSmallFiber P J ell O₀) by
            apply Finset.sum_congr rfl
            intro O hO
            exact hfib O]
      simp
    _ = _ := by rfl

theorem smallFlag_of_not_big (P : PrimeGroups) (g : P.Group)
    (h : ¬ P.big g = true) : P.big g = false := by
  cases hb : P.big g with
  | false => rfl
  | true => exact (h hb).elim

def combinePermutations (P : PrimeGroups) {M : ℕ}
    (πB : P.BigPermutations M) (πS : SmallPermutations P M) : P.Permutations M :=
  fun g => if hb : P.big g = true then πB ⟨g, hb⟩
    else πS ⟨g, smallFlag_of_not_big P g hb⟩

/-- Full group permutations split into their big and small coordinates. -/
noncomputable def permutationSplitEquiv (P : PrimeGroups) (M : ℕ) :
    P.Permutations M ≃ P.BigPermutations M × SmallPermutations P M where
  toFun π := (fun g => π g.val, fun g => π g.val)
  invFun z := combinePermutations P z.1 z.2
  left_inv := by
    intro π
    funext g
    by_cases hb : P.big g = true
    · simp [combinePermutations, hb]
    · have hs := smallFlag_of_not_big P g hb
      simp [combinePermutations, hb, hs]
  right_inv := by
    rintro ⟨πB, πS⟩
    apply Prod.ext
    · funext g
      simp [combinePermutations, g.property]
    · funext g
      simp [combinePermutations, g.property]

/-- A full omission fiber is the product of arbitrary big permutations and
the corresponding small-only fiber. -/
noncomputable def omissionAssignmentFiberSplitEquiv (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell) :
    OmissionAssignmentFiber P J ell O ≃
      P.BigPermutations (J + ell) × OmissionSmallFiber P J ell O where
  toFun π :=
    (fun g => π.1 g.val,
      ⟨fun g => π.1 g.val, by
        change omissionOfPerm P J ell π.1 = O
        exact π.2⟩)
  invFun z :=
    ⟨combinePermutations P z.1 z.2.1, by
      funext g
      apply Subtype.ext
      have hz := congrArg (fun Q : OmissionChoices P (J + ell) ell => (Q g).val) z.2.2
      simpa [omissionOfPerm, omissionOfSmallPerm, combinePermutations, g.property]
        using hz⟩
  left_inv := by
    intro π
    apply Subtype.ext
    funext g
    by_cases hb : P.big g = true
    · simp [combinePermutations, hb]
    · have hs := smallFlag_of_not_big P g hb
      simp [combinePermutations, hb, hs]
  right_inv := by
    rintro ⟨πB, πS⟩
    apply Prod.ext
    · funext g
      simp [combinePermutations, g.property]
    · apply Subtype.ext
      funext g
      simp [combinePermutations, g.property]

def postcomposeFamily {P : PrimeGroups} {M : ℕ}
    (σ π : P.Permutations M) : P.Permutations M := fun g => (π g).trans (σ g)

/-- All full group-permutation fibers above omission configurations are equipotent. -/
noncomputable def omissionAssignmentFiberEquiv (P : PrimeGroups) (J ell : ℕ)
    (O O' : OmissionChoices P (J + ell) ell) :
    OmissionAssignmentFiber P J ell O ≃ OmissionAssignmentFiber P J ell O' := by
  classical
  let σ := omissionAlignment P J ell O O'
  let σi : P.Permutations (J + ell) := fun g => (σ g).symm
  refine
    { toFun := fun π => ⟨postcomposeFamily σ π.1, ?_⟩
      invFun := fun π => ⟨postcomposeFamily σi π.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · funext g
    apply Subtype.ext
    have hπ : (omissionTail J ell).image (π.1 g.val) = (O g).val := by
      simpa [omissionOfPerm, omissionSlotsFromPerm] using
        congrArg (fun Q : OmissionChoices P (J + ell) ell => (Q g).val) π.2
    have himage :
        (omissionTail J ell).image ((π.1 g.val).trans (σ g.val)) =
          ((omissionTail J ell).image (π.1 g.val)).image (σ g.val) := by
      ext x
      simp
    calc
      _ = ((omissionTail J ell).image (π.1 g.val)).image (σ g.val) := himage
      _ = (O g).val.image (σ g.val) := by rw [hπ]
      _ = (O' g).val := omissionAlignment_map P J ell O O' g
  · funext g
    apply Subtype.ext
    have hπ : (omissionTail J ell).image (π.1 g.val) = (O' g).val := by
      simpa [omissionOfPerm, omissionSlotsFromPerm] using
        congrArg (fun Q : OmissionChoices P (J + ell) ell => (Q g).val) π.2
    have himage :
        (omissionTail J ell).image ((π.1 g.val).trans (σi g.val)) =
          ((omissionTail J ell).image (π.1 g.val)).image (σi g.val) := by
      ext x
      simp
    calc
      _ = ((omissionTail J ell).image (π.1 g.val)).image (σi g.val) := himage
      _ = (O' g).val.image (σi g.val) := by rw [hπ]
      _ = (O g).val := omissionAlignment_symm_map P J ell O O' g
  · intro π
    apply Subtype.ext
    funext g
    ext i
    simp [postcomposeFamily, σi]
  · intro π
    apply Subtype.ext
    funext g
    ext i
    simp [postcomposeFamily, σi]

noncomputable def omissionFiberSigmaEquiv (P : PrimeGroups) (J ell : ℕ) :
    (Σ O : OmissionChoices P (J + ell) ell, OmissionAssignmentFiber P J ell O) ≃
      P.Permutations (J + ell) where
  toFun x := x.2.1
  invFun π := ⟨omissionOfPerm P J ell π, ⟨π, rfl⟩⟩
  left_inv := by
    rintro ⟨O, ⟨π, hπ⟩⟩
    dsimp
    cases hπ
    rfl
  right_inv := by
    intro π
    rfl

/-- The full permutation family splits into equal-size omission fibers. -/
theorem omissionAssignmentFiber_card_total (P : PrimeGroups) (J ell : ℕ) :
    Fintype.card (P.Permutations (J + ell)) =
      Fintype.card (OmissionChoices P (J + ell) ell) *
        Fintype.card (OmissionAssignmentFiber P J ell
          (omissionOfPerm P J ell (fun _ => Equiv.refl _))) := by
  classical
  let O₀ := omissionOfPerm P J ell (fun _ => Equiv.refl _)
  have hfib (O : OmissionChoices P (J + ell) ell) :
      Fintype.card (OmissionAssignmentFiber P J ell O) =
        Fintype.card (OmissionAssignmentFiber P J ell O₀) :=
    Fintype.card_congr (omissionAssignmentFiberEquiv P J ell O O₀)
  have hcard := Fintype.card_congr (omissionFiberSigmaEquiv P J ell)
  rw [Fintype.card_sigma] at hcard
  calc
    Fintype.card (P.Permutations (J + ell)) =
        ∑ O : OmissionChoices P (J + ell) ell,
          Fintype.card (OmissionAssignmentFiber P J ell O) := hcard.symm
    _ = Fintype.card (OmissionChoices P (J + ell) ell) *
        Fintype.card (OmissionAssignmentFiber P J ell O₀) := by
      rw [show (∑ O : OmissionChoices P (J + ell) ell,
          Fintype.card (OmissionAssignmentFiber P J ell O)) =
        ∑ O : OmissionChoices P (J + ell) ell,
          Fintype.card (OmissionAssignmentFiber P J ell O₀) by
            apply Finset.sum_congr rfl
            intro O hO
            exact hfib O]
      simp
    _ = _ := by rfl

/-- With the big permutation fixed, its small omission fiber contributes
exactly one reciprocal big-permutation factor after symmetry averaging. -/
theorem omissionSmallFiber_symmetry_normalization (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell) :
    (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
      edgeSymmetryFactor P (J + ell) *
      (Fintype.card (P.Permutations (J + ell)) : ℝ) *
      (Fintype.card (OmissionSmallFiber P J ell O) : ℝ) =
      (Fintype.card (P.BigPermutations (J + ell)) : ℝ)⁻¹ := by
  classical
  let O₀ := omissionOfPerm P J ell (fun _ => Equiv.refl _)
  have hfiber : Fintype.card (OmissionAssignmentFiber P J ell O) =
      Fintype.card (P.BigPermutations (J + ell)) *
        Fintype.card (OmissionSmallFiber P J ell O) := by
    have h := Fintype.card_congr (omissionAssignmentFiberSplitEquiv P J ell O)
    simpa [Fintype.card_prod] using h
  have hfiber_eq : Fintype.card (OmissionAssignmentFiber P J ell O) =
      Fintype.card (OmissionAssignmentFiber P J ell O₀) :=
    Fintype.card_congr (omissionAssignmentFiberEquiv P J ell O O₀)
  have htotal0 := omissionAssignmentFiber_card_total P J ell
  have htotal : Fintype.card (P.Permutations (J + ell)) =
      Fintype.card (OmissionChoices P (J + ell) ell) *
        Fintype.card (OmissionAssignmentFiber P J ell O) := by
    calc
      _ = Fintype.card (OmissionChoices P (J + ell) ell) *
          Fintype.card (OmissionAssignmentFiber P J ell O₀) := by
            simpa [O₀] using htotal0
      _ = _ := by rw [← hfiber_eq]
  have hNat : Fintype.card (P.Permutations (J + ell)) =
      Fintype.card (OmissionChoices P (J + ell) ell) *
        (Fintype.card (P.BigPermutations (J + ell)) *
          Fintype.card (OmissionSmallFiber P J ell O)) := by
    rw [hfiber] at htotal
    exact htotal
  have hreal : (Fintype.card (P.Permutations (J + ell)) : ℝ) =
      (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        ((Fintype.card (P.BigPermutations (J + ell)) : ℝ) *
          (Fintype.card (OmissionSmallFiber P J ell O) : ℝ)) := by
    exact_mod_cast hNat
  have hchoices_pos : 0 < (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) := by
    have hne : Nonempty (OmissionChoices P (J + ell) ell) :=
      ⟨fun _ => ⟨omissionTail J ell, omissionTail_card J ell⟩⟩
    letI := hne
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hbig_pos : 0 < (Fintype.card (P.BigPermutations (J + ell)) : ℝ) := by
    have hne : Nonempty (P.BigPermutations (J + ell)) :=
      ⟨fun _ => Equiv.refl _⟩
    letI := hne
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hsmall_pos : 0 < (Fintype.card (OmissionSmallFiber P J ell O) : ℝ) := by
    let O₁ := omissionOfSmallPerm P J ell (fun _ => Equiv.refl _)
    have hne₁ : Nonempty (OmissionSmallFiber P J ell O₁) :=
      ⟨⟨fun _ => Equiv.refl _, rfl⟩⟩
    have hne : Nonempty (OmissionSmallFiber P J ell O) :=
      ⟨omissionSmallFiberEquiv P J ell O₁ O (Classical.choice hne₁)⟩
    letI := hne
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hperms_pos : 0 < (Fintype.card (P.Permutations (J + ell)) : ℝ) := by
    have hne : Nonempty (P.Permutations (J + ell)) :=
      ⟨fun _ => Equiv.refl _⟩
    letI := hne
    exact Nat.cast_pos.mpr Fintype.card_pos
  unfold edgeSymmetryFactor
  rw [hreal]
  field_simp [ne_of_gt hchoices_pos, ne_of_gt hbig_pos,
    ne_of_gt hsmall_pos, ne_of_gt hperms_pos]

/-- A per-permutation-pair row cost bound survives conditioning on the small
omission fiber with one big source permutation fixed. -/
theorem omissionSmallFiberAverage_le (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell)
    (πB : P.BigPermutations (J + ell))
    (f : P.Permutations (J + ell) → P.Permutations (J + ell) → ℝ)
    (C : ℝ)
    (hterm : ∀ πS : OmissionSmallFiber P J ell O,
      ∀ τ : P.Permutations (J + ell),
        f (combinePermutations P πB πS.1) τ ≤ C) :
    (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) *
        ∑ πS : OmissionSmallFiber P J ell O,
          ∑ τ : P.Permutations (J + ell),
            f (combinePermutations P πB πS.1) τ ≤
      C / (Fintype.card (P.BigPermutations (J + ell)) : ℝ) := by
  classical
  let K : ℝ := Fintype.card (P.Permutations (J + ell))
  let Fsmall : ℝ := Fintype.card (OmissionSmallFiber P J ell O)
  have hinner (πS : OmissionSmallFiber P J ell O) :
      (∑ τ : P.Permutations (J + ell),
          f (combinePermutations P πB πS.1) τ) ≤ K * C := by
    calc
      _ ≤ ∑ _τ : P.Permutations (J + ell), C :=
        Finset.sum_le_sum (fun τ _ => hterm πS τ)
      _ = K * C := by
        simp [K, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have houter :
      (∑ πS : OmissionSmallFiber P J ell O,
          ∑ τ : P.Permutations (J + ell),
            f (combinePermutations P πB πS.1) τ) ≤ Fsmall * (K * C) := by
    calc
      _ ≤ ∑ _πS : OmissionSmallFiber P J ell O, K * C :=
        Finset.sum_le_sum (fun πS _ => hinner πS)
      _ = Fsmall * (K * C) := by
        simp [Fsmall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfactor_nonneg :
      0 ≤ (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) :=
    mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  have hcancel := omissionSmallFiber_symmetry_normalization P J ell O
  calc
    _ ≤ (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) * (Fsmall * (K * C)) :=
      mul_le_mul_of_nonneg_left houter hfactor_nonneg
    _ = ((Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
          edgeSymmetryFactor P (J + ell) * K * Fsmall) * C := by ring
    _ = (Fintype.card (P.BigPermutations (J + ell)) : ℝ)⁻¹ * C := by
      dsimp [K, Fsmall]
      rw [hcancel]
    _ = C / (Fintype.card (P.BigPermutations (J + ell)) : ℝ) := by
      rw [div_eq_mul_inv]
      ring

/-- The same fiber normalization applies when the conditioned small omission
permutation is at the target endpoint. -/
theorem omissionSmallFiberTargetAverage_le (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell)
    (πB : P.BigPermutations (J + ell))
    (f : P.Permutations (J + ell) → P.Permutations (J + ell) → ℝ)
    (C : ℝ)
    (hterm : ∀ πS : OmissionSmallFiber P J ell O,
      ∀ π : P.Permutations (J + ell),
        f π (combinePermutations P πB πS.1) ≤ C) :
    (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) *
        ∑ π : P.Permutations (J + ell),
          ∑ τS : OmissionSmallFiber P J ell O,
            f π (combinePermutations P πB τS.1) ≤
      C / (Fintype.card (P.BigPermutations (J + ell)) : ℝ) := by
  classical
  let g : P.Permutations (J + ell) → P.Permutations (J + ell) → ℝ :=
    fun τ π => f π τ
  have h := omissionSmallFiberAverage_le P J ell O πB g C (by
    intro πS τ
    exact hterm πS τ)
  calc
    _ = (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) *
        ∑ τS : OmissionSmallFiber P J ell O,
          ∑ π : P.Permutations (J + ell),
            f π (combinePermutations P πB τS.1) := by
      rw [Finset.sum_comm]
    _ ≤ C / (Fintype.card (P.BigPermutations (J + ell)) : ℝ) := by
      simpa [g] using h

theorem omissionChoices_card_eq_number (F : FixedData) (P : PrimeGroups) (J : ℕ) :
    Fintype.card (OmissionChoices P (J + F.ell) F.ell) = omissionNumber F P J := by
  rw [omissionChoices_card, omissionNumber]

/-- The small omission conditioning factor cancels the size of each source
permutation fiber when combined with the two-endpoint symmetry average. -/
theorem omissionFiber_symmetry_normalization (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell) :
    (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
      edgeSymmetryFactor P (J + ell) *
      (Fintype.card (P.Permutations (J + ell)) : ℝ) *
      (Fintype.card (OmissionAssignmentFiber P J ell O) : ℝ) = 1 := by
  classical
  let O₀ := omissionOfPerm P J ell (fun _ => Equiv.refl _)
  have hFib : Fintype.card (OmissionAssignmentFiber P J ell O) =
      Fintype.card (OmissionAssignmentFiber P J ell O₀) :=
    Fintype.card_congr (omissionAssignmentFiberEquiv P J ell O O₀)
  have hcard := omissionAssignmentFiber_card_total P J ell
  have hcardO : Fintype.card (P.Permutations (J + ell)) =
      Fintype.card (OmissionChoices P (J + ell) ell) *
        Fintype.card (OmissionAssignmentFiber P J ell O) := by
    dsimp [O₀] at hFib
    rw [← hFib] at hcard
    exact hcard
  have hcardReal : (Fintype.card (P.Permutations (J + ell)) : ℝ) =
      (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        (Fintype.card (OmissionAssignmentFiber P J ell O) : ℝ) := by
    exact_mod_cast hcardO
  have hPerm : (Fintype.card (P.Permutations (J + ell)) : ℝ) ≠ 0 := by
    have hnonempty : Nonempty (P.Permutations (J + ell)) :=
      ⟨fun _ => Equiv.refl _⟩
    letI := hnonempty
    have hcardPos : 0 < Fintype.card (P.Permutations (J + ell)) := Fintype.card_pos
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  unfold edgeSymmetryFactor
  field_simp [hPerm]
  rw [hcardReal]

/-- A uniform bound for each ordered pair of endpoint permutations is
preserved after conditioning the source permutation on one omission fiber.
The exact fiber cardinal cancels the omission count and endpoint symmetry. -/
theorem omissionFiberAverage_le (P : PrimeGroups) (J ell : ℕ)
    (O : OmissionChoices P (J + ell) ell)
    (f : P.Permutations (J + ell) → P.Permutations (J + ell) → ℝ)
    (C : ℝ)
    (hterm : ∀ π τ, f π τ ≤ C) :
    (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) *
        ∑ π : OmissionAssignmentFiber P J ell O,
          ∑ τ : P.Permutations (J + ell), f π.1 τ ≤ C := by
  classical
  let K : ℝ := Fintype.card (P.Permutations (J + ell))
  let F : ℝ := Fintype.card (OmissionAssignmentFiber P J ell O)
  have hnorm := omissionFiber_symmetry_normalization P J ell O
  have hinner (π : OmissionAssignmentFiber P J ell O) :
      (∑ τ : P.Permutations (J + ell), f π.1 τ) ≤ K * C := by
    calc
      _ ≤ ∑ _τ : P.Permutations (J + ell), C :=
        Finset.sum_le_sum (fun τ _ => hterm π.1 τ)
      _ = K * C := by
        simp [K, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have houter :
      (∑ π : OmissionAssignmentFiber P J ell O,
          ∑ τ : P.Permutations (J + ell), f π.1 τ) ≤ F * (K * C) := by
    calc
      _ ≤ ∑ _π : OmissionAssignmentFiber P J ell O, K * C :=
        Finset.sum_le_sum (fun π _ => hinner π)
      _ = F * (K * C) := by
        simp [F, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hfactor_nonneg :
      0 ≤ (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) :=
    mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  calc
    _ ≤ (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
        edgeSymmetryFactor P (J + ell) * (F * (K * C)) :=
      mul_le_mul_of_nonneg_left houter hfactor_nonneg
    _ = C := by
      have hcancel :
          (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
            edgeSymmetryFactor P (J + ell) * K * F = 1 := by
        simpa [K, F, mul_assoc] using hnorm
      dsimp [K, F]
      rw [show (Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
          edgeSymmetryFactor P (J + ell) *
          ((Fintype.card (OmissionAssignmentFiber P J ell O) : ℝ) *
            ((Fintype.card (P.Permutations (J + ell)) : ℝ) * C)) =
          ((Fintype.card (OmissionChoices P (J + ell) ell) : ℝ) *
            edgeSymmetryFactor P (J + ell) *
            (Fintype.card (P.Permutations (J + ell)) : ℝ) *
            (Fintype.card (OmissionAssignmentFiber P J ell O) : ℝ)) * C by ring]
      rw [hnorm]
      ring

/-- After fixing the source big permutation, omission-fiber averaging keeps
the fixed-context row cost uniform, with the expected reciprocal big-permutation factor. -/
theorem fixedContextOmissionRowCost_le (A : Model F P J m) (r : MemoryParameters F)
    (n : ℕ) (theta : ℝ) (i : Fin n) (v : Fin A.patternCount) (u : P.Aux J)
    (s : P.MemoryState (J + F.ell)) (πB : P.BigPermutations (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell)
    (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVpos : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val,
      tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
        edgeSymmetryFactor P (J + F.ell) *
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            fixedContextRowCost A r n theta i v u s
              (combinePermutations P πB πS.1) τ S ≤
      (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
        P.memoryWeight r.v s *
        ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup)) /
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
  let C : ℝ := Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
    P.memoryWeight r.v s *
      ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
          Fintype.card P.SmallGroup)
  have hterm (πS : OmissionSmallFiber P J F.ell O)
      (τ : P.Permutations (J + F.ell)) :
      fixedContextRowCost A r n theta i v u s
        (combinePermutations P πB πS.1) τ S ≤ C := by
    simpa [C] using fixedContextRowCost_le A r n theta i v u s
      (combinePermutations P πB πS.1) τ S hVlo hVpos htilted htiltedSum
      Cprom Csmall0 hCsmall0Pos hCprom hCsmall0
  simpa [C] using omissionSmallFiberAverage_le P J F.ell O πB
    (fun π τ => fixedContextRowCost A r n theta i v u s π τ S) C hterm

/-- The dual conditioned column bound: fix the target big permutation and
average its small omission fiber after reversal. -/
theorem fixedContextOmissionColumnCost_le (A : Model F P J m) (r : MemoryParameters F)
    (n : ℕ) (theta : ℝ) (i : Fin n) (v : Fin A.patternCount) (u : P.Aux J)
    (t : P.MemoryState (J + F.ell)) (πB : P.BigPermutations (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell)
    (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVhi : ∀ g : P.Group, P.V g ≤ F.vMax)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val,
      tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
        edgeSymmetryFactor P (J + F.ell) *
        ∑ π : P.Permutations (J + F.ell),
          ∑ τS : OmissionSmallFiber P J F.ell O,
            fixedContextColumnCost A r n theta i v u t π
              (combinePermutations P πB τS.1) S ≤
      (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
        P.memoryMass F J n t * P.memoryWeight r.v t *
        ((Erdos821.P3Edge.colRevConst F m) ^ Fintype.card P.BigGroup *
          (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup)) /
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
  let C : ℝ := Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
    P.memoryMass F J n t * P.memoryWeight r.v t *
      ((Erdos821.P3Edge.colRevConst F m) ^ Fintype.card P.BigGroup *
        (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
          Fintype.card P.SmallGroup)
  have hterm (τS : OmissionSmallFiber P J F.ell O)
      (π : P.Permutations (J + F.ell)) :
      fixedContextColumnCost A r n theta i v u t π
        (combinePermutations P πB τS.1) S ≤ C := by
    simpa [C] using fixedContextColumnCost_le A r n theta i v u t π
      (combinePermutations P πB τS.1) S hVlo hVhi htilted htiltedSum
      Cprom Csmall0 hCsmall0Pos hCprom hCsmall0
  simpa [C] using omissionSmallFiberTargetAverage_le P J F.ell O πB
    (fun π τ => fixedContextColumnCost A r n theta i v u t π τ S) C hterm

def omittedChoiceProduct {P : PrimeGroups} {M ell : ℕ} (a : P.Labels M)
    (O : OmissionChoices P M ell) : ℕ :=
  omittedPrimeProduct a (fun g => (O g).val)

def omittedChoiceProductReal {P : PrimeGroups} {M ell : ℕ} (a : P.Labels M)
    (O : OmissionChoices P M ell) : ℝ :=
  ∏ g : P.SmallGroup, ∏ i ∈ (O g).val, (a g.val i).val

theorem omittedChoiceProduct_unfold {P : PrimeGroups} {M ell : ℕ}
    (a : P.Labels M) (O : OmissionChoices P M ell) :
    omittedChoiceProduct a O =
      ∏ g : P.SmallGroup, ∏ i ∈ (O g).val, (a g.val i).val := by
  classical
  unfold omittedChoiceProduct omittedPrimeProduct omittedSlots
  rw [Finset.prod_sigma]
  rfl

theorem omittedChoiceProductReal_eq_cast {P : PrimeGroups} {M ell : ℕ}
    (a : P.Labels M) (O : OmissionChoices P M ell) :
    omittedChoiceProductReal a O = (omittedChoiceProduct a O : ℝ) := by
  rw [omittedChoiceProduct_unfold]
  simp [omittedChoiceProductReal, Nat.cast_prod]

theorem real_exp_nat_pow (x : ℝ) (n : ℕ) :
    Real.exp x ^ n = Real.exp (x * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add, Nat.cast_succ]
      ring

theorem omittedChoiceProductReal_le_exp {F : FixedData} {P : PrimeGroups}
    {J : ℕ} {x : ℝ} (hAdm : P.Admissible F x)
    (a : P.Labels (J + F.ell)) (O : OmissionChoices P (J + F.ell) F.ell) :
    omittedChoiceProductReal a O ≤
      Real.exp ((F.ell : ℝ) * (P.smallGroups.card : ℝ) * (L x) ^ F.b) := by
  classical
  let B : ℝ := Real.exp ((L x) ^ F.b)
  have hprime (g : P.SmallGroup) (i : Fin (J + F.ell)) :
      ((a g.val i).val : ℝ) ≤ B := by
    have hrange := hAdm.2.2.2.2.2 g.val (a g.val i).val (a g.val i).property
    have hrange' : Real.exp ((L x) ^ F.a) ≤ (a g.val i).val ∧
        (a g.val i).val ≤ Real.exp ((L x) ^ F.b) := by
      simpa [g.property] using hrange
    simpa [B] using hrange'.2
  have hgroup (g : P.SmallGroup) :
      (∏ i ∈ (O g).val, ((a g.val i).val : ℝ)) ≤ B ^ F.ell := by
    calc
      _ ≤ ∏ i ∈ (O g).val, B := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Nat.cast_nonneg _
        · intro i hi
          exact hprime g i
      _ = B ^ (O g).val.card := by simp
      _ = B ^ F.ell := by rw [(O g).property]
  calc
    _ ≤ ∏ g : P.SmallGroup, B ^ F.ell := by
      apply Finset.prod_le_prod₀
      · intro g hg
        positivity
      · intro g hg
        exact hgroup g
    _ = B ^ (F.ell * P.smallGroups.card) := by
      rw [Finset.prod_const, Finset.card_univ]
      rw [pow_mul]
      congr 1
      have hsmall : Fintype.card P.SmallGroup = P.smallGroups.card := by
        simpa [PrimeGroups.SmallGroup, PrimeGroups.smallGroups] using
          (Fintype.card_subtype (fun g : P.Group => P.big g = false))
      exact hsmall
    _ = Real.exp ((F.ell : ℝ) * (P.smallGroups.card : ℝ) * (L x) ^ F.b) := by
      dsimp [B]
      rw [real_exp_nat_pow]
      congr 1
      push_cast
      ring

theorem const_log_mul_rpow_lt {C alpha beta : ℝ} (hC : 0 < C) (hαβ : alpha < beta) :
    ∀ᶠ y : ℝ in atTop, C * Real.log y * y ^ alpha < y ^ beta := by
  let delta : ℝ := (beta - alpha) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hpow : Tendsto (fun y : ℝ => y ^ delta) atTop atTop := tendsto_rpow_atTop hdelta
  have hlarge : ∀ᶠ y : ℝ in atTop, C / delta < y ^ delta :=
    hpow.eventually_gt_atTop (C / delta)
  have hypos : ∀ᶠ y : ℝ in atTop, 0 < y := eventually_gt_atTop (0 : ℝ)
  filter_upwards [hlarge, hypos] with y hlarge hy
  have hlog : delta * Real.log y ≤ y ^ delta := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy delta)
    rw [Real.log_rpow hy] at h
    linarith
  have hCdelta : 0 < C / delta := div_pos hC hdelta
  have hmain : C * Real.log y < y ^ (beta - alpha) := by
    have hupper : C * Real.log y ≤ (C / delta) * y ^ delta := by
      calc
        _ = (C / delta) * (delta * Real.log y) := by
          field_simp [ne_of_gt hdelta]
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog hCdelta.le
    have hsq := mul_lt_mul_of_pos_right hlarge (Real.rpow_pos_of_pos hy delta)
    calc
      _ ≤ (C / delta) * y ^ delta := hupper
      _ < y ^ delta * y ^ delta := hsq
      _ = y ^ (beta - alpha) := by
        calc
          _ = y ^ (delta + delta) := (Real.rpow_add hy delta delta).symm
          _ = y ^ (beta - alpha) := by
            rw [show delta + delta = beta - alpha by dsimp [delta]; ring]
  calc
    _ < y ^ (beta - alpha) * y ^ alpha :=
      mul_lt_mul_of_pos_right hmain (Real.rpow_pos_of_pos hy alpha)
    _ = y ^ beta := by
      calc
        _ = y ^ ((beta - alpha) + alpha) := (Real.rpow_add hy (beta - alpha) alpha).symm
        _ = y ^ beta := by congr 1 <;> ring

theorem rpow_lt_exp_rpow_eventually {C beta : ℝ} (hbeta : 0 < beta) :
    ∀ᶠ y : ℝ in atTop, y ^ C < Real.exp (y ^ beta) := by
  let C' : ℝ := max 1 C
  have hC' : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog := const_log_mul_rpow_lt hC' (show 0 < beta by exact hbeta)
  have hlog' : ∀ᶠ y : ℝ in atTop, C' * Real.log y < y ^ beta := by
    filter_upwards [hlog] with y hy
    simpa using hy
  have hy : ∀ᶠ y : ℝ in atTop, 1 < y := eventually_gt_atTop (1 : ℝ)
  filter_upwards [hlog', hy] with y hlogy hy
  have hypos : 0 < y := lt_trans zero_lt_one hy
  have hpow : y ^ C ≤ y ^ C' :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hy) (le_max_right _ _)
  have hpowExp : y ^ C' < Real.exp (y ^ beta) := by
    rw [Real.rpow_def_of_pos hypos C']
    apply Real.exp_lt_exp.mpr
    nlinarith [hlogy]
  exact hpow.trans_lt hpowExp

theorem not_dvd_int_of_natAbs_lt {p : ℕ} (k : ℤ) (hk0 : k ≠ 0)
    (hlt : k.natAbs < p) : ¬ (p : ℤ) ∣ k := by
  intro hdiv
  have hle := Int.natAbs_le_of_dvd_ne_zero hdiv hk0
  have hle' : p ≤ k.natAbs := by simpa using hle
  omega

theorem not_dvd_bigPrime_of_small_k {x : ℝ} (C₂ : ℝ) {p : ℕ} (k : ℤ)
    (hk0 : k ≠ 0) (hK : (|k| : ℝ) ≤ (L x) ^ C₂)
    (hlarge : (L x) ^ C₂ < (p : ℝ)) : ¬ (p : ℤ) ∣ k := by
  have hAbsCast : (k.natAbs : ℝ) = (|k| : ℝ) := by
    calc
      _ = ((k.natAbs : ℤ) : ℝ) := by
        symm
        exact Int.cast_natCast _
      _ = ((|k| : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs k)
      _ = _ := by rw [Int.cast_abs]
  have hnatAbsLt : (k.natAbs : ℝ) < (p : ℝ) := by
    rw [hAbsCast]
    exact lt_of_le_of_lt hK hlarge
  exact not_dvd_int_of_natAbs_lt k hk0 (by exact_mod_cast hnatAbsLt)

/-- Big-group primes eventually exceed any fixed logarithmic power. -/
theorem bigPrime_gt_logpow_eventually (F : FixedData) (C₂ : ℝ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
        (L x) ^ C₂ < (p.val : ℝ) := by
  have hc : 0 < F.c := lt_trans F.a_pos (lt_trans F.ab F.bc)
  have hPow := rpow_lt_exp_rpow_eventually (C := C₂) hc
  have hEv : ∀ᶠ x : ℝ in atTop, (L x) ^ C₂ < Real.exp ((L x) ^ F.c) :=
    Real.tendsto_log_atTop.eventually hPow
  rcases Filter.eventually_atTop.1 hEv with ⟨x₀, hx₀⟩
  refine ⟨x₀, ?_⟩
  intro x hx P hAdm g p
  have hbase := hx₀ x hx
  have hrange := hAdm.2.2.2.2.2 g.val p.val p.property
  have hbig : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) ∧
      (p.val : ℝ) ≤ Real.exp ((L x) ^ F.d) := by
    simpa [g.property] using hrange
  exact hbase.trans_le hbig.1

/-- The source k-size condition rules out a big prime dividing k. -/
theorem bigPrime_not_dvd_k_of_bound {F : FixedData} {x C₂ : ℝ}
    (P : PrimeGroups) (hAdm : P.Admissible F x) (g : P.BigGroup)
    (p : P.Prime g.val) (k : ℤ) (hk : 0 < |k|)
    (hK : (|k| : ℝ) ≤ (L x) ^ C₂)
    (hlarge : (L x) ^ C₂ < (p.val : ℝ)) : ¬ (p.val : ℤ) ∣ k := by
  have hk0 : k ≠ 0 := by
    intro h
    simp [h] at hk
  exact not_dvd_bigPrime_of_small_k C₂ k hk0 hK hlarge

/-- Eventually every omitted small-prime product is below every eligible big prime. -/
theorem omittedChoiceProduct_lt_bigPrime_eventually (F : FixedData) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ J : ℕ, ∀ a : P.Labels (J + F.ell),
        ∀ O : OmissionChoices P (J + F.ell) F.ell,
          ∀ g : P.BigGroup, ∀ p : P.Prime g.val,
            omittedChoiceProduct a O < p.val := by
  let C : ℝ := (F.ell : ℝ) * F.C₀
  have hell : 0 < (F.ell : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one F.ell_pos)
  have hC : 0 < C := by dsimp [C]; exact mul_pos hell F.C₀_pos
  have hlog := const_log_mul_rpow_lt hC F.bc
  have hlogX : ∀ᶠ x : ℝ in atTop,
      C * Real.log (L x) * (L x) ^ F.b < (L x) ^ F.c :=
    Real.tendsto_log_atTop.eventually hlog
  have hL : ∀ᶠ x : ℝ in atTop, 1 < L x :=
    Real.tendsto_log_atTop.eventually_gt_atTop 1
  have hAll := hlogX.and hL
  rcases Filter.eventually_atTop.1 hAll with ⟨x₀, hx₀⟩
  refine ⟨x₀, ?_⟩
  intro x hx P hAdm J a O g p
  obtain ⟨hlogx, hLx⟩ := hx₀ x hx
  have hsmallCard : (P.smallGroups.card : ℝ) ≤ F.C₀ * T x := hAdm.2.1
  have hcount :
      (F.ell : ℝ) * (P.smallGroups.card : ℝ) * (L x) ^ F.b ≤
        C * Real.log (L x) * (L x) ^ F.b := by
    have hmul := mul_le_mul_of_nonneg_left hsmallCard (Nat.cast_nonneg F.ell)
    have hLpos : 0 < L x := lt_trans zero_lt_one hLx
    have hyPow : 0 ≤ (L x) ^ F.b := Real.rpow_nonneg hLpos.le _
    calc
      _ ≤ ((F.ell : ℝ) * (F.C₀ * T x)) * (L x) ^ F.b :=
        mul_le_mul_of_nonneg_right hmul hyPow
      _ = C * Real.log (L x) * (L x) ^ F.b := by
        dsimp [C, T]
        ring
  have hprod := omittedChoiceProductReal_le_exp hAdm a O
  have hbigRange := hAdm.2.2.2.2.2 g.val p.val p.property
  have hpLower : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) := by
    have hpair : Real.exp ((L x) ^ F.c) ≤ (p.val : ℝ) ∧
        (p.val : ℝ) ≤ Real.exp ((L x) ^ F.d) := by
      simpa [g.property] using hbigRange
    exact hpair.1
  have hltReal : omittedChoiceProductReal a O < (p.val : ℝ) := by
    calc
      _ ≤ Real.exp ((F.ell : ℝ) * (P.smallGroups.card : ℝ) * (L x) ^ F.b) := hprod
      _ < Real.exp ((L x) ^ F.c) := Real.exp_lt_exp.mpr (lt_of_le_of_lt hcount hlogx)
      _ ≤ (p.val : ℝ) := hpLower
  have hltNat : (omittedChoiceProduct a O : ℝ) < (p.val : ℝ) := by
    rw [← omittedChoiceProductReal_eq_cast a O]
    exact hltReal
  exact_mod_cast hltNat

theorem omittedChoiceProduct_pos {P : PrimeGroups} {M ell : ℕ}
    (a : P.Labels M) (O : OmissionChoices P M ell) : 0 < omittedChoiceProduct a O := by
  have hreal : 0 < omittedChoiceProductReal a O := by
    unfold omittedChoiceProductReal
    apply Finset.prod_pos
    intro g hg
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast (P.prime g.val (a g.val i).val (a g.val i).property).pos
  rw [omittedChoiceProductReal_eq_cast] at hreal
  exact_mod_cast hreal

def smallLabelProduct {P : PrimeGroups} {M : ℕ} (a : P.Labels M) : ℕ :=
  ∏ g : P.SmallGroup, ∏ i : Fin M, (a g.val i).val

theorem smallLabelProduct_eq_slots {P : PrimeGroups} {M : ℕ} (a : P.Labels M) :
    smallLabelProduct a = (Finset.univ : Finset (SmallSlot P M)).prod (smallSlotPrime a) := by
  classical
  unfold smallLabelProduct
  change (∏ g : P.SmallGroup, ∏ i : Fin M, (a g.val i).val) =
    ∏ z : SmallSlot P M, (a z.1.val z.2).val
  exact (Fintype.prod_sigma (fun z : SmallSlot P M => (a z.1.val z.2).val)).symm

theorem bigPrime_not_dvd_smallLabelProduct {P : PrimeGroups} {M : ℕ}
    (a : P.Labels M) (g : P.BigGroup) (p : P.Prime g.val) :
    ¬ p.val ∣ smallLabelProduct a := by
  classical
  have hp : Nat.Prime p.val := P.prime g.val p.val p.property
  intro hdiv
  rw [smallLabelProduct_eq_slots] at hdiv
  obtain ⟨z, hz, hzdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdiv
  let q := a z.1.val z.2
  have hq : Nat.Prime q.val := P.prime z.1.val q.val q.property
  have hgroups : z.1.val ≠ g.val := by
    intro he
    have hb := congrArg P.big he
    rw [z.1.property, g.property] at hb
    cases hb
  have hval : p.val ≠ q.val := by
    intro he
    have hmem : q.val ∈ P.primes g.val := by simpa [q, he] using p.property
    exact (Finset.disjoint_left.mp (P.disjoint z.1.val g.val hgroups)) q.property hmem
  have heq := (Nat.prime_dvd_prime_iff_eq hp hq).mp hzdvd
  exact hval heq

def sourceSmallHeadProduct {P : PrimeGroups} {J ell : ℕ}
    (a : P.Labels (J + ell)) (π : P.Permutations (J + ell)) : ℕ :=
  ∏ g : P.SmallGroup, ∏ j : Fin J,
    (a g.val (π g.val (Fin.castAdd ell j))).val

theorem omittedChoiceProduct_eq_tailProduct {P : PrimeGroups} {J ell : ℕ}
    (a : P.Labels (J + ell)) (π : P.Permutations (J + ell)) :
    omittedChoiceProduct a (omissionOfPerm P J ell π) =
      ∏ g : P.SmallGroup, ∏ k : Fin ell,
        (a g.val (π g.val (Fin.natAdd J k))).val := by
  classical
  rw [omittedChoiceProduct_unfold]
  apply Finset.prod_congr rfl
  intro g hg
  let f : Fin ell → Fin (J + ell) := fun k => π g.val (Fin.natAdd J k)
  have hinj : Function.Injective f := by
    intro k l h
    have h' : π g.val (Fin.natAdd J k) = π g.val (Fin.natAdd J l) := by simpa [f] using h
    have htail : Fin.natAdd J k = Fin.natAdd J l := (π g.val).injective h'
    apply Fin.ext
    have hv := congrArg Fin.val htail
    simp only [Fin.natAdd] at hv
    omega
  have himage : (omissionSlotsFromPerm (π g.val)) = Finset.univ.image f := by
    unfold omissionSlotsFromPerm omissionTail
    rw [Finset.image_image]
    change Finset.univ.image (fun k : Fin ell => π g.val (Fin.natAdd J k)) =
      Finset.univ.image f
    rfl
  change (∏ i ∈ omissionSlotsFromPerm (π g.val), (a g.val i).val) = _
  rw [himage, Finset.prod_image hinj.injOn]

/-- The full small-prime product splits into retained source labels and omissions. -/
theorem smallLabelProduct_source_split {P : PrimeGroups} {J ell : ℕ}
    (a : P.Labels (J + ell)) (π : P.Permutations (J + ell)) :
    smallLabelProduct a =
      sourceSmallHeadProduct a π * omittedChoiceProduct a (omissionOfPerm P J ell π) := by
  classical
  have hgroup (g : P.SmallGroup) :
      (∏ i : Fin (J + ell), (a g.val i).val) =
        (∏ j : Fin J, (a g.val (π g.val (Fin.castAdd ell j))).val) *
          (∏ k : Fin ell, (a g.val (π g.val (Fin.natAdd J k))).val) := by
    let f : Fin (J + ell) → ℕ := fun i => (a g.val (π g.val i)).val
    calc
      _ = ∏ i : Fin (J + ell), f i := by
        symm
        exact Equiv.prod_comp (π g.val) (fun i => (a g.val i).val)
      _ = ∏ z : Fin J ⊕ Fin ell, f (finSumFinEquiv z) :=
        (Equiv.prod_comp finSumFinEquiv f).symm
      _ = (∏ j : Fin J, f (finSumFinEquiv (Sum.inl j))) *
            ∏ k : Fin ell, f (finSumFinEquiv (Sum.inr k)) := by
        rw [Fintype.prod_sum_type]
      _ = _ := by
        simp [f, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  calc
    _ = ∏ g : P.SmallGroup,
          ((∏ j : Fin J, (a g.val (π g.val (Fin.castAdd ell j))).val) *
            ∏ k : Fin ell, (a g.val (π g.val (Fin.natAdd J k))).val) := by
      apply Finset.prod_congr rfl
      intro g hg
      exact hgroup g
    _ = (∏ g : P.SmallGroup, ∏ j : Fin J,
          (a g.val (π g.val (Fin.castAdd ell j))).val) *
        ∏ g : P.SmallGroup, ∏ k : Fin ell,
          (a g.val (π g.val (Fin.natAdd J k))).val := Finset.prod_mul_distrib
    _ = sourceSmallHeadProduct a π * omittedChoiceProduct a (omissionOfPerm P J ell π) := by
      rw [omittedChoiceProduct_eq_tailProduct]
      rfl

def patternSmallPart {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) : ℕ :=
  ∏ g : P.Group, ∏ j : Fin J,
    if P.big g = false then (a g (ν.slot j)).val else 1

def patternBigPart {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J) : ℕ :=
  ∏ g : P.Group, ∏ j : Fin J,
    if P.big g = true then
      if j ∈ ν.changed g then (u g j).val else (a g (ν.slot j)).val
    else 1

theorem prod_smallGroup_if_false {P : PrimeGroups} {J : ℕ}
    (f : P.Group → Fin J → ℕ) :
    (∏ g : P.Group, ∏ j : Fin J, if P.big g = false then f g j else 1) =
      ∏ g : P.SmallGroup, ∏ j : Fin J, f g.val j := by
  classical
  calc
    _ = ∏ g ∈ P.smallGroups, ∏ j : Fin J, f g j := by
      simp [PrimeGroups.smallGroups, Finset.prod_filter]
    _ = ∏ g : P.SmallGroup, ∏ j : Fin J, f g.val j := by
      exact Finset.prod_subtype (p := fun g : P.Group => P.big g = false)
        P.smallGroups (by intro g; simp [PrimeGroups.smallGroups])
        (fun g => ∏ j : Fin J, f g j)

theorem pattern_D_split {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J) :
    ν.D a u = patternSmallPart ν a * patternBigPart ν a u := by
  classical
  have hterm (g : P.Group) (j : Fin J) :
      (if j ∈ ν.changed g then (u g j).val else (a g (ν.slot j)).val) =
        (if P.big g = false then (a g (ν.slot j)).val else 1) *
          (if P.big g = true then
            (if j ∈ ν.changed g then (u g j).val else (a g (ν.slot j)).val)
            else 1) := by
    cases hb : P.big g with
    | false =>
        have hchanged := ν.small g hb
        have hj : j ∉ ν.changed g := by simp [hchanged]
        simp [hb, hj]
    | true => simp [hb]
  calc
    _ = ∏ g : P.Group, ∏ j : Fin J,
          ((if P.big g = false then (a g (ν.slot j)).val else 1) *
            (if P.big g = true then
              (if j ∈ ν.changed g then (u g j).val else (a g (ν.slot j)).val)
              else 1)) := by
        unfold Pattern.D
        apply Finset.prod_congr rfl
        intro g hg
        apply Finset.prod_congr rfl
        intro j hj
        exact hterm g j
    _ = ∏ g : P.Group,
          ((∏ j : Fin J, if P.big g = false then (a g (ν.slot j)).val else 1) *
            ∏ j : Fin J, if P.big g = true then
              (if j ∈ ν.changed g then (u g j).val else (a g (ν.slot j)).val)
              else 1) := by
        apply Finset.prod_congr rfl
        intro g hg
        rw [Finset.prod_mul_distrib]
    _ = (∏ g : P.Group, ∏ j : Fin J,
            if P.big g = false then (a g (ν.slot j)).val else 1) *
          (∏ g : P.Group, ∏ j : Fin J,
            if P.big g = true then
              (if j ∈ ν.changed g then (u g j).val else (a g (ν.slot j)).val)
              else 1) := Finset.prod_mul_distrib
    _ = patternSmallPart ν a * patternBigPart ν a u := rfl

theorem patternBigPart_eq_of_bigRestriction {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J)
    (π π' : P.Permutations (J + ell))
    (hπ : ∀ g : P.BigGroup, π g.val = π' g.val) :
    patternBigPart ν (P.act π a) u = patternBigPart ν (P.act π' a) u := by
  classical
  unfold patternBigPart
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro j hj
  cases hb : P.big g with
  | false => simp [hb]
  | true =>
      have heq := hπ ⟨g, hb⟩
      simp [hb, heq, PrimeGroups.act]

theorem patternSmallPart_act_eq_sourceHead {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (π : P.Permutations (J + ell)) :
    patternSmallPart ν (P.act π a) = sourceSmallHeadProduct a π := by
  classical
  unfold patternSmallPart sourceSmallHeadProduct
  rw [prod_smallGroup_if_false]
  apply Finset.prod_congr rfl
  intro g hg
  apply Finset.prod_congr rfl
  intro j hj
  simp only [PrimeGroups.act]
  apply congrArg (fun k : Fin (J + ell) => (a g.val (π g.val k)).val)
  apply Fin.ext
  rfl

theorem pattern_D_mul_omitted_eq {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J)
    (π : P.Permutations (J + ell)) :
    ν.D (P.act π a) u * omittedChoiceProduct a (omissionOfPerm P J ell π) =
      patternBigPart ν (P.act π a) u * smallLabelProduct a := by
  rw [pattern_D_split, patternSmallPart_act_eq_sourceHead, smallLabelProduct_source_split]
  ring

theorem patternBigPart_not_dvd_of_D_not_dvd {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (a : P.Labels (J + ell)) (u : P.Aux J)
    (p : ℕ) (hD : ¬ p ∣ ν.D a u) : ¬ p ∣ patternBigPart ν a u := by
  intro hB
  apply hD
  rw [pattern_D_split]
  rcases hB with ⟨k, hk⟩
  refine ⟨patternSmallPart ν a * k, ?_⟩
  rw [hk]
  ring

theorem promotionZModConstant_ne_zero {p : ℕ} (hp : Nat.Prime p)
    (k : ℤ) (hk : ¬ (p : ℤ) ∣ k) (B S : ℕ)
    (hB : ¬ p ∣ B) (hS : ¬ p ∣ S) (forward : Bool) :
    (if forward then (k : ZMod p) * (B : ZMod p) * (S : ZMod p)
      else -((k : ZMod p) * (B : ZMod p) * (S : ZMod p))) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hkz : (k : ZMod p) ≠ 0 := by
    intro h
    exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h)
  have hBz : (B : ZMod p) ≠ 0 := by
    intro h
    exact hB ((CharP.cast_eq_zero_iff (ZMod p) p B).mp h)
  have hSz : (S : ZMod p) ≠ 0 := by
    intro h
    exact hS ((CharP.cast_eq_zero_iff (ZMod p) p S).mp h)
  have hprod : (k : ZMod p) * (B : ZMod p) * (S : ZMod p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hkz hBz) hSz
  by_cases hf : forward <;> simp [hf, hprod]

theorem edgeDelta_mul_omitted_eq {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (a : P.Labels (J + F.ell)) (π : P.Permutations (J + F.ell))
    (forward : Bool) (p B S : ℕ)
    (hDF : ν.D (P.act π a) u * omittedChoiceProduct a (omissionOfPerm P J F.ell π) = B * S) :
    (edgeDelta A ν forward (P.act π a) u : ZMod p) *
        (omittedChoiceProduct a (omissionOfPerm P J F.ell π) : ZMod p) =
      if forward then (A.k : ZMod p) * (B : ZMod p) * (S : ZMod p)
      else -((A.k : ZMod p) * (B : ZMod p) * (S : ZMod p)) := by
  have hcast : (ν.D (P.act π a) u : ZMod p) *
      (omittedChoiceProduct a (omissionOfPerm P J F.ell π) : ZMod p) =
      (B : ZMod p) * (S : ZMod p) := by
    calc
      _ = ((ν.D (P.act π a) u * omittedChoiceProduct a (omissionOfPerm P J F.ell π) : ℕ) : ZMod p) := by
        simp [Nat.cast_mul]
      _ = ((B * S : ℕ) : ZMod p) := congrArg (fun n : ℕ => (n : ZMod p)) hDF
      _ = _ := by simp [Nat.cast_mul]
  cases forward with
  | false =>
      have hdelta :
          (edgeDelta A ν false (P.act π a) u : ZMod p) =
            -((A.k : ZMod p) * (ν.D (P.act π a) u : ZMod p)) := by
        simp [edgeDelta, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
      calc
        _ = -((A.k : ZMod p) * (ν.D (P.act π a) u : ZMod p)) *
              (omittedChoiceProduct a (omissionOfPerm P J F.ell π) : ZMod p) := by rw [hdelta]
        _ = -((A.k : ZMod p) *
              ((ν.D (P.act π a) u : ZMod p) *
                (omittedChoiceProduct a (omissionOfPerm P J F.ell π) : ZMod p))) := by ring
        _ = -((A.k : ZMod p) * ((B : ZMod p) * (S : ZMod p))) := by rw [hcast]
        _ = _ := by simp <;> ring
  | true =>
      have hdelta :
          (edgeDelta A ν true (P.act π a) u : ZMod p) =
            (A.k : ZMod p) * (ν.D (P.act π a) u : ZMod p) := by
        simp [edgeDelta, Int.cast_mul, Int.cast_natCast]
      calc
        _ = (A.k : ZMod p) * (ν.D (P.act π a) u : ZMod p) *
              (omittedChoiceProduct a (omissionOfPerm P J F.ell π) : ZMod p) := by rw [hdelta]
        _ = (A.k : ZMod p) *
              ((ν.D (P.act π a) u : ZMod p) *
                (omittedChoiceProduct a (omissionOfPerm P J F.ell π) : ZMod p)) := by ring
        _ = (A.k : ZMod p) * ((B : ZMod p) * (S : ZMod p)) := by rw [hcast]
        _ = _ := by simp <;> ring

/-- A valid old-particle promotion pins the translated residue and excludes D. -/
theorem rawEdgeValid_promotion_data {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) (tr : TransferChoice s)
    (hvalid : rawEdgeValid A ν forward u s t tr) (g : P.BigGroup)
    (j : {j : Fin (J + F.ell) // j ∈ tr.2.1 g}) :
    ∃ z : P.Particle g.val, z = memoryEntry (s.2.2 g) (tr.2.2 g j) ∧
      z.1 = t.2.1 g.val j.val ∧
      z.2 + (edgeDelta A ν forward s.2.1 u : ZMod z.1.val) = 0 ∧
      ¬ z.1.val ∣ ν.D s.2.1 u := by
  rcases hvalid with ⟨_, _, _, _, _, hgroups⟩
  rcases hgroups g with ⟨_, _, _, hdata, _⟩
  have hj := hdata j
  change
    (let z := memoryEntry (s.2.2 g) (tr.2.2 g j);
      z.1 = t.2.1 g.val j.val ∧
        z.2 + (edgeDelta A ν forward s.2.1 u : ZMod z.1.val) = 0 ∧
          ¬ z.1.val ∣ ν.D s.2.1 u) at hj
  exact ⟨memoryEntry (s.2.2 g) (tr.2.2 g j), rfl, hj.1, hj.2.1, hj.2.2⟩

/-- Compatibility leaves the dilation product unchanged across a valid edge. -/
theorem rawEdgeValid_D_eq {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) (tr : TransferChoice s)
    (hvalid : rawEdgeValid A ν forward u s t tr) :
    ν.D s.2.1 u = ν.D t.2.1 u := by
  rcases hvalid with ⟨_, _, hcompat, _, _, _⟩
  exact compatible_D_eq ν s.2.1 t.2.1 u hcompat

/-- A particle stored on a valid edge also avoids the target dilation product,
which is the exclusion needed after reversing that edge. -/
theorem rawEdgeValid_store_not_dvd_target {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) (tr : TransferChoice s)
    (hvalid : rawEdgeValid A ν forward u s t tr) (g : P.BigGroup)
    (i : Fin (J + F.ell)) (hi : i ∈ tr.1 g) :
    ¬ (s.2.1 g.val i).val ∣ ν.D t.2.1 u := by
  have hD := rawEdgeValid_D_eq A ν forward u s t tr hvalid
  rcases hvalid with ⟨_, _, _, _, _, hgroups⟩
  have hstore := (hgroups g).1 i hi
  rw [← hD]
  exact hstore.2

theorem translateParticle_cancel {P : PrimeGroups} {g : P.Group}
    (delta : ℤ) (z : P.Particle g) :
    translateParticle (-delta) (translateParticle delta z) = z := by
  rcases z with ⟨p, r⟩
  change (⟨p, (r + (delta : ZMod p.val)) + ((-delta : ℤ) : ZMod p.val)⟩ :
    P.Particle g) = ⟨p, r⟩
  have hr : r + (delta : ZMod p.val) + ((-delta : ℤ) : ZMod p.val) = r := by simp
  exact Sigma.ext rfl (heq_of_eq hr)

theorem translateMemory_add {P : PrimeGroups} {g : P.Group}
    (delta : ℤ) (z w : P.Memory g) :
    translateMemory delta (z + w) = translateMemory delta z + translateMemory delta w := by
  simp [translateMemory, Multiset.map_add]

theorem translateMemory_cancel {P : PrimeGroups} {g : P.Group}
    (delta : ℤ) (z : P.Memory g) :
    translateMemory (-delta) (translateMemory delta z) = z := by
  simp only [translateMemory, Multiset.map_map]
  calc
    _ = Multiset.map (fun x => translateParticle (-delta) (translateParticle delta x)) z := by rfl
    _ = Multiset.map id z := by
      apply Multiset.map_congr rfl
      intro x hx
      exact translateParticle_cancel delta x
    _ = z := Multiset.map_id z

theorem translateSmallResidues_cancel {P : PrimeGroups}
    (delta : ℤ) (y : P.SmallResidues) :
    translateSmallResidues (-delta) (translateSmallResidues delta y) = y := by
  funext g p
  simp [translateSmallResidues, add_assoc]

/-- The signed translation increment changes sign under reversal of a valid
compatible edge. -/
theorem edgeDelta_reverse_eq {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell))
    (hcompat : ν.compatible s.2.1 t.2.1) :
    edgeDelta A ν (!forward) t.2.1 u = -edgeDelta A ν forward s.2.1 u := by
  have hD : ν.D s.2.1 u = ν.D t.2.1 u :=
    compatible_D_eq ν s.2.1 t.2.1 u hcompat
  cases forward <;> simp [edgeDelta, hD]

/-- Index pending particles by their big group and their multiset position. -/
abbrev OldMemoryIndex {P : PrimeGroups} {M : ℕ} (s : P.MemoryState M) :=
  Σ g : P.BigGroup, Fin (s.2.2 g).card

theorem oldMemoryIndex_card {P : PrimeGroups} {M : ℕ} (s : P.MemoryState M) :
    Fintype.card (OldMemoryIndex s) = P.memorySize s := by
  classical
  simp [OldMemoryIndex, PrimeGroups.memorySize, Fintype.card_sigma]

/-- The old-memory indices carrying a given particle record its multiset count. -/
theorem memoryEntry_fiber_card {P : PrimeGroups} {g : P.Group}
    (z : P.Memory g) (q : P.Particle g) :
    Fintype.card {i : Fin z.card // memoryEntry z i = q} = z.count q := by
  classical
  calc
    _ = (Finset.univ.filter (fun i : Fin z.card => memoryEntry z i = q)).card := by
      rw [Fintype.card_subtype]
    _ = (Finset.univ.val.map (memoryEntry z)).count q := by
      rw [Multiset.count_map]
      change (Finset.univ.filter (fun i : Fin z.card => memoryEntry z i = q)).card =
        (Finset.univ.filter (fun i : Fin z.card => q = memoryEntry z i)).card
      congr 1
      ext i
      simp [eq_comm]
    _ = z.count q := by rw [memoryEntry_enumeration]

/-- A multiset subobject embeds its occurrence indices into those of the larger
multiset, preserving numerical particle values even when entries repeat. -/
theorem memoryEntry_embedding_of_le {P : PrimeGroups} {g : P.Group}
    (w z : P.Memory g) (hwz : w ≤ z) :
    ∃ f : Fin w.card ↪ Fin z.card, ∀ i, memoryEntry z (f i) = memoryEntry w i := by
  classical
  let Fiber (v : P.Memory g) (q : P.Particle g) :=
    {i : Fin v.card // memoryEntry v i = q}
  have hcard (q : P.Particle g) : Fintype.card (Fiber w q) ≤ Fintype.card (Fiber z q) := by
    rw [memoryEntry_fiber_card, memoryEntry_fiber_card]
    exact Multiset.count_le_of_le q hwz
  let fiberEmbed (q : P.Particle g) : Fiber w q ↪ Fiber z q :=
    Classical.choice (Function.Embedding.nonempty_iff_card_le.mpr (hcard q))
  let sourceEquiv : Fin w.card ≃ (Σ q : P.Particle g, Fiber w q) :=
    { toFun := fun i => ⟨memoryEntry w i, ⟨i, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨q, ⟨i, hi⟩⟩
        cases hi
        rfl }
  let targetEquiv : Fin z.card ≃ (Σ q : P.Particle g, Fiber z q) :=
    { toFun := fun i => ⟨memoryEntry z i, ⟨i, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨q, ⟨i, hi⟩⟩
        cases hi
        rfl }
  let sigmaEmbed : (Σ q : P.Particle g, Fiber w q) ↪
      (Σ q : P.Particle g, Fiber z q) :=
    { toFun := fun x => ⟨x.1, fiberEmbed x.1 x.2⟩
      inj' := by
        rintro ⟨q, x⟩ ⟨q', y⟩ h
        have hq : q = q' := congrArg Sigma.fst h
        subst q'
        have hxy : fiberEmbed q x = fiberEmbed q y :=
          eq_of_heq (Sigma.ext_iff.mp h).2
        have hxy' : x = y := (fiberEmbed q).injective hxy
        subst y
        rfl }
  let f := sourceEquiv.toEmbedding.trans
    (sigmaEmbed.trans targetEquiv.symm.toEmbedding)
  refine ⟨f, ?_⟩
  intro i
  change memoryEntry z ((fiberEmbed (memoryEntry w i) ⟨i, rfl⟩).val) =
    memoryEntry w i
  exact (fiberEmbed (memoryEntry w i) ⟨i, rfl⟩).property

/-- The image of a value-preserving occurrence embedding enumerates the source
multiset exactly. -/
theorem memoryEntry_embedding_map_eq {P : PrimeGroups} {g : P.Group}
    (w z : P.Memory g) (f : Fin w.card ↪ Fin z.card)
    (hf : ∀ i, memoryEntry z (f i) = memoryEntry w i) :
    (Finset.univ.map f).val.map (memoryEntry z) = w := by
  calc
    _ = Finset.univ.val.map (fun i => memoryEntry z (f i)) := by
      rw [Finset.map_val, Multiset.map_map]
      rfl
    _ = Finset.univ.val.map (memoryEntry w) := by
      apply Multiset.map_congr rfl
      intro i hi
      exact hf i
    _ = w := memoryEntry_enumeration w

/-- Any finite indexed multiset subobject embeds into the indexed occurrences
of the containing memory, preserving the underlying particle values. -/
theorem finiteFiberEmbeddingOfSubmultiset {P : PrimeGroups} {g : P.Group}
    {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → P.Particle g) (z : P.Memory g)
    (hsub : Finset.univ.val.map v ≤ z) :
    ∃ f : α ↪ Fin z.card, ∀ a, memoryEntry z (f a) = v a := by
  classical
  let SourceFiber (q : P.Particle g) := {a : α // v a = q}
  let TargetFiber (q : P.Particle g) := {i : Fin z.card // memoryEntry z i = q}
  have hsourceCard (q : P.Particle g) :
      Fintype.card (SourceFiber q) = (Finset.univ.val.map v).count q := by
    calc
      _ = (Finset.univ.filter (fun a : α => v a = q)).card := by
        rw [Fintype.card_subtype]
      _ = (Finset.univ.val.map v).count q := by
        rw [Multiset.count_map]
        change (Finset.univ.filter (fun a : α => v a = q)).card =
          (Finset.univ.filter (fun a : α => q = v a)).card
        congr 1
        ext a
        simp [eq_comm]
  have hfiberCard (q : P.Particle g) :
      Fintype.card (SourceFiber q) ≤ Fintype.card (TargetFiber q) := by
    rw [hsourceCard, memoryEntry_fiber_card]
    exact Multiset.count_le_of_le q hsub
  let fiberEmbed (q : P.Particle g) : SourceFiber q ↪ TargetFiber q :=
    Classical.choice (Function.Embedding.nonempty_iff_card_le.mpr (hfiberCard q))
  let sourceEquiv : α ≃ (Σ q : P.Particle g, SourceFiber q) :=
    { toFun := fun a => ⟨v a, ⟨a, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨q, ⟨a, ha⟩⟩
        cases ha
        rfl }
  let targetEquiv : Fin z.card ≃ (Σ q : P.Particle g, TargetFiber q) :=
    { toFun := fun i => ⟨memoryEntry z i, ⟨i, rfl⟩⟩
      invFun := fun x => x.2.1
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨q, ⟨i, hi⟩⟩
        cases hi
        rfl }
  let sigmaEmbed : (Σ q : P.Particle g, SourceFiber q) ↪
      (Σ q : P.Particle g, TargetFiber q) :=
    { toFun := fun x => ⟨x.1, fiberEmbed x.1 x.2⟩
      inj' := by
        rintro ⟨q, x⟩ ⟨q', y⟩ h
        have hq : q = q' := congrArg Sigma.fst h
        cases hq
        have hxy : fiberEmbed q x = fiberEmbed q y :=
          eq_of_heq (Sigma.ext_iff.mp h).2
        have hxy' : x = y := (fiberEmbed q).injective hxy
        subst y
        rfl }
  let f := sourceEquiv.toEmbedding.trans
    (sigmaEmbed.trans targetEquiv.symm.toEmbedding)
  refine ⟨f, ?_⟩
  intro a
  change memoryEntry z ((fiberEmbed (v a) ⟨a, rfl⟩).val) = v a
  exact (fiberEmbed (v a) ⟨a, rfl⟩).property

/-- The image indices selected by a value-preserving embedding enumerate the
source indexed multiset. -/
theorem finiteFiberEmbedding_map_eq {P : PrimeGroups} {g : P.Group}
    {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → P.Particle g) (z : P.Memory g) (f : α ↪ Fin z.card)
    (hf : ∀ a, memoryEntry z (f a) = v a) :
    (Finset.univ.map f).val.map (memoryEntry z) = Finset.univ.val.map v := by
  calc
    _ = Finset.univ.val.map (fun a => memoryEntry z (f a)) := by
      rw [Finset.map_val, Multiset.map_map]
      rfl
    _ = Finset.univ.val.map v := by
      apply Multiset.map_congr rfl
      intro a ha
      exact hf a

/-- Deleting the image of an indexed submultiset leaves exactly its complement. -/
theorem deleteMemoryIndices_add_fiberEmbedding {P : PrimeGroups} {g : P.Group}
    {α : Type*} [Fintype α] [DecidableEq α]
    (v : α → P.Particle g) (z : P.Memory g) (f : α ↪ Fin z.card)
    (hf : ∀ a, memoryEntry z (f a) = v a) :
    deleteMemoryIndices z (Finset.univ.map f) + Finset.univ.val.map v = z := by
  classical
  let S : Finset (Fin z.card) := Finset.univ.map f
  have hdisj : Disjoint (Finset.univ \ S) S := Finset.sdiff_disjoint
  have hpart : (Finset.univ \ S).val + S.val = Finset.univ.val := by
    have hUnion : (Finset.univ \ S).disjUnion S hdisj = Finset.univ := by
      ext i
      simp [Finset.mem_disjUnion, Finset.mem_sdiff]
    have hval := congrArg Finset.val hUnion
    simpa [Finset.disjUnion] using hval
  calc
    _ = (Finset.univ \ S).val.map (memoryEntry z) + S.val.map (memoryEntry z) := by
      rw [deleteMemoryIndices_eq_map, finiteFiberEmbedding_map_eq v z f hf]
    _ = ((Finset.univ \ S).val + S.val).map (memoryEntry z) := by
      rw [Multiset.map_add]
    _ = z := by rw [hpart, memoryEntry_enumeration]

/-- Deleting a finite set of occurrences and re-enumerating it recovers the
original memory multiset. -/
theorem deleteMemoryIndices_add_selected {P : PrimeGroups} {g : P.Group}
    (z : P.Memory g) (R : Finset (Fin z.card)) :
    deleteMemoryIndices z R + R.val.map (memoryEntry z) = z := by
  classical
  let f : {i : Fin z.card // i ∈ R} ↪ Fin z.card :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hf : ∀ i, memoryEntry z (f i) = memoryEntry z i.1 := by
    intro i
    rfl
  have h := deleteMemoryIndices_add_fiberEmbedding
    (fun i : {i : Fin z.card // i ∈ R} => memoryEntry z i.1) z f hf
  have hR : Finset.univ.map f = R := by
    ext i
    simp [f]
  have hUniv : (Finset.univ : Finset {i : Fin z.card // i ∈ R}) = R.attach := by
    ext i
    simp
  have hM : Finset.univ.val.map (fun i : {i : Fin z.card // i ∈ R} => memoryEntry z i.1) =
      R.val.map (memoryEntry z) := by
    calc
      _ = R.val.attach.map (fun i => memoryEntry z i.1) := by
        rw [hUniv, Finset.attach_val]
        rfl
      _ = _ := Multiset.attach_map_val' R.val (memoryEntry z)
  rw [hR, hM] at h
  exact h

/-- Stored active labels are enumerated by their own active-slot indices. -/
theorem storedMemory_indexed_map {P : PrimeGroups} {M : ℕ} {g : P.Group}
    (a : Fin M → P.Prime g) (B : Finset (Fin M)) :
    Finset.univ.val.map
      (fun i : {i : Fin M // i ∈ B} => (⟨a i.1, 0⟩ : P.Particle g)) =
      storedMemory a B := by
  classical
  have hUniv : (Finset.univ : Finset {i : Fin M // i ∈ B}) = B.attach := by
    ext i
    simp
  have hstored : storedMemory a B =
      B.val.map (fun j : Fin M => (⟨a j, 0⟩ : P.Particle g)) := by
    unfold storedMemory
    rw [← Multiset.map_coe, Finset.coe_toList]
  calc
    _ = B.val.attach.map (fun i => (⟨a i.1, 0⟩ : P.Particle g)) := by
      rw [hUniv, Finset.attach_val]
      rfl
    _ = B.val.map (fun j : Fin M => (⟨a j, 0⟩ : P.Particle g)) := by
      exact Multiset.attach_map_val' B.val (fun j => (⟨a j, 0⟩ : P.Particle g))
    _ = storedMemory a B := hstored.symm

/-- Translating the stored particles and then indexing by active slots gives the
same multiset as translating `storedMemory`. -/
theorem translatedStoredMemory_indexed_map {P : PrimeGroups} {M : ℕ} {g : P.Group}
    (a : Fin M → P.Prime g) (B : Finset (Fin M)) (delta : ℤ) :
    Finset.univ.val.map
      (fun i : {i : Fin M // i ∈ B} => translateParticle delta (⟨a i.1, 0⟩ : P.Particle g)) =
      translateMemory delta (storedMemory a B) := by
  unfold translateMemory
  change Finset.univ.val.map
      (translateParticle delta ∘ fun i : {i : Fin M // i ∈ B} =>
        (⟨a i.1, 0⟩ : P.Particle g)) =
    (storedMemory a B).map (translateParticle delta)
  rw [← Multiset.map_map]
  exact congrArg (Multiset.map (translateParticle delta)) (storedMemory_indexed_map a B)

/-- A valid memory update contains an indexed copy of every translated store,
even when those particles coincide with survivors. -/
theorem reverseStoreEmbedding_of_memoryStep {P : PrimeGroups} {M : ℕ} {g : P.Group}
    (a : Fin M → P.Prime g) (B : Finset (Fin M)) (delta : ℤ)
    (sMem tMem : P.Memory g) (R : Finset (Fin sMem.card))
    (hmem : tMem = translateMemory delta (deleteMemoryIndices sMem R + storedMemory a B)) :
    ∃ f : {i : Fin M // i ∈ B} ↪ Fin tMem.card,
      ∀ i, memoryEntry tMem (f i) = translateParticle delta (⟨a i.1, 0⟩ : P.Particle g) := by
  classical
  let v : {i : Fin M // i ∈ B} → P.Particle g :=
    fun i => translateParticle delta (⟨a i.1, 0⟩ : P.Particle g)
  have hsub : Finset.univ.val.map v ≤ tMem := by
    have hExpanded : tMem =
        translateMemory delta (deleteMemoryIndices sMem R) +
          translateMemory delta (storedMemory a B) := by
      calc
        _ = translateMemory delta (deleteMemoryIndices sMem R + storedMemory a B) := hmem
        _ = _ := translateMemory_add delta _ _
    calc
      _ = translateMemory delta (storedMemory a B) := by
        exact translatedStoredMemory_indexed_map a B delta
      _ ≤ translateMemory delta (deleteMemoryIndices sMem R) +
            translateMemory delta (storedMemory a B) := Multiset.le_add_left _ _
      _ = tMem := hExpanded.symm
  obtain ⟨f, hf⟩ := finiteFiberEmbeddingOfSubmultiset v tMem hsub
  exact ⟨f, hf⟩

/-- Reversing a promoted transfer restores precisely its original retrieved
particles, with their original multiplicities. -/
theorem reversePromotion_store_multiset {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) (tr : TransferChoice s)
    (hvalid : rawEdgeValid A ν forward u s t tr) (g : P.BigGroup) :
    translateMemory (-(edgeDelta A ν forward s.2.1 u))
        (storedMemory (t.2.1 g.val) (tr.2.1 g)) =
      (retrievedIndices tr g).val.map (memoryEntry (s.2.2 g)) := by
  classical
  have hvalid0 := hvalid
  rcases hvalid with ⟨_, _, _, _, _, hgroups⟩
  obtain ⟨_, _, hinj, _, _⟩ := hgroups g
  let e : {i : Fin (J + F.ell) // i ∈ tr.2.1 g} ↪ Fin (s.2.2 g).card :=
    ⟨tr.2.2 g, hinj⟩
  have hR : Finset.univ.map e = retrievedIndices tr g := by
    change Finset.univ.map e = Finset.univ.image (tr.2.2 g)
    rw [Finset.map_eq_image]
    rfl
  have hpoint (i : {i : Fin (J + F.ell) // i ∈ tr.2.1 g}) :
      translateParticle (-(edgeDelta A ν forward s.2.1 u))
          (⟨t.2.1 g.val i.1, 0⟩ : P.Particle g.val) =
        memoryEntry (s.2.2 g) (tr.2.2 g i) := by
    obtain ⟨z, hzDef, hactive, hzero, _⟩ := rawEdgeValid_promotion_data A ν forward u
      s t tr hvalid0 g i
    have hres : z.2 = -(edgeDelta A ν forward s.2.1 u : ZMod z.1.val) :=
      eq_neg_of_add_eq_zero_left hzero
    have hparticle :
        translateParticle (-(edgeDelta A ν forward s.2.1 u))
            (⟨t.2.1 g.val i.1, 0⟩ : P.Particle g.val) = z := by
      rw [← hactive]
      simp only [translateParticle, Int.cast_neg, zero_add]
      exact Sigma.ext rfl (heq_of_eq hres.symm)
    exact hparticle.trans hzDef
  have hmap :
      Finset.univ.val.map (fun i : {i : Fin (J + F.ell) // i ∈ tr.2.1 g} =>
        translateParticle (-(edgeDelta A ν forward s.2.1 u))
          (⟨t.2.1 g.val i.1, 0⟩ : P.Particle g.val)) =
      Finset.univ.val.map (fun i : {i : Fin (J + F.ell) // i ∈ tr.2.1 g} =>
        memoryEntry (s.2.2 g) (tr.2.2 g i)) := by
    apply Multiset.map_congr rfl
    intro i hi
    exact hpoint i
  have hmapR :
      (Finset.univ.map e).val.map (memoryEntry (s.2.2 g)) =
        Finset.univ.val.map (fun i : {i : Fin (J + F.ell) // i ∈ tr.2.1 g} =>
          memoryEntry (s.2.2 g) (tr.2.2 g i)) :=
    finiteFiberEmbedding_map_eq (fun i => memoryEntry (s.2.2 g) (tr.2.2 g i))
      (s.2.2 g) e (fun _ => rfl)
  calc
    _ = Finset.univ.val.map (fun i : {i : Fin (J + F.ell) // i ∈ tr.2.1 g} =>
          translateParticle (-(edgeDelta A ν forward s.2.1 u))
            (⟨t.2.1 g.val i.1, 0⟩ : P.Particle g.val)) :=
        (translatedStoredMemory_indexed_map (t.2.1 g.val) (tr.2.1 g)
          (-(edgeDelta A ν forward s.2.1 u))).symm
    _ = Finset.univ.val.map (fun i : {i : Fin (J + F.ell) // i ∈ tr.2.1 g} =>
          memoryEntry (s.2.2 g) (tr.2.2 g i)) := hmap
    _ = (retrievedIndices tr g).val.map (memoryEntry (s.2.2 g)) := by
      rw [← hmapR, hR]

/-- The reversed memory update restores a group's exact source multiset. -/
theorem reverseMemoryGroup_eq {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) (tr : TransferChoice s)
    (hvalid : rawEdgeValid A ν forward u s t tr) (g : P.BigGroup) :
    ∃ f : {i : Fin (J + F.ell) // i ∈ tr.1 g} ↪ Fin (t.2.2 g).card,
      (∀ i, memoryEntry (t.2.2 g) (f i) =
        translateParticle (edgeDelta A ν forward s.2.1 u)
          (⟨s.2.1 g.val i.1, 0⟩ : P.Particle g.val)) ∧
      s.2.2 g = translateMemory (-(edgeDelta A ν forward s.2.1 u))
        (deleteMemoryIndices (t.2.2 g) (Finset.univ.map f) +
          storedMemory (t.2.1 g.val) (tr.2.1 g)) := by
  classical
  have hvalid0 := hvalid
  obtain ⟨_, _, _, _, _, hgroups⟩ := hvalid
  have hmem := (hgroups g).2.2.2.2
  let delta := edgeDelta A ν forward s.2.1 u
  obtain ⟨f, hf⟩ := reverseStoreEmbedding_of_memoryStep
    (s.2.1 g.val) (tr.1 g) delta (s.2.2 g) (t.2.2 g)
    (retrievedIndices tr g) hmem
  have hsource : Finset.univ.val.map
      (fun i : {i : Fin (J + F.ell) // i ∈ tr.1 g} =>
        translateParticle delta (⟨s.2.1 g.val i.1, 0⟩ : P.Particle g.val)) =
      translateMemory delta (storedMemory (s.2.1 g.val) (tr.1 g)) :=
    translatedStoredMemory_indexed_map (s.2.1 g.val) (tr.1 g) delta
  have hdelEmbedding := deleteMemoryIndices_add_fiberEmbedding
    (fun i : {i : Fin (J + F.ell) // i ∈ tr.1 g} =>
      translateParticle delta (⟨s.2.1 g.val i.1, 0⟩ : P.Particle g.val))
    (t.2.2 g) f hf
  rw [hsource] at hdelEmbedding
  have hmemExpanded : t.2.2 g =
      translateMemory delta (deleteMemoryIndices (s.2.2 g) (retrievedIndices tr g)) +
        translateMemory delta (storedMemory (s.2.1 g.val) (tr.1 g)) := by
    calc
      _ = translateMemory delta
          (deleteMemoryIndices (s.2.2 g) (retrievedIndices tr g) +
            storedMemory (s.2.1 g.val) (tr.1 g)) := hmem
      _ = _ := translateMemory_add delta _ _
  have hsameSum := hdelEmbedding.trans hmemExpanded
  have hdelRev : deleteMemoryIndices (t.2.2 g) (Finset.univ.map f) =
      translateMemory delta (deleteMemoryIndices (s.2.2 g) (retrievedIndices tr g)) :=
    Multiset.add_left_inj.mp hsameSum
  have hstoreRev := reversePromotion_store_multiset A ν forward u s t tr hvalid0 g
  have hselected := deleteMemoryIndices_add_selected (s.2.2 g) (retrievedIndices tr g)
  refine ⟨f, hf, ?_⟩
  calc
    _ = deleteMemoryIndices (s.2.2 g) (retrievedIndices tr g) +
          (retrievedIndices tr g).val.map (memoryEntry (s.2.2 g)) := hselected.symm
    _ = translateMemory (-delta)
          (translateMemory delta (deleteMemoryIndices (s.2.2 g) (retrievedIndices tr g)) +
            storedMemory (t.2.1 g.val) (tr.2.1 g)) := by
      rw [translateMemory_add, translateMemory_cancel, hstoreRev]
    _ = _ := by rw [← hdelRev]

/-- Reverse a valid raw edge, swapping stores and promotions while preserving
all occurrence multiplicities. -/
theorem rawEdgeValid_reverse {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) (tr : TransferChoice s)
    (hvalid : rawEdgeValid A ν forward u s t tr) :
    ∃ trRev : TransferChoice t,
      (∀ g, trRev.1 g = tr.2.1 g) ∧
      (∀ g, trRev.2.1 g = tr.1 g) ∧
      rawEdgeValid A ν (!forward) u t s trRev := by
  classical
  have hvalid0 := hvalid
  rcases hvalid with ⟨hsPhys, htPhys, hcompat, hban, hy, hgroups⟩
  have hD : ν.D s.2.1 u = ν.D t.2.1 u := compatible_D_eq ν s.2.1 t.2.1 u hcompat
  have hdelta : edgeDelta A ν (!forward) t.2.1 u =
      -edgeDelta A ν forward s.2.1 u :=
    edgeDelta_reverse_eq A ν forward u s t hcompat
  have hyRev : s.1 = translateSmallResidues
      (edgeDelta A ν (!forward) t.2.1 u) t.1 := by
    rw [hdelta, hy]
    exact (translateSmallResidues_cancel (edgeDelta A ν forward s.2.1 u) s.1).symm
  have hcompatRev : ν.compatible t.2.1 s.2.1 := by
    intro g i hi
    exact (hcompat g i hi).symm
  have hbanRev : ν.ban t.2.1 s.2.1 u := by
    intro g i hi j
    exact ⟨(hban g i hi j).2, (hban g i hi j).1⟩
  have hReverseGroup (g : P.BigGroup) :=
    reverseMemoryGroup_eq A ν forward u s t tr hvalid0 g
  let fRev (g : P.BigGroup) :
      {i : Fin (J + F.ell) // i ∈ tr.1 g} ↪ Fin (t.2.2 g).card :=
    Classical.choose (hReverseGroup g)
  have hfRev (g : P.BigGroup) :
      (∀ i, memoryEntry (t.2.2 g) (fRev g i) =
        translateParticle (edgeDelta A ν forward s.2.1 u)
          (⟨s.2.1 g.val i.1, 0⟩ : P.Particle g.val)) ∧
      s.2.2 g = translateMemory (-(edgeDelta A ν forward s.2.1 u))
        (deleteMemoryIndices (t.2.2 g) (Finset.univ.map (fRev g)) +
          storedMemory (t.2.1 g.val) (tr.2.1 g)) :=
    Classical.choose_spec (hReverseGroup g)
  let trRev : TransferChoice t :=
    Prod.mk (fun g => tr.2.1 g)
      (Sigma.mk (fun g => tr.1 g) (fun g i => fRev g i))
  have hretrievedRev (g : P.BigGroup) :
      retrievedIndices trRev g = Finset.univ.map (fRev g) := by
    unfold retrievedIndices
    change Finset.univ.image (fRev g) = Finset.univ.map (fRev g)
    exact (Finset.map_eq_image (fRev g) Finset.univ).symm
  refine ⟨trRev, ?_, ?_, ?_⟩
  · intro g
    rfl
  · intro g
    rfl
  · refine ⟨htPhys, hsPhys, hcompatRev, hbanRev, hyRev, ?_⟩
    intro g
    obtain ⟨hstores, hpromNoShared, hretrievalInj, hpromData, hmem⟩ := hgroups g
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hdata := rawEdgeValid_promotion_data A ν forward u s t tr hvalid0 g ⟨i, hi⟩
      obtain ⟨z, hzDef, hactive, _, hnotdiv⟩ := hdata
      have hnotdivTarget : ¬ (t.2.1 g.val i).val ∣ ν.D t.2.1 u := by
        rw [← hD]
        simpa [hactive] using hnotdiv
      exact ⟨hpromNoShared i hi, hnotdivTarget⟩
    · intro i hi
      exact (hstores i hi).1
    · exact (fRev g).injective
    · intro i
      let z : P.Particle g.val := translateParticle (edgeDelta A ν forward s.2.1 u)
        (⟨s.2.1 g.val i.1, 0⟩ : P.Particle g.val)
      have hentry : memoryEntry (t.2.2 g) (fRev g i) = z := by
        simpa [z] using (hfRev g).1 i
      have hprime : z.1 = s.2.1 g.val i.1 := by simp [z, translateParticle]
      have hzero : z.2 +
          (edgeDelta A ν (!forward) t.2.1 u : ZMod z.1.val) = 0 := by
        have hz : z.2 = (edgeDelta A ν forward s.2.1 u : ZMod z.1.val) := by
          simp [z, translateParticle]
          rfl
        rw [hdelta, Int.cast_neg, hz]
        exact add_neg_cancel _
      have hnotdiv : ¬ z.1.val ∣ ν.D t.2.1 u := by
        rw [← hD]
        simpa [z, translateParticle] using (hstores i.1 i.2).2
      refine ⟨?_, ?_, ?_⟩
      · rw [hentry]
        exact hprime
      · rw [hentry]
        exact hzero
      · rw [hentry]
        exact hnotdiv
    · simpa [trRev, hdelta, hretrievedRev] using (hfRev g).2
/-- A transfer choice retrieves this particular old multiset position. -/
def transferRetrievesOldIndex {P : PrimeGroups} {M : ℕ} {s : P.MemoryState M}
    (tr : TransferChoice s) (i : OldMemoryIndex s) : Prop :=
  ∃ j : {j : Fin M // j ∈ tr.2.1 i.1}, tr.2.2 i.1 j = i.2

theorem smallPhysical_act_iff {P : PrimeGroups} {M : ℕ}
    (y : P.SmallResidues) (π : P.Permutations M) (a : P.Labels M) :
    P.smallPhysical y (P.act π a) ↔ P.smallPhysical y a := by
  classical
  constructor
  · intro h g
    obtain ⟨hinj, hzero⟩ := h g
    refine ⟨?_, ?_⟩
    · change Function.Injective (a g)
      intro i j hij
      have h' : (P.act π a) g ((π g).symm i) = (P.act π a) g ((π g).symm j) := by
        change a g ((π g) ((π g).symm i)) = a g ((π g) ((π g).symm j))
        simpa using hij
      have hsymm := hinj h'
      have hEq := congrArg (π g) hsymm
      simpa using hEq
    · intro i
      change y g (a g i) = 0
      have hz := hzero ((π g).symm i)
      change y g (a g ((π g) ((π g).symm i))) = 0 at hz
      have hi : (π g) ((π g).symm i) = i := Equiv.apply_symm_apply (π g) i
      rw [hi] at hz
      exact hz
  · intro h g
    obtain ⟨hinj, hzero⟩ := h g
    refine ⟨?_, ?_⟩
    · change Function.Injective (fun i : Fin M => a g (π g i))
      exact hinj.comp (π g).injective
    · intro i
      change y g (a g (π g i)) = 0
      exact hzero (π g i)

/-- One pending particle can certify at most one omission configuration. -/
theorem omission_config_eq_of_congruence {P : PrimeGroups} {M ell : ℕ}
    (y : P.SmallResidues) (a : P.Labels M) (hphys : P.smallPhysical y a)
    (p : ℕ) (hp : Nat.Prime p) (r C : ZMod p) (hC : C ≠ 0)
    (O O' : OmissionChoices P M ell)
    (hO : 0 < omittedChoiceProduct a O) (hOp : omittedChoiceProduct a O < p)
    (hO' : 0 < omittedChoiceProduct a O') (hO'p : omittedChoiceProduct a O' < p)
    (h₁ : r * (omittedChoiceProduct a O : ZMod p) + C = 0)
    (h₂ : r * (omittedChoiceProduct a O' : ZMod p) + C = 0) : O = O' := by
  have hprod : omittedChoiceProduct a O = omittedChoiceProduct a O' :=
    omission_congruence_unique p hp r C hC
      (omittedChoiceProduct a O) (omittedChoiceProduct a O') hO hOp hO' hO'p h₁ h₂
  funext g
  apply Subtype.ext
  exact congrFun (omittedPrimeProduct_injective y a hphys (by simpa [omittedChoiceProduct] using hprod)) g


/-- Once the big labels and one old pending particle are fixed, its promotion
congruence determines the omitted small-label product. -/
theorem promotion_omission_unique {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s : P.MemoryState (J + F.ell))
    (π π' : P.Permutations (J + F.ell)) (t t' : P.MemoryState (J + F.ell))
    (tr tr' : TransferChoice s) (idx : OldMemoryIndex s)
    (hraw : rawEdgeValid A ν forward u (permuteActive π s) t tr)
    (hraw' : rawEdgeValid A ν forward u (permuteActive π' s) t' tr')
    (hbig : ∀ g : P.BigGroup, π g.val = π' g.val)
    (hret : transferRetrievesOldIndex tr idx)
    (hret' : transferRetrievesOldIndex tr' idx)
    (hk : ¬ ((memoryEntry (s.2.2 idx.1) idx.2).1.val : ℤ) ∣ A.k)
    (hO : omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π) <
      (memoryEntry (s.2.2 idx.1) idx.2).1.val)
    (hO' : omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π') <
      (memoryEntry (s.2.2 idx.1) idx.2).1.val) :
    omissionOfPerm P J F.ell π = omissionOfPerm P J F.ell π' := by
  classical
  have hphys : P.smallPhysical s.1 s.2.1 := by
    exact (smallPhysical_act_iff s.1 π s.2.1).mp hraw.1
  obtain ⟨j, hj⟩ := hret
  obtain ⟨j', hj'⟩ := hret'
  obtain ⟨z, hzDef, _, hzero, hnotdiv⟩ := rawEdgeValid_promotion_data A ν forward u
    (permuteActive π s) t tr hraw idx.1 j
  obtain ⟨z', hzDef', _, hzero', hnotdiv'⟩ := rawEdgeValid_promotion_data A ν forward u
    (permuteActive π' s) t' tr' hraw' idx.1 j'
  have hentry : z = memoryEntry (s.2.2 idx.1) idx.2 := by
    calc
      _ = memoryEntry (s.2.2 idx.1) (tr.2.2 idx.1 j) := hzDef
      _ = _ := congrArg (memoryEntry (s.2.2 idx.1)) hj
  have hzEq : z' = z := by
    calc
      _ = memoryEntry (s.2.2 idx.1) (tr'.2.2 idx.1 j') := hzDef'
      _ = memoryEntry (s.2.2 idx.1) idx.2 := congrArg (memoryEntry (s.2.2 idx.1)) hj'
      _ = memoryEntry (s.2.2 idx.1) (tr.2.2 idx.1 j) :=
        (congrArg (memoryEntry (s.2.2 idx.1)) hj).symm
      _ = _ := hzDef.symm
  have hkz : ¬ (z.1.val : ℤ) ∣ A.k := by rw [hentry]; exact hk
  have hOz : omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π) < z.1.val := by
    rw [hentry]
    exact hO
  have hO'z : omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π') < z.1.val := by
    rw [hentry]
    exact hO'
  have hzeroZ : z.2 + (edgeDelta A ν forward (P.act π s.2.1) u : ZMod z.1.val) = 0 := by
    simpa [permuteActive] using hzero
  have hzeroZ' : z.2 + (edgeDelta A ν forward (P.act π' s.2.1) u : ZMod z.1.val) = 0 := by
    rw [← hzEq]
    simpa [permuteActive] using hzero'
  have hnotdivZ : ¬ z.1.val ∣ ν.D (P.act π s.2.1) u := by
    simpa [permuteActive] using hnotdiv
  have hnotdivZ' : ¬ z.1.val ∣ ν.D (P.act π' s.2.1) u := by
    rw [← hzEq]
    simpa [permuteActive] using hnotdiv'
  let B : ℕ := patternBigPart ν (P.act π s.2.1) u
  let S : ℕ := smallLabelProduct s.2.1
  have hBpart : patternBigPart ν (P.act π' s.2.1) u = B := by
    dsimp [B]
    exact (patternBigPart_eq_of_bigRestriction ν s.2.1 u π π' hbig).symm
  have hBndiv : ¬ z.1.val ∣ B := by
    dsimp [B]
    exact patternBigPart_not_dvd_of_D_not_dvd ν (P.act π s.2.1) u z.1.val hnotdivZ
  have hBndiv' : ¬ z.1.val ∣ patternBigPart ν (P.act π' s.2.1) u := by
    rw [hBpart]
    exact hBndiv
  have hSndiv : ¬ z.1.val ∣ S := by
    dsimp [S]
    exact bigPrime_not_dvd_smallLabelProduct s.2.1 idx.1 z.1
  have hp : Nat.Prime z.1.val := P.prime idx.1.val z.1.val z.1.property
  let C : ZMod z.1.val :=
    if forward then (A.k : ZMod z.1.val) * (B : ZMod z.1.val) * (S : ZMod z.1.val)
    else -((A.k : ZMod z.1.val) * (B : ZMod z.1.val) * (S : ZMod z.1.val))
  have hC : C ≠ 0 := by
    dsimp [C]
    exact promotionZModConstant_ne_zero hp A.k hkz B S hBndiv hSndiv forward
  have hDF : ν.D (P.act π s.2.1) u *
        omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π) = B * S := by
    dsimp [B, S]
    exact pattern_D_mul_omitted_eq ν s.2.1 u π
  have hDF' : ν.D (P.act π' s.2.1) u *
        omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π') = B * S := by
    rw [← hBpart]
    dsimp [S]
    exact pattern_D_mul_omitted_eq ν s.2.1 u π'
  have hdelta := edgeDelta_mul_omitted_eq A ν u s.2.1 π forward z.1.val B S hDF
  have hdelta' := edgeDelta_mul_omitted_eq A ν u s.2.1 π' forward z.1.val B S hDF'
  let O : ℕ := omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π)
  let O' : ℕ := omittedChoiceProduct s.2.1 (omissionOfPerm P J F.ell π')
  have hcong : z.2 * (O : ZMod z.1.val) + C = 0 := by
    calc
      _ = z.2 * (O : ZMod z.1.val) +
          (edgeDelta A ν forward (P.act π s.2.1) u : ZMod z.1.val) * (O : ZMod z.1.val) := by
            rw [hdelta]
      _ = (z.2 + (edgeDelta A ν forward (P.act π s.2.1) u : ZMod z.1.val)) *
          (O : ZMod z.1.val) := by ring
      _ = 0 := by rw [hzeroZ]; simp
  have hcong' : z.2 * (O' : ZMod z.1.val) + C = 0 := by
    calc
      _ = z.2 * (O' : ZMod z.1.val) +
          (edgeDelta A ν forward (P.act π' s.2.1) u : ZMod z.1.val) * (O' : ZMod z.1.val) := by
            rw [hdelta']
      _ = (z.2 + (edgeDelta A ν forward (P.act π' s.2.1) u : ZMod z.1.val)) *
          (O' : ZMod z.1.val) := by ring
      _ = 0 := by rw [hzeroZ']; simp
  have hOpos : 0 < O := by dsimp [O]; exact omittedChoiceProduct_pos s.2.1 _
  have hO'pos : 0 < O' := by dsimp [O']; exact omittedChoiceProduct_pos s.2.1 _
  have hOlt : O < z.1.val := by exact hOz
  have hO'lt : O' < z.1.val := by exact hO'z
  exact omission_config_eq_of_congruence s.1 s.2.1 hphys z.1.val hp z.2 C hC
    (omissionOfPerm P J F.ell π) (omissionOfPerm P J F.ell π')
    hOpos hOlt hO'pos hO'lt hcong hcong'

/-- A finite family of particles with unique omission witnesses covers at most its own size. -/
theorem finite_bad_omission_card_le {Ω I : Type*} [Fintype Ω] [Fintype I]
    (promotes : I → Ω → Prop)
    (hunique : ∀ i o o', promotes i o → promotes i o' → o = o') :
    (Finset.univ.filter (fun o : Ω => ∃ i, promotes i o)).card ≤ Fintype.card I := by
  classical
  let S : Finset Ω := Finset.univ.filter (fun o => ∃ i, promotes i o)
  have hmem (o : {o : Ω // o ∈ S}) : ∃ i, promotes i o.val := by
    have ho := o.property
    change o.val ∈ Finset.univ.filter (fun z => ∃ i, promotes i z) at ho
    exact (Finset.mem_filter.mp ho).2
  let witness : {o : Ω // o ∈ S} → I := fun o => Classical.choose (hmem o)
  have hwitness (o : {o : Ω // o ∈ S}) : promotes (witness o) o.val :=
    Classical.choose_spec (hmem o)
  have hinj : Function.Injective witness := by
    intro o o' hoo
    apply Subtype.ext
    exact hunique (witness o) o.val o'.val (hwitness o)
      (by simpa [hoo] using hwitness o')
  have hcard : Fintype.card {o : Ω // o ∈ S} = S.card := by
    simpa [S] using (Fintype.card_subtype (fun o : Ω => ∃ i, promotes i o))
  rw [← hcard]
  exact Fintype.card_le_of_injective witness hinj

/-- A context and one retrieved old index witness a promotion at an omission. -/
def PromotionWitness {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s : P.MemoryState (J + F.ell))
    (πBig : P.BigPermutations (J + F.ell)) (idx : OldMemoryIndex s)
    (O : OmissionChoices P (J + F.ell) F.ell) : Prop :=
  ∃ (π : P.Permutations (J + F.ell)) (t : P.MemoryState (J + F.ell))
      (tr : TransferChoice s),
    (∀ g : P.BigGroup, π g.val = πBig g) ∧
    rawEdgeValid A ν forward u (permuteActive π s) t tr ∧
    ∃ j : {j : Fin (J + F.ell) // j ∈ tr.2.1 idx.1},
      tr.2.2 idx.1 j = idx.2 ∧ O = omissionOfPerm P J F.ell π

/-- A fixed context and old particle cannot witness two different omissions. -/
theorem promotionWitness_omission_unique {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (u : P.Aux J) (s : P.MemoryState (J + F.ell))
    (πBig : P.BigPermutations (J + F.ell))
    (hk : ∀ idx : OldMemoryIndex s,
      ¬ ((memoryEntry (s.2.2 idx.1) idx.2).1.val : ℤ) ∣ A.k)
    (hprod : ∀ (idx : OldMemoryIndex s) (O : OmissionChoices P (J + F.ell) F.ell),
      omittedChoiceProduct s.2.1 O < (memoryEntry (s.2.2 idx.1) idx.2).1.val)
    {idx : OldMemoryIndex s} {O O' : OmissionChoices P (J + F.ell) F.ell}
    (h : PromotionWitness A ν forward u s πBig idx O)
    (h' : PromotionWitness A ν forward u s πBig idx O') : O = O' := by
  rcases h with ⟨π, t, tr, hbig, hraw, j, hj, hO⟩
  rcases h' with ⟨π', t', tr', hbig', hraw', j', hj', hO'⟩
  have hunique := promotion_omission_unique A ν forward u s π π' t t' tr tr' idx
    hraw hraw' (fun g => (hbig g).trans (hbig' g).symm)
    ⟨j, hj⟩ ⟨j', hj'⟩ (hk idx) (hprod idx (omissionOfPerm P J F.ell π))
    (hprod idx (omissionOfPerm P J F.ell π'))
  simpa [hO, hO'] using hunique

/-- At most one omission configuration per old pending particle can admit a
promotion in a fixed pattern, auxiliary-label, and big-permutation context. -/
theorem promotionWitness_bad_card_le {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (u : P.Aux J) (s : P.MemoryState (J + F.ell))
    (πBig : P.BigPermutations (J + F.ell))
    (hk : ∀ idx : OldMemoryIndex s,
      ¬ ((memoryEntry (s.2.2 idx.1) idx.2).1.val : ℤ) ∣ A.k)
    (hprod : ∀ (idx : OldMemoryIndex s) (O : OmissionChoices P (J + F.ell) F.ell),
      omittedChoiceProduct s.2.1 O < (memoryEntry (s.2.2 idx.1) idx.2).1.val) :
    (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
      ∃ idx : OldMemoryIndex s, PromotionWitness A ν forward u s πBig idx O)).card ≤
      P.memorySize s := by
  classical
  calc
    _ ≤ Fintype.card (OldMemoryIndex s) := finite_bad_omission_card_le
      (fun idx O => PromotionWitness A ν forward u s πBig idx O)
      (fun idx O O' h h' =>
        promotionWitness_omission_unique A ν forward u s πBig hk hprod h h')
    _ = P.memorySize s := oldMemoryIndex_card s

/-- The task's size bound on `k` and the eventual omitted-product estimate
instantiate the fixed-context union bound. -/
theorem promotionWitness_bad_card_le_from_bounds {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} {x C₂ : ℝ} (A : Model F P J m)
    (hAdm : P.Admissible F x) (hk : 0 < |A.k|)
    (hK : (|A.k| : ℝ) ≤ (L x) ^ C₂)
    (hbig : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, (L x) ^ C₂ < (p.val : ℝ))
    (ν : Pattern P J F.ell m) (forward : Bool) (u : P.Aux J)
    (s : P.MemoryState (J + F.ell)) (πBig : P.BigPermutations (J + F.ell))
    (hsmall : ∀ (O : OmissionChoices P (J + F.ell) F.ell)
      (g : P.BigGroup) (p : P.Prime g.val),
        omittedChoiceProduct s.2.1 O < p.val) :
    (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
      ∃ idx : OldMemoryIndex s, PromotionWitness A ν forward u s πBig idx O)).card ≤
      P.memorySize s := by
  apply promotionWitness_bad_card_le A ν forward u s πBig
  · intro idx
    exact bigPrime_not_dvd_k_of_bound P hAdm idx.1
      (memoryEntry (s.2.2 idx.1) idx.2).1 A.k hk hK (hbig idx.1 _)
  · intro idx O
    exact hsmall O idx.1 (memoryEntry (s.2.2 idx.1) idx.2).1

/-- With the task cutoff on the row state, a fixed context has at most `B`
bad promotion omissions. -/
theorem promotionWitness_bad_card_le_cutoff {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} {x C₂ : ℝ} (A : Model F P J m)
    (hAdm : P.Admissible F x) (hk : 0 < |A.k|)
    (hK : (|A.k| : ℝ) ≤ (L x) ^ C₂)
    (hbig : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, (L x) ^ C₂ < (p.val : ℝ))
    (ν : Pattern P J F.ell m) (forward : Bool) (u : P.Aux J)
    (s : P.MemoryState (J + F.ell)) (πBig : P.BigPermutations (J + F.ell))
    (hsmall : ∀ (O : OmissionChoices P (J + F.ell) F.ell)
      (g : P.BigGroup) (p : P.Prime g.val), omittedChoiceProduct s.2.1 O < p.val)
    (hs : P.memorySize s ≤ memoryCutoff x) :
    (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
      ∃ idx : OldMemoryIndex s, PromotionWitness A ν forward u s πBig idx O)).card ≤
      memoryCutoff x := by
  exact (promotionWitness_bad_card_le_from_bounds A hAdm hk hK hbig ν forward u s πBig
    hsmall).trans hs

/-- Uniformly for large `x`, admissibility and the task's `k`-bound give the
cutoff-sized bad-omission estimate in every fixed promotion context. -/
theorem promotionWitness_bad_card_le_eventually (F : FixedData) (C₂ : ℝ)
    (J m : ℕ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, 0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      ∀ (ν : Pattern P J F.ell m) (forward : Bool) (u : P.Aux J)
        (s : P.MemoryState (J + F.ell)) (πBig : P.BigPermutations (J + F.ell)),
        P.memorySize s ≤ memoryCutoff x →
        (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
          ∃ idx : OldMemoryIndex s, PromotionWitness A ν forward u s πBig idx O)).card ≤
          memoryCutoff x := by
  obtain ⟨xBig, hBig⟩ := bigPrime_gt_logpow_eventually F C₂
  obtain ⟨xSmall, hSmall⟩ := omittedChoiceProduct_lt_bigPrime_eventually F
  refine ⟨max xBig xSmall, ?_⟩
  intro x hx P hAdm A hk hK ν forward u s πBig hs
  have hxBig : xBig ≤ x := (le_max_left _ _).trans hx
  have hxSmall : xSmall ≤ x := (le_max_right _ _).trans hx
  exact promotionWitness_bad_card_le_cutoff A hAdm hk hK
    (fun g p => hBig x hxBig P hAdm g p) ν forward u s πBig
    (fun O g p => hSmall x hxSmall P hAdm J s.2.1 O g p) hs

/-- Every valid dirty choice with a promotion supplies one old-index witness. -/
theorem promotionWitness_of_validPromotion {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (hvalid : edgeChoiceValid A .dirty i s t c)
    (hprom : ∃ g : P.BigGroup, c.2.2.2.2.2.1 g ≠ ∅) :
    ∃ idx : OldMemoryIndex s,
      PromotionWitness A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1 s
        (fun g => c.1 g.val) idx (omissionOfPerm P J F.ell c.1) := by
  classical
  obtain ⟨g, hne⟩ := hprom
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  let j' : {j : Fin (J + F.ell) // j ∈ c.2.2.2.2.2.1 g} := ⟨j, hj⟩
  let idx : OldMemoryIndex s := ⟨g, c.2.2.2.2.2.2 g j'⟩
  refine ⟨idx, c.1, permuteActive c.2.1 t, c.2.2.2.2, ?_, ?_, ?_⟩
  · intro h
    rfl
  · simpa [edgeChoiceValid] using hvalid.1
  · refine ⟨j', ?_, rfl⟩
    rfl

/-- A valid choice with a store becomes a promotion witness after reversing
the raw edge. -/
theorem promotionWitness_of_validStoreChoice {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (hvalid : edgeChoiceValid A .dirty i s t c)
    (hstore : ∃ g : P.BigGroup, c.2.2.2.2.1 g ≠ ∅) :
    ∃ idx : OldMemoryIndex t,
      PromotionWitness A (A.pattern c.2.2.1) (!(edgeForward i)) c.2.2.2.1 t
        (fun g => c.2.1 g.val) idx (omissionOfPerm P J F.ell c.2.1) := by
  classical
  obtain ⟨g, hne⟩ := hstore
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  let tr : TransferChoice s := c.2.2.2.2
  have hraw : rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
      (permuteActive c.1 s) (permuteActive c.2.1 t) tr := by
    simpa [edgeChoiceValid] using hvalid.1
  obtain ⟨trRev, hstores, hprom, hrev⟩ :=
    rawEdgeValid_reverse A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
      (permuteActive c.1 s) (permuteActive c.2.1 t) tr hraw
  have hj' : j ∈ trRev.2.1 g := by
    rw [hprom g]
    exact hj
  let j' : {j : Fin (J + F.ell) // j ∈ trRev.2.1 g} := ⟨j, hj'⟩
  let idx : OldMemoryIndex t := ⟨g, trRev.2.2 g j'⟩
  refine ⟨idx, c.2.1, permuteActive c.1 s, trRev, ?_, ?_, ?_⟩
  · intro hgroup
    rfl
  · exact hrev
  · exact ⟨j', rfl, rfl⟩

/-- A valid edge with a store at a fixed target permutation produces a
promotion witness in the reversed edge context. -/
def EdgeStoreOmissionWitness {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (i : Fin n) (ν : Pattern P J F.ell m)
    (u : P.Aux J) (t : P.MemoryState (J + F.ell))
    (πBig : P.BigPermutations (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell) : Prop :=
  ∃ (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s),
    A.pattern c.2.2.1 = ν ∧ c.2.2.2.1 = u ∧
    (∀ g : P.BigGroup, c.2.1 g.val = πBig g) ∧
    edgeChoiceValid A .dirty i s t c ∧
    (∃ g : P.BigGroup, c.2.2.2.2.1 g ≠ ∅) ∧
    O = omissionOfPerm P J F.ell c.2.1

theorem promotionWitness_of_edgeStoreOmissionWitness {F : FixedData}
    {P : PrimeGroups} {J m n : ℕ} (A : Model F P J m) (i : Fin n)
    (ν : Pattern P J F.ell m) (u : P.Aux J) (t : P.MemoryState (J + F.ell))
    (πBig : P.BigPermutations (J + F.ell))
    {O : OmissionChoices P (J + F.ell) F.ell}
    (h : EdgeStoreOmissionWitness A i ν u t πBig O) :
    ∃ idx : OldMemoryIndex t,
      PromotionWitness A ν (!(edgeForward i)) u t πBig idx O := by
  rcases h with ⟨s, c, hν, hu, hbig, hvalid, hstore, hO⟩
  obtain ⟨idx, hwitness⟩ := promotionWitness_of_validStoreChoice A i s t c hvalid hstore
  exact ⟨idx, by simpa [hν, hu, hbig, hO] using hwitness⟩

/-- The number of target omissions allowing any store in a fixed reverse
context is bounded by the target memory size. -/
theorem edgeStoreBadOmission_card_le_eventually (F : FixedData) (C₂ : ℝ)
    (J m : ℕ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, 0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      ∀ n : ℕ, ∀ i : Fin n, ∀ (ν : Pattern P J F.ell m) (u : P.Aux J)
        (t : P.MemoryState (J + F.ell)) (πBig : P.BigPermutations (J + F.ell)),
        P.memorySize t ≤ memoryCutoff x →
        (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
          EdgeStoreOmissionWitness A i ν u t πBig O)).card ≤ memoryCutoff x := by
  obtain ⟨x₀, hbound⟩ := promotionWitness_bad_card_le_eventually F C₂ J m
  refine ⟨x₀, ?_⟩
  intro x hx P hAdm A hk hK n i ν u t πBig ht
  calc
    _ ≤ (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
        ∃ idx : OldMemoryIndex t,
          PromotionWitness A ν (!(edgeForward i)) u t πBig idx O)).card := by
      apply Finset.card_le_card
      intro O hO
      obtain ⟨_, hstore⟩ := Finset.mem_filter.mp hO
      obtain ⟨idx, hidx⟩ := promotionWitness_of_edgeStoreOmissionWitness A i ν u t πBig hstore
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨idx, hidx⟩⟩
    _ ≤ memoryCutoff x := hbound x hx P hAdm A hk hK ν (!(edgeForward i)) u t πBig ht

/-- Absolute edge choices conditioned on a source or target omission configuration. -/
def omissionRestrictedAbsoluteKernel {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n) (mode : TransferMode)
    (source : Bool) (O : OmissionChoices P (J + F.ell) F.ell)
    (extra : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → Prop)
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
    edgeSymmetryFactor P (J + F.ell) *
      ∑ c : EdgeChoice A s,
        if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
          omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
          ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0

theorem omissionRestrictedAbsoluteKernel_nonneg {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (mode : TransferMode) (source : Bool)
    (O : OmissionChoices P (J + F.ell) F.ell)
    (extra : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → Prop)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ omissionRestrictedAbsoluteKernel A n rho theta i mode source O extra s t := by
  classical
  unfold omissionRestrictedAbsoluteKernel
  have hsum : 0 ≤ ∑ c : EdgeChoice A s,
      if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
        omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
        ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := by
    apply Finset.sum_nonneg
    intro c hc
    split_ifs <;> positivity
  rw [mul_assoc]
  exact mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell)) hsum)

/-- Averaging the omission-conditioned absolute kernels recovers the original absolute sum. -/
theorem omissionRestrictedAbsoluteKernel_average {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ) (i : Fin n) (mode : TransferMode)
    (source : Bool) (extra : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → Prop)
    (s t : P.MemoryState (J + F.ell)) :
    ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          omissionRestrictedAbsoluteKernel A n rho theta i mode source O extra s t =
      edgeSymmetryFactor P (J + F.ell) *
        ∑ c : EdgeChoice A s,
          if edgeChoiceValid A mode i s t c ∧ extra s t c then
            ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := by
  classical
  let D : ℝ := Fintype.card (OmissionChoices P (J + F.ell) F.ell)
  have hD : 0 < D := by
    dsimp [D]
    have hnonempty : Nonempty (OmissionChoices P (J + F.ell) F.ell) :=
      ⟨fun _ => ⟨omissionTail J F.ell, omissionTail_card J F.ell⟩⟩
    letI : Nonempty (OmissionChoices P (J + F.ell) F.ell) := hnonempty
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hinner (c : EdgeChoice A s) :
      (∑ O : OmissionChoices P (J + F.ell) F.ell,
        if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
          omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
          ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) =
        if edgeChoiceValid A mode i s t c ∧ extra s t c then
          ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := by
    by_cases hv : edgeChoiceValid A mode i s t c
    · by_cases he : extra s t c
      · simp [hv, he]
      · simp [hv, he]
    · simp [hv]
  calc
    _ = D⁻¹ * ∑ O : OmissionChoices P (J + F.ell) F.ell,
        (D * edgeSymmetryFactor P (J + F.ell)) *
          ∑ c : EdgeChoice A s,
            if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
              omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
              ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := by
        rfl
    _ = edgeSymmetryFactor P (J + F.ell) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          ∑ c : EdgeChoice A s,
            if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
              omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
              ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := by
        calc
          _ = ∑ O : OmissionChoices P (J + F.ell) F.ell,
              D⁻¹ * ((D * edgeSymmetryFactor P (J + F.ell)) *
                ∑ c : EdgeChoice A s,
                  if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
                    omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
                    ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) := by
            rw [Finset.mul_sum]
          _ = ∑ O : OmissionChoices P (J + F.ell) F.ell,
              edgeSymmetryFactor P (J + F.ell) *
                ∑ c : EdgeChoice A s,
                  if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
                    omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
                    ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := by
            apply Finset.sum_congr rfl
            intro O hO
            have hscalar : D⁻¹ * (D * edgeSymmetryFactor P (J + F.ell)) =
                edgeSymmetryFactor P (J + F.ell) := by
              field_simp [ne_of_gt hD]
            calc
              _ = (D⁻¹ * (D * edgeSymmetryFactor P (J + F.ell))) *
                    (∑ c : EdgeChoice A s,
                      if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
                        omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
                        ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) := by ring
              _ = _ := by rw [hscalar]
          _ = _ := (Finset.mul_sum _ _ _).symm
    _ = edgeSymmetryFactor P (J + F.ell) *
        ∑ c : EdgeChoice A s,
          ∑ O : OmissionChoices P (J + F.ell) F.ell,
            if edgeChoiceValid A mode i s t c ∧ extra s t c ∧
              omissionOfPerm P J F.ell (if source then c.1 else c.2.1) = O then
              ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0 := by
        congr 1
        exact Finset.sum_comm
    _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro c hc
        exact hinner c

def edgeHasPromotion {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    {A : Model F P J m} {s : P.MemoryState (J + F.ell)} (c : EdgeChoice A s) : Prop :=
  ∃ g : P.BigGroup, c.2.2.2.2.2.1 g ≠ ∅

def edgeHasStore {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    {A : Model F P J m} {s : P.MemoryState (J + F.ell)} (c : EdgeChoice A s) : Prop :=
  ∃ g : P.BigGroup, c.2.2.2.2.1 g ≠ ∅

def edgeHasStoreOnly {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    {A : Model F P J m} {s : P.MemoryState (J + F.ell)} (c : EdgeChoice A s) : Prop :=
  edgeHasStore c ∧ ¬ edgeHasPromotion c

abbrev EdgeTransferContext {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) :=
  Fin A.patternCount × P.Aux J × P.BigPermutations (J + F.ell)

theorem omissionOfPerm_combinePermutations {P : PrimeGroups} {J ell : ℕ}
    (πB : P.BigPermutations (J + ell)) (πS : SmallPermutations P (J + ell)) :
    omissionOfPerm P J ell (combinePermutations P πB πS) = omissionOfSmallPerm P J ell πS := by
  funext g
  apply Subtype.ext
  simp [omissionOfPerm, omissionOfSmallPerm, combinePermutations, g.property]

/-- For a fixed omission, a pattern/auxiliary/big-permutation context and a
small source fiber are exactly one full source-permutation fiber. -/
noncomputable def edgeContextOmissionEquiv {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (O : OmissionChoices P (J + F.ell) F.ell) :
    (Σ ctx : EdgeTransferContext A, OmissionSmallFiber P J F.ell O) ≃
      Fin A.patternCount × P.Aux J × OmissionAssignmentFiber P J F.ell O where
  toFun x :=
    Prod.mk x.1.1 (Prod.mk x.1.2.1
      ⟨combinePermutations P x.1.2.2 x.2.1, by
        rw [omissionOfPerm_combinePermutations]
        exact x.2.2⟩)
  invFun y :=
    let z := omissionAssignmentFiberSplitEquiv P J F.ell O y.2.2
    Sigma.mk (Prod.mk y.1 (Prod.mk y.2.1 z.1)) z.2
  left_inv := by
    rintro ⟨⟨v, ⟨u, πB⟩⟩, ⟨πS, hπS⟩⟩
    have hB : (fun g : P.BigGroup => combinePermutations P πB πS g.val) = πB := by
      funext g
      simp [combinePermutations, g.property]
    have hS : (fun g : P.SmallGroup => combinePermutations P πB πS g.val) = πS := by
      funext g
      simp [combinePermutations, g.property]
    have hfiber :
        omissionAssignmentFiberSplitEquiv P J F.ell O
          ⟨combinePermutations P πB πS, by
            rw [omissionOfPerm_combinePermutations]
            exact hπS⟩ = (πB, ⟨πS, hπS⟩) := by
      apply Prod.ext
      · change (fun g : P.BigGroup => combinePermutations P πB πS g.val) = πB
        exact hB
      · apply Subtype.ext
        change (fun g : P.SmallGroup => combinePermutations P πB πS g.val) = πS
        exact hS
    dsimp
    rw [hfiber]
  right_inv := by
    rintro ⟨v, ⟨u, ⟨π, hπ⟩⟩⟩
    have hsplit := (omissionAssignmentFiberSplitEquiv P J F.ell O).left_inv ⟨π, hπ⟩
    have hperm := congrArg Subtype.val hsplit
    dsimp
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact hperm

/-- Promotion summands with the pattern, auxiliary tuple and source big
permutation fixed. -/
def promotionContextKernel {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (ctx : EdgeTransferContext A) (O : OmissionChoices P (J + F.ell) F.ell)
    [Fintype (OmissionSmallFiber P J F.ell O)]
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
    edgeSymmetryFactor P (J + F.ell) *
      ∑ πS : OmissionSmallFiber P J F.ell O,
        ∑ τ : P.Permutations (J + F.ell),
          ∑ tr : TransferChoice s,
            let c : EdgeChoice A s :=
              (combinePermutations P ctx.2.2 πS.1, τ, ctx.1, ctx.2.1, tr)
            if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
              ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0

/-- Store-only summands with the pattern, auxiliary tuple and target big
permutation fixed. -/
def storeOnlyContextKernel {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (ctx : EdgeTransferContext A) (O : OmissionChoices P (J + F.ell) F.ell)
    [Fintype (OmissionSmallFiber P J F.ell O)]
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
    edgeSymmetryFactor P (J + F.ell) *
      ∑ π : P.Permutations (J + F.ell),
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ tr : TransferChoice s,
            let c : EdgeChoice A s :=
              (π, combinePermutations P ctx.2.2 τS.1, ctx.1, ctx.2.1, tr)
            if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
              ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0

abbrev EdgeContextChoice {F : FixedData} {P : PrimeGroups} {J m : ℕ}
    (A : Model F P J m) (s : P.MemoryState (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell) :=
  Σ ctx : EdgeTransferContext A,
    OmissionSmallFiber P J F.ell O ×
      (P.Permutations (J + F.ell) × TransferChoice s)

/-- Full edge choices in an omission fiber are the same data as a fixed
pattern/auxiliary/big-permutation context, a small omission fiber, and the
remaining target-permutation and transfer choices. -/
noncomputable def edgeChoiceContextEquiv {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (s : P.MemoryState (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell) :
    EdgeContextChoice A s O ≃
      {c : EdgeChoice A s // omissionOfPerm P J F.ell c.1 = O} where
  toFun x :=
    let c : EdgeChoice A s :=
      Prod.mk (combinePermutations P x.1.2.2 x.2.1.1)
        (Prod.mk x.2.2.1
          (Prod.mk x.1.1 (Prod.mk x.1.2.1 x.2.2.2)))
    ⟨c, by
      change omissionOfPerm P J F.ell (combinePermutations P x.1.2.2 x.2.1.1) = O
      rw [omissionOfPerm_combinePermutations]
      exact x.2.1.2⟩
  invFun y :=
    let c := y.1
    let z := (edgeContextOmissionEquiv A O).symm
      (Prod.mk c.2.2.1 (Prod.mk c.2.2.2.1 (Subtype.mk c.1 y.2)))
    Sigma.mk z.1 (Prod.mk z.2 (Prod.mk c.2.1 c.2.2.2.2))
  left_inv := by
    intro x
    have hctx := (edgeContextOmissionEquiv A O).left_inv (Sigma.mk x.1 x.2.1)
    exact congrArg
      (fun z : Σ c : EdgeTransferContext A, OmissionSmallFiber P J F.ell O =>
        (Sigma.mk z.1 (Prod.mk z.2 x.2.2) : EdgeContextChoice A s O)) hctx
  right_inv := by
    rintro ⟨c, hO⟩
    let q : Fin A.patternCount × P.Aux J × OmissionAssignmentFiber P J F.ell O :=
      Prod.mk c.2.2.1 (Prod.mk c.2.2.2.1 (Subtype.mk c.1 hO))
    have hctx := (edgeContextOmissionEquiv A O).right_inv q
    have hv := congrArg Prod.fst hctx
    have hrest := congrArg Prod.snd hctx
    have hu := congrArg Prod.fst hrest
    have hsource := congrArg Subtype.val (congrArg Prod.snd hrest)
    dsimp
    apply Subtype.ext
    apply Prod.ext
    · exact hsource
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact hv
        · apply Prod.ext
          · exact hu
          · rfl

/-- Swapping the endpoint permutations carries a source-omission fiber to a
target-omission fiber. -/
noncomputable def edgeChoiceSourceTargetSwapEquiv {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (s : P.MemoryState (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell) :
    {c : EdgeChoice A s // omissionOfPerm P J F.ell c.1 = O} ≃
      {c : EdgeChoice A s // omissionOfPerm P J F.ell c.2.1 = O} where
  toFun y :=
    ⟨(y.1.2.1, y.1.1, y.1.2.2), by
      change omissionOfPerm P J F.ell y.1.1 = O
      exact y.2⟩
  invFun y :=
    ⟨(y.1.2.1, y.1.1, y.1.2.2), by
      change omissionOfPerm P J F.ell y.1.2.1 = O
      exact y.2⟩
  left_inv := by
    intro y
    apply Subtype.ext
    rfl
  right_inv := by
    intro y
    apply Subtype.ext
    rfl

/-- Reindex edge choices by fixing the target-side big permutation and its
small omission fiber. -/
noncomputable def edgeChoiceTargetContextEquiv {F : FixedData} {P : PrimeGroups}
    {J m : ℕ} (A : Model F P J m) (s : P.MemoryState (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell) :
    EdgeContextChoice A s O ≃
      {c : EdgeChoice A s // omissionOfPerm P J F.ell c.2.1 = O} :=
  (edgeChoiceContextEquiv A s O).trans (edgeChoiceSourceTargetSwapEquiv A s O)

/-- Summing the promotion contexts at a fixed source omission reconstructs
the corresponding omission-restricted edge kernel. -/
theorem promotionContextKernel_sum {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (O : OmissionChoices P (J + F.ell) F.ell)
    [Fintype (OmissionSmallFiber P J F.ell O)]
    (s t : P.MemoryState (J + F.ell)) :
    (∑ ctx : EdgeTransferContext A,
      promotionContextKernel A r theta i ctx O s t) =
      omissionRestrictedAbsoluteKernel A n r.rho theta i .dirty true O
        (fun _ _ c => edgeHasPromotion c) s t := by
  classical
  let pred : EdgeChoice A s → Prop :=
    fun c => omissionOfPerm P J F.ell c.1 = O
  let f : EdgeChoice A s → ℝ := fun c =>
    if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
      ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0
  letI : Fintype (EdgeContextChoice A s O) := by
    dsimp [EdgeContextChoice]
    infer_instance
  have hflat :
      (∑ ctx : EdgeTransferContext A,
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceContextEquiv A s O
                ⟨ctx, ⟨πS, ⟨τ, tr⟩⟩⟩).1) =
        ∑ x : EdgeContextChoice A s O,
          f (edgeChoiceContextEquiv A s O x).1 := by
    change (∑ ctx : EdgeTransferContext A,
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceContextEquiv A s O
                ⟨ctx, (πS, (τ, tr))⟩).1) =
      ∑ x : Σ ctx : EdgeTransferContext A,
          OmissionSmallFiber P J F.ell O ×
            (P.Permutations (J + F.ell) × TransferChoice s),
        f (edgeChoiceContextEquiv A s O x).1
    calc
      _ = ∑ ctx : EdgeTransferContext A,
            ∑ q : OmissionSmallFiber P J F.ell O ×
              (P.Permutations (J + F.ell) × TransferChoice s),
              f (edgeChoiceContextEquiv A s O ⟨ctx, q⟩).1 := by
            apply Finset.sum_congr rfl
            intro ctx hctx
            calc
              _ = ∑ πS : OmissionSmallFiber P J F.ell O,
                    ∑ q : P.Permutations (J + F.ell) × TransferChoice s,
                      f (edgeChoiceContextEquiv A s O
                        ⟨ctx, (πS, q)⟩).1 := by
                    apply Finset.sum_congr rfl
                    intro πS hπS
                    rw [Fintype.sum_prod_type]
              _ = ∑ q : OmissionSmallFiber P J F.ell O ×
                      (P.Permutations (J + F.ell) × TransferChoice s),
                    f (edgeChoiceContextEquiv A s O ⟨ctx, q⟩).1 := by
                    rw [Fintype.sum_prod_type]
      _ = _ := by rw [Fintype.sum_sigma]
  have hsubtype :
      (∑ y : {c : EdgeChoice A s // pred c}, f y.1) =
        ∑ c : EdgeChoice A s, if pred c then f c else 0 := by
    calc
      _ = ∑ y ∈ Finset.univ.subtype pred, f y.1 := by simp
      _ = ∑ c ∈ Finset.univ.filter pred, f c :=
        Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := pred) f
      _ = _ := by
        rw [Finset.sum_filter]
  have hctx :
      (∑ ctx : EdgeTransferContext A,
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceContextEquiv A s O
                ⟨ctx, (πS, (τ, tr))⟩).1) =
      (∑ ctx : EdgeTransferContext A,
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              let c : EdgeChoice A s :=
                (combinePermutations P ctx.2.2 πS.1, τ, ctx.1, ctx.2.1, tr)
              if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
                ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) := by
    apply Finset.sum_congr rfl
    intro ctx hctx
    apply Finset.sum_congr rfl
    intro πS hπS
    apply Finset.sum_congr rfl
    intro τ hτ
    apply Finset.sum_congr rfl
    intro tr htr
    dsimp [edgeChoiceContextEquiv, f]
    rfl
  have hsum :
      (∑ ctx : EdgeTransferContext A,
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceContextEquiv A s O
                ⟨ctx, ⟨πS, ⟨τ, tr⟩⟩⟩).1) =
        ∑ c : EdgeChoice A s,
          if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c ∧ pred c then
            ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0 := by
    calc
      _ = ∑ x : EdgeContextChoice A s O,
            f (edgeChoiceContextEquiv A s O x).1 := hflat
      _ = ∑ y : {c : EdgeChoice A s // pred c}, f y.1 := by
            apply Fintype.sum_equiv (edgeChoiceContextEquiv A s O)
            intro x
            rfl
      _ = ∑ c : EdgeChoice A s, if pred c then f c else 0 := hsubtype
      _ = _ := by
            apply Finset.sum_congr rfl
            intro c hc
            by_cases hp : pred c <;> simp [hp, f]
  have hsumExplicit :
      (∑ ctx : EdgeTransferContext A,
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              let c : EdgeChoice A s :=
                (combinePermutations P ctx.2.2 πS.1, τ, ctx.1, ctx.2.1, tr)
              if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
                ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) =
      ∑ c : EdgeChoice A s,
        if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c ∧ pred c then
          ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0 :=
    hctx.trans hsum
  unfold promotionContextKernel omissionRestrictedAbsoluteKernel
  calc
    _ = (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
        edgeSymmetryFactor P (J + F.ell) *
        ∑ ctx : EdgeTransferContext A,
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              ∑ tr : TransferChoice s,
                (let c : EdgeChoice A s :=
                    (combinePermutations P ctx.2.2 πS.1, τ, ctx.1, ctx.2.1, tr)
                 if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
                   ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) := by
          rw [← Finset.mul_sum]
    _ = (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
        edgeSymmetryFactor P (J + F.ell) *
        ∑ c : EdgeChoice A s,
          if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c ∧ pred c then
            ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0 := by
          exact congrArg
            (fun x : ℝ =>
              (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
                edgeSymmetryFactor P (J + F.ell) * x)
            hsumExplicit
    _ = _ := rfl

/- Reassembling the target-omission fibers is the store-side counterpart of
the source promotion identity. -/
theorem storeOnlyContextKernel_sum {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (O : OmissionChoices P (J + F.ell) F.ell)
    [Fintype (OmissionSmallFiber P J F.ell O)]
    (s t : P.MemoryState (J + F.ell)) :
    (∑ ctx : EdgeTransferContext A,
      storeOnlyContextKernel A r theta i ctx O s t) =
      omissionRestrictedAbsoluteKernel A n r.rho theta i .dirty false O
        (fun _ _ c => edgeHasStoreOnly c) s t := by
  classical
  let pred : EdgeChoice A s → Prop :=
    fun c => omissionOfPerm P J F.ell c.2.1 = O
  let f : EdgeChoice A s → ℝ := fun c =>
    if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
      ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0
  letI : Fintype (EdgeContextChoice A s O) := by
    dsimp [EdgeContextChoice]
    infer_instance
  have hflat :
      (∑ ctx : EdgeTransferContext A,
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ π : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceTargetContextEquiv A s O
                ⟨ctx, ⟨τS, ⟨π, tr⟩⟩⟩).1) =
        ∑ x : EdgeContextChoice A s O,
          f (edgeChoiceTargetContextEquiv A s O x).1 := by
    change (∑ ctx : EdgeTransferContext A,
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ π : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceTargetContextEquiv A s O
                ⟨ctx, (τS, (π, tr))⟩).1) =
      ∑ x : Σ ctx : EdgeTransferContext A,
          OmissionSmallFiber P J F.ell O ×
            (P.Permutations (J + F.ell) × TransferChoice s),
        f (edgeChoiceTargetContextEquiv A s O x).1
    calc
      _ = ∑ ctx : EdgeTransferContext A,
            ∑ q : OmissionSmallFiber P J F.ell O ×
              (P.Permutations (J + F.ell) × TransferChoice s),
              f (edgeChoiceTargetContextEquiv A s O ⟨ctx, q⟩).1 := by
            apply Finset.sum_congr rfl
            intro ctx hctx
            calc
              _ = ∑ τS : OmissionSmallFiber P J F.ell O,
                    ∑ q : P.Permutations (J + F.ell) × TransferChoice s,
                      f (edgeChoiceTargetContextEquiv A s O
                        ⟨ctx, (τS, q)⟩).1 := by
                    apply Finset.sum_congr rfl
                    intro τS hτS
                    rw [Fintype.sum_prod_type]
              _ = ∑ q : OmissionSmallFiber P J F.ell O ×
                      (P.Permutations (J + F.ell) × TransferChoice s),
                    f (edgeChoiceTargetContextEquiv A s O ⟨ctx, q⟩).1 := by
                    rw [Fintype.sum_prod_type]
      _ = _ := by rw [Fintype.sum_sigma]
  have hsubtype :
      (∑ y : {c : EdgeChoice A s // pred c}, f y.1) =
        ∑ c : EdgeChoice A s, if pred c then f c else 0 := by
    calc
      _ = ∑ y ∈ Finset.univ.subtype pred, f y.1 := by simp
      _ = ∑ c ∈ Finset.univ.filter pred, f c :=
        Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := pred) f
      _ = _ := by rw [Finset.sum_filter]
  have hctx :
      (∑ ctx : EdgeTransferContext A,
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ π : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceTargetContextEquiv A s O
                ⟨ctx, (τS, (π, tr))⟩).1) =
      (∑ ctx : EdgeTransferContext A,
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ π : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              let c : EdgeChoice A s :=
                (π, combinePermutations P ctx.2.2 τS.1, ctx.1, ctx.2.1, tr)
              if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
                ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) := by
    apply Finset.sum_congr rfl
    intro ctx hctx
    apply Finset.sum_congr rfl
    intro τS hτS
    apply Finset.sum_congr rfl
    intro π hπ
    apply Finset.sum_congr rfl
    intro tr htr
    dsimp [edgeChoiceTargetContextEquiv, edgeChoiceSourceTargetSwapEquiv,
      edgeChoiceContextEquiv, f]
    rfl
  have hsum :
      (∑ ctx : EdgeTransferContext A,
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ π : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              f (edgeChoiceTargetContextEquiv A s O
                ⟨ctx, ⟨τS, ⟨π, tr⟩⟩⟩).1) =
        ∑ c : EdgeChoice A s,
          if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c ∧ pred c then
            ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0 := by
    calc
      _ = ∑ x : EdgeContextChoice A s O,
            f (edgeChoiceTargetContextEquiv A s O x).1 := hflat
      _ = ∑ y : {c : EdgeChoice A s // pred c}, f y.1 := by
            apply Fintype.sum_equiv (edgeChoiceTargetContextEquiv A s O)
            intro x
            rfl
      _ = ∑ c : EdgeChoice A s, if pred c then f c else 0 := hsubtype
      _ = _ := by
            apply Finset.sum_congr rfl
            intro c hc
            by_cases hp : pred c <;> simp [hp, f]
  have hsumExplicit :
      (∑ ctx : EdgeTransferContext A,
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ π : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              let c : EdgeChoice A s :=
                (π, combinePermutations P ctx.2.2 τS.1, ctx.1, ctx.2.1, tr)
              if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
                ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) =
      ∑ c : EdgeChoice A s,
        if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c ∧ pred c then
          ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0 :=
    hctx.trans hsum
  unfold storeOnlyContextKernel omissionRestrictedAbsoluteKernel
  calc
    _ = (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
        edgeSymmetryFactor P (J + F.ell) *
        ∑ ctx : EdgeTransferContext A,
          ∑ τS : OmissionSmallFiber P J F.ell O,
            ∑ π : P.Permutations (J + F.ell),
              ∑ tr : TransferChoice s,
                (let c : EdgeChoice A s :=
                    (π, combinePermutations P ctx.2.2 τS.1, ctx.1, ctx.2.1, tr)
                 if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
                   ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) := by
          rw [← Finset.mul_sum]
          apply congrArg
            (fun x : ℝ =>
              (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
                edgeSymmetryFactor P (J + F.ell) * x)
          apply Finset.sum_congr rfl
          intro ctx hctx
          rw [Finset.sum_comm]
    _ = (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
        edgeSymmetryFactor P (J + F.ell) *
        ∑ c : EdgeChoice A s,
          if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c ∧ pred c then
            ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0 := by
          exact congrArg
            (fun x : ℝ =>
              (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ) *
                edgeSymmetryFactor P (J + F.ell) * x)
            hsumExplicit
    _ = _ := rfl

/- The promotion context inherits the uniform conditioned row bound from the
fixed-context absolute estimate. -/
theorem promotionContextKernel_rowCost_le {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (ctx : EdgeTransferContext A)
    (O : OmissionChoices P (J + F.ell) F.ell)
    (s : P.MemoryState (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVpos : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val,
      tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    (∑ t ∈ S, promotionContextKernel A r theta i ctx O s t *
        P.memoryWeight r.v t) ≤
      (Erdos821.P3Edge.patternSup A ctx.1 * (A.pattern ctx.1).auxMass ctx.2.1 *
        P.memoryWeight r.v s *
        ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup)) /
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
  classical
  let v := ctx.1
  let u := ctx.2.1
  let πB := ctx.2.2
  let D : ℝ := Fintype.card (OmissionChoices P (J + F.ell) F.ell)
  let H : ℝ := edgeSymmetryFactor P (J + F.ell)
  have hcombine :
      (∑ t ∈ S, promotionContextKernel A r theta i ctx O s t *
          P.memoryWeight r.v t) =
        D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              ∑ tr : TransferChoice s,
                ∑ t ∈ S,
                  if edgeChoiceValid A .dirty i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                      edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0 := by
    unfold promotionContextKernel
    have hMul (t : P.MemoryState (J + F.ell)) :
        (∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              if edgeChoiceValid A .dirty i s t
                  (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                  edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                ‖edgeChoiceCoefficient A n r.rho theta i s t
                  (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
          P.memoryWeight r.v t =
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ tr : TransferChoice s,
              if edgeChoiceValid A .dirty i s t
                  (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                  edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                ‖edgeChoiceCoefficient A n r.rho theta i s t
                  (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                  P.memoryWeight r.v t else 0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro πS hπS
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ hτ
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro tr htr
      by_cases hp : edgeChoiceValid A .dirty i s t
          (combinePermutations P πB πS.1, τ, v, u, tr) ∧
          edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr)
      · simp [hp]
      · simp [hp]
    calc
      _ = D * H *
            ∑ t ∈ S,
              ∑ πS : OmissionSmallFiber P J F.ell O,
                ∑ τ : P.Permutations (J + F.ell),
                  ∑ tr : TransferChoice s,
                    if edgeChoiceValid A .dirty i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                        edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                      ‖edgeChoiceCoefficient A n r.rho theta i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                        P.memoryWeight r.v t else 0 := by
          calc
            _ = ∑ t ∈ S, D * H *
                  (∑ πS : OmissionSmallFiber P J F.ell O,
                    ∑ τ : P.Permutations (J + F.ell),
                      ∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                            edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                            P.memoryWeight r.v t else 0) := by
                apply Finset.sum_congr rfl
                intro t ht
                calc
                  _ = D * H *
                        ((∑ πS : OmissionSmallFiber P J F.ell O,
                          ∑ τ : P.Permutations (J + F.ell),
                            ∑ tr : TransferChoice s,
                              if edgeChoiceValid A .dirty i s t
                                  (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                                  edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                                ‖edgeChoiceCoefficient A n r.rho theta i s t
                                  (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
                          P.memoryWeight r.v t) := by ring
                  _ = D * H *
                        (∑ πS : OmissionSmallFiber P J F.ell O,
                          ∑ τ : P.Permutations (J + F.ell),
                            ∑ tr : TransferChoice s,
                              if edgeChoiceValid A .dirty i s t
                                  (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                                  edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                                ‖edgeChoiceCoefficient A n r.rho theta i s t
                                  (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                                  P.memoryWeight r.v t else 0) := by
                      exact congrArg (fun z : ℝ => D * H * z) (hMul t)
            _ = D * H *
                  ∑ t ∈ S,
                    ∑ πS : OmissionSmallFiber P J F.ell O,
                      ∑ τ : P.Permutations (J + F.ell),
                        ∑ tr : TransferChoice s,
                          if edgeChoiceValid A .dirty i s t
                              (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                              edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                            ‖edgeChoiceCoefficient A n r.rho theta i s t
                              (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                              P.memoryWeight r.v t else 0 := by
                rw [Finset.mul_sum]
      _ = D * H *
            ∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ τ : P.Permutations (J + F.ell),
                ∑ tr : TransferChoice s,
                  ∑ t ∈ S,
                    if edgeChoiceValid A .dirty i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                        edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                      ‖edgeChoiceCoefficient A n r.rho theta i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                        P.memoryWeight r.v t else 0 := by
          congr 1
          calc
            _ = ∑ πS : OmissionSmallFiber P J F.ell O,
                  ∑ t ∈ S,
                    ∑ τ : P.Permutations (J + F.ell),
                      ∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                            edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                            P.memoryWeight r.v t else 0 := Finset.sum_comm
            _ = ∑ πS : OmissionSmallFiber P J F.ell O,
                  ∑ τ : P.Permutations (J + F.ell),
                    ∑ t ∈ S,
                      ∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                            edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                            P.memoryWeight r.v t else 0 := by
                apply Finset.sum_congr rfl
                intro πS hπS
                exact Finset.sum_comm
            _ = ∑ πS : OmissionSmallFiber P J F.ell O,
                  ∑ τ : P.Permutations (J + F.ell),
                    ∑ tr : TransferChoice s,
                      ∑ t ∈ S,
                        if edgeChoiceValid A .dirty i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                            edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                            P.memoryWeight r.v t else 0 := by
                apply Finset.sum_congr rfl
                intro πS hπS
                apply Finset.sum_congr rfl
                intro τ hτ
                exact Finset.sum_comm
  have hpoint (πS : OmissionSmallFiber P J F.ell O)
      (τ : P.Permutations (J + F.ell)) :
      (∑ tr : TransferChoice s,
        ∑ t ∈ S,
          if edgeChoiceValid A .dirty i s t
              (combinePermutations P πB πS.1, τ, v, u, tr) ∧
              edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
            ‖edgeChoiceCoefficient A n r.rho theta i s t
              (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
              P.memoryWeight r.v t else 0) ≤
        fixedContextRowCost A r n theta i v u s
          (combinePermutations P πB πS.1) τ S := by
    unfold fixedContextRowCost
    apply Finset.sum_le_sum
    intro tr htr
    apply Finset.sum_le_sum
    intro t ht
    let c : EdgeChoice A s :=
      (combinePermutations P πB πS.1, τ, v, u, tr)
    have hweight : 0 ≤ P.memoryWeight r.v t :=
      (Erdos821.P3Edge.memoryWeight_pos r t).le
    by_cases hdirty : edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c
    · have hall : edgeChoiceValid A .all i s t c := by
        rcases hdirty.1 with ⟨hraw, hmode⟩
        exact ⟨hraw, by simp [transferModeAccept]⟩
      simp [c, hdirty, hall]
    · simp only [c, if_neg hdirty]
      by_cases hall : edgeChoiceValid A .all i s t c
      · have hall' : edgeChoiceValid A .all i s t
            (combinePermutations P πB πS.1, τ, v, u, tr) := by
          simpa [c] using hall
        simpa [hall'] using mul_nonneg
          (norm_nonneg (edgeChoiceCoefficient A n r.rho theta i s t
            (combinePermutations P πB πS.1, τ, v, u, tr))) hweight
      · have hall' : ¬ edgeChoiceValid A .all i s t
            (combinePermutations P πB πS.1, τ, v, u, tr) := by
          simpa [c] using hall
        simp [hall']
  have hfactor : 0 ≤ D * H := by
    dsimp [D, H]
    exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  have hcompare :
      D * H * (
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              ∑ tr : TransferChoice s,
                ∑ t ∈ S,
                  if edgeChoiceValid A .dirty i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                      edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0) ≤
        D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              fixedContextRowCost A r n theta i v u s
                (combinePermutations P πB πS.1) τ S := by
    apply mul_le_mul_of_nonneg_left _ hfactor
    apply Finset.sum_le_sum
    intro πS hπS
    apply Finset.sum_le_sum
    intro τ hτ
    exact hpoint πS τ
  have hrows :
      D * H * (∑ πS : OmissionSmallFiber P J F.ell O,
        ∑ τ : P.Permutations (J + F.ell),
          fixedContextRowCost A r n theta i v u s
            (combinePermutations P πB πS.1) τ S) ≤
      (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
        P.memoryWeight r.v s *
        ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup)) /
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
    simpa [D, H] using fixedContextOmissionRowCost_le A r n theta i v u s πB O S
      hVlo hVpos htilted htiltedSum Cprom Csmall0 hCsmall0Pos hCprom hCsmall0
  calc
    _ = D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              ∑ tr : TransferChoice s,
                ∑ t ∈ S,
                  if edgeChoiceValid A .dirty i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                      edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0 := hcombine
    _ ≤ D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              fixedContextRowCost A r n theta i v u s
                (combinePermutations P πB πS.1) τ S := hcompare
    _ ≤ (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
          P.memoryWeight r.v s *
          ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
            (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
              Fintype.card P.SmallGroup)) /
          (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
        exact hrows

theorem edgeChoiceValid_dirty_iff {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (i : Fin n) (s t : P.MemoryState (J + F.ell))
    (c : EdgeChoice A s) :
    edgeChoiceValid A .dirty i s t c ↔
      rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
        (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 ∧
        (edgeHasStore c ∨ edgeHasPromotion c) := by
  simp [edgeChoiceValid, transferModeAccept, edgeHasStore, edgeHasPromotion, exists_or]

theorem absoluteDirty_choice_split {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    (if edgeChoiceValid A .dirty i s t c then
        ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) =
      (if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
        ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) +
      (if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
        ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) := by
  classical
  by_cases hv : edgeChoiceValid A .dirty i s t c
  · have hmode := (edgeChoiceValid_dirty_iff A i s t c).mp hv
    by_cases hp : edgeHasPromotion c
    · simp [hv, hp, edgeHasStoreOnly]
    · have hs : edgeHasStore c := hmode.2.resolve_right hp
      simp [hv, hp, hs, edgeHasStoreOnly]
  · simp [hv]

theorem absoluteMemoryEdgeKernel_dirty_split {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    absoluteMemoryEdgeKernel A n rho theta i .dirty s t =
      edgeSymmetryFactor P (J + F.ell) *
        ∑ c : EdgeChoice A s,
          (if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
            ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) +
        edgeSymmetryFactor P (J + F.ell) *
        ∑ c : EdgeChoice A s,
          (if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
            ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) := by
  classical
  unfold absoluteMemoryEdgeKernel
  have hsum :
      (∑ c : EdgeChoice A s,
        if edgeChoiceValid A .dirty i s t c then
          ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) =
      (∑ c : EdgeChoice A s,
        ((if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
            ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) +
          (if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
            ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0))) := by
    apply Finset.sum_congr rfl
    intro c hc
    exact absoluteDirty_choice_split A rho theta i s t c
  rw [hsum, Finset.sum_add_distrib, mul_add]

theorem absoluteMemoryEdgeKernel_dirty_omission_split {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    absoluteMemoryEdgeKernel A n rho theta i .dirty s t =
      ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          omissionRestrictedAbsoluteKernel A n rho theta i .dirty true O
            (fun _ _ c => edgeHasPromotion c) s t +
      ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          omissionRestrictedAbsoluteKernel A n rho theta i .dirty false O
            (fun _ _ c => edgeHasStoreOnly c) s t := by
  have hprom := omissionRestrictedAbsoluteKernel_average A rho theta i .dirty true
    (fun _ _ c => edgeHasPromotion c) s t
  have hstore := omissionRestrictedAbsoluteKernel_average A rho theta i .dirty false
    (fun _ _ c => edgeHasStoreOnly c) s t
  calc
    _ = (edgeSymmetryFactor P (J + F.ell) *
          ∑ c : EdgeChoice A s,
            (if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
              ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0) +
        edgeSymmetryFactor P (J + F.ell) *
          ∑ c : EdgeChoice A s,
            (if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
              ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0)) :=
      absoluteMemoryEdgeKernel_dirty_split A rho theta i s t
    _ = _ := by
      exact congrArg₂ (fun x y : ℝ => x + y) hprom.symm hstore.symm

/-- The promotion part averaged over its source omission. -/
def promotionOmissionAverageKernel {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
    ∑ O : OmissionChoices P (J + F.ell) F.ell,
      omissionRestrictedAbsoluteKernel A n rho theta i .dirty true O
        (fun _ _ c => edgeHasPromotion c) s t

/-- The store-only part averaged over its target omission. -/
def storeOnlyOmissionAverageKernel {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) : ℝ :=
  ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
    ∑ O : OmissionChoices P (J + F.ell) F.ell,
      omissionRestrictedAbsoluteKernel A n rho theta i .dirty false O
        (fun _ _ c => edgeHasStoreOnly c) s t

theorem promotionOmissionAverageKernel_nonneg {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ promotionOmissionAverageKernel A rho theta i s t := by
  unfold promotionOmissionAverageKernel
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro O hO
    exact omissionRestrictedAbsoluteKernel_nonneg A rho theta i .dirty true O
      (fun _ _ c => edgeHasPromotion c) s t

theorem storeOnlyOmissionAverageKernel_nonneg {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    0 ≤ storeOnlyOmissionAverageKernel A rho theta i s t := by
  unfold storeOnlyOmissionAverageKernel
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro O hO
    exact omissionRestrictedAbsoluteKernel_nonneg A rho theta i .dirty false O
      (fun _ _ c => edgeHasStoreOnly c) s t

/-- The signed dirty kernel is pointwise dominated by its two omission averages. -/
theorem memoryEdgeKernel_dirty_omission_domination {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ) (i : Fin n)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1)
    (s t : P.MemoryState (J + F.ell)) :
    ‖memoryEdgeKernel A n rho theta i .dirty phi s t‖ ≤
      ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          omissionRestrictedAbsoluteKernel A n rho theta i .dirty true O
            (fun _ _ c => edgeHasPromotion c) s t +
      ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          omissionRestrictedAbsoluteKernel A n rho theta i .dirty false O
            (fun _ _ c => edgeHasStoreOnly c) s t := by
  calc
    _ ≤ absoluteMemoryEdgeKernel A n rho theta i .dirty s t :=
      memoryEdgeKernel_norm_le A n rho theta i .dirty phi hphi s t
    _ = _ := absoluteMemoryEdgeKernel_dirty_omission_split A rho theta i s t

/-- Finite-support weighted Schur bound, without a finiteness assumption on α. -/
theorem normBound_of_finiteSchur {α : Type*} (mass w : α → ℝ)
    (K : α → α → ℝ) (R C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ a b, 0 ≤ K a b) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ a t, ∑ b ∈ t, K a b * w b ≤ R * w a)
    (hcol : ∀ b s, ∑ a ∈ s, mass a * K a b * w a ≤ C * mass b * w b) :
    NormBound mass (fun a b => (K a b : ℂ)) (Real.sqrt (R * C)) := by
  classical
  intro s t f g
  let U : ℝ := ∑ a ∈ s, mass a * ‖f a‖ ^ 2
  let V : ℝ := ∑ b ∈ t, mass b * ‖g b‖ ^ 2
  let S : Finset (α × α) := s.product t
  let rho (u : α × α) : ℝ := mass u.1 * K u.1 u.2 * ‖f u.1‖ * ‖g u.2‖
  let FF (u : α × α) : ℝ :=
    mass u.1 * K u.1 u.2 * w u.2 / w u.1 * ‖f u.1‖ ^ 2
  let GG (u : α × α) : ℝ :=
    mass u.1 * K u.1 u.2 * w u.1 / w u.2 * ‖g u.2‖ ^ 2
  have hU : 0 ≤ U := Finset.sum_nonneg (fun a _ => mul_nonneg (hm a) (sq_nonneg _))
  have hV : 0 ≤ V := Finset.sum_nonneg (fun b _ => mul_nonneg (hm b) (sq_nonneg _))
  have hFF (u : α × α) : 0 ≤ FF u :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (hm u.1) (hK u.1 u.2))
      (hw u.2).le) (hw u.1).le) (sq_nonneg _)
  have hGG (u : α × α) : 0 ≤ GG u :=
    mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (hm u.1) (hK u.1 u.2))
      (hw u.1).le) (hw u.2).le) (sq_nonneg _)
  have hsq (u : α × α) : rho u ^ 2 = FF u * GG u := by
    dsimp only [rho, FF, GG]
    field_simp [ne_of_gt (hw u.1), ne_of_gt (hw u.2)]
  have hFs : (∑ u ∈ S, FF u) ≤ R * U := by
    calc
      (∑ u ∈ S, FF u) = ∑ a ∈ s, ∑ b ∈ t, FF (a, b) := Finset.sum_product s t FF
      _ ≤ ∑ a ∈ s, R * (mass a * ‖f a‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro a _
        have ha : 0 ≤ mass a * ‖f a‖ ^ 2 / w a :=
          div_nonneg (mul_nonneg (hm a) (sq_nonneg _)) (hw a).le
        calc
          _ = (mass a * ‖f a‖ ^ 2 / w a) * (∑ b ∈ t, K a b * w b) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            dsimp only [FF]
            simp only [div_eq_mul_inv]
            ring
          _ ≤ (mass a * ‖f a‖ ^ 2 / w a) * (R * w a) :=
            mul_le_mul_of_nonneg_left (hrow a t) ha
          _ = R * (mass a * ‖f a‖ ^ 2) := by
            field_simp [ne_of_gt (hw a)]
      _ = R * U := (Finset.mul_sum s (fun a => mass a * ‖f a‖ ^ 2) R).symm
  have hGs : (∑ u ∈ S, GG u) ≤ C * V := by
    calc
      (∑ u ∈ S, GG u) = ∑ a ∈ s, ∑ b ∈ t, GG (a, b) := Finset.sum_product s t GG
      _ = ∑ b ∈ t, ∑ a ∈ s, GG (a, b) := Finset.sum_comm
      _ ≤ ∑ b ∈ t, C * (mass b * ‖g b‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro b _
        have hb : 0 ≤ ‖g b‖ ^ 2 / w b := div_nonneg (sq_nonneg _) (hw b).le
        calc
          _ = (‖g b‖ ^ 2 / w b) * (∑ a ∈ s, mass a * K a b * w a) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            dsimp only [GG]
            simp only [div_eq_mul_inv]
            ring
          _ ≤ (‖g b‖ ^ 2 / w b) * (C * mass b * w b) :=
            mul_le_mul_of_nonneg_left (hcol b s) hb
          _ = C * (mass b * ‖g b‖ ^ 2) := by
            field_simp [ne_of_gt (hw b)]
      _ = C * V := (Finset.mul_sum t (fun b => mass b * ‖g b‖ ^ 2) C).symm
  have hcs : (∑ u ∈ S, rho u) ^ 2 ≤ (∑ u ∈ S, FF u) * (∑ u ∈ S, GG u) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (fun u _ => hFF u) (fun u _ => hGG u) (fun u _ => (hsq u).le)
  have hnormEntry (a b : α) :
      ‖(mass a : ℂ) * star (f a) * (K a b : ℂ) * g b‖ = rho (a, b) := by
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hm a), abs_of_nonneg (hK a b)]
    dsimp only [rho]
    ring
  have hnorm :
      ‖∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) * (K a b : ℂ) * g b‖ ≤
        ∑ u ∈ S, rho u := by
    calc
      _ ≤ ∑ a ∈ s, ‖∑ b ∈ t,
          (mass a : ℂ) * star (f a) * (K a b : ℂ) * g b‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ s, ∑ b ∈ t,
          ‖(mass a : ℂ) * star (f a) * (K a b : ℂ) * g b‖ :=
        Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
      _ = ∑ a ∈ s, ∑ b ∈ t, rho (a, b) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        exact hnormEntry a b
      _ = ∑ u ∈ S, rho u := (Finset.sum_product s t rho).symm
  have hpos : 0 ≤ ∑ u ∈ S, rho u := Finset.sum_nonneg (fun u _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (hm u.1) (hK u.1 u.2)) (norm_nonneg _))
      (norm_nonneg _))
  let B : ℝ := Real.sqrt (R * C) * Real.sqrt U * Real.sqrt V
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  have hBsq : B ^ 2 = (R * U) * (C * V) := by
    dsimp only [B]
    simp only [mul_pow, Real.sq_sqrt (mul_nonneg hR hC), Real.sq_sqrt hU,
      Real.sq_sqrt hV]
    ring
  have hfinal :
      ‖∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) * (K a b : ℂ) * g b‖ ^ 2 ≤ B ^ 2 := by
    calc
      _ ≤ (∑ u ∈ S, rho u) ^ 2 := (sq_le_sq₀ (norm_nonneg _) hpos).mpr hnorm
      _ ≤ (∑ u ∈ S, FF u) * (∑ u ∈ S, GG u) := hcs
      _ ≤ (R * U) * (C * V) := mul_le_mul hFs hGs
        (Finset.sum_nonneg (fun u _ => hGG u)) (mul_nonneg hR hU)
      _ = B ^ 2 := hBsq.symm
  have hbound := (sq_le_sq₀ (norm_nonneg _) hB).mp hfinal
  simpa [U, V, B] using hbound

/-- Averaging kernels with sparse bad rows improves one Schur factor by B / |Ω|. -/
theorem normBound_average_sparseRows {α Ω : Type*} [Fintype Ω]
    (mass w : α → ℝ) (K : Ω → α → α → ℝ) (bad : α → Ω → Prop)
    (R C : ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ ω a b, 0 ≤ K ω a b) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ a ω t, ∑ b ∈ t, K ω a b * w b ≤ R * w a)
    (hcol : ∀ b ω s, ∑ a ∈ s, mass a * K ω a b * w a ≤ C * mass b * w b)
    (hbad : ∀ a, (Finset.univ.filter (bad a)).card ≤ B)
    (hzero : ∀ a ω, ¬ bad a ω → ∀ b, K ω a b = 0) :
    NormBound mass
      (fun a b => (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω, K ω a b : ℝ) : ℂ))
      (Real.sqrt ((R * ((B : ℝ) / (Fintype.card Ω : ℝ))) * C)) := by
  classical
  let d : ℝ := (Fintype.card Ω : ℝ)
  let δ : ℝ := (B : ℝ) / d
  let Kavg : α → α → ℝ := fun a b => d⁻¹ * ∑ ω, K ω a b
  have hd : 0 < d := by simpa [d] using hD
  have hdinv : 0 ≤ d⁻¹ := (inv_nonneg.mpr hd.le)
  have hδ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg B) hd.le
  have hKavg (a b : α) : 0 ≤ Kavg a b :=
    mul_nonneg hdinv (Finset.sum_nonneg fun ω _ => hK ω a b)
  have hrowAvg (a : α) (t : Finset α) :
      (∑ b ∈ t, Kavg a b * w b) ≤ (R * δ) * w a := by
    let S : Finset Ω := Finset.univ.filter (bad a)
    have hrewrite :
        (∑ b ∈ t, Kavg a b * w b) =
          d⁻¹ * ∑ ω ∈ S, ∑ b ∈ t, K ω a b * w b := by
      calc
        _ = ∑ b ∈ t, d⁻¹ * ((∑ ω, K ω a b) * w b) := by
          apply Finset.sum_congr rfl
          intro b hb
          dsimp [Kavg]
          ring
        _ = d⁻¹ * ∑ b ∈ t, (∑ ω, K ω a b) * w b := (Finset.mul_sum _ _ _).symm
        _ = d⁻¹ * ∑ b ∈ t, ∑ ω, K ω a b * w b := by
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]
        _ = d⁻¹ * ∑ ω, ∑ b ∈ t, K ω a b * w b := by
          congr 1
          exact Finset.sum_comm
        _ = d⁻¹ * ∑ ω ∈ S, ∑ b ∈ t, K ω a b * w b := by
          congr 1
          symm
          apply Finset.sum_subset (by intro ω hω; simp)
          intro ω hω hωS
          have hnot : ¬ bad a ω := by simpa [S] using hωS
          have hzero' : ∀ b, K ω a b = 0 := fun b => hzero a ω hnot b
          simp [hzero']
    have hsum :
        (∑ ω ∈ S, ∑ b ∈ t, K ω a b * w b) ≤
          (B : ℝ) * (R * w a) := by
      calc
        _ ≤ ∑ ω ∈ S, R * w a :=
          Finset.sum_le_sum (fun ω hω => hrow a ω t)
        _ = (S.card : ℝ) * (R * w a) := by simp
        _ ≤ (B : ℝ) * (R * w a) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hR (hw a).le)
          exact_mod_cast (show S.card ≤ B by simpa [S] using hbad a)
    calc
      _ = d⁻¹ * ∑ ω ∈ S, ∑ b ∈ t, K ω a b * w b := hrewrite
      _ ≤ d⁻¹ * ((B : ℝ) * (R * w a)) := mul_le_mul_of_nonneg_left hsum hdinv
      _ = (R * δ) * w a := by
        dsimp [δ]
        field_simp [ne_of_gt hd]
  have hcolAvg (b : α) (s : Finset α) :
      (∑ a ∈ s, mass a * Kavg a b * w a) ≤ C * mass b * w b := by
    have hterm (a : α) :
        mass a * Kavg a b * w a = d⁻¹ * ∑ ω, mass a * K ω a b * w a := by
      calc
        _ = d⁻¹ * (mass a * (∑ ω, K ω a b) * w a) := by
          dsimp [Kavg]
          ring
        _ = d⁻¹ * ∑ ω, mass a * K ω a b * w a := by
          congr 1
          rw [Finset.mul_sum, Finset.sum_mul]
    have hrewrite :
        (∑ a ∈ s, mass a * Kavg a b * w a) =
          d⁻¹ * ∑ ω, ∑ a ∈ s, mass a * K ω a b * w a := by
      calc
        _ = ∑ a ∈ s, d⁻¹ * ∑ ω, mass a * K ω a b * w a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hterm a
        _ = d⁻¹ * ∑ a ∈ s, ∑ ω, mass a * K ω a b * w a :=
          (Finset.mul_sum _ _ _).symm
        _ = d⁻¹ * ∑ ω, ∑ a ∈ s, mass a * K ω a b * w a := by
          congr 1
          exact Finset.sum_comm
    have hsum :
        (∑ ω, ∑ a ∈ s, mass a * K ω a b * w a) ≤
          (Fintype.card Ω : ℝ) * (C * mass b * w b) := by
      calc
        _ ≤ ∑ ω, C * mass b * w b :=
          Finset.sum_le_sum (fun ω _ => hcol b ω s)
        _ = (Fintype.card Ω : ℝ) * (C * mass b * w b) := by simp
    calc
      _ = d⁻¹ * ∑ ω, ∑ a ∈ s, mass a * K ω a b * w a := hrewrite
      _ ≤ d⁻¹ * ((Fintype.card Ω : ℝ) * (C * mass b * w b)) := by
        exact mul_le_mul_of_nonneg_left hsum hdinv
      _ = C * mass b * w b := by
        dsimp [d]
        field_simp [ne_of_gt hd]
  have hRavg : 0 ≤ R * δ := mul_nonneg hR hδ
  simpa [Kavg, d, δ] using
    normBound_of_finiteSchur mass w Kavg (R * δ) C hm hw hKavg hRavg hC
      hrowAvg hcolAvg

/-- The dual averaging estimate: sparse bad columns improve the other Schur factor. -/
theorem normBound_average_sparseCols {α Ω : Type*} [Fintype Ω]
    (mass w : α → ℝ) (K : Ω → α → α → ℝ) (bad : α → Ω → Prop)
    (R C : ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ ω a b, 0 ≤ K ω a b) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ a ω t, ∑ b ∈ t, K ω a b * w b ≤ R * w a)
    (hcol : ∀ b ω s, ∑ a ∈ s, mass a * K ω a b * w a ≤ C * mass b * w b)
    (hbad : ∀ b, (Finset.univ.filter (bad b)).card ≤ B)
    (hzero : ∀ b ω, ¬ bad b ω → ∀ a, K ω a b = 0) :
    NormBound mass
      (fun a b => (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω, K ω a b : ℝ) : ℂ))
      (Real.sqrt (R * (C * ((B : ℝ) / (Fintype.card Ω : ℝ))))) := by
  classical
  let d : ℝ := (Fintype.card Ω : ℝ)
  let δ : ℝ := (B : ℝ) / d
  let Kavg : α → α → ℝ := fun a b => d⁻¹ * ∑ ω, K ω a b
  have hd : 0 < d := by simpa [d] using hD
  have hdinv : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hδ : 0 ≤ δ := div_nonneg (Nat.cast_nonneg B) hd.le
  have hKavg (a b : α) : 0 ≤ Kavg a b :=
    mul_nonneg hdinv (Finset.sum_nonneg fun ω _ => hK ω a b)
  have hrowAvg (a : α) (t : Finset α) :
      (∑ b ∈ t, Kavg a b * w b) ≤ R * w a := by
    have hrewrite :
        (∑ b ∈ t, Kavg a b * w b) =
          d⁻¹ * ∑ ω, ∑ b ∈ t, K ω a b * w b := by
      calc
        _ = ∑ b ∈ t, d⁻¹ * ((∑ ω, K ω a b) * w b) := by
          apply Finset.sum_congr rfl
          intro b hb
          dsimp [Kavg]
          ring
        _ = d⁻¹ * ∑ b ∈ t, (∑ ω, K ω a b) * w b := (Finset.mul_sum _ _ _).symm
        _ = d⁻¹ * ∑ b ∈ t, ∑ ω, K ω a b * w b := by
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.sum_mul]
        _ = d⁻¹ * ∑ ω, ∑ b ∈ t, K ω a b * w b := by
          congr 1
          exact Finset.sum_comm
    have hsum :
        (∑ ω, ∑ b ∈ t, K ω a b * w b) ≤
          (Fintype.card Ω : ℝ) * (R * w a) := by
      calc
        _ ≤ ∑ ω, R * w a := Finset.sum_le_sum (fun ω _ => hrow a ω t)
        _ = (Fintype.card Ω : ℝ) * (R * w a) := by simp
    calc
      _ = d⁻¹ * ∑ ω, ∑ b ∈ t, K ω a b * w b := hrewrite
      _ ≤ d⁻¹ * ((Fintype.card Ω : ℝ) * (R * w a)) :=
        mul_le_mul_of_nonneg_left hsum hdinv
      _ = R * w a := by
        dsimp [d]
        field_simp [ne_of_gt hd]
  have hcolAvg (b : α) (s : Finset α) :
      (∑ a ∈ s, mass a * Kavg a b * w a) ≤ (C * δ) * mass b * w b := by
    let S : Finset Ω := Finset.univ.filter (bad b)
    have hrewrite :
        (∑ a ∈ s, mass a * Kavg a b * w a) =
          d⁻¹ * ∑ ω ∈ S, ∑ a ∈ s, mass a * K ω a b * w a := by
      have hterm (a : α) :
          mass a * Kavg a b * w a = d⁻¹ * ∑ ω, mass a * K ω a b * w a := by
        calc
          _ = d⁻¹ * (mass a * (∑ ω, K ω a b) * w a) := by
            dsimp [Kavg]
            ring
          _ = d⁻¹ * ∑ ω, mass a * K ω a b * w a := by
            congr 1
            rw [Finset.mul_sum, Finset.sum_mul]
      calc
        _ = ∑ a ∈ s, d⁻¹ * ∑ ω, mass a * K ω a b * w a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hterm a
        _ = d⁻¹ * ∑ a ∈ s, ∑ ω, mass a * K ω a b * w a :=
          (Finset.mul_sum _ _ _).symm
        _ = d⁻¹ * ∑ ω, ∑ a ∈ s, mass a * K ω a b * w a := by
          congr 1
          exact Finset.sum_comm
        _ = d⁻¹ * ∑ ω ∈ S, ∑ a ∈ s, mass a * K ω a b * w a := by
          congr 1
          symm
          apply Finset.sum_subset (by intro ω hω; simp)
          intro ω hω hωS
          have hnot : ¬ bad b ω := by simpa [S] using hωS
          have hzero' : ∀ a, K ω a b = 0 := fun a => hzero b ω hnot a
          simp [hzero']
    have hsum :
        (∑ ω ∈ S, ∑ a ∈ s, mass a * K ω a b * w a) ≤
          (B : ℝ) * (C * mass b * w b) := by
      calc
        _ ≤ ∑ ω ∈ S, C * mass b * w b :=
          Finset.sum_le_sum (fun ω hω => hcol b ω s)
        _ = (S.card : ℝ) * (C * mass b * w b) := by simp
        _ ≤ (B : ℝ) * (C * mass b * w b) := by
          apply mul_le_mul_of_nonneg_right _
            (mul_nonneg (mul_nonneg hC (hm b)) (hw b).le)
          exact_mod_cast (show S.card ≤ B by simpa [S] using hbad b)
    calc
      _ = d⁻¹ * ∑ ω ∈ S, ∑ a ∈ s, mass a * K ω a b * w a := hrewrite
      _ ≤ d⁻¹ * ((B : ℝ) * (C * mass b * w b)) :=
        mul_le_mul_of_nonneg_left hsum hdinv
      _ = (C * δ) * mass b * w b := by
        dsimp [δ]
        field_simp [ne_of_gt hd]
  have hCavg : 0 ≤ C * δ := mul_nonneg hC hδ
  simpa [Kavg, d, δ] using
    normBound_of_finiteSchur mass w Kavg R (C * δ) hm hw hKavg hR hCavg
      hrowAvg hcolAvg

/-- Finite sums of kernels add their finite-support operator bounds. -/
theorem normBound_fintype_sum {α κ : Type*} [Fintype κ]
    (mass : α → ℝ) (K : κ → α → α → ℂ) (C : κ → ℝ)
    (hK : ∀ j, NormBound mass (K j) (C j)) :
    NormBound mass (fun a b => ∑ j, K j a b) (∑ j, C j) := by
  classical
  intro s t f g
  have hentry (a b : α) :
      (mass a : ℂ) * star (f a) * (∑ j, K j a b) * g b =
        ∑ j, (mass a : ℂ) * star (f a) * K j a b * g b := by
    calc
      _ = (mass a : ℂ) * star (f a) * ((∑ j, K j a b) * g b) := by ring
      _ = (mass a : ℂ) * star (f a) * (∑ j, K j a b * g b) := by rw [Finset.sum_mul]
      _ = ∑ j, (mass a : ℂ) * star (f a) * (K j a b * g b) := by
        rw [Finset.mul_sum]
      _ = ∑ j, (mass a : ℂ) * star (f a) * K j a b * g b := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hsum :
      (∑ a ∈ s, ∑ b ∈ t,
        (mass a : ℂ) * star (f a) * (∑ j, K j a b) * g b) =
        ∑ j, ∑ a ∈ s, ∑ b ∈ t,
          (mass a : ℂ) * star (f a) * K j a b * g b := by
    calc
      _ = ∑ a ∈ s, ∑ b ∈ t, ∑ j,
            (mass a : ℂ) * star (f a) * K j a b * g b := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          exact hentry a b
      _ = ∑ a ∈ s, ∑ j, ∑ b ∈ t,
            (mass a : ℂ) * star (f a) * K j a b * g b := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
      _ = ∑ j, ∑ a ∈ s, ∑ b ∈ t,
            (mass a : ℂ) * star (f a) * K j a b * g b := Finset.sum_comm
  calc
    _ = ‖∑ j, ∑ a ∈ s, ∑ b ∈ t,
          (mass a : ℂ) * star (f a) * K j a b * g b‖ := by rw [hsum]
    _ ≤ ∑ j, ‖∑ a ∈ s, ∑ b ∈ t,
          (mass a : ℂ) * star (f a) * K j a b * g b‖ := norm_sum_le _ _
    _ ≤ ∑ j, C j * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
          Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2) :=
      Finset.sum_le_sum (fun j hj => hK j s t f g)
    _ = (∑ j, C j) * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
          Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2) := by
      calc
        _ = ∑ j, C j * (Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
              Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ j, C j) *
              (Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
                Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2)) := by
          rw [← Finset.sum_mul]
        _ = _ := by ring

/-- Contextwise sparse-row gains survive summation over a finite family of edge contexts. -/
theorem normBound_sum_contexts_sparseRows {α Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (mass w : α → ℝ) (K : κ → Ω → α → α → ℝ) (bad : κ → α → Ω → Prop)
    (R C : κ → ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ j ω a b, 0 ≤ K j ω a b)
    (hR : ∀ j, 0 ≤ R j) (hC : ∀ j, 0 ≤ C j)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ j a ω t, ∑ b ∈ t, K j ω a b * w b ≤ R j * w a)
    (hcol : ∀ j b ω s, ∑ a ∈ s, mass a * K j ω a b * w a ≤ C j * mass b * w b)
    (hbad : ∀ j a, (Finset.univ.filter (bad j a)).card ≤ B)
    (hzero : ∀ j a ω, ¬ bad j a ω → ∀ b, K j ω a b = 0) :
    NormBound mass
      (fun a b => ∑ j,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω, K j ω a b : ℝ) : ℂ))
      (∑ j, Real.sqrt ((R j * ((B : ℝ) / (Fintype.card Ω : ℝ))) * C j)) := by
  classical
  apply normBound_fintype_sum mass
    (fun j a b => (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω, K j ω a b : ℝ) : ℂ))
    (fun j => Real.sqrt ((R j * ((B : ℝ) / (Fintype.card Ω : ℝ))) * C j))
  intro j
  exact normBound_average_sparseRows mass w (K j) (bad j) (R j) (C j) B hm hw
    (hK j) (hR j) (hC j) hD (hrow j) (hcol j) (hbad j) (hzero j)

/-- Contextwise sparse-column gains survive summation over a finite family of edge contexts. -/
theorem normBound_sum_contexts_sparseCols {α Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (mass w : α → ℝ) (K : κ → Ω → α → α → ℝ) (bad : κ → α → Ω → Prop)
    (R C : κ → ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ j ω a b, 0 ≤ K j ω a b)
    (hR : ∀ j, 0 ≤ R j) (hC : ∀ j, 0 ≤ C j)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ j a ω t, ∑ b ∈ t, K j ω a b * w b ≤ R j * w a)
    (hcol : ∀ j b ω s, ∑ a ∈ s, mass a * K j ω a b * w a ≤ C j * mass b * w b)
    (hbad : ∀ j b, (Finset.univ.filter (bad j b)).card ≤ B)
    (hzero : ∀ j b ω, ¬ bad j b ω → ∀ a, K j ω a b = 0) :
    NormBound mass
      (fun a b => ∑ j,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω, K j ω a b : ℝ) : ℂ))
      (∑ j, Real.sqrt (R j * (C j * ((B : ℝ) / (Fintype.card Ω : ℝ))))) := by
  classical
  apply normBound_fintype_sum mass
    (fun j a b => (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω, K j ω a b : ℝ) : ℂ))
    (fun j => Real.sqrt (R j * (C j * ((B : ℝ) / (Fintype.card Ω : ℝ)))))
  intro j
  exact normBound_average_sparseCols mass w (K j) (bad j) (R j) (C j) B hm hw
    (hK j) (hR j) (hC j) hD (hrow j) (hcol j) (hbad j) (hzero j)

/-- Pointwise domination by a nonnegative kernel preserves its finite-support
operator norm bound. -/
theorem normBound_of_pointwise_domination {α : Type*}
    (mass : α → ℝ) (K : α → α → ℂ) (H : α → α → ℝ) (C : ℝ)
    (hm : ∀ a, 0 ≤ mass a) (hH : ∀ a b, 0 ≤ H a b)
    (hdom : ∀ a b, ‖K a b‖ ≤ H a b)
    (hbound : NormBound mass (fun a b => (H a b : ℂ)) C) :
    NormBound mass K C := by
  classical
  intro s t f g
  let f' : α → ℂ := fun a => (‖f a‖ : ℝ)
  let g' : α → ℂ := fun b => (‖g b‖ : ℝ)
  have hterm (a b : α) :
      ‖(mass a : ℂ) * star (f a) * K a b * g b‖ ≤
        mass a * ‖f a‖ * H a b * ‖g b‖ := by
    have hmassNorm : ‖(mass a : ℂ)‖ = mass a := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm a)]
    simp only [norm_mul, norm_star, hmassNorm]
    calc
      _ = ((mass a * ‖f a‖) * ‖K a b‖) * ‖g b‖ := by ring
      _ ≤ ((mass a * ‖f a‖) * H a b) * ‖g b‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (hdom a b)
            (mul_nonneg (hm a) (norm_nonneg (f a)))
        · exact norm_nonneg (g b)
  have htri :
      ‖∑ a ∈ s, ∑ b ∈ t,
          (mass a : ℂ) * star (f a) * K a b * g b‖ ≤
        ∑ a ∈ s, ∑ b ∈ t, mass a * ‖f a‖ * H a b * ‖g b‖ := by
    calc
      _ ≤ ∑ a ∈ s, ‖∑ b ∈ t,
            (mass a : ℂ) * star (f a) * K a b * g b‖ := norm_sum_le _ _
      _ ≤ ∑ a ∈ s, ∑ b ∈ t, mass a * ‖f a‖ * H a b * ‖g b‖ := by
        apply Finset.sum_le_sum
        intro a ha
        calc
          _ ≤ ∑ b ∈ t,
              ‖(mass a : ℂ) * star (f a) * K a b * g b‖ := norm_sum_le _ _
          _ ≤ _ := Finset.sum_le_sum (fun b hb => hterm a b)
  have hnonneg :
      0 ≤ ∑ a ∈ s, ∑ b ∈ t, mass a * ‖f a‖ * H a b * ‖g b‖ := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    exact mul_nonneg (mul_nonneg (mul_nonneg (hm a) (norm_nonneg (f a)))
      (hH a b)) (norm_nonneg (g b))
  have hsum :
      ∑ a ∈ s, ∑ b ∈ t,
        (mass a : ℂ) * star (f' a) * (H a b : ℂ) * g' b =
      ((∑ a ∈ s, ∑ b ∈ t, mass a * ‖f a‖ * H a b * ‖g b‖ : ℝ) : ℂ) := by
    simp [f', g']
  have hbase := hbound s t f' g'
  rw [hsum] at hbase
  have hnorm :
      ‖((∑ a ∈ s, ∑ b ∈ t,
        mass a * ‖f a‖ * H a b * ‖g b‖ : ℝ) : ℂ)‖ =
      ∑ a ∈ s, ∑ b ∈ t, mass a * ‖f a‖ * H a b * ‖g b‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm] at hbase
  have hbase' :
      ∑ a ∈ s, ∑ b ∈ t, mass a * ‖f a‖ * H a b * ‖g b‖ ≤
        C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
          Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2) := by
    simpa [f', g', Complex.norm_real, Real.norm_eq_abs] using hbase
  exact htri.trans hbase'

/-- Combine two positive omission-sector norm bounds before domination. -/
theorem normBound_of_two_positive_dominations {α : Type*}
    (mass : α → ℝ) (K : α → α → ℂ) (K₁ K₂ : α → α → ℝ)
    (C₁ C₂ : ℝ) (hm : ∀ a, 0 ≤ mass a)
    (hK₁ : ∀ a b, 0 ≤ K₁ a b) (hK₂ : ∀ a b, 0 ≤ K₂ a b)
    (hdom : ∀ a b, ‖K a b‖ ≤ K₁ a b + K₂ a b)
    (h₁ : NormBound mass (fun a b => (K₁ a b : ℂ)) C₁)
    (h₂ : NormBound mass (fun a b => (K₂ a b : ℂ)) C₂) :
    NormBound mass K (C₁ + C₂) := by
  have hsum : NormBound mass (fun a b => ((K₁ a b + K₂ a b : ℝ) : ℂ)) (C₁ + C₂) := by
    have hadd := Erdos821.S2Core.normBound_add mass
      (fun a b => (K₁ a b : ℂ)) (fun a b => (K₂ a b : ℂ)) C₁ C₂ h₁ h₂
    simpa [Complex.ofReal_add] using hadd
  exact normBound_of_pointwise_domination mass K (fun a b => K₁ a b + K₂ a b)
    (C₁ + C₂) hm (fun a b => add_nonneg (hK₁ a b) (hK₂ a b)) hdom hsum

/-- Assemble the dirty-edge norm once the two omission-sector norms are known. -/
theorem normBound_memoryEdgeKernel_dirty_of_sectorBounds {F : FixedData}
    {P : PrimeGroups} {J m n : ℕ} (A : Model F P J m) (rho theta : ℝ)
    (i : Fin n) (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1)
    (mass : P.MemoryState (J + F.ell) → ℝ) (Cprom Cstore : ℝ)
    (hmass : ∀ s, 0 ≤ mass s)
    (hprom : NormBound mass
      (fun s t => (promotionOmissionAverageKernel A rho theta i s t : ℂ)) Cprom)
    (hstore : NormBound mass
      (fun s t => (storeOnlyOmissionAverageKernel A rho theta i s t : ℂ)) Cstore) :
    NormBound mass (memoryEdgeKernel A n rho theta i .dirty phi) (Cprom + Cstore) := by
  apply normBound_of_two_positive_dominations mass
    (memoryEdgeKernel A n rho theta i .dirty phi)
    (promotionOmissionAverageKernel A rho theta i)
    (storeOnlyOmissionAverageKernel A rho theta i) Cprom Cstore hmass
  · intro s t
    exact promotionOmissionAverageKernel_nonneg A rho theta i s t
  · intro s t
    exact storeOnlyOmissionAverageKernel_nonneg A rho theta i s t
  · intro s t
    simpa [promotionOmissionAverageKernel, storeOnlyOmissionAverageKernel] using
      memoryEdgeKernel_dirty_omission_domination A rho theta i phi hphi s t
  · exact hprom
  · exact hstore

/-- The store-only context inherits the conditioned column bound by expanding
the transfer choice into its literal reversed retrieval data. -/
theorem storeOnlyContextKernel_columnCost_le {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (ctx : EdgeTransferContext A)
    (O : OmissionChoices P (J + F.ell) F.ell)
    (t : P.MemoryState (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVhi : ∀ g : P.Group, P.V g ≤ F.vMax)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val,
      tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    (∑ s ∈ S, P.memoryMass F J n s *
        storeOnlyContextKernel A r theta i ctx O s t * P.memoryWeight r.v s) ≤
      (Erdos821.P3Edge.patternSup A ctx.1 *
        (A.pattern ctx.1).auxMass ctx.2.1 * P.memoryMass F J n t *
        P.memoryWeight r.v t *
        ((Erdos821.P3Edge.colRevConst F m) ^ Fintype.card P.BigGroup *
          (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup)) /
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
  classical
  let v := ctx.1
  let u := ctx.2.1
  let πB := ctx.2.2
  let D : ℝ := Fintype.card (OmissionChoices P (J + F.ell) F.ell)
  let H : ℝ := edgeSymmetryFactor P (J + F.ell)
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g =>
    lt_of_lt_of_le F.vMin_pos (hVlo g)
  have hfactor : 0 ≤ D * H := by
    dsimp [D, H]
    exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  have hmass (s : P.MemoryState (J + F.ell)) :
      0 ≤ P.memoryMass F J n s :=
    Erdos821.P3Edge.memoryMass_nonneg F J n hVpos htilted s
  have hweight (s : P.MemoryState (J + F.ell)) :
      0 ≤ P.memoryWeight r.v s :=
    (Erdos821.P3Edge.memoryWeight_nonneg r s)
  have hinner (s : P.MemoryState (J + F.ell))
      (π : P.Permutations (J + F.ell))
      (τ : P.Permutations (J + F.ell)) :
      P.memoryMass F J n s *
          (∑ tr : TransferChoice s,
            if edgeChoiceValid A .dirty i s t (π, τ, v, u, tr) ∧
                edgeHasStoreOnly (π, τ, v, u, tr) then
              ‖edgeChoiceCoefficient A n r.rho theta i s t (π, τ, v, u, tr)‖
            else 0) * P.memoryWeight r.v s ≤
        ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
          ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
            Erdos821.P3Edge.colSourceMapSum F r n theta i A t π τ v u
              B A_retr s := by
    rw [Finset.mul_sum, Finset.sum_mul]
    unfold TransferChoice Erdos821.P3Edge.colSourceMapSum
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro B hB
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro A_retr hA
    apply Finset.sum_le_sum
    intro f hf
    let tr : TransferChoice s := (B, ⟨A_retr, f⟩)
    by_cases hc : edgeChoiceValid A .dirty i s t (π, τ, v, u, tr) ∧
        edgeHasStoreOnly (π, τ, v, u, tr)
    · have hall : edgeChoiceValid A .all i s t (π, τ, v, u, tr) := by
        rcases hc.1 with ⟨hraw, _⟩
        exact ⟨hraw, by simp [transferModeAccept]⟩
      simp [tr, hc, hall]
    · simp only [tr, if_neg hc]
      by_cases hall : edgeChoiceValid A .all i s t (π, τ, v, u, tr)
      · have hall' : edgeChoiceValid A .all i s t
            (π, τ, v, u, B, ⟨A_retr, f⟩) := by simpa [tr] using hall
        simp only [if_pos hall']
        simpa using mul_nonneg (mul_nonneg (hmass s)
          (norm_nonneg (edgeChoiceCoefficient A n r.rho theta i s t
            (π, τ, v, u, B, ⟨A_retr, f⟩)))) (hweight s)
      · have hall' : ¬ edgeChoiceValid A .all i s t
            (π, τ, v, u, B, ⟨A_retr, f⟩) := by simpa [tr] using hall
        simp [hall']
  have hpoint (s : P.MemoryState (J + F.ell)) :
      P.memoryMass F J n s * storeOnlyContextKernel A r theta i ctx O s t *
          P.memoryWeight r.v s ≤
        D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                    (combinePermutations P πB τS.1) v u B A_retr s := by
    unfold storeOnlyContextKernel
    calc
      _ = D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              (P.memoryMass F J n s *
                (∑ tr : TransferChoice s,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ else 0) *
                P.memoryWeight r.v s) := by
          calc
            _ = D * H *
                (P.memoryMass F J n s *
                  (∑ π : P.Permutations (J + F.ell),
                    ∑ τS : OmissionSmallFiber P J F.ell O,
                      ∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (π, combinePermutations P πB τS.1, v, u, tr) ∧
                            edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (π, combinePermutations P πB τS.1, v, u, tr)‖ else 0) *
                  P.memoryWeight r.v s) := by ring
            _ = D * H *
                (∑ π : P.Permutations (J + F.ell),
                  P.memoryMass F J n s *
                    (∑ τS : OmissionSmallFiber P J F.ell O,
                      ∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (π, combinePermutations P πB τS.1, v, u, tr) ∧
                            edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (π, combinePermutations P πB τS.1, v, u, tr)‖ else 0) *
                    P.memoryWeight r.v s) := by
                apply congrArg (fun z : ℝ => D * H * z)
                rw [Finset.mul_sum, Finset.sum_mul]
            _ = D * H *
                (∑ π : P.Permutations (J + F.ell),
                  ∑ τS : OmissionSmallFiber P J F.ell O,
                    (P.memoryMass F J n s *
                      (∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (π, combinePermutations P πB τS.1, v, u, tr) ∧
                            edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (π, combinePermutations P πB τS.1, v, u, tr)‖ else 0) *
                      P.memoryWeight r.v s)) := by
                apply congrArg (fun z : ℝ => D * H * z)
                apply Finset.sum_congr rfl
                intro π hπ
                rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                    (combinePermutations P πB τS.1) v u B A_retr s := by
          apply mul_le_mul_of_nonneg_left _ hfactor
          apply Finset.sum_le_sum
          intro π hπ
          apply Finset.sum_le_sum
          intro τS hτS
          exact hinner s π (combinePermutations P πB τS.1)
  have hsumBound :
      (∑ s ∈ S, P.memoryMass F J n s * storeOnlyContextKernel A r theta i ctx O s t *
          P.memoryWeight r.v s) ≤
        D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              fixedContextColumnCost A r n theta i v u t π
                (combinePermutations P πB τS.1) S := by
    have hReorder :
        (∑ s ∈ S,
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                    (combinePermutations P πB τS.1) v u B A_retr s) =
        ∑ π : P.Permutations (J + F.ell),
          ∑ τS : OmissionSmallFiber P J F.ell O,
            ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
              ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ s ∈ S,
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                    (combinePermutations P πB τS.1) v u B A_retr s := by
      calc
        _ = ∑ π : P.Permutations (J + F.ell),
              ∑ s ∈ S,
                ∑ τS : OmissionSmallFiber P J F.ell O,
                  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                        (combinePermutations P πB τS.1) v u B A_retr s :=
            Finset.sum_comm
        _ = ∑ π : P.Permutations (J + F.ell),
              ∑ τS : OmissionSmallFiber P J F.ell O,
                ∑ s ∈ S,
                  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                        (combinePermutations P πB τS.1) v u B A_retr s := by
            apply Finset.sum_congr rfl
            intro π hπ
            exact Finset.sum_comm
        _ = ∑ π : P.Permutations (J + F.ell),
              ∑ τS : OmissionSmallFiber P J F.ell O,
                ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ s ∈ S,
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                        (combinePermutations P πB τS.1) v u B A_retr s := by
            apply Finset.sum_congr rfl
            intro π hπ
            apply Finset.sum_congr rfl
            intro τS hτS
            exact Finset.sum_comm
        _ = ∑ π : P.Permutations (J + F.ell),
              ∑ τS : OmissionSmallFiber P J F.ell O,
                ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ s ∈ S,
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                        (combinePermutations P πB τS.1) v u B A_retr s := by
            apply Finset.sum_congr rfl
            intro π hπ
            apply Finset.sum_congr rfl
            intro τS hτS
            apply Finset.sum_congr rfl
            intro B hB
            exact Finset.sum_comm
    calc
      _ ≤ ∑ s ∈ S,
          D * H *
            ∑ π : P.Permutations (J + F.ell),
              ∑ τS : OmissionSmallFiber P J F.ell O,
                ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    Erdos821.P3Edge.colSourceMapSum F r n theta i A t π
                      (combinePermutations P πB τS.1) v u B A_retr s :=
            Finset.sum_le_sum (fun s hs => hpoint s)
      _ = D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              fixedContextColumnCost A r n theta i v u t π
                (combinePermutations P πB τS.1) S := by
          rw [← Finset.mul_sum]
          exact congrArg (fun z : ℝ => D * H * z) (by
            calc
              _ = _ := hReorder
              _ = _ := by simp [fixedContextColumnCost])
  have hfinal := fixedContextOmissionColumnCost_le A r n theta i v u t πB O S
    hVlo hVhi htilted htiltedSum Cprom Csmall0 hCsmall0Pos hCprom hCsmall0
  exact hsumBound.trans hfinal

/-- Promotion contexts have the complementary column bound: after fixing a
source omission, use the literal reversed retrieval estimate for each endpoint
permutation pair, then average the source small-omission fiber. -/
theorem promotionContextKernel_columnCost_le {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (ctx : EdgeTransferContext A)
    (O : OmissionChoices P (J + F.ell) F.ell)
    (t : P.MemoryState (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVhi : ∀ g : P.Group, P.V g ≤ F.vMax)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val, tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    (∑ s ∈ S, P.memoryMass F J n s * promotionContextKernel A r theta i ctx O s t *
        P.memoryWeight r.v s) ≤
      (Erdos821.P3Edge.patternSup A ctx.1 *
        (A.pattern ctx.1).auxMass ctx.2.1 * P.memoryMass F J n t *
        P.memoryWeight r.v t *
        ((Erdos821.P3Edge.colRevConst F m) ^ Fintype.card P.BigGroup *
          (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup)) /
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
  classical
  let v := ctx.1
  let u := ctx.2.1
  let πB := ctx.2.2
  let D : ℝ := Fintype.card (OmissionChoices P (J + F.ell) F.ell)
  let H : ℝ := edgeSymmetryFactor P (J + F.ell)
  have hVpos : ∀ g : P.Group, 0 < P.V g := fun g =>
    lt_of_lt_of_le F.vMin_pos (hVlo g)
  have hfactor : 0 ≤ D * H := by
    dsimp [D, H]
    exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  have hmass (s : P.MemoryState (J + F.ell)) : 0 ≤ P.memoryMass F J n s :=
    Erdos821.P3Edge.memoryMass_nonneg F J n hVpos htilted s
  have hweight (s : P.MemoryState (J + F.ell)) : 0 ≤ P.memoryWeight r.v s :=
    Erdos821.P3Edge.memoryWeight_nonneg r s
  have hinner (s : P.MemoryState (J + F.ell))
      (πS : OmissionSmallFiber P J F.ell O)
      (τ : P.Permutations (J + F.ell)) :
      P.memoryMass F J n s *
          (∑ tr : TransferChoice s,
            if edgeChoiceValid A .dirty i s t
                (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
              ‖edgeChoiceCoefficient A n r.rho theta i s t
                (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
          P.memoryWeight r.v s ≤
        ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
          ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
            Erdos821.P3Edge.colSourceMapSum F r n theta i A t
              (combinePermutations P πB πS.1) τ v u B A_retr s := by
    rw [Finset.mul_sum, Finset.sum_mul]
    unfold TransferChoice Erdos821.P3Edge.colSourceMapSum
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro B hB
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro A_retr hA
    apply Finset.sum_le_sum
    intro f hf
    let tr : TransferChoice s := (B, ⟨A_retr, f⟩)
    by_cases hc : edgeChoiceValid A .dirty i s t
        (combinePermutations P πB πS.1, τ, v, u, tr) ∧
        edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr)
    · have hall : edgeChoiceValid A .all i s t
          (combinePermutations P πB πS.1, τ, v, u, tr) := by
        rcases hc.1 with ⟨hraw, _⟩
        exact ⟨hraw, by simp [transferModeAccept]⟩
      simp [tr, hc, hall]
    · simp only [tr, if_neg hc]
      by_cases hall : edgeChoiceValid A .all i s t
          (combinePermutations P πB πS.1, τ, v, u, tr)
      · have hall' : edgeChoiceValid A .all i s t
            (combinePermutations P πB πS.1, τ, v, u, B, ⟨A_retr, f⟩) := by
          simpa [tr] using hall
        simp only [if_pos hall']
        simpa using mul_nonneg (mul_nonneg (hmass s)
          (norm_nonneg (edgeChoiceCoefficient A n r.rho theta i s t
            (combinePermutations P πB πS.1, τ, v, u, B, ⟨A_retr, f⟩)))) (hweight s)
      · have hall' : ¬ edgeChoiceValid A .all i s t
            (combinePermutations P πB πS.1, τ, v, u, B, ⟨A_retr, f⟩) := by
          simpa [tr] using hall
        simp [hall']
  have hpoint (s : P.MemoryState (J + F.ell)) :
      P.memoryMass F J n s * promotionContextKernel A r theta i ctx O s t *
          P.memoryWeight r.v s ≤
        D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                    (combinePermutations P πB πS.1) τ v u B A_retr s := by
    unfold promotionContextKernel
    have hreshape :
        P.memoryMass F J n s *
            (∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ τ : P.Permutations (J + F.ell),
                ∑ tr : TransferChoice s,
                  if edgeChoiceValid A .dirty i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                      edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
            P.memoryWeight r.v s =
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              (P.memoryMass F J n s *
                (∑ tr : TransferChoice s,
                  if edgeChoiceValid A .dirty i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                      edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
                P.memoryWeight r.v s) := by
      calc
        _ = (∑ πS : OmissionSmallFiber P J F.ell O,
              P.memoryMass F J n s *
                (∑ τ : P.Permutations (J + F.ell),
                  ∑ tr : TransferChoice s,
                    if edgeChoiceValid A .dirty i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                        edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                      ‖edgeChoiceCoefficient A n r.rho theta i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0)) *
              P.memoryWeight r.v s := by
            rw [Finset.mul_sum]
        _ = ∑ πS : OmissionSmallFiber P J F.ell O,
              (P.memoryMass F J n s *
                (∑ τ : P.Permutations (J + F.ell),
                  ∑ tr : TransferChoice s,
                    if edgeChoiceValid A .dirty i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                        edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                      ‖edgeChoiceCoefficient A n r.rho theta i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0)) *
                P.memoryWeight r.v s := by
            rw [Finset.sum_mul]
        _ = ∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ τ : P.Permutations (J + F.ell),
                (P.memoryMass F J n s *
                  (∑ tr : TransferChoice s,
                    if edgeChoiceValid A .dirty i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                        edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                      ‖edgeChoiceCoefficient A n r.rho theta i s t
                        (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
                  P.memoryWeight r.v s) := by
            apply Finset.sum_congr rfl
            intro πS hπS
            rw [Finset.mul_sum, Finset.sum_mul]
    calc
      _ = D * H *
          (∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              (P.memoryMass F J n s *
                (∑ tr : TransferChoice s,
                  if edgeChoiceValid A .dirty i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                      edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
                P.memoryWeight r.v s)) := by
          calc
            _ = D * H * (P.memoryMass F J n s *
                (∑ πS : OmissionSmallFiber P J F.ell O,
                  ∑ τ : P.Permutations (J + F.ell),
                    ∑ tr : TransferChoice s,
                      if edgeChoiceValid A .dirty i s t
                          (combinePermutations P πB πS.1, τ, v, u, tr) ∧
                          edgeHasPromotion (combinePermutations P πB πS.1, τ, v, u, tr) then
                        ‖edgeChoiceCoefficient A n r.rho theta i s t
                          (combinePermutations P πB πS.1, τ, v, u, tr)‖ else 0) *
                P.memoryWeight r.v s) := by ring
            _ = _ := congrArg (fun z : ℝ => D * H * z) hreshape
      _ ≤ D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                    (combinePermutations P πB πS.1) τ v u B A_retr s := by
          apply mul_le_mul_of_nonneg_left _ hfactor
          apply Finset.sum_le_sum
          intro πS hπS
          apply Finset.sum_le_sum
          intro τ hτ
          exact hinner s πS τ
  have hsumBound :
      (∑ s ∈ S, P.memoryMass F J n s * promotionContextKernel A r theta i ctx O s t *
          P.memoryWeight r.v s) ≤
        D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              fixedContextColumnCost A r n theta i v u t
                (combinePermutations P πB πS.1) τ S := by
    have hReorder :
        (∑ s ∈ S,
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                    (combinePermutations P πB πS.1) τ v u B A_retr s) =
        ∑ πS : OmissionSmallFiber P J F.ell O,
          ∑ τ : P.Permutations (J + F.ell),
            ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
              ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                ∑ s ∈ S,
                  Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                    (combinePermutations P πB πS.1) τ v u B A_retr s := by
      calc
        _ = ∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ s ∈ S,
                ∑ τ : P.Permutations (J + F.ell),
                  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                        (combinePermutations P πB πS.1) τ v u B A_retr s :=
            Finset.sum_comm
        _ = ∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ τ : P.Permutations (J + F.ell),
                ∑ s ∈ S,
                  ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                        (combinePermutations P πB πS.1) τ v u B A_retr s := by
            apply Finset.sum_congr rfl
            intro πS hπS
            exact Finset.sum_comm
        _ = ∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ τ : P.Permutations (J + F.ell),
                ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ s ∈ S,
                    ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                        (combinePermutations P πB πS.1) τ v u B A_retr s := by
            apply Finset.sum_congr rfl
            intro πS hπS
            apply Finset.sum_congr rfl
            intro τ hτ
            exact Finset.sum_comm
        _ = ∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ τ : P.Permutations (J + F.ell),
                ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    ∑ s ∈ S,
                      Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                        (combinePermutations P πB πS.1) τ v u B A_retr s := by
            apply Finset.sum_congr rfl
            intro πS hπS
            apply Finset.sum_congr rfl
            intro τ hτ
            apply Finset.sum_congr rfl
            intro B hB
            exact Finset.sum_comm
    calc
      _ ≤ ∑ s ∈ S,
          D * H *
            ∑ πS : OmissionSmallFiber P J F.ell O,
              ∑ τ : P.Permutations (J + F.ell),
                ∑ B : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                  ∑ A_retr : (g : P.BigGroup) → Finset (Fin (J + F.ell)),
                    Erdos821.P3Edge.colSourceMapSum F r n theta i A t
                      (combinePermutations P πB πS.1) τ v u B A_retr s :=
            Finset.sum_le_sum (fun s hs => hpoint s)
      _ = D * H *
          ∑ πS : OmissionSmallFiber P J F.ell O,
            ∑ τ : P.Permutations (J + F.ell),
              fixedContextColumnCost A r n theta i v u t
                (combinePermutations P πB πS.1) τ S := by
          rw [← Finset.mul_sum]
          exact congrArg (fun z : ℝ => D * H * z) (by
            calc
              _ = _ := hReorder
              _ = _ := by simp [fixedContextColumnCost])
  have hfinal := omissionSmallFiberAverage_le P J F.ell O πB
    (fun π τ => fixedContextColumnCost A r n theta i v u t π τ S)
    (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
      P.memoryMass F J n t * P.memoryWeight r.v t *
      ((Erdos821.P3Edge.colRevConst F m) ^ Fintype.card P.BigGroup *
        (Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
          Fintype.card P.SmallGroup))
    (fun πS τ => by
      simpa using fixedContextColumnCost_le A r n theta i v u t
        (combinePermutations P ctx.2.2 πS.1) τ S
        hVlo hVhi htilted htiltedSum Cprom Csmall0 hCsmall0Pos hCprom hCsmall0)
  exact hsumBound.trans (by simpa [D, H] using hfinal)

set_option maxHeartbeats 1000000 in
/-- Store-only contexts have the complementary row bound by averaging the
target omission fiber after applying the literal fixed-pair row estimate. -/
theorem storeOnlyContextKernel_rowCost_le {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (ctx : EdgeTransferContext A)
    (O : OmissionChoices P (J + F.ell) F.ell)
    (s : P.MemoryState (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell)))
    (hVlo : ∀ g : P.Group, F.vMin ≤ P.V g)
    (hVpos : ∀ g : P.Group, 0 < P.V g)
    (htilted : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (htiltedSum : ∀ g : P.BigGroup, ∑ p : P.Prime g.val,
      tiltedMu F P n g.val p ≤ 2)
    (Cprom Csmall0 : ℝ) (hCsmall0Pos : 0 < Csmall0)
    (hCprom : ∀ Z' a : ℕ, a ≤ F.ell + m →
      (Z' : ℝ) ^ a * r.rho ^ (Z' - a) ≤ Cprom)
    (hCsmall0 : ∀ Y : ℕ, F.ell ≤ Y →
      (Y : ℝ) ^ F.ell * F.q ^ ((((Y - F.ell : ℕ)) : ℝ) / 2) ≤ Csmall0) :
    (∑ t ∈ S, storeOnlyContextKernel A r theta i ctx O s t * P.memoryWeight r.v t) ≤
      (Erdos821.P3Edge.patternSup A ctx.1 * (A.pattern ctx.1).auxMass ctx.2.1 *
        P.memoryWeight r.v s *
        ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
          (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
            Fintype.card P.SmallGroup)) /
        (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
  classical
  let v := ctx.1
  let u := ctx.2.1
  let πB := ctx.2.2
  let D : ℝ := Fintype.card (OmissionChoices P (J + F.ell) F.ell)
  let H : ℝ := edgeSymmetryFactor P (J + F.ell)
  have hfactor : 0 ≤ D * H := by
    dsimp [D, H]
    exact mul_nonneg (Nat.cast_nonneg _) (edgeSymmetryFactor_nonneg P _)
  have hMul (t : P.MemoryState (J + F.ell)) :
      (∑ π : P.Permutations (J + F.ell),
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ tr : TransferChoice s,
            if edgeChoiceValid A .dirty i s t
                (π, combinePermutations P πB τS.1, v, u, tr) ∧
                edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
              ‖edgeChoiceCoefficient A n r.rho theta i s t
                (π, combinePermutations P πB τS.1, v, u, tr)‖ else 0) *
          P.memoryWeight r.v t =
      ∑ π : P.Permutations (J + F.ell),
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ tr : TransferChoice s,
            if edgeChoiceValid A .dirty i s t
                (π, combinePermutations P πB τS.1, v, u, tr) ∧
                edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
              ‖edgeChoiceCoefficient A n r.rho theta i s t
                (π, combinePermutations P πB τS.1, v, u, tr)‖ * P.memoryWeight r.v t
            else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro τS hτS
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro tr htr
    by_cases hp : edgeChoiceValid A .dirty i s t
        (π, combinePermutations P πB τS.1, v, u, tr) ∧
        edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr)
    · simp [hp]
    · simp [hp]
  have hcombine :
      (∑ t ∈ S, storeOnlyContextKernel A r theta i ctx O s t *
          P.memoryWeight r.v t) =
        D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              ∑ tr : TransferChoice s,
                ∑ t ∈ S,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0 := by
    unfold storeOnlyContextKernel
    calc
      _ = ∑ t ∈ S,
          D * H *
            ((∑ π : P.Permutations (J + F.ell),
              ∑ τS : OmissionSmallFiber P J F.ell O,
                ∑ tr : TransferChoice s,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ else 0) *
              P.memoryWeight r.v t) := by
          apply Finset.sum_congr rfl
          intro t ht
          ring
      _ = D * H *
          ∑ t ∈ S,
            (∑ π : P.Permutations (J + F.ell),
              ∑ τS : OmissionSmallFiber P J F.ell O,
                ∑ tr : TransferChoice s,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ else 0) *
              P.memoryWeight r.v t := by
          rw [Finset.mul_sum]
      _ = D * H *
          ∑ t ∈ S,
            ∑ π : P.Permutations (J + F.ell),
              ∑ τS : OmissionSmallFiber P J F.ell O,
                ∑ tr : TransferChoice s,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro t ht
          exact hMul t
      _ = D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              ∑ tr : TransferChoice s,
                ∑ t ∈ S,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0 := by
          congr 1
          calc
            _ = ∑ π : P.Permutations (J + F.ell),
                  ∑ t ∈ S,
                    ∑ τS : OmissionSmallFiber P J F.ell O,
                      ∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (π, combinePermutations P πB τS.1, v, u, tr) ∧
                            edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                            P.memoryWeight r.v t else 0 := Finset.sum_comm
            _ = ∑ π : P.Permutations (J + F.ell),
                  ∑ τS : OmissionSmallFiber P J F.ell O,
                    ∑ t ∈ S,
                      ∑ tr : TransferChoice s,
                        if edgeChoiceValid A .dirty i s t
                            (π, combinePermutations P πB τS.1, v, u, tr) ∧
                            edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                            P.memoryWeight r.v t else 0 := by
                apply Finset.sum_congr rfl
                intro π hπ
                exact Finset.sum_comm
            _ = ∑ π : P.Permutations (J + F.ell),
                  ∑ τS : OmissionSmallFiber P J F.ell O,
                    ∑ tr : TransferChoice s,
                      ∑ t ∈ S,
                        if edgeChoiceValid A .dirty i s t
                            (π, combinePermutations P πB τS.1, v, u, tr) ∧
                            edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                          ‖edgeChoiceCoefficient A n r.rho theta i s t
                            (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                            P.memoryWeight r.v t else 0 := by
                apply Finset.sum_congr rfl
                intro π hπ
                apply Finset.sum_congr rfl
                intro τS hτS
                exact Finset.sum_comm
  have hpoint (π : P.Permutations (J + F.ell))
      (τS : OmissionSmallFiber P J F.ell O) :
      (∑ tr : TransferChoice s,
        ∑ t ∈ S,
          if edgeChoiceValid A .dirty i s t
              (π, combinePermutations P πB τS.1, v, u, tr) ∧
              edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
            ‖edgeChoiceCoefficient A n r.rho theta i s t
              (π, combinePermutations P πB τS.1, v, u, tr)‖ *
              P.memoryWeight r.v t else 0) ≤
        fixedContextRowCost A r n theta i v u s π
          (combinePermutations P πB τS.1) S := by
    unfold fixedContextRowCost
    apply Finset.sum_le_sum
    intro tr htr
    apply Finset.sum_le_sum
    intro t ht
    let c : EdgeChoice A s :=
      (π, combinePermutations P πB τS.1, v, u, tr)
    have hweight' : 0 ≤ P.memoryWeight r.v t :=
      (Erdos821.P3Edge.memoryWeight_pos r t).le
    by_cases hsOnly : edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c
    · have hall : edgeChoiceValid A .all i s t c := by
        rcases hsOnly.1 with ⟨hraw, _⟩
        exact ⟨hraw, by simp [transferModeAccept]⟩
      simp [c, hsOnly, hall]
    · simp only [c, if_neg hsOnly]
      by_cases hall : edgeChoiceValid A .all i s t c
      · have hall' : edgeChoiceValid A .all i s t
            (π, combinePermutations P πB τS.1, v, u, tr) := by
          simpa [c] using hall
        simpa [hall'] using mul_nonneg
          (norm_nonneg (edgeChoiceCoefficient A n r.rho theta i s t
            (π, combinePermutations P πB τS.1, v, u, tr))) hweight'
      · have hall' : ¬ edgeChoiceValid A .all i s t
            (π, combinePermutations P πB τS.1, v, u, tr) := by
          simpa [c] using hall
        simp [hall']
  have hcompare :
      D * H *
          (∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              ∑ tr : TransferChoice s,
                ∑ t ∈ S,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0) ≤
        D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              fixedContextRowCost A r n theta i v u s π
                (combinePermutations P πB τS.1) S := by
    apply mul_le_mul_of_nonneg_left _ hfactor
    apply Finset.sum_le_sum
    intro π hπ
    apply Finset.sum_le_sum
    intro τS hτS
    exact hpoint π τS
  have hfinal := omissionSmallFiberTargetAverage_le P J F.ell O πB
    (fun π τ => fixedContextRowCost A r n theta i v u s π τ S)
    (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
      P.memoryWeight r.v s *
      ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
        (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
          Fintype.card P.SmallGroup))
    (fun τS π => by
      simpa using fixedContextRowCost_le A r n theta i v u s π
        (combinePermutations P ctx.2.2 τS.1) S
        hVlo hVpos htilted htiltedSum Cprom Csmall0 hCsmall0Pos hCprom hCsmall0)
  calc
    _ = D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              ∑ tr : TransferChoice s,
                ∑ t ∈ S,
                  if edgeChoiceValid A .dirty i s t
                      (π, combinePermutations P πB τS.1, v, u, tr) ∧
                      edgeHasStoreOnly (π, combinePermutations P πB τS.1, v, u, tr) then
                    ‖edgeChoiceCoefficient A n r.rho theta i s t
                      (π, combinePermutations P πB τS.1, v, u, tr)‖ *
                      P.memoryWeight r.v t else 0 := hcombine
    _ ≤ D * H *
          ∑ π : P.Permutations (J + F.ell),
            ∑ τS : OmissionSmallFiber P J F.ell O,
              fixedContextRowCost A r n theta i v u s π
                (combinePermutations P πB τS.1) S := hcompare
    _ ≤ (Erdos821.P3Edge.patternSup A v * (A.pattern v).auxMass u *
          P.memoryWeight r.v s *
          ((Erdos821.P3Edge.bigGroupConst F r m Cprom) ^ Fintype.card P.BigGroup *
            (max 1 (max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * Csmall0)) ^
              Fintype.card P.SmallGroup)) /
          (Fintype.card (P.BigPermutations (J + F.ell)) : ℝ) := by
        exact hfinal

def promotionContextBadOmission {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (i : Fin n)
    (ctx : EdgeTransferContext A) (s : P.MemoryState (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell) : Prop :=
  ∃ idx : OldMemoryIndex s,
    PromotionWitness A (A.pattern ctx.1) (edgeForward i) ctx.2.1 s ctx.2.2 idx O

/-- A promotion context has no mass at an omission that has no old-particle
witness. -/
theorem promotionContextKernel_zero_of_not_bad {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (ctx : EdgeTransferContext A)
    (O : OmissionChoices P (J + F.ell) F.ell)
    (s t : P.MemoryState (J + F.ell))
    (hbad : ¬ promotionContextBadOmission A i ctx s O) :
    promotionContextKernel A r theta i ctx O s t = 0 := by
  classical
  unfold promotionContextKernel
  have hsum :
      (∑ πS : OmissionSmallFiber P J F.ell O,
        ∑ τ : P.Permutations (J + F.ell),
          ∑ tr : TransferChoice s,
            let c : EdgeChoice A s :=
              (combinePermutations P ctx.2.2 πS.1, τ, ctx.1, ctx.2.1, tr)
            if edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c then
              ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro πS hπS
    apply Finset.sum_eq_zero
    intro τ hτ
    apply Finset.sum_eq_zero
    intro tr htr
    let c : EdgeChoice A s :=
      (combinePermutations P ctx.2.2 πS.1, τ, ctx.1, ctx.2.1, tr)
    by_cases hp : edgeChoiceValid A .dirty i s t c ∧ edgeHasPromotion c
    · obtain ⟨idx, hW⟩ := promotionWitness_of_validPromotion A i s t c hp.1 hp.2
      have hO : omissionOfPerm P J F.ell c.1 = O := by
        dsimp [c]
        rw [omissionOfPerm_combinePermutations]
        exact πS.property
      have hBig : (fun g : P.BigGroup => c.1 g.val) = ctx.2.2 := by
        funext g
        dsimp [c]
        simp [combinePermutations, g.property]
      rw [hBig] at hW
      have hW' :
          PromotionWitness A (A.pattern ctx.1) (edgeForward i) ctx.2.1 s ctx.2.2 idx O := by
        simpa [c, combinePermutations, hO] using hW
      exact False.elim (hbad ⟨idx, hW'⟩)
    · simp [c, hp]
  rw [hsum]
  simp

def storeOnlyContextBadOmission {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (i : Fin n)
    (ctx : EdgeTransferContext A) (t : P.MemoryState (J + F.ell))
    (O : OmissionChoices P (J + F.ell) F.ell) : Prop :=
  EdgeStoreOmissionWitness A i (A.pattern ctx.1) ctx.2.1 t ctx.2.2 O

/-- A store-only context has no mass at a target omission that has no store
witness. -/
theorem storeOnlyContextKernel_zero_of_not_bad {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (ctx : EdgeTransferContext A)
    (O : OmissionChoices P (J + F.ell) F.ell)
    (s t : P.MemoryState (J + F.ell))
    (hbad : ¬ storeOnlyContextBadOmission A i ctx t O) :
    storeOnlyContextKernel A r theta i ctx O s t = 0 := by
  classical
  unfold storeOnlyContextKernel
  have hsum :
      (∑ π : P.Permutations (J + F.ell),
        ∑ τS : OmissionSmallFiber P J F.ell O,
          ∑ tr : TransferChoice s,
            let c : EdgeChoice A s :=
              (π, combinePermutations P ctx.2.2 τS.1, ctx.1, ctx.2.1, tr)
            if edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c then
              ‖edgeChoiceCoefficient A n r.rho theta i s t c‖ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro π hπ
    apply Finset.sum_eq_zero
    intro τS hτS
    apply Finset.sum_eq_zero
    intro tr htr
    let c : EdgeChoice A s :=
      (π, combinePermutations P ctx.2.2 τS.1, ctx.1, ctx.2.1, tr)
    by_cases hp : edgeChoiceValid A .dirty i s t c ∧ edgeHasStoreOnly c
    · have hO : omissionOfPerm P J F.ell c.2.1 = O := by
        dsimp [c]
        rw [omissionOfPerm_combinePermutations]
        exact τS.property
      have hBig : (fun g : P.BigGroup => c.2.1 g.val) = ctx.2.2 := by
        funext g
        dsimp [c]
        simp [combinePermutations, g.property]
      have hWitness : EdgeStoreOmissionWitness A i (A.pattern ctx.1)
          ctx.2.1 t ctx.2.2 O := by
        refine ⟨s, c, rfl, rfl, ?_, hp.1, ?_, ?_⟩
        · intro g
          exact congrFun hBig g
        · rcases hp.2 with ⟨hstore, _⟩
          simpa [edgeHasStore] using hstore
        · exact hO.symm
      exact False.elim (hbad hWitness)
    · simp [c, hp]
  rw [hsum]
  simp

/-- The cutoff-size promotion omission bound in a fixed edge context. -/
theorem promotionContextBadOmission_card_le_eventually (F : FixedData) (C₂ : ℝ)
    (J m : ℕ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, 0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      ∀ n : ℕ, ∀ i : Fin n, ∀ ctx : EdgeTransferContext A,
        ∀ s : P.MemoryState (J + F.ell), P.memorySize s ≤ memoryCutoff x →
        (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
          promotionContextBadOmission A i ctx s O)).card ≤ memoryCutoff x := by
  obtain ⟨x₀, hbound⟩ := promotionWitness_bad_card_le_eventually F C₂ J m
  refine ⟨x₀, ?_⟩
  intro x hx P hAdm A hk hK n i ctx s hs
  simpa [promotionContextBadOmission] using hbound x hx P hAdm A hk hK
    (A.pattern ctx.1) (edgeForward i) ctx.2.1 s ctx.2.2 hs

/-- The cutoff-size store omission bound in a fixed target context. -/
theorem storeOnlyContextBadOmission_card_le_eventually (F : FixedData)
    (C₂ : ℝ) (J m : ℕ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ P : PrimeGroups, P.Admissible F x →
      ∀ A : Model F P J m, 0 < |A.k| → (|A.k| : ℝ) ≤ (L x) ^ C₂ →
      ∀ n : ℕ, ∀ i : Fin n, ∀ ctx : EdgeTransferContext A,
        ∀ t : P.MemoryState (J + F.ell), P.memorySize t ≤ memoryCutoff x →
        (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
          storeOnlyContextBadOmission A i ctx t O)).card ≤ memoryCutoff x := by
  obtain ⟨x₀, hbound⟩ := edgeStoreBadOmission_card_le_eventually F C₂ J m
  refine ⟨x₀, ?_⟩
  intro x hx P hAdm A hk hK n i ctx t ht
  change (Finset.univ.filter (fun O : OmissionChoices P (J + F.ell) F.ell =>
    EdgeStoreOmissionWitness A i (A.pattern ctx.1) ctx.2.1 t ctx.2.2 O)).card ≤
      memoryCutoff x
  exact hbound x hx P hAdm A hk hK n i (A.pattern ctx.1) ctx.2.1 t ctx.2.2 ht

theorem promotionOmissionAverageKernel_context_sum {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (s t : P.MemoryState (J + F.ell)) :
    promotionOmissionAverageKernel A r.rho theta i s t =
      ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ ctx : EdgeTransferContext A,
          ∑ O : OmissionChoices P (J + F.ell) F.ell,
            promotionContextKernel A r theta i ctx O s t := by
  classical
  unfold promotionOmissionAverageKernel
  calc
    _ = ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          ∑ ctx : EdgeTransferContext A,
            promotionContextKernel A r theta i ctx O s t := by
      congr 1
      apply Finset.sum_congr rfl
      intro O hO
      exact (promotionContextKernel_sum A r theta i O s t).symm
    _ = _ := by
      congr 1
      exact Finset.sum_comm

theorem storeOnlyOmissionAverageKernel_context_sum {F : FixedData} {P : PrimeGroups}
    {J m n : ℕ} (A : Model F P J m) (r : MemoryParameters F)
    (theta : ℝ) (i : Fin n) (s t : P.MemoryState (J + F.ell)) :
    storeOnlyOmissionAverageKernel A r.rho theta i s t =
      ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ ctx : EdgeTransferContext A,
          ∑ O : OmissionChoices P (J + F.ell) F.ell,
            storeOnlyContextKernel A r theta i ctx O s t := by
  classical
  unfold storeOnlyOmissionAverageKernel
  calc
    _ = ((Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ)⁻¹) *
        ∑ O : OmissionChoices P (J + F.ell) F.ell,
          ∑ ctx : EdgeTransferContext A,
            storeOnlyContextKernel A r theta i ctx O s t := by
      congr 1
      apply Finset.sum_congr rfl
      intro O hO
      exact (storeOnlyContextKernel_sum A r theta i O s t).symm
    _ = _ := by
      congr 1
      exact Finset.sum_comm

theorem normBound_sum_projected_contexts_sparseRows
    {α Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (mass w : α → ℝ) (keep : α → Prop)
    (K : κ → Ω → α → α → ℝ) (bad : κ → α → Ω → Prop)
    (R C : κ → ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ j ω a b, 0 ≤ K j ω a b)
    (hR : ∀ j, 0 ≤ R j) (hC : ∀ j, 0 ≤ C j)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ j a ω t, ∑ b ∈ t, K j ω a b * w b ≤ R j * w a)
    (hcol : ∀ j b ω s, ∑ a ∈ s, mass a * K j ω a b * w a ≤ C j * mass b * w b)
    (hbad : ∀ j a, (Finset.univ.filter (fun ω => keep a ∧ bad j a ω)).card ≤ B)
    (hzero : ∀ j a ω, ¬ (keep a ∧ bad j a ω) → ∀ b, K j ω a b = 0) :
    NormBound mass
      (fun a b => ∑ j,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω,
          (if keep a ∧ keep b then K j ω a b else 0) : ℝ) : ℂ))
      (∑ j, Real.sqrt ((R j * ((B : ℝ) / (Fintype.card Ω : ℝ))) * C j)) := by
  classical
  let K' : κ → Ω → α → α → ℝ := fun j ω a b =>
    if keep a ∧ keep b then K j ω a b else 0
  let bad' : κ → α → Ω → Prop := fun j a ω => keep a ∧ bad j a ω
  letI : ∀ j a, DecidablePred (bad' j a) := fun j a ω => by
    change Decidable (keep a ∧ bad j a ω)
    infer_instance
  have hK' : ∀ j ω a b, 0 ≤ K' j ω a b := by
    intro j ω a b
    by_cases h : keep a ∧ keep b <;> simp [K', h, hK]
  have hrow' : ∀ j a ω t, ∑ b ∈ t, K' j ω a b * w b ≤ R j * w a := by
    intro j a ω t
    by_cases ha : keep a
    · simpa [K', ha, Finset.sum_filter] using hrow j a ω (t.filter keep)
    · simpa [K', ha] using mul_nonneg (hR j) (hw a).le
  have hcol' : ∀ j b ω s,
      ∑ a ∈ s, mass a * K' j ω a b * w a ≤ C j * mass b * w b := by
    intro j b ω s
    by_cases hb : keep b
    · simpa [K', hb, Finset.sum_filter] using hcol j b ω (s.filter keep)
    · simpa [K', hb] using mul_nonneg (mul_nonneg (hC j) (hm b)) (hw b).le
  have hbadConverted : ∀ j a,
      (@Finset.filter Ω (fun ω => bad' j a ω)
        (fun ω => Classical.propDecidable (bad' j a ω)) Finset.univ).card ≤ B := by
    intro j a
    have hf : (@Finset.filter Ω (fun ω => bad' j a ω)
        (fun ω => Classical.propDecidable (bad' j a ω)) Finset.univ) =
        Finset.univ.filter (fun ω => keep a ∧ bad j a ω) := by
      ext ω
      simp [bad']
    rw [hf]
    exact hbad j a
  have hzero' : ∀ j a ω, ¬ bad' j a ω → ∀ b, K' j ω a b = 0 := by
    intro j a ω hnot b
    by_cases ha : keep a
    · have hnotOrig : ¬ (keep a ∧ bad j a ω) := by
        simpa [bad'] using hnot
      by_cases hb : keep b
      · simp [K', ha, hb, hzero j a ω hnotOrig b]
      · simp [K', ha, hb]
    · simp [K', ha]
  simpa [K'] using normBound_sum_contexts_sparseRows mass w K' bad' R C B
    hm hw hK' hR hC hD hrow' hcol' hbadConverted hzero'

theorem normBound_sum_projected_contexts_sparseCols
    {α Ω κ : Type*} [Fintype Ω] [Fintype κ]
    (mass w : α → ℝ) (keep : α → Prop)
    (K : κ → Ω → α → α → ℝ) (bad : κ → α → Ω → Prop)
    (R C : κ → ℝ) (B : ℕ)
    (hm : ∀ a, 0 ≤ mass a) (hw : ∀ a, 0 < w a)
    (hK : ∀ j ω a b, 0 ≤ K j ω a b)
    (hR : ∀ j, 0 ≤ R j) (hC : ∀ j, 0 ≤ C j)
    (hD : 0 < (Fintype.card Ω : ℝ))
    (hrow : ∀ j a ω t, ∑ b ∈ t, K j ω a b * w b ≤ R j * w a)
    (hcol : ∀ j b ω s, ∑ a ∈ s, mass a * K j ω a b * w a ≤ C j * mass b * w b)
    (hbad : ∀ j b, (Finset.univ.filter (fun ω => keep b ∧ bad j b ω)).card ≤ B)
    (hzero : ∀ j b ω, ¬ (keep b ∧ bad j b ω) → ∀ a, K j ω a b = 0) :
    NormBound mass
      (fun a b => ∑ j,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ ω,
          (if keep a ∧ keep b then K j ω a b else 0) : ℝ) : ℂ))
      (∑ j, Real.sqrt (R j * (C j * ((B : ℝ) / (Fintype.card Ω : ℝ))))) := by
  classical
  let K' : κ → Ω → α → α → ℝ := fun j ω a b =>
    if keep a ∧ keep b then K j ω a b else 0
  let bad' : κ → α → Ω → Prop := fun j b ω => keep b ∧ bad j b ω
  letI : ∀ j b, DecidablePred (bad' j b) := fun j b ω => by
    change Decidable (keep b ∧ bad j b ω)
    infer_instance
  have hK' : ∀ j ω a b, 0 ≤ K' j ω a b := by
    intro j ω a b
    by_cases h : keep a ∧ keep b <;> simp [K', h, hK]
  have hrow' : ∀ j a ω t, ∑ b ∈ t, K' j ω a b * w b ≤ R j * w a := by
    intro j a ω t
    by_cases ha : keep a
    · simpa [K', ha, Finset.sum_filter] using hrow j a ω (t.filter keep)
    · simpa [K', ha] using mul_nonneg (hR j) (hw a).le
  have hcol' : ∀ j b ω s,
      ∑ a ∈ s, mass a * K' j ω a b * w a ≤ C j * mass b * w b := by
    intro j b ω s
    by_cases hb : keep b
    · simpa [K', hb, Finset.sum_filter] using hcol j b ω (s.filter keep)
    · simpa [K', hb] using mul_nonneg (mul_nonneg (hC j) (hm b)) (hw b).le
  have hbadConverted : ∀ j b,
      (@Finset.filter Ω (fun ω => bad' j b ω)
        (fun ω => Classical.propDecidable (bad' j b ω)) Finset.univ).card ≤ B := by
    intro j b
    have hf : (@Finset.filter Ω (fun ω => bad' j b ω)
        (fun ω => Classical.propDecidable (bad' j b ω)) Finset.univ) =
        Finset.univ.filter (fun ω => keep b ∧ bad j b ω) := by
      ext ω
      simp [bad']
    rw [hf]
    exact hbad j b
  have hzero' : ∀ j b ω, ¬ bad' j b ω → ∀ a, K' j ω a b = 0 := by
    intro j b ω hnot a
    by_cases hb : keep b
    · have hnotOrig : ¬ (keep b ∧ bad j b ω) := by
        simpa [bad'] using hnot
      by_cases ha : keep a
      · simp [K', ha, hb, hzero j b ω hnotOrig a]
      · simp [K', ha, hb]
    · simp [K', hb]
  simpa [K'] using normBound_sum_contexts_sparseCols mass w K' bad' R C B
    hm hw hK' hR hC hD hrow' hcol' hbadConverted hzero'

theorem promotionOmissionAverage_projectedNormBound
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (keep : P.MemoryState (J + F.ell) → Prop)
    (mass w : P.MemoryState (J + F.ell) → ℝ)
    (R C : EdgeTransferContext A → ℝ) (B : ℕ)
    (hm : ∀ s, 0 ≤ mass s) (hw : ∀ s, 0 < w s)
    (hD : 0 < (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))
    (hK : ∀ ctx O s t, 0 ≤ promotionContextKernel A r theta i ctx O s t)
    (hR : ∀ ctx, 0 ≤ R ctx) (hC : ∀ ctx, 0 ≤ C ctx)
    (hrow : ∀ ctx O s T,
      ∑ t ∈ T, promotionContextKernel A r theta i ctx O s t * w t ≤ R ctx * w s)
    (hcol : ∀ ctx O t S,
      ∑ s ∈ S, mass s * promotionContextKernel A r theta i ctx O s t * w s ≤
        C ctx * mass t * w t)
    (hbad : ∀ ctx s,
      (Finset.univ.filter (fun O => keep s ∧ promotionContextBadOmission A i ctx s O)).card ≤ B)
    (hzero : ∀ ctx s O, ¬ (keep s ∧ promotionContextBadOmission A i ctx s O) →
      ∀ t, promotionContextKernel A r theta i ctx O s t = 0) :
    NormBound mass
      (projectKernel keep (fun s t =>
        (promotionOmissionAverageKernel A r.rho theta i s t : ℂ)))
      (∑ ctx : EdgeTransferContext A,
        Real.sqrt ((R ctx * ((B : ℝ) /
          (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))) * C ctx)) := by
  classical
  let Ω := OmissionChoices P (J + F.ell) F.ell
  let K : EdgeTransferContext A → Ω → P.MemoryState (J + F.ell) →
      P.MemoryState (J + F.ell) → ℝ := fun ctx O s t =>
    promotionContextKernel A r theta i ctx O s t
  let bad : EdgeTransferContext A → P.MemoryState (J + F.ell) → Ω → Prop :=
    fun ctx s O => promotionContextBadOmission A i ctx s O
  have hK' : ∀ ctx O s t, 0 ≤ K ctx O s t := by
    intro ctx O s t
    exact hK ctx O s t
  have hrow' : ∀ ctx s O T, ∑ t ∈ T, K ctx O s t * w t ≤ R ctx * w s := by
    intro ctx s O T
    simpa [K] using hrow ctx O s T
  have hcol' : ∀ ctx t O S,
      ∑ s ∈ S, mass s * K ctx O s t * w s ≤ C ctx * mass t * w t := by
    intro ctx t O S
    simpa [K] using hcol ctx O t S
  have hbad' : ∀ ctx s,
      (Finset.univ.filter (fun O : Ω => keep s ∧ bad ctx s O)).card ≤ B := by
    intro ctx s
    simpa [bad] using hbad ctx s
  have hzero' : ∀ ctx s O, ¬ (keep s ∧ bad ctx s O) →
      ∀ t, K ctx O s t = 0 := by
    intro ctx s O hnot t
    simpa [K, bad] using hzero ctx s O (by simpa [bad] using hnot) t
  have hbase := normBound_sum_projected_contexts_sparseRows mass w keep K bad R C B
    hm hw hK' hR hC hD hrow' hcol' hbad' hzero'
  have hEq (s t : P.MemoryState (J + F.ell)) :
      projectKernel keep (fun s t =>
        (promotionOmissionAverageKernel A r.rho theta i s t : ℂ)) s t =
      ∑ ctx : EdgeTransferContext A,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ O : Ω,
          (if keep s ∧ keep t then K ctx O s t else 0) : ℝ) : ℂ) := by
    by_cases hs : keep s <;> by_cases ht : keep t
    · simp only [projectKernel, hs, ht, and_self, ite_true]
      rw [promotionOmissionAverageKernel_context_sum]
      simp [K, Ω, Finset.mul_sum]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
  intro S T f g
  simpa only [hEq] using hbase S T f g

theorem storeOnlyOmissionAverage_projectedNormBound
    {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m) (r : MemoryParameters F) (theta : ℝ) (i : Fin n)
    (keep : P.MemoryState (J + F.ell) → Prop)
    (mass w : P.MemoryState (J + F.ell) → ℝ)
    (R C : EdgeTransferContext A → ℝ) (B : ℕ)
    (hm : ∀ s, 0 ≤ mass s) (hw : ∀ s, 0 < w s)
    (hD : 0 < (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))
    (hK : ∀ ctx O s t, 0 ≤ storeOnlyContextKernel A r theta i ctx O s t)
    (hR : ∀ ctx, 0 ≤ R ctx) (hC : ∀ ctx, 0 ≤ C ctx)
    (hrow : ∀ ctx O s T,
      ∑ t ∈ T, storeOnlyContextKernel A r theta i ctx O s t * w t ≤ R ctx * w s)
    (hcol : ∀ ctx O t S,
      ∑ s ∈ S, mass s * storeOnlyContextKernel A r theta i ctx O s t * w s ≤
        C ctx * mass t * w t)
    (hbad : ∀ ctx t,
      (Finset.univ.filter (fun O => keep t ∧ storeOnlyContextBadOmission A i ctx t O)).card ≤ B)
    (hzero : ∀ ctx t O, ¬ (keep t ∧ storeOnlyContextBadOmission A i ctx t O) →
      ∀ s, storeOnlyContextKernel A r theta i ctx O s t = 0) :
    NormBound mass
      (projectKernel keep (fun s t =>
        (storeOnlyOmissionAverageKernel A r.rho theta i s t : ℂ)))
      (∑ ctx : EdgeTransferContext A,
        Real.sqrt (R ctx * (C ctx * ((B : ℝ) /
          (Fintype.card (OmissionChoices P (J + F.ell) F.ell) : ℝ))))) := by
  classical
  let Ω := OmissionChoices P (J + F.ell) F.ell
  let K : EdgeTransferContext A → Ω → P.MemoryState (J + F.ell) →
      P.MemoryState (J + F.ell) → ℝ := fun ctx O s t =>
    storeOnlyContextKernel A r theta i ctx O s t
  let bad : EdgeTransferContext A → P.MemoryState (J + F.ell) → Ω → Prop :=
    fun ctx t O => storeOnlyContextBadOmission A i ctx t O
  have hK' : ∀ ctx O s t, 0 ≤ K ctx O s t := by
    intro ctx O s t
    exact hK ctx O s t
  have hrow' : ∀ ctx s O T, ∑ t ∈ T, K ctx O s t * w t ≤ R ctx * w s := by
    intro ctx s O T
    simpa [K] using hrow ctx O s T
  have hcol' : ∀ ctx t O S,
      ∑ s ∈ S, mass s * K ctx O s t * w s ≤ C ctx * mass t * w t := by
    intro ctx t O S
    simpa [K] using hcol ctx O t S
  have hbad' : ∀ ctx t,
      (Finset.univ.filter (fun O : Ω => keep t ∧ bad ctx t O)).card ≤ B := by
    intro ctx t
    simpa [bad] using hbad ctx t
  have hzero' : ∀ ctx t O, ¬ (keep t ∧ bad ctx t O) →
      ∀ s, K ctx O s t = 0 := by
    intro ctx t O hnot s
    simpa [K, bad] using hzero ctx t O (by simpa [bad] using hnot) s
  have hbase := normBound_sum_projected_contexts_sparseCols mass w keep K bad R C B
    hm hw hK' hR hC hD hrow' hcol' hbad' hzero'
  have hEq (s t : P.MemoryState (J + F.ell)) :
      projectKernel keep (fun s t =>
        (storeOnlyOmissionAverageKernel A r.rho theta i s t : ℂ)) s t =
      ∑ ctx : EdgeTransferContext A,
        (((Fintype.card Ω : ℝ)⁻¹ * ∑ O : Ω,
          (if keep s ∧ keep t then K ctx O s t else 0) : ℝ) : ℂ) := by
    by_cases hs : keep s <;> by_cases ht : keep t
    · simp only [projectKernel, hs, ht, and_self, ite_true]
      rw [storeOnlyOmissionAverageKernel_context_sum]
      simp [K, Ω, Finset.mul_sum]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
    · simp [projectKernel, hs, ht, K]
  intro S T f g
  simpa only [hEq] using hbase S T f g

end Erdos821.P3Rare
