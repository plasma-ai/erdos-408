import Erdos821.Blueprint.Classical
import Mathlib.NumberTheory.MulChar.Lemmas

set_option autoImplicit false

open Filter

namespace Erdos821.P4Cell

open Blueprint Blueprint.Analytic

noncomputable section

/-- §3 ideal-character-cell, with harmonic SW supplied as a hypothesis.
Use the common lcm modulus of two distinct primitive characters, whose
quotient is nonprincipal. Condition on all but one selected big group;
the log cell and the prime group restrict that label to an interval.
Apply HarmonicCharacters, divide by the group mass, and average the other
labels. Precision is absolute and uniform in the cell width/location.
Use no owned blueprint placeholder. -/
def CharacterCellTask : Prop :=
  HarmonicCharacters → ∀ (P : Geometry) (m : ℕ) (qexp D : ℝ),
    0 < qexp → 0 < D → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x in atTop,
      ∀ G : PrimeGroups, Admissible P x G → ∀ k, bigSlots G k m →
      ∀ (Q : ℕ) (h : ℝ) (j : ℤ) (χ ψ : CharacterIndex Q),
        (Q : ℝ) ≤ L x ^ qexp → 0 < h → χ ∈ primitiveCharacters Q →
        ψ ∈ primitiveCharacters Q → χ ≠ ψ →
        ‖expect G k (fun z => if cell h (product G k z) = j then
          star (charValue χ (product G k z)) * charValue ψ (product G k z) else 0)‖ ≤
          K * L x ^ (-D)

private def level {Q : ℕ} (χ : CharacterIndex Q) : ℕ := χ.1.val + 1

/-- The quotient character after both characters have been lifted to their common level. -/
private noncomputable def cellQuotient {Q : ℕ} (χ ψ : CharacterIndex Q) :
    DirichletCharacter ℂ (Nat.lcm (level χ) (level ψ)) :=
  (DirichletCharacter.changeLevel (Nat.dvd_lcm_left _ _) χ.2)⁻¹ *
    DirichletCharacter.changeLevel (Nat.dvd_lcm_right _ _) ψ.2

private lemma primitive_of_mem {Q : ℕ} {χ : CharacterIndex Q}
    (hχ : χ ∈ primitiveCharacters Q) : χ.2.IsPrimitive := by
  classical
  exact (Finset.mem_filter.mp hχ).2

private lemma cellQuotient_ne_one {Q : ℕ} {χ ψ : CharacterIndex Q}
    (hχ : χ ∈ primitiveCharacters Q) (hψ : ψ ∈ primitiveCharacters Q)
    (hne : χ ≠ ψ) : cellQuotient χ ψ ≠ 1 := by
  intro hq
  let n := level χ
  let m := level ψ
  have hn : 0 < n := Nat.succ_pos _
  have hm : 0 < m := Nat.succ_pos _
  have hL : 0 < Nat.lcm n m := Nat.lcm_pos hn hm
  letI : NeZero (Nat.lcm n m) := ⟨ne_of_gt hL⟩
  have hEq :
      DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ.2 =
        DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ.2 := by
    let A := DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ.2
    let B := DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ.2
    have hq' : A⁻¹ * B = 1 := by
      change A⁻¹ * B = 1 at hq
      exact hq
    calc
      A = A * 1 := by simp
      _ = A * (A⁻¹ * B) := by rw [← hq']
      _ = B := by group
  have hCond := congrArg DirichletCharacter.conductor hEq
  have hlevels : n = m := by
    have hnprim : χ.2.conductor = n := primitive_of_mem hχ
    have hmprim : ψ.2.conductor = m := primitive_of_mem hψ
    have hCondχ :
        (DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ.2).conductor = χ.2.conductor :=
      χ.2.conductor_changeLevel (Nat.dvd_lcm_left n m)
    have hCondψ :
        (DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ.2).conductor = ψ.2.conductor :=
      ψ.2.conductor_changeLevel (Nat.dvd_lcm_right n m)
    simpa [hCondχ, hCondψ, hnprim, hmprim] using hCond
  apply hne
  cases χ with
  | mk a c =>
    cases ψ with
    | mk b d =>
      have hab : a.val = b.val := by
        simpa [n, m, level] using congrArg (fun q : ℕ => q - 1) hlevels
      have hab' : a = b := Fin.ext hab
      subst b
      have hcd : c = d := by
        letI : NeZero (Nat.lcm (a.val + 1) (a.val + 1)) :=
          ⟨Nat.ne_of_gt (Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _))⟩
        have hEq' :
            DirichletCharacter.changeLevel
                (Nat.dvd_lcm_left (a.val + 1) (a.val + 1)) c =
              DirichletCharacter.changeLevel
                (Nat.dvd_lcm_left (a.val + 1) (a.val + 1)) d := by
          exact hEq
        exact DirichletCharacter.changeLevel_injective
          (Nat.dvd_lcm_left (a.val + 1) (a.val + 1)) hEq'
      subst d
      rfl

private lemma cellQuotient_eval {Q : ℕ} (χ ψ : CharacterIndex Q) (a : ℕ) :
    cellQuotient χ ψ (a : ZMod (Nat.lcm (level χ) (level ψ))) =
      star (charValue χ a) * charValue ψ a := by
  classical
  let n := level χ
  let m := level ψ
  let r := Nat.lcm n m
  letI : NeZero r := ⟨Nat.ne_of_gt (Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _))⟩
  by_cases ha : IsUnit (a : ZMod r)
  · have hac : a.Coprime r := (ZMod.isUnit_iff_coprime a r).mp ha
    have hχ :
        DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ.2 (a : ZMod r) =
          χ.2 (a : ZMod n) := by
      have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.2
        (Nat.dvd_lcm_left n m) ha.unit
      calc
        _ = DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ.2
            (ha.unit : ZMod r) := by rw [ha.unit_spec]
        _ = χ.2 (ZMod.cast (ha.unit : ZMod r)) := h
        _ = χ.2 (a : ZMod n) := by
          congr 1
          calc
            ZMod.cast (ha.unit : ZMod r) = ZMod.cast (a : ZMod r) := by
              rw [ha.unit_spec]
            _ = (a : ZMod n) := ZMod.cast_natCast (Nat.dvd_lcm_left n m) a
    have hψ :
        DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ.2 (a : ZMod r) =
          ψ.2 (a : ZMod m) := by
      have h := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ.2
        (Nat.dvd_lcm_right n m) ha.unit
      calc
        _ = DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ.2
            (ha.unit : ZMod r) := by rw [ha.unit_spec]
        _ = ψ.2 (ZMod.cast (ha.unit : ZMod r)) := h
        _ = ψ.2 (a : ZMod m) := by
          congr 1
          calc
            ZMod.cast (ha.unit : ZMod r) = ZMod.cast (a : ZMod r) := by
              rw [ha.unit_spec]
            _ = (a : ZMod m) := ZMod.cast_natCast (Nat.dvd_lcm_right n m) a
    change
      ((DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ.2)⁻¹ *
        DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ.2)
          (a : ZMod r) = _
    rw [MulChar.mul_apply, ← MulChar.star_apply']
    rw [hχ, hψ]
    rfl
  · have hnot : ¬ (a.Coprime n ∧ a.Coprime m) := by
      intro h
      have hprod : a.Coprime (n * m) := Nat.Coprime.mul_right h.1 h.2
      exact ha ((ZMod.isUnit_iff_coprime a r).2 <|
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul n m) hprod)
    rcases not_and_or.mp hnot with hn | hm
    · have hχ : ¬ IsUnit (a : ZMod n) := by
        rwa [ZMod.isUnit_iff_coprime]
      have hq : cellQuotient χ ψ (a : ZMod r) = 0 := by
        exact MulChar.map_nonunit (cellQuotient χ ψ) ha
      have hv : charValue χ a = 0 := by
        exact MulChar.map_nonunit χ.2 hχ
      simp [hq, hv]
    · have hψ : ¬ IsUnit (a : ZMod m) := by
        rwa [ZMod.isUnit_iff_coprime]
      have hq : cellQuotient χ ψ (a : ZMod r) = 0 := by
        exact MulChar.map_nonunit (cellQuotient χ ψ) ha
      have hv : charValue ψ a = 0 := by
        exact MulChar.map_nonunit ψ.2 hψ
      simp [hq, hv]

private abbrev Coordinate (G : PrimeGroups) (k : Fin G.size → ℕ) :=
  Σ g, Fin (k g)

private def coordinateEquiv (G : PrimeGroups) (k : Fin G.size → ℕ) :
    Tuple G k ≃ (∀ i : Coordinate G k, Label G i.1) :=
  (Equiv.piCurry (fun g (j : Fin (k g)) => Label G g)).symm

private def splitCoordinate (G : PrimeGroups) (k : Fin G.size → ℕ)
    (i₀ : Coordinate G k) :
    Tuple G k ≃ Label G i₀.1 ×
      (∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1) :=
  (coordinateEquiv G k).trans
    (Equiv.piSplitAt i₀ (fun i : Coordinate G k => Label G i.1))

private def restWeight {G : PrimeGroups} {k : Fin G.size → ℕ}
    (i₀ : Coordinate G k) (y : ∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1) : ℝ :=
  ∏ i, mu G i.1.1 (y i).val

private def restProduct {G : PrimeGroups} {k : Fin G.size → ℕ}
    (i₀ : Coordinate G k) (y : ∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1) : ℕ :=
  ∏ i, (y i).val

private lemma product_coordinate {G : PrimeGroups} {k : Fin G.size → ℕ}
    (z : Tuple G k) :
    product G k z = ∏ i : Coordinate G k, (coordinateEquiv G k z i).val := by
  classical
  simp [product, coordinateEquiv, Finset.prod_sigma']
  rfl

private lemma tupleWeight_coordinate {G : PrimeGroups} {k : Fin G.size → ℕ}
    (z : Tuple G k) :
    tupleWeight G k z = ∏ i : Coordinate G k,
      mu G i.1 (coordinateEquiv G k z i).val := by
  classical
  simp [tupleWeight, coordinateEquiv, Finset.prod_sigma']
  rfl

private lemma tupleWeight_split {G : PrimeGroups} {k : Fin G.size → ℕ}
    (i₀ : Coordinate G k) (p : Label G i₀.1)
    (y : ∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1) :
    tupleWeight G k ((splitCoordinate G k i₀).symm (p, y)) =
      mu G i₀.1 p.val * restWeight i₀ y := by
  classical
  rw [tupleWeight_coordinate]
  change
    (∏ i : Coordinate G k,
      mu G i.1 (((Equiv.piSplitAt i₀ (fun i : Coordinate G k => Label G i.1)).symm
        (p, y) i).val) = _)
  let f : Coordinate G k → ℝ := fun i =>
    mu G i.1 (((Equiv.piSplitAt i₀ (fun i : Coordinate G k => Label G i.1)).symm
      (p, y) i).val)
  calc
    ∏ i, f i = f i₀ * ∏ i ∈ Finset.univ.erase i₀, f i := by
      symm
      exact Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)
    _ = mu G i₀.1 p.val * restWeight i₀ y := by
      have hfirst : f i₀ = mu G i₀.1 p.val := by simp [f, Equiv.piSplitAt]
      have hrest : ∏ i ∈ Finset.univ.erase i₀, f i = restWeight i₀ y := by
        rw [Finset.prod_subtype (s := Finset.univ.erase i₀)
          (p := fun i : Coordinate G k => i ≠ i₀) (F := inferInstance)
          (by intro i; simp)]
        apply Finset.prod_congr rfl
        intro i hi
        simp [f, restWeight, Equiv.piSplitAt, i.property]
      rw [hfirst, hrest]

private lemma product_split {G : PrimeGroups} {k : Fin G.size → ℕ}
    (i₀ : Coordinate G k) (p : Label G i₀.1)
    (y : ∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1) :
    product G k ((splitCoordinate G k i₀).symm (p, y)) =
      restProduct i₀ y * p.val := by
  classical
  rw [product_coordinate]
  change
    (∏ i : Coordinate G k,
      (((Equiv.piSplitAt i₀ (fun i : Coordinate G k => Label G i.1)).symm
        (p, y) i).val) = _)
  let f : Coordinate G k → ℕ := fun i =>
    (((Equiv.piSplitAt i₀ (fun i : Coordinate G k => Label G i.1)).symm
      (p, y) i).val)
  calc
    ∏ i, f i = f i₀ * ∏ i ∈ Finset.univ.erase i₀, f i := by
      symm
      exact Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)
    _ = restProduct i₀ y * p.val := by
      have hfirst : f i₀ = p.val := by simp [f, Equiv.piSplitAt]
      have hrest : ∏ i ∈ Finset.univ.erase i₀, f i = restProduct i₀ y := by
        rw [Finset.prod_subtype (s := Finset.univ.erase i₀)
          (p := fun i : Coordinate G k => i ≠ i₀) (F := inferInstance)
          (by intro i; simp)]
        apply Finset.prod_congr rfl
        intro i hi
        simp [f, restProduct, Equiv.piSplitAt, i.property]
      rw [hfirst, hrest, Nat.mul_comm]

private lemma labelWeight_sum {G : PrimeGroups} (g : Fin G.size)
    (hmass : 0 < mass G g) :
    ∑ p : Label G g, mu G g p.val = 1 := by
  classical
  have hrecip : ∑ p : Label G g, (p.val : ℝ)⁻¹ = mass G g := by
    simpa [mass, Label] using
      (Finset.sum_attach (G.primes g) fun p : ℕ => (p : ℝ)⁻¹)
  have hm0 : mass G g ≠ 0 := ne_of_gt hmass
  calc
    ∑ p : Label G g, mu G g p.val =
        ∑ p : Label G g, (mass G g)⁻¹ * (p.val : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := G.prime g p.val p.property
      have hp0 : (p.val : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
      simp [mu, div_eq_mul_inv]
      field_simp
    _ = (mass G g)⁻¹ * ∑ p : Label G g, (p.val : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ = 1 := by rw [hrecip]; field_simp

set_option maxHeartbeats 1000000 in
private lemma groupWeight_sum_one {G : PrimeGroups} {k : Fin G.size → ℕ}
    (g : Fin G.size) (hmass : 0 < mass G g) :
    ∑ f : Fin (k g) → Label G g, ∏ j, mu G g (f j).val = 1 := by
  classical
  calc
    (∑ f : Fin (k g) → Label G g, ∏ j, mu G g (f j).val) =
      (∑ p : Label G g, mu G g p.val) ^ k g := by
        exact (Fintype.sum_pow (fun p : Label G g => mu G g p.val) (k g)).symm
    _ = 1 := by rw [labelWeight_sum g hmass]; simp

set_option maxHeartbeats 1000000 in
private lemma tupleWeight_sum_one {G : PrimeGroups} {k : Fin G.size → ℕ}
    (hmass : ∀ g, 0 < mass G g) :
    ∑ z : Tuple G k, tupleWeight G k z = 1 := by
  classical
  calc
    (∑ z : Tuple G k, tupleWeight G k z) =
        ∏ g : Fin G.size,
          ∑ f : Fin (k g) → Label G g, ∏ j, mu G g (f j).val := by
      unfold tupleWeight
      exact (Fintype.prod_sum
        (κ := fun g : Fin G.size => Fin (k g) → Label G g)
        (f := fun g f => ∏ j, mu G g (f j).val)).symm
    _ = 1 := by
      calc
        _ = ∏ g : Fin G.size, (1 : ℝ) := by
          apply Finset.prod_congr rfl
          intro g hg
          exact groupWeight_sum_one g (hmass g)
        _ = 1 := by simp

private lemma restWeight_sum_one {G : PrimeGroups} {k : Fin G.size → ℕ}
    (i₀ : Coordinate G k) (hmass : ∀ g, 0 < mass G g) :
    ∑ y : (∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1), restWeight i₀ y = 1 := by
  classical
  let e := splitCoordinate G k i₀
  have htotal : ∑ z : Tuple G k, tupleWeight G k z = 1 := tupleWeight_sum_one hmass
  have hfactor :
      (∑ z : Tuple G k, tupleWeight G k z) =
        (∑ p : Label G i₀.1, mu G i₀.1 p.val) *
          ∑ y : (∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1), restWeight i₀ y := by
    calc
      (∑ z : Tuple G k, tupleWeight G k z) =
          ∑ xy : Label G i₀.1 ×
              (∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1),
            tupleWeight G k (e.symm xy) := by
        exact Fintype.sum_equiv e (fun z => tupleWeight G k z)
          (fun xy => tupleWeight G k (e.symm xy)) (by intro z; simp [e])
      _ = ∑ xy : Label G i₀.1 ×
              (∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1),
            mu G i₀.1 xy.1.val * restWeight i₀ xy.2 := by
        apply Finset.sum_congr rfl
        intro xy hxy
        exact tupleWeight_split i₀ xy.1 xy.2
      _ = _ := by
        rw [Fintype.sum_prod_type]
        exact (Finset.sum_mul_sum Finset.univ Finset.univ
          (fun p : Label G i₀.1 => mu G i₀.1 p.val)
          (fun y : (∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1) =>
            restWeight i₀ y)).symm
  have hlabel := labelWeight_sum i₀.1 (hmass i₀.1)
  rw [htotal, hlabel] at hfactor
  simpa using hfactor.symm

private lemma restProduct_pos {G : PrimeGroups} {k : Fin G.size → ℕ}
    (i₀ : Coordinate G k)
    (y : ∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1) :
    0 < restProduct i₀ y := by
  classical
  unfold restProduct
  apply Finset.prod_pos
  intro i hi
  exact Nat.Prime.pos (G.prime i.1.1 (y i).val (y i).property)

private lemma restWeight_nonneg {G : PrimeGroups} {k : Fin G.size → ℕ}
    (i₀ : Coordinate G k)
    (y : ∀ i : {i : Coordinate G k // i ≠ i₀}, Label G i.1.1)
    (hmass : ∀ g, 0 < mass G g) :
    0 ≤ restWeight i₀ y := by
  classical
  unfold restWeight
  apply Finset.prod_nonneg
  intro i hi
  exact one_div_nonneg.mpr (mul_nonneg (le_of_lt (hmass i.1.1)) (Nat.cast_nonneg _))

private lemma cell_mul_eq_iff_band (h : ℝ) (j : ℤ) (a p : ℕ)
    (hh : 0 < h) (ha : 0 < a) (hp : 0 < p) :
    cell h (a * p) = j ↔
      Real.exp ((j : ℝ) * h) / (a : ℝ) ≤ (p : ℝ) ∧
        (p : ℝ) < Real.exp (((j + 1 : ℤ) : ℝ) * h) / (a : ℝ) := by
  have haR : 0 < (a : ℝ) := Nat.cast_pos.mpr ha
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hprod : 0 < ((a * p : ℕ) : ℝ) := by positivity
  rw [cell, Int.floor_eq_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hlo' : (j : ℝ) * h ≤ Real.log ((a * p : ℕ) : ℝ) := by
      exact (le_div_iff₀ hh).mp hlo
    have hhi' : Real.log ((a * p : ℕ) : ℝ) < ((j + 1 : ℤ) : ℝ) * h := by
      simpa [Int.cast_add, Int.cast_one] using (div_lt_iff₀ hh).mp hhi
    constructor
    · apply (div_le_iff₀ haR).2
      calc
        Real.exp ((j : ℝ) * h) ≤ Real.exp (Real.log ((a * p : ℕ) : ℝ)) :=
          Real.exp_le_exp.mpr hlo'
        _ = ((a * p : ℕ) : ℝ) := Real.exp_log hprod
        _ = (p : ℝ) * (a : ℝ) := by rw [Nat.cast_mul]; ring
    · apply (lt_div_iff₀ haR).2
      calc
        (p : ℝ) * (a : ℝ) = (a : ℝ) * (p : ℝ) := by ring
        _ = ((a * p : ℕ) : ℝ) := by rw [Nat.cast_mul]
        _ = Real.exp (Real.log ((a * p : ℕ) : ℝ)) := (Real.exp_log hprod).symm
        _ < Real.exp (((j + 1 : ℤ) : ℝ) * h) := Real.exp_lt_exp.mpr hhi'
  · rintro ⟨hlo, hhi⟩
    constructor
    · apply (le_div_iff₀ hh).2
      have hmul : Real.exp ((j : ℝ) * h) ≤ ((a * p : ℕ) : ℝ) := by
        calc
          Real.exp ((j : ℝ) * h) ≤ (a : ℝ) * (p : ℝ) := by
            nlinarith [(div_le_iff₀ haR).1 hlo]
          _ = ((a * p : ℕ) : ℝ) := by rw [Nat.cast_mul]
      have hmul' : Real.exp ((j : ℝ) * h) ≤ Real.exp (Real.log ((a * p : ℕ) : ℝ)) := by
        calc
          Real.exp ((j : ℝ) * h) ≤ ((a * p : ℕ) : ℝ) := hmul
          _ = Real.exp (Real.log ((a * p : ℕ) : ℝ)) := (Real.exp_log hprod).symm
      have hlog := Real.exp_le_exp.mp hmul'
      simpa using hlog
    ·
      have hmul : ((a * p : ℕ) : ℝ) < Real.exp (((j + 1 : ℤ) : ℝ) * h) := by
        calc
          ((a * p : ℕ) : ℝ) = (a : ℝ) * (p : ℝ) := by rw [Nat.cast_mul]
          _ < Real.exp (((j + 1 : ℤ) : ℝ) * h) := by
            nlinarith [(lt_div_iff₀ haR).1 hhi]
      have hmul' : Real.exp (Real.log ((a * p : ℕ) : ℝ)) <
          Real.exp (((j + 1 : ℤ) : ℝ) * h) := by
        calc
          Real.exp (Real.log ((a * p : ℕ) : ℝ)) = ((a * p : ℕ) : ℝ) := Real.exp_log hprod
          _ < Real.exp (((j + 1 : ℤ) : ℝ) * h) := hmul
      have hloghi := Real.exp_lt_exp.mp hmul'
      have hloghi' : Real.log ((a * p : ℕ) : ℝ) < ((j + 1 : ℤ) : ℝ) * h := by
        exact hloghi
      simpa [Int.cast_add, Int.cast_one] using (div_lt_iff₀ hh).2 hloghi'

private lemma nat_mem_Icc_ceil_floor (lo hi : ℝ) (hhi : 0 ≤ hi) (p : ℕ) :
    p ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ ↔ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi := by
  simp [Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hhi]

private lemma cell_group_interval_set_eq {G : PrimeGroups} (g : Fin G.size)
    (a : ℕ) (h : ℝ) (j : ℤ) (loGroup hiGroup lowerPrime upperPrime lo hi : ℝ)
    (hgroup : ∀ p, p ∈ G.primes g ↔ p.Prime ∧ loGroup ≤ (p : ℝ) ∧ (p : ℝ) ≤ hiGroup)
    (hprimeLower : ∀ p, p ∈ G.primes g → lowerPrime ≤ (p : ℝ))
    (hprimeUpper : ∀ p, p ∈ G.primes g → (p : ℝ) ≤ upperPrime)
    (ha : 0 < a) (hh : 0 < h) (hhiNonneg : 0 ≤ hi)
    (hlo : lo = max loGroup (max lowerPrime
      (Real.exp ((j : ℝ) * h) / (a : ℝ))))
    (hhi : hi = min hiGroup (min upperPrime
      ((Nat.ceil (Real.exp (((j + 1 : ℤ) : ℝ) * h) / (a : ℝ)) - 1 : ℕ) : ℝ))) :
    (G.primes g).filter (fun p => cell h (a * p) = j) =
      (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter Nat.Prime := by
  classical
  let upperCell := Real.exp (((j + 1 : ℤ) : ℝ) * h) / (a : ℝ)
  let lastNat := Nat.ceil upperCell - 1
  have hupperCell : 0 < upperCell := by
    dsimp [upperCell]
    positivity
  have hceil : 1 ≤ Nat.ceil upperCell := Nat.one_le_ceil_iff.mpr hupperCell
  have hlast_lt : (lastNat : ℝ) < upperCell := by
    dsimp [lastNat]
    rw [Nat.cast_sub hceil]
    simpa [sub_lt_iff_lt_add] using Nat.ceil_lt_add_one hupperCell.le
  have hceil_of_lt {p : ℕ} (hp : (p : ℝ) < upperCell) : p < Nat.ceil upperCell := by
    exact Nat.lt_ceil.mpr hp
  have hp_le_last {p : ℕ} (hp : (p : ℝ) < upperCell) : p ≤ lastNat := by
    have := hceil_of_lt hp
    dsimp [lastNat]
    omega
  have hlastNat_lt {p : ℕ} (hp : p ≤ lastNat) : (p : ℝ) < upperCell := by
    exact lt_of_le_of_lt (Nat.cast_le.mpr hp) hlast_lt
  ext p
  simp only [Finset.mem_filter]
  rw [nat_mem_Icc_ceil_floor lo hi hhiNonneg p]
  constructor
  · rintro ⟨hpgroup, hcell⟩
    have hpinfo := (hgroup p).mp hpgroup
    rcases hpinfo with ⟨hpprime, hpLoGroup, hpHiGroup⟩
    have hpBounds := cell_mul_eq_iff_band h j a p hh ha (Nat.Prime.pos hpprime) |>.mp hcell
    have hpLo : lo ≤ (p : ℝ) := by
      rw [hlo]
      exact max_le_iff.mpr ⟨hpLoGroup, max_le_iff.mpr ⟨hprimeLower p hpgroup, hpBounds.1⟩⟩
    have hpHi : (p : ℝ) ≤ hi := by
      rw [hhi]
      apply le_min
      · exact hpHiGroup
      · apply le_min
        · exact hprimeUpper p hpgroup
        · exact_mod_cast hp_le_last hpBounds.2
    exact ⟨⟨hpLo, hpHi⟩, hpprime⟩
  · rintro ⟨⟨hpLo, hpHi⟩, hpprime⟩
    rw [hlo] at hpLo
    rcases max_le_iff.mp hpLo with ⟨hpLoGroup, hpLower⟩
    rcases max_le_iff.mp hpLower with ⟨hpLowerPrime, hpCellLower⟩
    rw [hhi] at hpHi
    rcases le_min_iff.mp hpHi with ⟨hpHiGroup, hpUpper⟩
    rcases le_min_iff.mp hpUpper with ⟨hpUpperPrime, hpLast⟩
    have hpLast' : p ≤ lastNat := by exact_mod_cast hpLast
    have hpCellUpper : (p : ℝ) < upperCell := hlastNat_lt hpLast'
    have hpgroup : p ∈ G.primes g := (hgroup p).mpr ⟨hpprime, hpLoGroup, hpHiGroup⟩
    have hcell := (cell_mul_eq_iff_band h j a p hh ha (Nat.Prime.pos hpprime)).mpr
      ⟨hpCellLower, hpCellUpper⟩
    exact ⟨hpgroup, hcell⟩

private lemma commonModulus_bound {x qexp : ℝ} {Q : ℕ} (χ ψ : CharacterIndex Q)
    (hlog : 1 ≤ L x) (hQ : (Q : ℝ) ≤ L x ^ qexp) :
    (Nat.lcm (level χ) (level ψ) : ℝ) ≤ L x ^ (2 * qexp) := by
  have hn : level χ ≤ Q := Nat.succ_le_of_lt χ.1.is_lt
  have hm : level ψ ≤ Q := Nat.succ_le_of_lt ψ.1.is_lt
  have hnpos : 0 < level χ := Nat.succ_pos _
  have hmpos : 0 < level ψ := Nat.succ_pos _
  have hlcm : Nat.lcm (level χ) (level ψ) ≤ level χ * level ψ :=
    Nat.le_of_dvd (Nat.mul_pos hnpos hmpos) (Nat.lcm_dvd_mul _ _)
  have hprod : level χ * level ψ ≤ Q * Q := Nat.mul_le_mul hn hm
  calc
    (Nat.lcm (level χ) (level ψ) : ℝ) ≤ (level χ : ℝ) * (level ψ : ℝ) := by
      exact_mod_cast hlcm
    _ ≤ (Q : ℝ) * (Q : ℝ) := by exact_mod_cast hprod
    _ = (Q : ℝ) ^ 2 := by ring
    _ ≤ (L x ^ qexp) ^ 2 := by gcongr
    _ = L x ^ (2 * qexp) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_trans zero_le_one hlog)]
      ring_nf

private lemma conditional_cell_harmonic_bound
    {P : Geometry} {x qexp D Kharm : ℝ} {G : PrimeGroups} {g : Fin G.size}
    (hHarm : ∀ (lo hi t : ℝ) (r : ℕ) (q : DirichletCharacter ℂ r),
      Real.exp (L x ^ P.c) ≤ lo → lo ≤ hi → hi ≤ x ^ (1 : ℝ) →
      1 ≤ r → (r : ℝ) ≤ L x ^ (2 * qexp) → q ≠ 1 →
      |t| ≤ L x ^ (2 * qexp) →
      ‖∑ p ∈ ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter Nat.Prime),
        q (p : ZMod r) * mellin p t / (p : ℂ)‖ ≤ Kharm * L x ^ (-D))
    (hKharm : 0 < Kharm) (hG : Admissible P x G) (hgsmall : g ∉ G.small)
    (a : ℕ) (ha : 0 < a) (h : ℝ) (hh : 0 < h) (j : ℤ)
    (Q : ℕ) (χ ψ : CharacterIndex Q) (hQ : (Q : ℝ) ≤ L x ^ qexp)
    (hχ : χ ∈ primitiveCharacters Q) (hψ : ψ ∈ primitiveCharacters Q)
    (hne : χ ≠ ψ) (hlog : 1 ≤ L x)
    (hExpUpper : Real.exp (L x ^ P.d) ≤ x) :
    ‖∑ p : Label G g, if cell h (a * p.val) = j then
        (mu G g p.val : ℂ) * cellQuotient χ ψ (a * p.val) else 0‖ ≤
      (Kharm / P.vmin) * L x ^ (-D) := by
  classical
  let n := level χ
  let m := level ψ
  let r := Nat.lcm n m
  let q := cellQuotient χ ψ
  have hrpos : 0 < r := Nat.lcm_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hrone : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrpos.ne'
  have hrBound : (r : ℝ) ≤ L x ^ (2 * qexp) := by
    exact commonModulus_bound χ ψ hlog hQ
  have hqnot : q ≠ 1 := cellQuotient_ne_one hχ hψ hne
  have hmass : P.vmin ≤ mass G g := (hG.2.2.1 g).1
  have hvmin : 0 < P.vmin := P.positive.2.2.1
  have hmassPos : 0 < mass G g := lt_of_lt_of_le hvmin hmass
  have hgBig : g ∈ G.big := by simp [PrimeGroups.big, hgsmall]
  obtain ⟨loGroup, hiGroup, hgroup⟩ := hG.2.2.2.2 g hgBig
  have hprimeLower : ∀ p, p ∈ G.primes g → Real.exp (L x ^ P.c) ≤ (p : ℝ) := by
    intro p hp
    have h := hG.2.2.2.1 g p hp
    have h' : Real.exp (L x ^ P.c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L x ^ P.d) := by
      simpa [hgsmall] using h
    exact h'.1
  have hprimeUpper : ∀ p, p ∈ G.primes g → (p : ℝ) ≤ Real.exp (L x ^ P.d) := by
    intro p hp
    have h := hG.2.2.2.1 g p hp
    have h' : Real.exp (L x ^ P.c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L x ^ P.d) := by
      simpa [hgsmall] using h
    exact h'.2
  have hprimesNonempty : (G.primes g).Nonempty := by
    by_contra hne'
    have hempty : G.primes g = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
    have : mass G g = 0 := by simp [mass, hempty]
    linarith
  obtain ⟨p₀, hp₀⟩ := hprimesNonempty
  have hhiGroupNonneg : 0 ≤ hiGroup := by
    have hpInfo := (hgroup p₀).mp hp₀
    exact le_trans (Nat.cast_nonneg _) hpInfo.2.2
  let upperCell := Real.exp (((j + 1 : ℤ) : ℝ) * h) / (a : ℝ)
  let lastNat := Nat.ceil upperCell - 1
  let lo := max loGroup (max (Real.exp (L x ^ P.c)) (Real.exp ((j : ℝ) * h) / (a : ℝ)))
  let hi := min hiGroup (min (Real.exp (L x ^ P.d)) (lastNat : ℝ))
  have hhiNonneg : 0 ≤ hi := by
    dsimp [hi]
    apply le_min_iff.mpr
    constructor
    · exact hhiGroupNonneg
    · apply le_min_iff.mpr
      exact ⟨le_of_lt (Real.exp_pos _), Nat.cast_nonneg _⟩
  have hLoBound : Real.exp (L x ^ P.c) ≤ lo := by
    dsimp [lo]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHiBound : hi ≤ x := by
    dsimp [hi]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hExpUpper)
  have hIntervalSet := cell_group_interval_set_eq g a h j loGroup hiGroup
    (Real.exp (L x ^ P.c)) (Real.exp (L x ^ P.d)) lo hi hgroup
    hprimeLower hprimeUpper ha hh hhiNonneg rfl rfl
  let S : Finset ℕ := (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter Nat.Prime
  have hSet : (G.primes g).filter (fun p => cell h (a * p) = j) = S := by
    simpa [S] using hIntervalSet
  have hμ (p : Label G g) :
      (mu G g p.val : ℂ) = (mass G g : ℂ)⁻¹ * (p.val : ℂ)⁻¹ := by
    have hm0 : (mass G g : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hmassPos
    have hpPrime := G.prime g p.val p.property
    have hp0 : (p.val : ℂ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
    simp [mu, map_div, map_one, map_mul, map_inv]
    ring
  have hqmul (p : ℕ) : q ((a : ZMod r) * (p : ZMod r)) =
      q (a : ZMod r) * q (p : ZMod r) := map_mul q _ _
  let c : ℂ := (mass G g : ℂ)⁻¹ * q (a : ZMod r)
  let f (p : ℕ) : ℂ := q (p : ZMod r) * mellin p 0 / (p : ℂ)
  have hterm (p : Label G g) :
      (mu G g p.val : ℂ) * q (a * p.val) = c * f p.val := by
    rw [hμ p, hqmul p.val]
    have hmell : mellin p.val 0 = 1 := by
      simp [Erdos821.Blueprint.Analytic.mellin]
    dsimp [c, f]
    simp only [hmell, div_eq_mul_inv]
    ring
  have hsum :
      (∑ p : Label G g, if cell h (a * p.val) = j then
          (mu G g p.val : ℂ) * q (a * p.val) else 0) =
        c * ∑ p ∈ S, f p := by
    calc
      _ = ∑ p : Label G g, c * (if cell h (a * p.val) = j then f p.val else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hc : cell h (a * p.val) = j
        · simp only [if_pos hc]
          exact hterm p
        · simp [hc]
      _ = c * ∑ p : Label G g, if cell h (a * p.val) = j then f p.val else 0 := by
        rw [Finset.mul_sum]
      _ = c * ∑ p ∈ G.primes g, if cell h (a * p) = j then f p else 0 := by
        congr 1
        simpa [Label] using (Finset.sum_attach (G.primes g)
          (fun p : ℕ => if cell h (a * p) = j then f p else 0))
      _ = c * ∑ p ∈ (G.primes g).filter (fun p => cell h (a * p) = j), f p := by
        rw [← Finset.sum_filter]
      _ = c * ∑ p ∈ S, f p := by rw [hSet]
  by_cases hlohi : lo ≤ hi
  · have hHarmVal := hHarm lo hi 0 r q hLoBound hlohi (by simpa using hHiBound)
      hrone hrBound hqnot (by simp; positivity)
    have hqNorm : ‖q (a : ZMod r)‖ ≤ 1 := DirichletCharacter.norm_le_one q _
    have hInvNorm : ‖(mass G g : ℂ)⁻¹‖ = (mass G g)⁻¹ := by
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmassPos]
    have hCoeff : ‖c‖ ≤ P.vmin⁻¹ := by
      dsimp [c]
      rw [norm_mul, hInvNorm]
      calc
        (mass G g)⁻¹ * ‖q (a : ZMod r)‖ ≤ (mass G g)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hqNorm (by positivity)
        _ ≤ P.vmin⁻¹ := by
          simpa using one_div_le_one_div_of_le hvmin hmass
    rw [hsum]
    calc
      ‖c * ∑ p ∈ S, f p‖ = ‖c‖ * ‖∑ p ∈ S, f p‖ := norm_mul _ _
      _ ≤ P.vmin⁻¹ * (Kharm * L x ^ (-D)) :=
        mul_le_mul hCoeff hHarmVal (norm_nonneg _) (by positivity)
      _ = (Kharm / P.vmin) * L x ^ (-D) := by ring
  · have hSempty : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpint := (nat_mem_Icc_ceil_floor lo hi hhiNonneg p).mp (Finset.mem_filter.mp hp).1
      exact (not_le_of_gt (lt_of_not_ge hlohi)) (hpint.1.trans hpint.2)
    rw [hsum, hSempty]
    simp
    positivity

theorem CharacterCellTask_proof : CharacterCellTask := by
  intro H P m qexp D hqexp hD
  have hPc : 0 < P.c := by
    rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩
    linarith
  have hB : 0 < 2 * qexp := by positivity
  have hC : (0 : ℝ) < 1 := by norm_num
  obtain ⟨K0, hK0, hHEvent⟩ := H P.c 1 (2 * qexp) D hPc hC hB hD
  have hvmin : 0 < P.vmin := P.positive.2.2.1
  have hK : 0 < K0 / P.vmin := div_pos hK0 hvmin
  refine ⟨K0 / P.vmin, hK, ?_⟩
  have hLarge : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x :=
    Filter.eventually_atTop.2 ⟨Real.exp 1, fun _ hx => hx⟩
  filter_upwards [hHEvent, hLarge] with x hHarm hxLarge
  have hlogx : 1 ≤ L x := by
    unfold L
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hxLarge
  have hdle1 : P.d ≤ 1 := by
    rcases P.ordered with ⟨ha, hab, hbc, hcd, hd⟩
    linarith
  have hpow : L x ^ P.d ≤ L x := Real.rpow_le_self_of_one_le hlogx hdle1
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxLarge
  have hExpUpper : Real.exp (L x ^ P.d) ≤ x := by
    calc
      Real.exp (L x ^ P.d) ≤ Real.exp (L x) := Real.exp_le_exp.mpr hpow
      _ = x := Real.exp_log hxpos
  intro G hG k hk Q h j χ ψ hQ hwidth hχ hψ hne
  have hactive : ∃ g : Fin G.size, 0 < k g := by
    have hsumPos := hk.1
    by_contra hnone
    have hzero : ∀ g : Fin G.size, k g = 0 := by
      intro g
      have hn : ¬ 0 < k g := fun hkg => hnone ⟨g, hkg⟩
      omega
    have hsum : (∑ g : Fin G.size, k g) = 0 := by
      apply Finset.sum_eq_zero
      intro g hg
      exact hzero g
    omega
  obtain ⟨g, hgk⟩ := hactive
  have hgsmall : g ∉ G.small := by
    intro hgs
    have hkzero := (hk.2 g).2 hgs
    omega
  let i0 : Coordinate G k := ⟨g, ⟨0, hgk⟩⟩
  have hmassAll : ∀ g : Fin G.size, 0 < mass G g := by
    intro g
    exact lt_of_lt_of_le hvmin (hG.2.2.1 g).1
  let e := splitCoordinate G k i0
  have hrestMass : ∑ y : (∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1),
      restWeight i0 y = 1 := restWeight_sum_one i0 hmassAll
  let F : Tuple G k → ℂ := fun z =>
    if cell h (product G k z) = j then
      star (charValue χ (product G k z)) * charValue ψ (product G k z) else 0
  have hsplit :
      expect G k F =
        ∑ xy : Label G g ×
            (∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1),
          (restWeight i0 xy.2 : ℂ) *
            (if cell h (restProduct i0 xy.2 * xy.1.val) = j then
              (mu G g xy.1.val : ℂ) * cellQuotient χ ψ
                (restProduct i0 xy.2 * xy.1.val) else 0) := by
    calc
      expect G k F =
          ∑ z : Tuple G k, (tupleWeight G k z : ℂ) * F z := rfl
      _ = ∑ xy : Label G g ×
              (∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1),
            (tupleWeight G k (e.symm xy) : ℂ) * F (e.symm xy) := by
        exact Fintype.sum_equiv e
          (fun z => (tupleWeight G k z : ℂ) * F z)
          (fun xy => (tupleWeight G k (e.symm xy) : ℂ) * F (e.symm xy))
          (by intro z; simp [e])
      _ = ∑ xy : Label G g ×
              (∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1),
            (restWeight i0 xy.2 : ℂ) *
              (if cell h (restProduct i0 xy.2 * xy.1.val) = j then
                (mu G g xy.1.val : ℂ) *
                  cellQuotient χ ψ (restProduct i0 xy.2 * xy.1.val) else 0) := by
        apply Finset.sum_congr rfl
        intro xy hxy
        change
          (tupleWeight G k ((splitCoordinate G k i0).symm xy) : ℂ) *
            (if cell h (product G k ((splitCoordinate G k i0).symm xy)) = j then
              star (charValue χ (product G k ((splitCoordinate G k i0).symm xy))) *
                charValue ψ (product G k ((splitCoordinate G k i0).symm xy)) else 0) = _
        rw [tupleWeight_split, product_split]
        by_cases hc : cell h (restProduct i0 xy.2 * xy.1.val) = j
        · simp only [if_pos hc]
          rw [← cellQuotient_eval χ ψ (restProduct i0 xy.2 * xy.1.val)]
          push_cast
          ring
        · simp [hc]
  have hsplitOuter :
      (∑ xy : Label G g ×
          (∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1),
        (restWeight i0 xy.2 : ℂ) *
          (if cell h (restProduct i0 xy.2 * xy.1.val) = j then
            (mu G g xy.1.val : ℂ) *
              cellQuotient χ ψ (restProduct i0 xy.2 * xy.1.val) else 0)) =
        ∑ y : (∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1),
          (restWeight i0 y : ℂ) *
            ∑ p : Label G g, if cell h (restProduct i0 y * p.val) = j then
              (mu G g p.val : ℂ) *
                cellQuotient χ ψ (restProduct i0 y * p.val) else 0 := by
    rw [Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.mul_sum]
  have hinner (y : ∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1) :
      ‖∑ p : Label G g, if cell h (restProduct i0 y * p.val) = j then
        (mu G g p.val : ℂ) *
          cellQuotient χ ψ (restProduct i0 y * p.val) else 0‖ ≤
        (K0 / P.vmin) * L x ^ (-D) := by
    exact conditional_cell_harmonic_bound hHarm hK0 hG hgsmall
      (restProduct i0 y) (restProduct_pos i0 y) h hwidth j Q χ ψ hQ hχ hψ hne
      hlogx hExpUpper
  have htermNorm (y : ∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1) :
      ‖(restWeight i0 y : ℂ) *
        (∑ p : Label G g, if cell h (restProduct i0 y * p.val) = j then
          (mu G g p.val : ℂ) *
            cellQuotient χ ψ (restProduct i0 y * p.val) else 0)‖ ≤
        restWeight i0 y * ((K0 / P.vmin) * L x ^ (-D)) := by
    have hnonneg := restWeight_nonneg i0 y hmassAll
    rw [norm_mul]
    have hnormCast : ‖(restWeight i0 y : ℂ)‖ = restWeight i0 y := by
      simp [Complex.norm_real, abs_of_nonneg hnonneg]
    rw [hnormCast]
    exact mul_le_mul_of_nonneg_left (hinner y) hnonneg
  rw [hsplit, hsplitOuter]
  calc
    ‖∑ y : (∀ i : {i : Coordinate G k // i ≠ i0}, Label G i.1.1),
        (restWeight i0 y : ℂ) *
          ∑ p : Label G g, if cell h (restProduct i0 y * p.val) = j then
            (mu G g p.val : ℂ) *
              cellQuotient χ ψ (restProduct i0 y * p.val) else 0‖ ≤
      ∑ y, ‖(restWeight i0 y : ℂ) *
          ∑ p : Label G g, if cell h (restProduct i0 y * p.val) = j then
            (mu G g p.val : ℂ) *
              cellQuotient χ ψ (restProduct i0 y * p.val) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ y, restWeight i0 y * ((K0 / P.vmin) * L x ^ (-D)) := by
      apply Finset.sum_le_sum
      intro y hy
      exact htermNorm y
    _ = (K0 / P.vmin) * L x ^ (-D) := by
      rw [← Finset.sum_mul, hrestMass]
      simp

end

end Erdos821.P4Cell
