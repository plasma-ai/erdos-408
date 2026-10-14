import Erdos821.S2.SpanMarkWeightTask

/-! The original mark coefficient, separated into its V normalization and
the prime's single reciprocal baseline charge. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Mark

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

theorem tiltedMu_eq_Vinv_mul_charge (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (g : P.Group) (p : P.Prime g) :
    tiltedMu F P n g p = (P.V g)⁻¹ * ((p.val * baselinePrime F n p.val : ℝ)⁻¹) := by
  simp [tiltedMu, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

theorem unsharedTargetSlots_card {P : PrimeGroups} {J ell m : ℕ}
    (ν : Pattern P J ell m) (g : P.Group) :
    (Finset.univ.filter (fun j : Fin (J + ell) => ¬ν.shared g j)).card = ν.t g := by
  classical
  let U : Finset (Fin (J + ell)) := Finset.univ.filter (fun j => ¬ν.shared g j)
  let S : Finset (Fin (J + ell)) := Finset.univ.filter (fun j => ν.shared g j)
  let R : Finset (Fin J) := Finset.univ \ ν.changed g
  have hslot : Function.Injective ν.slot := by
    intro i j hij
    apply Fin.ext
    simpa [Pattern.slot] using congrArg Fin.val hij
  have hshared : S = R.image ν.slot := by
    ext j
    simp [S, R, Pattern.shared, and_comm, eq_comm]
  have hsharedCard : S.card = R.card := by
    rw [hshared]
    exact Finset.card_image_of_injective _ hslot
  have hpartition : S.card + U.card = J + ell := by
    dsimp [S, U]
    simpa using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (J + ell))))
      (p := fun j : Fin (J + ell) => ν.shared g j))
  have hR : R.card + (ν.changed g).card = J := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (ν.changed g))
    simpa [R] using h
  rw [hsharedCard] at hpartition
  change U.card = ν.t g
  dsimp [Pattern.t]
  omega

def freshTargetSlots {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (i : Fin n) (g : P.BigGroup) : Finset (Fin (J + F.ell)) :=
  Finset.univ.filter (fun j => ¬(A.pattern (Q.pattern i)).shared g.val j ∧
    j ∉ Q.promotionSlots S i g)

theorem freshTargetSlots_card {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (i : Fin n) (g : P.BigGroup) :
    (freshTargetSlots Q S i g).card + (Q.promotionSlots S i g).card =
      (A.pattern (Q.pattern i)).t g.val := by
  classical
  let ν := A.pattern (Q.pattern i)
  let U : Finset (Fin (J + F.ell)) := Finset.univ.filter (fun j => ¬ν.shared g.val j)
  let B := Q.promotionSlots S i g
  have hset : freshTargetSlots Q S i g = U \ B := by
    ext j
    simp [freshTargetSlots, U, B, ν, Finset.mem_sdiff, Finset.mem_filter]
  have hsub : B ⊆ U := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩
  have hU : U.card = ν.t g.val := by
    simpa [U, ν] using unsharedTargetSlots_card ν g.val
  calc
    _ = (U \ B).card + B.card := by rw [hset]
    _ = U.card := Finset.card_sdiff_add_card_eq_card hsub
    _ = ν.t g.val := hU
    _ = (A.pattern (Q.pattern i)).t g.val := by rfl

theorem initialMark_factorization {F : FixedData} {P : PrimeGroups} {M n : ℕ}
    (g : P.Group) (a : Fin M → P.Prime g) :
    (∏ j : Fin M, tiltedMu F P n g (a j)) =
      (P.V g) ^ (-(M : ℤ)) *
        (∏ j : Fin M, ((a j).val * baselinePrime F n (a j).val : ℝ)⁻¹) := by
  calc
    _ = ∏ j : Fin M, (P.V g)⁻¹ * ((a j).val * baselinePrime F n (a j).val : ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro j hj
      exact tiltedMu_eq_Vinv_mul_charge F P n g (a j)
    _ = (P.V g)⁻¹ ^ M *
        (∏ j : Fin M, ((a j).val * baselinePrime F n (a j).val : ℝ)⁻¹) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = (P.V g) ^ (-(M : ℤ)) *
        (∏ j : Fin M, ((a j).val * baselinePrime F n (a j).val : ℝ)⁻¹) := by
      congr 1
      simp [zpow_neg, zpow_natCast, inv_pow]

theorem edgeFreshMark_factorization {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    (A : Model F P J m)
    (Q : ResiduePath A n) (S : LifespanAssignment P n) (i : Fin n) (g : P.BigGroup)
    (hV : P.V g.val ≠ 0) :
    (∏ j : Fin (J + F.ell),
      if (A.pattern (Q.pattern i)).shared g.val j ∨ j ∈ Q.promotionSlots S i g then 1
      else tiltedMu F P n g.val (Q.target i g.val j)) *
        (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ)) =
      (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ)) *
        (∏ j ∈ freshTargetSlots Q S i g,
          ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹) := by
  classical
  let ν := A.pattern (Q.pattern i)
  let B := Q.promotionSlots S i g
  let U : Finset (Fin (J + F.ell)) := Finset.univ.filter (fun j => ¬ν.shared g.val j)
  let W := freshTargetSlots Q S i g
  have hset : W = U \ B := by
    ext j
    simp [freshTargetSlots, U, W, B, ν, Finset.mem_sdiff, Finset.mem_filter]
  have hprod :
      (∏ j : Fin (J + F.ell),
        if ν.shared g.val j ∨ j ∈ B then 1 else tiltedMu F P n g.val (Q.target i g.val j)) =
        ∏ j ∈ W, tiltedMu F P n g.val (Q.target i g.val j) := by
    calc
      _ = ∏ j : Fin (J + F.ell),
          if j ∈ W then tiltedMu F P n g.val (Q.target i g.val j) else 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        by_cases hs : ν.shared g.val j <;> by_cases hb : j ∈ B <;>
          simp [freshTargetSlots, W, B, ν, hs, hb]
      _ = ∏ j ∈ W, tiltedMu F P n g.val (Q.target i g.val j) := by simp
  have htilt :
      (∏ j ∈ W, tiltedMu F P n g.val (Q.target i g.val j)) =
        (P.V g.val)⁻¹ ^ W.card *
          (∏ j ∈ W,
            ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹) := by
    calc
      _ = ∏ j ∈ W,
          (P.V g.val)⁻¹ *
            ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹ := by
        apply Finset.prod_congr rfl
        intro j hj
        exact tiltedMu_eq_Vinv_mul_charge F P n g.val (Q.target i g.val j)
      _ = _ := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const]
  have hcard : W.card + B.card = ν.t g.val := by
    simpa [W, B, ν] using freshTargetSlots_card Q S i g
  have hpow :
      (P.V g.val)⁻¹ ^ W.card * (P.V g.val) ^ (-((B.card : ℕ) : ℤ)) =
        (P.V g.val) ^ (-((ν.t g.val : ℕ) : ℤ)) := by
    rw [show (P.V g.val)⁻¹ ^ W.card =
      (P.V g.val) ^ (-((W.card : ℕ) : ℤ)) by simp [zpow_neg, zpow_natCast, inv_pow]]
    rw [← zpow_add₀ hV]
    congr 1
    have hc : (W.card : ℤ) + (B.card : ℤ) = (ν.t g.val : ℤ) := by exact_mod_cast hcard
    omega
  rw [hprod, htilt]
  calc
    _ = ((P.V g.val)⁻¹ ^ W.card * (P.V g.val) ^ (-((B.card : ℕ) : ℤ))) *
        (∏ j ∈ W,
          ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹) := by ring
    _ = _ := by rw [hpow]

theorem spanGhost_product_some {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (g : P.BigGroup) (p : P.Prime g.val) (birth stop : Fin (n + 1))
    (hspan : S g p = some (birth, stop)) :
    (∏ i : Fin (n + 1), Q.spanGhostFactor S i g p) =
      (if birth ∈ Q.activeVisits g p then 1
        else -eta F n birth * ((p.val * baselinePrime F n p.val : ℝ)⁻¹)) *
      (if stop ∈ Q.activeVisits g p then 1 else -eta F n stop) *
      (∏ i ∈ Finset.univ.filter
          (fun i => birth < i ∧ i < stop ∧ i ∉ Q.activeVisits g p),
        if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
          then visitQ F.q n i else 1) := by
  classical
  let active := Q.activeVisits g p
  let charge : ℝ := (p.val * baselinePrime F n p.val : ℝ)⁻¹
  have hbeforeafter (i : Fin (n + 1)) :
      (Q.pendingBefore g p (S g p) i ∧ Q.pendingAfter g p (S g p) i ∧
        ((Q.offset i - Q.spanAnchor (S g p) : ℤ) : ZMod p.val) = 0) ↔
        birth < i ∧ i < stop ∧ i ∉ active ∧
          ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 := by
    simp only [ResiduePath.pendingBefore, ResiduePath.pendingAfter, hspan,
      ResiduePath.spanAnchor]
    constructor
    · rintro ⟨⟨hbi, _, hnot⟩, ⟨_, hiz, _⟩, hz⟩
      exact ⟨hbi, hiz, hnot, hz⟩
    · rintro ⟨hbi, hiz, hnot, hz⟩
      exact ⟨⟨hbi, le_of_lt hiz, hnot⟩, ⟨le_of_lt hbi, hiz, hnot⟩, hz⟩
  have hbirth (i : Fin (n + 1)) :
      Q.ghostBirthAt g p (S g p) i ↔ i = birth ∧ birth ∉ active := by
    simp only [ResiduePath.ghostBirthAt, hspan]
    constructor
    · rintro ⟨h, hnot⟩
      subst i
      exact ⟨rfl, hnot⟩
    · rintro ⟨h, hnot⟩
      subst i
      exact ⟨rfl, hnot⟩
  have hstop (i : Fin (n + 1)) :
      Q.ghostStopAt g p (S g p) i ↔ i = stop ∧ stop ∉ active := by
    simp only [ResiduePath.ghostStopAt, hspan]
    constructor
    · rintro ⟨h, hnot⟩
      subst i
      exact ⟨rfl, hnot⟩
    · rintro ⟨h, hnot⟩
      subst i
      exact ⟨rfl, hnot⟩
  have hpoint (i : Fin (n + 1)) :
      Q.spanGhostFactor S i g p =
        (if i = birth ∧ birth ∉ active then -eta F n birth * charge else 1) *
        (if i = stop ∧ stop ∉ active then -eta F n stop else 1) *
        (if birth < i ∧ i < stop ∧ i ∉ active ∧
            ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
          then visitQ F.q n i else 1) := by
    simp only [ResiduePath.spanGhostFactor, hbirth i, hstop i, hbeforeafter i]
    by_cases hb : i = birth
    · by_cases hs : i = stop
      · have hbs : birth = stop := hb.symm.trans hs
        simp [hb, hs, hbs, eq_comm, charge]
      · have hne : birth ≠ stop := by
          intro h
          exact hs (hb.trans h)
        simp [hb, hs, hne, charge]
    · by_cases hs : i = stop
      · have hne : birth ≠ stop := by
          intro h
          exact hb (hs.trans h.symm)
        have hne' : stop ≠ birth := Ne.symm hne
        simp [hb, hs, hne, hne', charge]
      · simp [hb, hs, charge]
  have hbprod :
      (∏ i : Fin (n + 1), if i = birth ∧ birth ∉ active then -eta F n birth * charge else 1) =
        if birth ∈ active then 1 else -eta F n birth * charge := by
    by_cases hb : birth ∈ active
    · simp [hb]
    · have hfac (i : Fin (n + 1)) :
          (if i = birth ∧ birth ∉ active then -eta F n birth * charge else 1) =
            if i = birth then -eta F n birth * charge else 1 := by
        by_cases hi : i = birth <;> simp [hi, hb]
      simp_rw [hfac]
      simp [Finset.prod_ite_eq', hb]
  have hsprod :
      (∏ i : Fin (n + 1), if i = stop ∧ stop ∉ active then -eta F n stop else 1) =
        if stop ∈ active then 1 else -eta F n stop := by
    by_cases hs : stop ∈ active
    · simp [hs]
    · have hfac (i : Fin (n + 1)) :
          (if i = stop ∧ stop ∉ active then -eta F n stop else 1) =
            if i = stop then -eta F n stop else 1 := by
        by_cases hi : i = stop <;> simp [hi, hs]
      simp_rw [hfac]
      simp [Finset.prod_ite_eq', hs]
  have hiprod :
      (∏ i : Fin (n + 1),
        if birth < i ∧ i < stop ∧ i ∉ active ∧
            ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
          then visitQ F.q n i else 1) =
      ∏ i ∈ Finset.univ.filter (fun i => birth < i ∧ i < stop ∧ i ∉ active),
        if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
          then visitQ F.q n i else 1 := by
    calc
      _ = ∏ i : Fin (n + 1),
          if birth < i ∧ i < stop ∧ i ∉ active then
            (if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
              then visitQ F.q n i else 1)
          else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hbi : birth < i
        · by_cases hiz : i < stop
          · by_cases hnot : i ∉ active <;> by_cases hz :
                ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 <;>
              simp [hbi, hiz, hnot, hz]
          · simp [hiz]
        · simp [hbi]
      _ = _ := (Finset.prod_filter _ _).symm
  calc
    _ = ∏ i : Fin (n + 1),
        ((if i = birth ∧ birth ∉ active then -eta F n birth * charge else 1) *
          (if i = stop ∧ stop ∉ active then -eta F n stop else 1) *
          (if birth < i ∧ i < stop ∧ i ∉ active ∧
              ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
            then visitQ F.q n i else 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hpoint i
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hbprod, hsprod, hiprod]

theorem spanWeight_some_ghost_scalar {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (g : P.BigGroup) (p : P.Prime g.val) (birth stop : Fin (n + 1))
    (hspan : S g p = some (birth, stop))
    (hvalid : Q.spanValid g p (some (birth, stop))) :
    (if birth ∈ Q.activeVisits g p then
        (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) *
      (∏ i : Fin (n + 1), Q.spanGhostFactor S i g p) =
        Q.spanWeight g p (some (birth, stop)) := by
  classical
  have hghost := spanGhost_product_some Q S g p birth stop hspan
  let I : Finset (Fin (n + 1)) := Finset.univ.filter
    (fun i => birth < i ∧ i < stop ∧ i ∉ Q.activeVisits g p)
  have hinterior :
      Finset.prod I (fun i =>
        if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
          then visitQ F.q n i else 1) =
      Finset.prod I (fun i =>
        1 - eta F n i *
          if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 then 1 else 0) := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hz : ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0
    · have hz' :
          ((Q.offset i : ℤ) : ZMod p.val) - ((Q.offset birth : ℤ) : ZMod p.val) = 0 := by
        simpa only [Int.cast_sub] using hz
      simp [hz', eta] <;> ring_nf
    · have hz' :
          ¬(((Q.offset i : ℤ) : ZMod p.val) - ((Q.offset birth : ℤ) : ZMod p.val) = 0) := by
        simpa only [Int.cast_sub] using hz
      simp [hz']
  rw [hghost]
  unfold ResiduePath.spanWeight
  simp only [hvalid]
  rw [hinterior]
  let c : ℝ := (p.val * baselinePrime F n p.val : ℝ)⁻¹
  have hbirthFactor :
      (if birth ∈ Q.activeVisits g p then c else 1) *
        (if birth ∈ Q.activeVisits g p then 1 else -eta F n birth * c) =
          c * (if birth ∈ Q.activeVisits g p then 1 else -eta F n birth) := by
    by_cases hb : birth ∈ Q.activeVisits g p <;> simp [hb, c] <;> ring
  have hres (i : Fin (n + 1)) :
      ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) =
        ((-Q.offset birth + Q.offset i : ℤ) : ZMod p.val) := by
    congr 1
    ring
  have hprod :
      Finset.prod I (fun i => 1 - eta F n i *
        if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 then 1 else 0) =
      Finset.prod (Finset.univ.filter
          (fun i => birth < i ∧ i < stop ∧ i ∉ Q.activeVisits g p)) (fun i =>
        1 - eta F n i *
          if ((-Q.offset birth + Q.offset i : ℤ) : ZMod p.val) = 0 then 1 else 0) := by
    apply Finset.prod_congr
    · simp [I]
    · intro i hi
      simp [hres i]
  calc
    _ = ((if birth ∈ Q.activeVisits g p then c else 1) *
          (if birth ∈ Q.activeVisits g p then 1 else -eta F n birth * c)) *
        ((if stop ∈ Q.activeVisits g p then 1 else -eta F n stop) *
          Finset.prod I (fun i => 1 - eta F n i *
            if ((Q.offset i - Q.offset birth : ℤ) : ZMod p.val) = 0 then 1 else 0)) := by ring
    _ = _ := by
      rw [hbirthFactor]
      simp only [ite_true]
      rw [show c = (p.val : ℝ)⁻¹ * (baselinePrime F n p.val)⁻¹ by
        dsimp [c]
        rw [mul_inv_rev]
        ring]
      rw [hprod]
      ring

theorem spanWeight_scalarFactor {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (g : P.BigGroup) (p : P.Prime g.val)
    (hvalid : Q.spanValid g p (S g p)) :
    (match S g p with
      | none => (1 : ℝ)
      | some (birth, _) => if birth ∈ Q.activeVisits g p then
          (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) *
      (∏ i : Fin (n + 1), Q.spanGhostFactor S i g p) =
        Q.spanWeight g p (S g p) := by
  classical
  cases hspan : S g p with
  | none =>
      have hactive : Q.activeVisits g p = ∅ := by
        simpa [hspan, ResiduePath.spanValid] using hvalid
      simp [hspan, ResiduePath.spanWeight, ResiduePath.spanValid,
        ResiduePath.spanGhostFactor, ResiduePath.ghostBirthAt, ResiduePath.ghostStopAt,
        ResiduePath.pendingBefore, ResiduePath.pendingAfter, hactive]
  | some pair =>
      rcases pair with ⟨birth, stop⟩
      have hvalid' : Q.spanValid g p (some (birth, stop)) := by simpa [hspan] using hvalid
      simpa [hspan] using
        spanWeight_some_ghost_scalar Q S g p birth stop hspan hvalid'

theorem activeVisits_iff_label {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (g : P.BigGroup)
    (p : P.Prime g.val) (i : Fin (n + 1)) :
    i ∈ Q.activeVisits g p ↔ ∃ j : Fin (J + F.ell), Q.labels i g.val j = p := by
  simp [ResiduePath.activeVisits]

theorem freshTarget_birth_eq {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (i : Fin n) (g : P.BigGroup) (j : Fin (J + F.ell))
    (hj : j ∈ freshTargetSlots Q S i g) :
    ∃ stop, S g (Q.target i g.val j) = some (i.succ, stop) := by
  classical
  let ν := A.pattern (Q.pattern i)
  let p := Q.target i g.val j
  have hfresh := (Finset.mem_filter.mp hj).2
  have htarget : i.succ ∈ Q.activeVisits g p := Q.target_activeVisit i g j
  have hnotPrev : i.castSucc ∉ Q.activeVisits g p := by
    intro hprev
    obtain ⟨h, hlab⟩ := (activeVisits_iff_label Q g p i.castSucc).mp hprev
    let js := (Q.sourcePerm i g.val).symm h
    have hsource : Q.source i g.val js = Q.target i g.val j := by
      calc
        _ = Q.labels i.castSucc g.val h := by
          simp [ResiduePath.source, PrimeGroups.act, js]
        _ = p := hlab
        _ = _ := rfl
    have hhitA := Q.span_active_hit S hS i.castSucc g p hprev
    have hhitB := Q.span_active_hit S hS i.succ g p htarget
    have hdivA : (p.val : ℤ) ∣ Q.offset i.castSucc - Q.spanAnchor (S g p) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hhitA
    let kk : ℤ := if edgeForward i then A.k else -A.k
    have hstep : Q.step i = kk * (ν.D (Q.source i) (Q.free i) : ℤ) := by
      dsimp [ResiduePath.step, kk, edgeDelta]
      split_ifs <;> ring
    have hoff : Q.offset i.succ - Q.spanAnchor (S g p) =
        (Q.offset i.castSucc - Q.spanAnchor (S g p)) +
          kk * (ν.D (Q.source i) (Q.free i) : ℤ) := by
      rw [residuePath_offset_succ, hstep]
      ring
    have hdivB : (p.val : ℤ) ∣
        (Q.offset i.castSucc - Q.spanAnchor (S g p)) +
          kk * (ν.D (Q.source i) (Q.free i) : ℤ) := by
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hhitB
      rw [← hoff]
      exact h
    have hkk : ¬ (p.val : ℤ) ∣ kk := by
      dsimp [kk]
      by_cases hf : edgeForward i
      · simpa [hf] using hk g p
      · simpa [hf] using hk g p
    have hdivA' : ((Q.source i g.val js).val : ℤ) ∣
        Q.offset i.castSucc - Q.spanAnchor (S g p) := by
      rw [hsource]
      exact hdivA
    have hdivB' : ((Q.source i g.val js).val : ℤ) ∣
        (Q.offset i.castSucc - Q.spanAnchor (S g p)) +
          kk * (ν.D (Q.source i) (Q.free i) : ℤ) := by
      rw [hsource]
      exact hdivB
    have hkk' : ¬ ((Q.source i g.val js).val : ℤ) ∣ kk := by
      simpa [hsource] using hkk
    have hshared := Erdos821.S2Core.active_both_shared ν (Q.source i) (Q.target i)
      (Q.free i) (Q.source_injective hQ i) (Q.target_injective hQ i)
      (hQ.2 i).1 (hQ.2 i).2 g.val js j hsource
      (Q.offset i.castSucc - Q.spanAnchor (S g p)) kk
      hdivA' hdivB' hkk'
    exact hfresh.1 hshared.2.1
  rcases hspan : S g p with _ | ⟨birth, stop⟩
  · have hnone := hS g p
    rw [hspan] at hnone
    simp [ResiduePath.spanValid] at hnone
    exact False.elim ((Finset.ne_empty_of_mem htarget) hnone)
  · have hv := hS g p
    rw [hspan] at hv
    have hbounds := hv.2.2.1 i.succ htarget
    by_cases heq : birth = i.succ
    · exact ⟨stop, by simpa [hspan, heq]⟩
    · have hlt : birth < i.succ := lt_of_le_of_ne hbounds.1 heq
      have hltVal : birth.val < i.val + 1 := by
        have h := Fin.lt_iff_val_lt_val.mp hlt
        simpa using h
      have hlePrevVal : birth.val ≤ i.val := by omega
      have hstopLeVal : i.val + 1 ≤ stop.val := by
        have h := Fin.le_iff_val_le_val.mp hbounds.2
        simpa only [Fin.val_succ] using h
      have hltStopVal : i.val < stop.val := by omega
      have hlePrev : birth ≤ i.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        simpa using hlePrevVal
      have hltStop : i.castSucc < stop := by
        apply Fin.lt_iff_val_lt_val.mpr
        simpa using hltStopVal
      have hpending : Q.pendingAfter g p (some (birth, stop)) i.castSucc := by
        change birth ≤ i.castSucc ∧ i.castSucc < stop ∧ i.castSucc ∉ Q.activeVisits g p
        exact ⟨hlePrev, hltStop, hnotPrev⟩
      have hpendingPrime : p ∈ Q.pendingAfterPrimes S i.castSucc g := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hspan]
        exact hpending
      have hprom : j ∈ Q.promotionSlots S i g := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, ⟨hfresh.1, hpendingPrime⟩⟩
      exact False.elim (hfresh.2 hprom)

theorem active_birth_has_freshTarget {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (i : Fin n) (g : P.BigGroup) (p : P.Prime g.val) (stop : Fin (n + 1))
    (hspan : S g p = some (i.succ, stop))
    (hactive : i.succ ∈ Q.activeVisits g p) :
    ∃ j, j ∈ freshTargetSlots Q S i g ∧ Q.target i g.val j = p := by
  classical
  let ν := A.pattern (Q.pattern i)
  obtain ⟨h, hlabel⟩ := (activeVisits_iff_label Q g p i.succ).mp hactive
  let j := (Q.targetPerm i g.val).symm h
  have htarget : Q.target i g.val j = p := by
    dsimp [j, ResiduePath.target, PrimeGroups.act]
    simpa using hlabel
  have hnotShared : ¬ν.shared g.val j := by
    intro hshared
    have hcompat := (hQ.2 i).1 g.val j hshared
    have hlabel' : Q.labels i.castSucc g.val (Q.sourcePerm i g.val j) = p := by
      simpa [ResiduePath.source, PrimeGroups.act] using hcompat.trans htarget
    have hp : i.castSucc ∈ Q.activeVisits g p :=
      (activeVisits_iff_label Q g p i.castSucc).2 ⟨Q.sourcePerm i g.val j, hlabel'⟩
    have hv := hS g p
    rw [hspan] at hv
    have hpos : i.castSucc < i.succ := by
      apply Fin.lt_iff_val_lt_val.mpr
      simp
    have hbound := (hv.2.2.1 i.castSucc hp).1
    exact (not_le_of_gt hpos) hbound
  have hnotPromotion : j ∉ Q.promotionSlots S i g := by
    intro hj
    have hpending := (Finset.mem_filter.mp hj).2.2
    have hmem := (Finset.mem_filter.mp hpending).2
    rw [htarget, hspan] at hmem
    simp [ResiduePath.pendingAfter] at hmem
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, htarget⟩
  exact ⟨hnotShared, hnotPromotion⟩

theorem freshTargetSlots_image_eq {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (i : Fin n) (g : P.BigGroup) :
    ((freshTargetSlots Q S i g).image (Q.target i g.val)) =
      (Finset.univ.filter (fun p : P.Prime g.val =>
        (∃ stop, S g p = some (i.succ, stop)) ∧ i.succ ∈ Q.activeVisits g p)) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj, htarget⟩ := Finset.mem_image.mp hp
    obtain ⟨stop, hborn⟩ := freshTarget_birth_eq Q S hQ hS hk i g j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩
    · exact ⟨stop, by simpa [htarget] using hborn⟩
    · simpa [htarget] using Q.target_activeVisit i g j
  · intro hp
    obtain ⟨⟨stop, hborn⟩, hactive⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨j, hj, htarget⟩ :=
      active_birth_has_freshTarget Q S hQ hS i g p stop hborn hactive
    exact Finset.mem_image.mpr ⟨j, hj, htarget⟩

theorem freshCharge_product_eq {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (i : Fin n) (g : P.BigGroup) :
    (∏ j ∈ freshTargetSlots Q S i g,
      ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹) =
    (∏ p : P.Prime g.val,
      if (∃ stop, S g p = some (i.succ, stop)) ∧
          i.succ ∈ Q.activeVisits g p then
        (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) := by
  classical
  calc
    _ = ∏ p ∈ (freshTargetSlots Q S i g).image (Q.target i g.val),
        (p.val * baselinePrime F n p.val : ℝ)⁻¹ := by
      rw [Finset.prod_image (fun j hj k hk he => Q.target_injective hQ i g.val he)]
    _ = _ := by
      rw [freshTargetSlots_image_eq Q S hQ hS hk i g]
      symm
      simpa using (Fintype.prod_ite_mem
        (s := Finset.univ.filter (fun p : P.Prime g.val =>
          (∃ stop, S g p = some (i.succ, stop)) ∧ i.succ ∈ Q.activeVisits g p))
        (f := fun p => (p.val * baselinePrime F n p.val : ℝ)⁻¹))

theorem initialCharge_product_eq {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (hQ : Q.Valid) (g : P.BigGroup) :
    (∏ j : Fin (J + F.ell),
      ((Q.labels 0 g.val j).val * baselinePrime F n (Q.labels 0 g.val j).val : ℝ)⁻¹) =
    (∏ p : P.Prime g.val,
      if 0 ∈ Q.activeVisits g p then (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) := by
  classical
  let f := fun j : Fin (J + F.ell) => Q.labels 0 g.val j
  have himage : (Finset.univ.image f) =
      (Finset.univ.filter (fun p : P.Prime g.val => 0 ∈ Q.activeVisits g p)) := by
    ext p
    simp [f, ResiduePath.activeVisits]
  calc
    _ = ∏ p ∈ Finset.univ.image f, (p.val * baselinePrime F n p.val : ℝ)⁻¹ := by
      rw [Finset.prod_image (fun j hj k hk he => hQ.1 0 g.val he)]
    _ = _ := by
      rw [himage]
      symm
      simpa using (Fintype.prod_ite_mem
        (s := Finset.univ.filter (fun p : P.Prime g.val => 0 ∈ Q.activeVisits g p))
        (f := fun p => (p.val * baselinePrime F n p.val : ℝ)⁻¹))

theorem exists_fin_succ_eq {n : ℕ} (b : Fin (n + 1)) (hb : b ≠ 0) :
    ∃ i : Fin n, i.succ = b := by
  have hbval : 0 < b.val := by
    by_contra h
    have hz : b.val = 0 := by omega
    apply hb
    apply Fin.ext
    exact hz
  let i : Fin n := ⟨b.val - 1, by omega⟩
  refine ⟨i, ?_⟩
  apply Fin.ext
  simp only [Fin.val_succ]
  simp [i]
  omega

theorem freshBirthIndicator_product {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (g : P.BigGroup) (p : P.Prime g.val) :
    (∏ i : Fin n,
      if (∃ stop, S g p = some (i.succ, stop) ∧ i.succ ∈ Q.activeVisits g p) then
        (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) =
      if (∃ i : Fin n, ∃ stop, S g p = some (i.succ, stop) ∧
          i.succ ∈ Q.activeVisits g p) then
        (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1 := by
  classical
  have huniq (i j : Fin n)
      (hi : ∃ stop, S g p = some (i.succ, stop) ∧ i.succ ∈ Q.activeVisits g p)
      (hj : ∃ stop, S g p = some (j.succ, stop) ∧ j.succ ∈ Q.activeVisits g p) : i = j := by
    obtain ⟨s₁, hs₁, _⟩ := hi
    obtain ⟨s₂, hs₂, _⟩ := hj
    have hpair : (i.succ, s₁) = (j.succ, s₂) :=
      Option.some.inj (hs₁.symm.trans hs₂)
    have hs : i.succ = j.succ := congrArg Prod.fst hpair
    apply Fin.ext
    have hv := congrArg Fin.val hs
    simp only [Fin.val_succ] at hv
    omega
  simpa using Fintype.prod_ite_eq_ite_exists
    (fun i : Fin n => ∃ stop, S g p = some (i.succ, stop) ∧
      i.succ ∈ Q.activeVisits g p) huniq
    ((p.val * baselinePrime F n p.val : ℝ)⁻¹)

theorem initialFreshCharge_single_prime {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (hS : Q.lifespanValid S) (g : P.BigGroup) (p : P.Prime g.val) :
    (if 0 ∈ Q.activeVisits g p then (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) *
      (∏ i : Fin n,
        if (∃ stop, S g p = some (i.succ, stop)) ∧
            i.succ ∈ Q.activeVisits g p then
          (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) =
      (match S g p with
        | none => (1 : ℝ)
        | some (birth, _) => if birth ∈ Q.activeVisits g p then
            (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) := by
  classical
  have hprod := freshBirthIndicator_product Q S g p
  have hpred (i : Fin n) :
      (∃ stop, S g p = some (i.succ, stop) ∧ i.succ ∈ Q.activeVisits g p) ↔
      (∃ stop, S g p = some (i.succ, stop)) ∧ i.succ ∈ Q.activeVisits g p := by
    constructor
    · rintro ⟨stop, hs, ha⟩
      exact ⟨⟨stop, hs⟩, ha⟩
    · rintro ⟨⟨stop, hs⟩, ha⟩
      exact ⟨stop, hs, ha⟩
  have hprodOut :
      (∏ i : Fin n,
        if (∃ stop, S g p = some (i.succ, stop)) ∧
            i.succ ∈ Q.activeVisits g p then
          (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) =
      if (∃ i : Fin n, (∃ stop, S g p = some (i.succ, stop)) ∧
          i.succ ∈ Q.activeVisits g p) then
        (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1 := by
    simpa only [hpred] using hprod
  cases hspan : S g p with
  | none =>
      have hactive : Q.activeVisits g p = ∅ := by
        simpa [hspan, ResiduePath.spanValid] using hS g p
      simp [hspan, hactive]
  | some pair =>
      rcases pair with ⟨birth, stop⟩
      have hprod' :
          (∏ i : Fin n,
            if (∃ stop', some (birth, stop) = some (i.succ, stop')) ∧
                i.succ ∈ Q.activeVisits g p then
              (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) =
          if (∃ i : Fin n, (∃ stop', some (birth, stop) = some (i.succ, stop')) ∧
              i.succ ∈ Q.activeVisits g p) then
            (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1 := by
        simpa [hspan] using hprodOut
      have hvalid : Q.spanValid g p (some (birth, stop)) := by
        simpa [hspan] using hS g p
      have hborn :
          (∃ i : Fin n, ∃ stop', S g p = some (i.succ, stop') ∧
            i.succ ∈ Q.activeVisits g p) ↔
          birth ≠ 0 ∧ birth ∈ Q.activeVisits g p := by
        constructor
        · rintro ⟨i, stop', he, hi⟩
          have hpair : (birth, stop) = (i.succ, stop') :=
            Option.some.inj (hspan.symm.trans he)
          have hbirth : birth = i.succ := congrArg Prod.fst hpair
          refine ⟨?_, ?_⟩
          · intro hz
            have hv := congrArg Fin.val hbirth
            rw [hz] at hv
            simp only [Fin.val_zero, Fin.val_succ] at hv
            omega
          · simpa [hbirth] using hi
        · rintro ⟨hb, hbact⟩
          obtain ⟨i, hi⟩ := exists_fin_succ_eq birth hb
          refine ⟨i, stop, ?_, ?_⟩
          · exact hspan.trans (congrArg
              (fun b : Fin (n + 1) => some (b, stop)) hi.symm)
          · simpa [hi] using hbact
      have hborn' :
          (∃ i : Fin n, (∃ stop', some (birth, stop) = some (i.succ, stop')) ∧
            i.succ ∈ Q.activeVisits g p) ↔
          birth ≠ 0 ∧ birth ∈ Q.activeVisits g p := by
        simpa [hspan, exists_and_left] using hborn
      have hzero : 0 ∈ Q.activeVisits g p ↔ birth = 0 ∧ birth ∈ Q.activeVisits g p := by
        constructor
        · intro h0
          have hle : birth.val ≤ 0 :=
            Fin.le_iff_val_le_val.mp (hvalid.2.2.1 0 h0).1
          have hval : birth.val = 0 := Nat.eq_zero_of_le_zero hle
          have hb0 : birth = 0 := Fin.ext hval
          exact ⟨hb0, by simpa [hb0] using h0⟩
        · rintro ⟨hb, hbact⟩
          simpa [hb] using hbact
      rw [hprod']
      simp only [hzero, hborn']
      simp
      by_cases hb : birth ∈ Q.activeVisits g p <;>
        by_cases hz : birth = 0 <;> simp [hb, hz] <;> ring

theorem initialFreshCharge_product_eq {F : FixedData} {P : PrimeGroups} {J m n : ℕ}
    {A : Model F P J m} (Q : ResiduePath A n) (S : LifespanAssignment P n)
    (hQ : Q.Valid) (hS : Q.lifespanValid S)
    (hk : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, ¬ (p.val : ℤ) ∣ A.k)
    (g : P.BigGroup) :
    (∏ j : Fin (J + F.ell),
      ((Q.labels 0 g.val j).val * baselinePrime F n (Q.labels 0 g.val j).val : ℝ)⁻¹) *
      (∏ i : Fin n, ∏ j ∈ freshTargetSlots Q S i g,
        ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹) =
    (∏ p : P.Prime g.val,
      match S g p with
      | none => (1 : ℝ)
      | some (birth, _) => if birth ∈ Q.activeVisits g p then
          (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) := by
  classical
  have hinit := initialCharge_product_eq Q hQ g
  have hfresh (i : Fin n) := freshCharge_product_eq Q S hQ hS hk i g
  have hfreshProd :
      (∏ i : Fin n, ∏ j ∈ freshTargetSlots Q S i g,
        ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹) =
      (∏ i : Fin n, ∏ p : P.Prime g.val,
        if (∃ stop, S g p = some (i.succ, stop)) ∧
            i.succ ∈ Q.activeVisits g p then
          (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hfresh i
  calc
    _ = (∏ p : P.Prime g.val,
          if 0 ∈ Q.activeVisits g p then
            (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) *
        (∏ p : P.Prime g.val, ∏ i : Fin n,
          if (∃ stop, S g p = some (i.succ, stop)) ∧
              i.succ ∈ Q.activeVisits g p then
            (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) := by
      rw [hinit, hfreshProd, Finset.prod_comm]
    _ = ∏ p : P.Prime g.val,
        ((if 0 ∈ Q.activeVisits g p then
            (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) *
          ∏ i : Fin n,
            if (∃ stop, S g p = some (i.succ, stop)) ∧
                i.succ ∈ Q.activeVisits g p then
              (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) := by
      rw [← Finset.prod_mul_distrib]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      exact initialFreshCharge_single_prime Q S hS g p

theorem SpanMarkWeightTask_proof : Erdos821.S2Core.SpanMarkWeightTask := by
  intro F P J m n A Q S hQ hS hk g hV
  classical
  let initialCharge :=
    (∏ j : Fin (J + F.ell),
      ((Q.labels 0 g.val j).val * baselinePrime F n (Q.labels 0 g.val j).val : ℝ)⁻¹)
  let freshCharge :=
    (∏ i : Fin n, ∏ j ∈ freshTargetSlots Q S i g,
      ((Q.target i g.val j).val * baselinePrime F n (Q.target i g.val j).val : ℝ)⁻¹)
  let ghostFactor :=
    (∏ i : Fin (n + 1), ∏ p : P.Prime g.val, Q.spanGhostFactor S i g p)
  have hinitV :
      (∏ j : Fin (J + F.ell), tiltedMu F P n g.val (Q.labels 0 g.val j)) =
        (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ) * initialCharge := by
    calc
      _ = (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ) *
          (∏ j : Fin (J + F.ell),
            ((Q.labels 0 g.val j).val * baselinePrime F n
              (Q.labels 0 g.val j).val : ℝ)⁻¹) :=
        initialMark_factorization (F := F) (P := P) (M := J + F.ell) (n := n)
          g.val (fun j => Q.labels 0 g.val j)
      _ = _ := by
        congr 1
  have hedge (i : Fin n) :
      ((∏ j : Fin (J + F.ell),
        if (A.pattern (Q.pattern i)).shared g.val j ∨ j ∈ Q.promotionSlots S i g then 1
        else tiltedMu F P n g.val (Q.target i g.val j)) *
          (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ))) =
        (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ)) *
          (∏ j ∈ freshTargetSlots Q S i g,
            ((Q.target i g.val j).val * baselinePrime F n
              (Q.target i g.val j).val : ℝ)⁻¹) :=
    edgeFreshMark_factorization A Q S i g hV
  have hedges :
      (∏ i : Fin n,
        (∏ j : Fin (J + F.ell),
          if (A.pattern (Q.pattern i)).shared g.val j ∨
              j ∈ Q.promotionSlots S i g then 1
          else tiltedMu F P n g.val (Q.target i g.val j)) *
          (P.V g.val) ^ (-((Q.promotionSlots S i g).card : ℤ))) =
      (∏ i : Fin n,
        (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ))) * freshCharge := by
    calc
      _ = ∏ i : Fin n,
          (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ)) *
            (∏ j ∈ freshTargetSlots Q S i g,
              ((Q.target i g.val j).val * baselinePrime F n
                (Q.target i g.val j).val : ℝ)⁻¹) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hedge i
      _ = _ := by
        rw [Finset.prod_mul_distrib]
  have hcharge := initialFreshCharge_product_eq Q S hQ hS hk g
  have hscalar : initialCharge * freshCharge * ghostFactor =
      ∏ p : P.Prime g.val, Q.spanWeight g p (S g p) := by
    calc
      _ = (∏ p : P.Prime g.val,
          match S g p with
          | none => (1 : ℝ)
          | some (birth, _) => if birth ∈ Q.activeVisits g p then
              (p.val * baselinePrime F n p.val : ℝ)⁻¹ else 1) *
          (∏ i : Fin (n + 1), ∏ p : P.Prime g.val,
            Q.spanGhostFactor S i g p) := by
        unfold initialCharge freshCharge ghostFactor
        rw [hcharge]
      _ = _ := by
        rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro p hp
        exact spanWeight_scalarFactor Q S g p (hS g p)
  calc
    _ = ((P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ) * initialCharge) *
        ((∏ i : Fin n,
          (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ))) * freshCharge) *
        ghostFactor := by rw [hinitV, hedges]
    _ = (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ) *
        (∏ i : Fin n,
          (P.V g.val) ^ (-((A.pattern (Q.pattern i)).t g.val : ℤ))) *
        (initialCharge * freshCharge * ghostFactor) := by ring
    _ = _ := by rw [hscalar]

example : Erdos821.S2Core.SpanMarkWeightTask :=
  Erdos821.P3Mark.SpanMarkWeightTask_proof



end Erdos821.P3Mark
