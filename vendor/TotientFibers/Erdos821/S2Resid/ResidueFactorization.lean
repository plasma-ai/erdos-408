import Erdos821.S2.ResidueFactorizationTask

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Resid

open Erdos821.Blueprint.Graph

variable (P : PrimeGroups)

theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) :
    (∑ x : (i : ι) → α i, ∏ i, f i (x i)) = ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using
    (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) f).symm

theorem uniform_pi_average {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) :
    (Fintype.card ((i : ι) → α i) : ℝ)⁻¹ *
        ∑ x : (i : ι) → α i, ∏ i, f i (x i) =
      ∏ i, ((Fintype.card (α i) : ℝ)⁻¹ * ∑ a : α i, f i a) := by
  classical
  rw [sum_pi_prod, Fintype.card_pi, Nat.cast_prod, ← Finset.prod_inv_distrib,
    Finset.prod_mul_distrib]

theorem uniform_product_average {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α → ℝ) (g : β → ℝ) :
    (Fintype.card (α × β) : ℝ)⁻¹ *
        ∑ z : α × β, f z.1 * g z.2 =
      ((Fintype.card α : ℝ)⁻¹ * ∑ a : α, f a) *
        ((Fintype.card β : ℝ)⁻¹ * ∑ b : β, g b) := by
  classical
  have hcardA : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ‹Nonempty α›
  have hcardB : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ‹Nonempty β›
  have hsum :
      (∑ z : α × β, f z.1 * g z.2) =
        (∑ a : α, f a) * ∑ b : β, g b := by
    calc
      (∑ z : α × β, f z.1 * g z.2) =
          ∑ a : α, ∑ b : β, f a * g b := by
        rw [Fintype.sum_prod_type]
      _ = ∑ a : α, f a * ∑ b : β, g b := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.mul_sum]
      _ = (∑ a : α, f a) * ∑ b : β, g b := by
        rw [← Finset.sum_mul]
  rw [Fintype.card_prod, Nat.cast_mul, hsum]
  have hA : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcardA)
  have hB : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hcardB)
  field_simp [hA, hB]

theorem edge_product_formula (n : ℕ) (f : Fin (n + 2) → ℝ) :
    (∏ e : Fin (n + 1), f e.castSucc * f e.succ) =
      f 0 * f (Fin.last (n + 1)) * ∏ i : Fin n, f i.succ.castSucc ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htail :
        (∏ e : Fin (n + 1), f e.succ.castSucc * f e.succ.succ) =
          f 1 * f (Fin.last (n + 2)) *
            ∏ i : Fin n, f (i.succ.castSucc).succ ^ 2 := by
      have h := ih (fun i : Fin (n + 2) => f i.succ)
      calc
        (∏ e : Fin (n + 1), f e.succ.castSucc * f e.succ.succ) =
            ∏ e : Fin (n + 1), f e.castSucc.succ * f e.succ.succ := by
          apply Finset.prod_congr rfl
          intro e he
          congr 1
        _ = f 1 * f (Fin.last (n + 2)) *
              ∏ i : Fin n, f (i.succ.castSucc).succ ^ 2 := by
          simpa only [Fin.succ_zero_eq_one, Fin.succ_last] using h
    calc
      (∏ e : Fin (n + 2), f e.castSucc * f e.succ) =
          (f 0 * f 1) *
            ∏ e : Fin (n + 1), f e.succ.castSucc * f e.succ.succ := by
        rw [Fin.prod_univ_succ]
        simp
      _ = (f 0 * f 1) *
            (f 1 * f (Fin.last (n + 2)) *
              ∏ i : Fin n, f (i.succ.castSucc).succ ^ 2) := by
        rw [htail]
      _ = f 0 * f (Fin.last (n + 2)) *
            ∏ i : Fin (n + 1), f i.succ.castSucc ^ 2 := by
        rw [Fin.prod_univ_succ]
        have hOne : (Fin.succ (0 : Fin (n + 1))).castSucc =
            Fin.succ (0 : Fin (n + 2)) := by
          apply Fin.ext
          rfl
        have hidx (i : Fin n) : i.succ.castSucc.succ = i.succ.succ.castSucc := by
          apply Fin.ext
          rfl
        have hprod :
            (∏ i : Fin n, f i.succ.castSucc.succ ^ 2) =
              ∏ i : Fin n, f i.succ.succ.castSucc ^ 2 := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hidx i]
        rw [hOne, hprod]
        simp only [Fin.succ_zero_eq_one]
        ring_nf

theorem zmod_finEquiv_val {p : ℕ} [NeZero p] (z : Fin p) :
    ZMod.finEquiv p z = (z.val : ZMod p) := by
  cases p with
  | zero => exact Fin.elim0 z
  | succ n => exact (Fin.cast_val_eq_self z).symm

def pointResidueFactor {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (p : ℕ) (r : ZMod p) : ℝ :=
  ∏ i : Fin (n + 1),
    if p ∈ active i then (if r + (h i : ZMod p) = 0 then 1 else 0)
    else if r + (h i : ZMod p) = 0 then q i else 1

def onePrimePointFactor {n p : ℕ} (eta : Fin n → ℝ)
    (h : Fin n → ZMod p) (active : Finset (Fin n)) (r : ZMod p) : ℝ :=
  ∏ i : Fin n,
    if i ∈ active then (if r + h i = 0 then 1 else 0)
    else 1 - eta i * (if r + h i = 0 then 1 else 0)

theorem pointResidueFactor_fin {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    {p : ℕ} [NeZero p] (z : Fin p) :
    pointResidueFactor q h active p (ZMod.finEquiv p z) =
      ∏ i : Fin (n + 1),
        if p ∈ active i then (if (p : ℤ) ∣ (z.val : ℤ) + h i then 1 else 0)
        else if (p : ℤ) ∣ (z.val : ℤ) + h i then q i else 1 := by
  classical
  unfold pointResidueFactor
  apply Finset.prod_congr rfl
  intro i hi
  have hcast : ((z.val : ℤ) + h i : ZMod p) =
      (z.val : ZMod p) + (h i : ZMod p) := by
    simp [Int.cast_add, Int.cast_natCast]
  have hhit : ZMod.finEquiv p z + (h i : ZMod p) = 0 ↔
      (p : ℤ) ∣ (z.val : ℤ) + h i := by
    rw [zmod_finEquiv_val, ← hcast]
    simpa only [Int.cast_add] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((z.val : ℤ) + h i) p)
  by_cases ha : p ∈ active i <;> simp [ha, hhit]

def globalPrime (g : P.Group) (p : P.Prime g) : P.GroupPrime :=
  ⟨p.val, by
    change p.val ∈ Finset.univ.biUnion P.primes
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, p.property⟩⟩

noncomputable def groupOfPrime (p : P.GroupPrime) : P.Group := by
  classical
  let hp : ∃ g : P.Group, p.val ∈ P.primes g := by
    rcases Finset.mem_biUnion.mp p.property with ⟨g, _, hg⟩
    exact ⟨g, hg⟩
  exact Classical.choose hp

theorem groupOfPrime_spec (p : P.GroupPrime) :
    p.val ∈ P.primes (groupOfPrime P p) := by
  classical
  exact Classical.choose_spec (show ∃ g : P.Group, p.val ∈ P.primes g from by
    rcases Finset.mem_biUnion.mp p.property with ⟨g, _, hg⟩
    exact ⟨g, hg⟩)

theorem groupOfPrime_eq (p : P.GroupPrime) (g : P.Group) (hp : p.val ∈ P.primes g) :
    groupOfPrime P p = g := by
  classical
  by_contra hne
  have hd := P.disjoint (groupOfPrime P p) g hne
  exact (Finset.disjoint_left.mp hd) (groupOfPrime_spec P p) hp

noncomputable def groupPrimeEquiv : P.GroupPrime ≃ Σ g : P.Group, P.Prime g where
  toFun p := ⟨groupOfPrime P p, ⟨p.val, groupOfPrime_spec P p⟩⟩
  invFun gp := globalPrime P gp.1 gp.2
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv gp := by
    rcases gp with ⟨g, p⟩
    let q : P.GroupPrime := globalPrime P g p
    have hg : groupOfPrime P q = g := groupOfPrime_eq P q g p.property
    apply Sigma.mk.inj_iff.mpr
    refine ⟨hg, ?_⟩
    apply (Subtype.heq_iff_coe_eq (by
      intro x
      have hiff := congrArg (fun k : P.Group => x ∈ P.primes k) hg
      exact ⟨hiff.mp, hiff.mpr⟩)).2
    rfl

abbrev GroupResidues := (g : P.Group) → (p : P.Prime g) → ZMod p.val
abbrev BigGroupResidues := (g : P.BigGroup) → (p : P.Prime g.val) → ZMod p.val

def groupResiduePathFactor {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (r : GroupResidues P) : ℝ :=
  ∏ g : P.Group, ∏ p : P.Prime g, pointResidueFactor q h active p.val (r g p)

theorem active_mem_iff {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (g : P.BigGroup) (p : P.Prime g.val) (i : Fin (n + 1)) :
    p.val ∈ Q.active i ↔ i ∈ Q.activeVisits g p := by
  classical
  constructor
  · intro hp
    obtain ⟨g', -, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hp
    have hgroup : g' = g.val := by
      by_contra hne
      have hd := P.disjoint g' g.val hne
      have h₁ : p.val ∈ P.primes g' := by
        rw [← hj]
        exact (Q.labels i g' j).property
      exact (Finset.disjoint_left.mp hd) h₁ p.property
    subst g'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change ∃ j' : Fin (J + F.ell), Q.labels i g.val j' = p
    refine ⟨j, ?_⟩
    exact Subtype.ext hj
  · intro hi
    have hi' : ∃ j : Fin (J + F.ell), Q.labels i g.val j = p := by
      simpa [Erdos821.S2Core.ResiduePath.activeVisits] using hi
    obtain ⟨j, hj⟩ := hi'
    apply Finset.mem_biUnion.mpr
    refine ⟨g.val, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val hj

theorem pointResidueFactor_eq_onePrimePointFactor {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (g : P.BigGroup) (p : P.Prime g.val) (r : ZMod p.val) :
    pointResidueFactor (visitQ F.q n) Q.offset Q.active p.val r =
      onePrimePointFactor (eta F n) (fun i => (Q.offset i : ZMod p.val))
        (Q.activeVisits g p) r := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have hactive := active_mem_iff P Q g p i
  by_cases ha : p.val ∈ Q.active i
  · have hv : i ∈ Q.activeVisits g p := hactive.mp ha
    by_cases hh : r + (Q.offset i : ZMod p.val) = 0 <;>
      simp [pointResidueFactor, onePrimePointFactor, ha, hv, hh]
  · have hv : i ∉ Q.activeVisits g p := fun hi => ha (hactive.mpr hi)
    by_cases hh : r + (Q.offset i : ZMod p.val) = 0 <;>
      simp [pointResidueFactor, onePrimePointFactor, ha, hv, hh, eta] <;> ring

noncomputable def primeCoordinateEquiv (p : P.GroupPrime) :
    Fin p.val ≃ ZMod ((groupPrimeEquiv P p).2.val) := by
    let g := groupOfPrime P p
    let hp : P.Prime g := ⟨p.val, groupOfPrime_spec P p⟩
    letI := P.primeNeZero g hp
    exact (ZMod.finEquiv p.val).toEquiv

noncomputable def residuesEquivSigma : P.Residues ≃
    ((gp : Σ g : P.Group, P.Prime g) → ZMod gp.2.val) :=
  (groupPrimeEquiv P).piCongr (primeCoordinateEquiv P)

noncomputable def residuesEquivGroup : P.Residues ≃ GroupResidues P :=
  (residuesEquivSigma P).trans
    (Equiv.piCurry (fun (g : P.Group) (p : P.Prime g) => ZMod p.val))

theorem residuesEquivSigma_apply (y : P.Residues) (p : P.GroupPrime) :
    residuesEquivSigma P y (groupPrimeEquiv P p) = primeCoordinateEquiv P p (y p) := by
  simpa [residuesEquivSigma] using
    (Equiv.piCongr_apply_apply
      (Z := fun gp : Σ g : P.Group, P.Prime g => ZMod gp.2.val)
      (groupPrimeEquiv P) (primeCoordinateEquiv P) y p)

theorem residuesEquivGroup_apply (y : P.Residues) (g : P.Group) (p : P.Prime g) :
    residuesEquivGroup P y g p = residuesEquivSigma P y ⟨g, p⟩ := by
  rfl

theorem groupResiduePathFactor_eq_residuePathFactor {n : ℕ}
    (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (y : P.Residues) :
    groupResiduePathFactor P q h active (residuesEquivGroup P y) =
      P.residuePathFactor n q h active y := by
  classical
  unfold groupResiduePathFactor
  rw [← Fintype.prod_sigma']
  calc
    (∏ gp : Σ g : P.Group, P.Prime g,
        pointResidueFactor q h active gp.2.val
          (residuesEquivGroup P y gp.1 gp.2)) =
        ∏ gp : Σ g : P.Group, P.Prime g,
          pointResidueFactor q h active gp.2.val (residuesEquivSigma P y gp) := by
      apply Finset.prod_congr rfl
      intro gp hgp
      rw [residuesEquivGroup_apply]
    _ = ∏ p : P.GroupPrime,
          pointResidueFactor q h active p.val
            (residuesEquivSigma P y (groupPrimeEquiv P p)) := by
      exact ((groupPrimeEquiv P).prod_comp
        (fun gp : Σ g : P.Group, P.Prime g =>
          pointResidueFactor q h active gp.2.val (residuesEquivSigma P y gp))).symm
    _ = ∏ p : P.GroupPrime,
          pointResidueFactor q h active p.val
            (primeCoordinateEquiv P p (y p)) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [residuesEquivSigma_apply]
    _ = P.residuePathFactor n q h active y := by
      unfold PrimeGroups.residuePathFactor
      apply Finset.prod_congr rfl
      intro p hp
      let gp := groupPrimeEquiv P p
      letI : NeZero p.val := ⟨(P.prime gp.1 gp.2.val gp.2.property).ne_zero⟩
      change pointResidueFactor q h active p.val
        (ZMod.finEquiv p.val (y p)) = _
      exact pointResidueFactor_fin q h active (p := p.val) (z := y p)

noncomputable def groupResiduesSplit : GroupResidues P ≃
    P.SmallResidues × BigGroupResidues P where
  toFun r := (fun g p => r g.val p, fun g p => r g.val p)
  invFun z g p := by
    by_cases hb : P.big g = false
    · exact z.1 ⟨g, hb⟩ p
    · have ht : P.big g = true := by
        cases h : P.big g <;> simp_all
      exact z.2 ⟨g, ht⟩ p
  left_inv r := by
    funext g
    funext p
    by_cases hb : P.big g = false
    · simp [hb]
    · have ht : P.big g = true := by
        cases h : P.big g <;> simp_all
      simp [hb]
  right_inv z := by
    rcases z with ⟨s, b⟩
    apply Prod.ext
    · funext g
      funext p
      simp [g.property]
    · funext g
      funext p
      simp [g.property]

noncomputable def groupSplitEquiv : P.Group ≃ P.SmallGroup ⊕ P.BigGroup where
  toFun g := by
    by_cases hg : P.big g = false
    · exact Sum.inl ⟨g, hg⟩
    · have ht : P.big g = true := by
        cases h : P.big g <;> simp_all
      exact Sum.inr ⟨g, ht⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv g := by
    by_cases hg : P.big g = false
    · simp [hg]
    · have ht : P.big g = true := by
        cases h : P.big g <;> simp_all
      simp [hg]
  right_inv s := by
    cases s with
    | inl g => simp [g.property]
    | inr g => simp [g.property]

def smallResiduePathFactor {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (s : P.SmallResidues) : ℝ :=
  ∏ g : P.SmallGroup, ∏ p : P.Prime g.val,
    pointResidueFactor q h active p.val (s g p)

def smallActiveLabelSet {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (i : Fin (n + 1)) (g : P.SmallGroup) : Finset (P.Prime g.val) :=
  Finset.univ.image (fun j : Fin (J + F.ell) => Q.labels i g.val j)

def smallHitSet {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (y : P.SmallResidues) (i : Fin (n + 1)) (g : P.SmallGroup) :
    Finset (P.Prime g.val) :=
  Finset.univ.filter (fun p =>
    Erdos821.S2Core.translateSmallResidues (Q.offset i) y g p = 0)

def smallGroupVisitFactor {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (y : P.SmallResidues) (i : Fin (n + 1)) (g : P.SmallGroup) : ℝ :=
  ∏ p : P.Prime g.val,
    if p.val ∈ Q.active i then
      (if Erdos821.S2Core.translateSmallResidues (Q.offset i) y g p = 0 then 1 else 0)
    else if Erdos821.S2Core.translateSmallResidues (Q.offset i) y g p = 0 then
      visitQ F.q n i else 1

theorem active_mem_iff_smallActiveLabelSet {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (i : Fin (n + 1)) (g : P.SmallGroup) (p : P.Prime g.val) :
    p.val ∈ Q.active i ↔ p ∈ smallActiveLabelSet P Q i g := by
  classical
  constructor
  · intro hp
    obtain ⟨g', -, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hp
    have hgroup : g' = g.val := by
      by_contra hne
      have hd := P.disjoint g' g.val hne
      have h₁ : p.val ∈ P.primes g' := by
        rw [← hj]
        exact (Q.labels i g' j).property
      exact (Finset.disjoint_left.mp hd) h₁ p.property
    subst g'
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    exact Subtype.ext hj
  · intro hp
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hp
    apply Finset.mem_biUnion.mpr
    refine ⟨g.val, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩

theorem smallCompatible_iff_labels_hit {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (y : P.SmallResidues) :
    Q.SmallCompatible y ↔
      ∀ i (g : P.SmallGroup) (j : Fin (J + F.ell)),
        Erdos821.S2Core.translateSmallResidues (Q.offset i) y g (Q.labels i g.val j) = 0 := by
  constructor
  · intro hy i g j
    exact (hy i g).2 j
  · intro hh i g
    exact ⟨hq.1 i g.val, hh i g⟩

theorem smallGroupVisitFactor_eq_pow {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (y : P.SmallResidues) (hcompat : Q.SmallCompatible y)
    (i : Fin (n + 1)) (g : P.SmallGroup) :
    smallGroupVisitFactor P Q y i g =
      (visitQ F.q n i) ^
        ((smallHitSet P Q y i g \ smallActiveLabelSet P Q i g).card) := by
  classical
  let T := smallActiveLabelSet P Q i g
  let U := smallHitSet P Q y i g
  have hTU : T ⊆ U := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (smallCompatible_iff_labels_hit P Q hq y).mp hcompat i g j⟩
  have hfactor : smallGroupVisitFactor P Q y i g =
      ∏ p : P.Prime g.val, if p ∈ U \ T then visitQ F.q n i else 1 := by
    unfold smallGroupVisitFactor
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hT : p ∈ T
    · have hA : p.val ∈ Q.active i :=
        (active_mem_iff_smallActiveLabelSet P Q i g p).2 hT
      have hU : p ∈ U := hTU hT
      have hhit := (Finset.mem_filter.mp hU).2
      simp [T, U, hA, hU, hT, hhit]
    · have hA : p.val ∉ Q.active i := fun hA => hT
        ((active_mem_iff_smallActiveLabelSet P Q i g p).1 hA)
      by_cases hU : p ∈ U
      · have hhit := (Finset.mem_filter.mp hU).2
        simp [T, U, hA, hU, hT, hhit]
      · by_cases hzero :
          Erdos821.S2Core.translateSmallResidues (Q.offset i) y g p = 0
        · exact False.elim (hU
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩))
        · simp [T, U, hA, hU, hT, hzero]
  rw [hfactor, Fintype.prod_ite_mem]
  exact Finset.prod_eq_pow_card (by intro p hp; rfl)

theorem smallOmega_eq_active_plus_unmarked {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (y : P.SmallResidues) (hcompat : Q.SmallCompatible y)
    (i : Fin (n + 1)) :
    Erdos821.S2Core.smallOmega (Erdos821.S2Core.translateSmallResidues (Q.offset i) y) =
      (J + F.ell) * Fintype.card P.SmallGroup +
        ∑ g : P.SmallGroup,
          (smallHitSet P Q y i g \ smallActiveLabelSet P Q i g).card := by
  classical
  let T : (g : P.SmallGroup) → Finset (P.Prime g.val) := fun g =>
    smallActiveLabelSet P Q i g
  let U : (g : P.SmallGroup) → Finset (P.Prime g.val) := fun g =>
    smallHitSet P Q y i g
  have hTU (g : P.SmallGroup) : T g ⊆ U g := by
    intro p hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (smallCompatible_iff_labels_hit P Q hq y).mp hcompat i g j⟩
  have hcardT (g : P.SmallGroup) : (T g).card = J + F.ell := by
    dsimp [T, smallActiveLabelSet]
    rw [Finset.card_image_of_injective _ (hq.1 i g.val)]
    simp
  calc
    Erdos821.S2Core.smallOmega (Erdos821.S2Core.translateSmallResidues (Q.offset i) y) =
        ∑ g : P.SmallGroup, (U g).card := by
      simp [Erdos821.S2Core.smallOmega, U, smallHitSet,
        Erdos821.S2Core.translateSmallResidues]
    _ = (∑ g : P.SmallGroup, (T g).card) +
          ∑ g : P.SmallGroup, (U g \ T g).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g hg
      have hc := Finset.card_sdiff_add_card_eq_card (hTU g)
      omega
    _ = (J + F.ell) * Fintype.card P.SmallGroup +
          ∑ g : P.SmallGroup, (U g \ T g).card := by
      have hsum : (∑ g : P.SmallGroup, (T g).card) =
          Fintype.card P.SmallGroup * (J + F.ell) := by
        simp [hcardT]
      rw [hsum]
      congr 1
      exact Nat.mul_comm _ _

def smallVisitPathFactor {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (y : P.SmallResidues) (i : Fin (n + 1)) : ℝ :=
  ∏ g : P.SmallGroup, smallGroupVisitFactor P Q y i g

theorem smallVisitPathFactor_eq_pow {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (y : P.SmallResidues) (hcompat : Q.SmallCompatible y)
    (i : Fin (n + 1)) :
    smallVisitPathFactor P Q y i =
      (visitQ F.q n i) ^
        (∑ g : P.SmallGroup,
          (smallHitSet P Q y i g \ smallActiveLabelSet P Q i g).card) := by
  classical
  unfold smallVisitPathFactor
  calc
    (∏ g : P.SmallGroup, smallGroupVisitFactor P Q y i g) =
        ∏ g : P.SmallGroup, (visitQ F.q n i) ^
          (smallHitSet P Q y i g \ smallActiveLabelSet P Q i g).card := by
      apply Finset.prod_congr rfl
      intro g hg
      exact smallGroupVisitFactor_eq_pow P Q hq y hcompat i g
    _ = (visitQ F.q n i) ^
          (∑ g : P.SmallGroup,
            (smallHitSet P Q y i g \ smallActiveLabelSet P Q i g).card) := by
      simpa using
        (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset P.SmallGroup)
          (fun g => (smallHitSet P Q y i g \ smallActiveLabelSet P Q i g).card)
          (visitQ F.q n i))

theorem smallResiduePathFactor_eq_visitProduct {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (y : P.SmallResidues) :
    smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active y =
      ∏ i : Fin (n + 1), smallVisitPathFactor P Q y i := by
  classical
  unfold smallResiduePathFactor smallVisitPathFactor smallGroupVisitFactor
    pointResidueFactor
  let f : (g : P.SmallGroup) → (p : P.Prime g.val) → Fin (n + 1) → ℝ :=
    fun g p i =>
      if p.val ∈ Q.active i then
        if Erdos821.S2Core.translateSmallResidues (Q.offset i) y g p = 0 then 1 else 0
      else if Erdos821.S2Core.translateSmallResidues (Q.offset i) y g p = 0 then
        visitQ F.q n i else 1
  change (∏ g : P.SmallGroup, ∏ p : P.Prime g.val, ∏ i : Fin (n + 1), f g p i) =
    ∏ i : Fin (n + 1), ∏ g : P.SmallGroup, ∏ p : P.Prime g.val, f g p i
  calc
    (∏ g : P.SmallGroup, ∏ p : P.Prime g.val, ∏ i : Fin (n + 1), f g p i) =
        ∏ k : Σ g : P.SmallGroup, P.Prime g.val, ∏ i : Fin (n + 1), f k.1 k.2 i := by
          rw [← Fintype.prod_sigma']
    _ = ∏ i : Fin (n + 1), ∏ k : Σ g : P.SmallGroup, P.Prime g.val,
          f k.1 k.2 i := by
      exact Finset.prod_comm
    _ = ∏ i : Fin (n + 1), ∏ g : P.SmallGroup, ∏ p : P.Prime g.val, f g p i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Fintype.prod_sigma']

theorem smallDamping_eq_unmarked_rpow {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (y : P.SmallResidues) (hcompat : Q.SmallCompatible y)
    (i : Fin (n + 1)) :
    Erdos821.S2Core.smallDamping F J
        (Erdos821.S2Core.translateSmallResidues (Q.offset i) y) =
      F.q ^ (((∑ g : P.SmallGroup,
        (smallHitSet P Q y i g \ smallActiveLabelSet P Q i g).card : ℕ) : ℝ) / 2) := by
  unfold Erdos821.S2Core.smallDamping
  rw [smallOmega_eq_active_plus_unmarked P Q hq y hcompat i]
  congr 1
  push_cast
  ring

theorem rpow_half_nat_sq (q : ℝ) (hq : 0 ≤ q) (k : ℕ) :
    (q ^ ((k : ℝ) / 2)) ^ 2 = q ^ k := by
  rw [← Real.rpow_natCast q k,
    ← Real.rpow_natCast (q ^ ((k : ℝ) / 2)) 2,
    ← Real.rpow_mul hq]
  congr 1
  ring

theorem sqrt_nat_pow_eq_rpow_half (q : ℝ) (hq : 0 ≤ q) (k : ℕ) :
    (Real.sqrt q) ^ k = q ^ ((k : ℝ) / 2) := by
  rw [← Real.rpow_natCast (Real.sqrt q) k, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hq]
  congr 1
  ring

theorem prod_fin_endpoints (m : ℕ) {α : Type*} [CommMonoid α]
    (f : Fin (m + 2) → α) :
    (∏ i : Fin (m + 2), f i) =
      f 0 * f (Fin.last (m + 1)) * ∏ i : Fin m, f i.succ.castSucc := by
  have hprod :
      (∏ i : Fin m, f i.castSucc.succ) = ∏ i : Fin m, f i.succ.castSucc := by
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
  have hlast : (Fin.last m).succ = Fin.last (m + 1) := by
    apply Fin.ext
    rfl
  calc
    (∏ i : Fin (m + 2), f i) =
        f 0 * ∏ i : Fin (m + 1), f i.succ := by
      rw [Fin.prod_univ_succ]
    _ = f 0 * ((∏ i : Fin m, f i.castSucc.succ) * f (Fin.last m).succ) := by
      rw [Fin.prod_univ_castSucc]
    _ = f 0 * f (Fin.last (m + 1)) * ∏ i : Fin m, f i.succ.castSucc := by
      rw [hprod, hlast]
      ac_rfl

theorem visit_power_prod_eq_edge_half (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (hn : 0 < n)
    (c : Fin (n + 1) → ℕ) :
    (∏ i : Fin (n + 1), (visitQ q n i) ^ c i) =
      ∏ e : Fin n,
        q ^ ((c e.castSucc : ℝ) / 2) * q ^ ((c e.succ : ℝ) / 2) := by
  cases n with
  | zero => omega
  | succ m =>
    let f : Fin (m + 2) → ℝ := fun i => q ^ ((c i : ℝ) / 2)
    have hvisit :
        (∏ i : Fin (m + 2), (visitQ q (m + 1) i) ^ c i) =
          f 0 * f (Fin.last (m + 1)) *
            ∏ i : Fin m, f i.succ.castSucc ^ 2 := by
      rw [prod_fin_endpoints m (fun i => (visitQ q (m + 1) i) ^ c i)]
      have hzero : visitQ q (m + 1) (0 : Fin (m + 2)) = Real.sqrt q := by
        simp [visitQ]
      have hlast : visitQ q (m + 1) (Fin.last (m + 1)) = Real.sqrt q := by
        simp [visitQ]
      have hinterior (i : Fin m) :
          visitQ q (m + 1) i.succ.castSucc = q := by
        have hne : i.val ≠ m := by omega
        simp [visitQ, hne]
      have hmiddle :
          (∏ i : Fin m, q ^ c (i.succ.castSucc)) =
            ∏ i : Fin m, (q ^ ((c (i.succ.castSucc) : ℝ) / 2)) ^ 2 := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (rpow_half_nat_sq q hq (c (i.succ.castSucc))).symm
      simp_rw [hinterior]
      rw [hmiddle]
      have hzero' := sqrt_nat_pow_eq_rpow_half q hq (c (0 : Fin (m + 2)))
      have hlast' := sqrt_nat_pow_eq_rpow_half q hq (c (Fin.last (m + 1)))
      dsimp [f]
      rw [hzero, hlast, hzero', hlast']
    have hedge := edge_product_formula m f
    calc
      (∏ i : Fin (m + 2), (visitQ q (m + 1) i) ^ c i) =
          f 0 * f (Fin.last (m + 1)) * ∏ i : Fin m, f i.succ.castSucc ^ 2 := hvisit
      _ = ∏ e : Fin (m + 1),
            q ^ ((c e.castSucc : ℝ) / 2) * q ^ ((c e.succ : ℝ) / 2) := by
        simpa [f] using hedge.symm

theorem smallResiduePathFactor_eq_edgeDamping {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (y : P.SmallResidues) (hcompat : Q.SmallCompatible y)
    (hn : 0 < n) :
    smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active y =
      ∏ e : Fin n,
        Erdos821.S2Core.smallDamping F J
          (Erdos821.S2Core.translateSmallResidues (Q.offset e.castSucc) y) *
        Erdos821.S2Core.smallDamping F J
          (Erdos821.S2Core.translateSmallResidues (Q.offset e.succ) y) := by
  rw [smallResiduePathFactor_eq_visitProduct P Q y]
  simp_rw [smallVisitPathFactor_eq_pow P Q hq y hcompat]
  simp_rw [smallDamping_eq_unmarked_rpow P Q hq y hcompat]
  exact visit_power_prod_eq_edge_half F.q (le_of_lt F.q_pos) n hn _

theorem smallResiduePathFactor_eq_zero_of_not_compatible {F : FixedData}
    {J m n : ℕ} {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (y : P.SmallResidues) (hbad : ¬ Q.SmallCompatible y) :
    smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active y = 0 := by
  classical
  have hnot : ¬ ∀ i (g : P.SmallGroup) (j : Fin (J + F.ell)),
      Erdos821.S2Core.translateSmallResidues (Q.offset i) y g (Q.labels i g.val j) = 0 := by
    intro hh
    exact hbad ((smallCompatible_iff_labels_hit P Q hq y).2 hh)
  push Not at hnot
  obtain ⟨i, g, j, hres⟩ := hnot
  let p : P.Prime g.val := Q.labels i g.val j
  have hactive : p.val ∈ Q.active i := by
    apply Finset.mem_biUnion.mpr
    refine ⟨g.val, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_univ _, rfl⟩
  have hhit : y g p + (Q.offset i : ZMod p.val) ≠ 0 := by
    simpa [Erdos821.S2Core.translateSmallResidues, p] using hres
  have hlocal : pointResidueFactor (visitQ F.q n) Q.offset Q.active p.val (y g p) = 0 := by
    unfold pointResidueFactor
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hactive, hhit]
  unfold smallResiduePathFactor
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  exact hlocal

theorem smallResiduePathFactor_eq_compatible_edgeDamping {F : FixedData}
    {J m n : ℕ} {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (hn : 0 < n) (y : P.SmallResidues) :
    smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active y =
      if Q.SmallCompatible y then
        ∏ e : Fin n,
          Erdos821.S2Core.smallDamping F J
            (Erdos821.S2Core.translateSmallResidues (Q.offset e.castSucc) y) *
          Erdos821.S2Core.smallDamping F J
            (Erdos821.S2Core.translateSmallResidues (Q.offset e.succ) y)
      else 0 := by
  by_cases hcompat : Q.SmallCompatible y
  · simp [hcompat, smallResiduePathFactor_eq_edgeDamping P Q hq y hcompat hn]
  · simp [hcompat, smallResiduePathFactor_eq_zero_of_not_compatible P Q hq y hcompat]

theorem smallResidueAverage_eq_smallResidueExpression {F : FixedData}
    {J m n : ℕ} {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (hq : Q.Valid) (hn : 0 < n) :
    (Fintype.card P.SmallResidues : ℝ)⁻¹ *
        ∑ y : P.SmallResidues,
          smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active y =
      Q.smallResidueExpression := by
  unfold Erdos821.S2Core.ResiduePath.smallResidueExpression
  simp_rw [smallResiduePathFactor_eq_compatible_edgeDamping P Q hq hn]

def bigGroupResiduePathFactor {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (b : BigGroupResidues P) : ℝ :=
  ∏ g : P.BigGroup, ∏ p : P.Prime g.val,
    pointResidueFactor q h active p.val (b g p)

abbrev BigResidueCoords :=
  (gp : Σ g : P.BigGroup, P.Prime g.val) → ZMod gp.2.val

noncomputable def bigResidueCoordsEquiv : BigGroupResidues P ≃ BigResidueCoords P :=
  (Equiv.piCurry (fun (g : P.BigGroup) (p : P.Prime g.val) => ZMod p.val)).symm

def bigCoordinatePathFactor {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (b : BigResidueCoords P) : ℝ :=
  ∏ gp : Σ g : P.BigGroup, P.Prime g.val,
    pointResidueFactor q h active gp.2.val (b gp)

theorem bigGroupPathFactor_eq_coords {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (b : BigGroupResidues P) :
    bigGroupResiduePathFactor P q h active b =
      bigCoordinatePathFactor P q h active (bigResidueCoordsEquiv P b) := by
  classical
  unfold bigGroupResiduePathFactor bigCoordinatePathFactor
  rw [← Fintype.prod_sigma']
  apply Finset.prod_congr rfl
  intro gp hgp
  rfl

theorem bigLocalAverage_eq_onePrimeExpectation {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n)
    (g : P.BigGroup) (p : P.Prime g.val) :
    (Fintype.card (ZMod p.val) : ℝ)⁻¹ *
        ∑ r : ZMod p.val,
          pointResidueFactor (visitQ F.q n) Q.offset Q.active p.val r =
      Erdos821.S2Core.onePrimeExpectation p.val (n + 1) (eta F n)
        (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) := by
  classical
  letI := P.primeNeZero g.val p
  rw [ZMod.card]
  unfold Erdos821.S2Core.onePrimeExpectation
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simpa [onePrimePointFactor] using
    (pointResidueFactor_eq_onePrimePointFactor P Q g p r)

theorem bigResidueExpectation_eq_product {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n) :
    (Fintype.card (BigGroupResidues P) : ℝ)⁻¹ *
        ∑ b : BigGroupResidues P,
          bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active b =
      ∏ g : P.BigGroup, ∏ p : P.Prime g.val,
        Erdos821.S2Core.onePrimeExpectation p.val (n + 1) (eta F n)
          (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) := by
  classical
  let e := bigResidueCoordsEquiv P
  calc
    (Fintype.card (BigGroupResidues P) : ℝ)⁻¹ *
        ∑ b : BigGroupResidues P,
          bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active b =
      (Fintype.card (BigResidueCoords P) : ℝ)⁻¹ *
        ∑ c : BigResidueCoords P,
          bigCoordinatePathFactor P (visitQ F.q n) Q.offset Q.active c := by
        rw [Fintype.card_congr e]
        congr 1
        exact Fintype.sum_equiv e
          (fun b => bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active b)
          (fun c => bigCoordinatePathFactor P (visitQ F.q n) Q.offset Q.active c)
          (fun b => bigGroupPathFactor_eq_coords P (visitQ F.q n) Q.offset Q.active b)
    _ = ∏ gp : Σ g : P.BigGroup, P.Prime g.val,
          ((Fintype.card (ZMod gp.2.val) : ℝ)⁻¹ *
            ∑ r : ZMod gp.2.val,
              pointResidueFactor (visitQ F.q n) Q.offset Q.active gp.2.val r) := by
        simpa [bigCoordinatePathFactor] using
          (uniform_pi_average
            (ι := Σ g : P.BigGroup, P.Prime g.val)
            (α := fun gp => ZMod gp.2.val)
            (fun gp r => pointResidueFactor (visitQ F.q n) Q.offset Q.active gp.2.val r))
    _ = ∏ g : P.BigGroup, ∏ p : P.Prime g.val,
          ((Fintype.card (ZMod p.val) : ℝ)⁻¹ *
            ∑ r : ZMod p.val,
              pointResidueFactor (visitQ F.q n) Q.offset Q.active p.val r) :=
        Fintype.prod_sigma'
          (fun (g : P.BigGroup) (p : P.Prime g.val) =>
            (Fintype.card (ZMod p.val) : ℝ)⁻¹ *
              ∑ r : ZMod p.val,
                pointResidueFactor (visitQ F.q n) Q.offset Q.active p.val r)
    _ = ∏ g : P.BigGroup, ∏ p : P.Prime g.val,
          Erdos821.S2Core.onePrimeExpectation p.val (n + 1) (eta F n)
            (fun i => (Q.offset i : ZMod p.val)) (Q.activeVisits g p) := by
        apply Finset.prod_congr rfl
        intro g hg
        apply Finset.prod_congr rfl
        intro p hp
        exact bigLocalAverage_eq_onePrimeExpectation P Q g p

theorem groupResiduePathFactor_split {n : ℕ} (q : Fin (n + 1) → ℝ)
    (h : Fin (n + 1) → ℤ) (active : Fin (n + 1) → Finset ℕ)
    (s : P.SmallResidues) (b : BigGroupResidues P) :
    groupResiduePathFactor P q h active ((groupResiduesSplit P).symm (s, b)) =
      smallResiduePathFactor P q h active s * bigGroupResiduePathFactor P q h active b := by
  classical
  let fs : P.SmallGroup → ℝ := fun g =>
    ∏ p : P.Prime g.val, pointResidueFactor q h active p.val (s g p)
  let fb : P.BigGroup → ℝ := fun g =>
    ∏ p : P.Prime g.val, pointResidueFactor q h active p.val (b g p)
  calc
    groupResiduePathFactor P q h active ((groupResiduesSplit P).symm (s, b)) =
        ∏ g : P.Group, Sum.elim fs fb (groupSplitEquiv P g) := by
      unfold groupResiduePathFactor
      apply Finset.prod_congr rfl
      intro g hg
      cases hg' : P.big g with
      | false => simp [groupSplitEquiv, groupResiduesSplit, hg', fs]
      | true => simp [groupSplitEquiv, groupResiduesSplit, hg', fb]
    _ = ∏ x : P.SmallGroup ⊕ P.BigGroup, Sum.elim fs fb x :=
      (groupSplitEquiv P).prod_comp (Sum.elim fs fb)
    _ = smallResiduePathFactor P q h active s * bigGroupResiduePathFactor P q h active b := by
      simp [smallResiduePathFactor, bigGroupResiduePathFactor, fs, fb,
        Fintype.prod_sum_type]

theorem residueExpectation_eq_smallBigAverages {F : FixedData} {J m n : ℕ}
    {A : Model F P J m} (Q : Erdos821.S2Core.ResiduePath A n) :
    P.residueExpectation n (visitQ F.q n) Q.offset Q.active =
      ((Fintype.card P.SmallResidues : ℝ)⁻¹ *
        ∑ s : P.SmallResidues,
          smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active s) *
      ((Fintype.card (BigGroupResidues P) : ℝ)⁻¹ *
        ∑ b : BigGroupResidues P,
          bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active b) := by
  classical
  let e : P.Residues ≃ P.SmallResidues × BigGroupResidues P :=
    (residuesEquivGroup P).trans (groupResiduesSplit P)
  have hfactor (y : P.Residues) :
      P.residuePathFactor n (visitQ F.q n) Q.offset Q.active y =
        smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active (e y).1 *
          bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active (e y).2 := by
    rw [← groupResiduePathFactor_eq_residuePathFactor P
      (visitQ F.q n) Q.offset Q.active y]
    have heq : residuesEquivGroup P y = (groupResiduesSplit P).symm (e y) := by
      dsimp [e]
      exact (Equiv.symm_apply_apply (groupResiduesSplit P)
        (residuesEquivGroup P y)).symm
    rw [heq]
    exact groupResiduePathFactor_split P (visitQ F.q n) Q.offset Q.active (e y).1 (e y).2
  calc
    P.residueExpectation n (visitQ F.q n) Q.offset Q.active =
        (Fintype.card (P.SmallResidues × BigGroupResidues P) : ℝ)⁻¹ *
          ∑ z : P.SmallResidues × BigGroupResidues P,
            smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active z.1 *
              bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active z.2 := by
      unfold PrimeGroups.residueExpectation
      rw [Fintype.card_congr e]
      congr 1
      exact Fintype.sum_equiv e
        (fun y => P.residuePathFactor n (visitQ F.q n) Q.offset Q.active y)
        (fun z => smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active z.1 *
          bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active z.2)
        hfactor
    _ =
        ((Fintype.card P.SmallResidues : ℝ)⁻¹ *
          ∑ s : P.SmallResidues,
            smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active s) *
        ((Fintype.card (BigGroupResidues P) : ℝ)⁻¹ *
          ∑ b : BigGroupResidues P,
            bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active b) := by
      letI : Nonempty (P.SmallResidues) := ⟨fun _ _ => 0⟩
      letI : Nonempty (BigGroupResidues P) := ⟨fun _ _ => 0⟩
      exact uniform_product_average
        (fun s => smallResiduePathFactor P (visitQ F.q n) Q.offset Q.active s)
        (fun b => bigGroupResiduePathFactor P (visitQ F.q n) Q.offset Q.active b)

theorem residueFactorizationTask_proof :
    Erdos821.S2Core.ResidueFactorizationTask := by
  intro F P J m n A Q hn hq
  rw [residueExpectation_eq_smallBigAverages P Q]
  rw [smallResidueAverage_eq_smallResidueExpression P Q hq hn]
  rw [bigResidueExpectation_eq_product P Q]


end Erdos821.S2Resid

end
