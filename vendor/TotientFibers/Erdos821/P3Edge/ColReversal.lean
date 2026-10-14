import Erdos821.P3Edge.BigFibres
import Erdos821.P3Edge.MultisetSum

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Edge

open Erdos821.Blueprint.Graph
open Erdos821.S2Core

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-! ### Particle and memory translation lemmas -/

lemma translateParticle_add (d₁ d₂ : ℤ) {g : P.Group} (z : P.Particle g) :
    translateParticle d₁ (translateParticle d₂ z) = translateParticle (d₁ + d₂) z := by
  cases z with
  | mk p r =>
    unfold translateParticle
    dsimp only []
    congr 1
    push_cast
    ring

lemma translateParticle_zero {g : P.Group} (z : P.Particle g) :
    translateParticle 0 z = z := by
  cases z with
  | mk p r =>
    unfold translateParticle
    dsimp only []
    congr 1
    simp

lemma translateParticle_neg_cancel (d : ℤ) {g : P.Group} (z : P.Particle g) :
    translateParticle (-d) (translateParticle d z) = z := by
  rw [translateParticle_add, neg_add_cancel, translateParticle_zero]

lemma translateParticle_cancel_neg (d : ℤ) {g : P.Group} (z : P.Particle g) :
    translateParticle d (translateParticle (-d) z) = z := by
  rw [translateParticle_add, add_neg_cancel, translateParticle_zero]

def translateParticle_equiv (d : ℤ) {g : P.Group} :
    P.Particle g ≃ P.Particle g where
  toFun := translateParticle d
  invFun := translateParticle (-d)
  left_inv := translateParticle_neg_cancel d
  right_inv := translateParticle_cancel_neg d

lemma translateParticle_injective (d : ℤ) {g : P.Group} :
    Function.Injective (translateParticle (P := P) (g := g) d) :=
  (translateParticle_equiv d).injective

lemma translateMemory_neg_cancel (d : ℤ) {g : P.Group} (z : P.Memory g) :
    translateMemory (-d) (translateMemory d z) = z := by
  unfold translateMemory
  rw [Multiset.map_map]
  have hcomp : (translateParticle (-d) ∘ translateParticle d) =
      (id : P.Particle g → P.Particle g) := by
    funext x
    exact translateParticle_neg_cancel d x
  rw [hcomp, Multiset.map_id]

lemma translateMemory_cancel_neg (d : ℤ) {g : P.Group} (z : P.Memory g) :
    translateMemory d (translateMemory (-d) z) = z := by
  unfold translateMemory
  rw [Multiset.map_map]
  have hcomp : (translateParticle d ∘ translateParticle (-d)) =
      (id : P.Particle g → P.Particle g) := by
    funext x
    exact translateParticle_cancel_neg d x
  rw [hcomp, Multiset.map_id]

lemma translateMemory_add (d : ℤ) {g : P.Group} (z₁ z₂ : P.Memory g) :
    translateMemory d (z₁ + z₂) = translateMemory d z₁ + translateMemory d z₂ := by
  unfold translateMemory
  exact Multiset.map_add _ z₁ z₂

lemma translateMemory_count (d : ℤ) {g : P.Group} (z : P.Memory g) (v : P.Particle g) :
    (translateMemory d z).count (translateParticle d v) = z.count v := by
  unfold translateMemory
  exact Multiset.count_map_eq_count' (translateParticle d) z (translateParticle_injective d) v

lemma multFact_eq_prod_univ {α : Type*} [Fintype α] [DecidableEq α] (z : Multiset α) :
    multFact z = ∏ u : α, ((z.count u).factorial : ℝ) := by
  unfold multFact
  apply Finset.prod_subset (Finset.subset_univ z.toFinset)
  intro u _ hu
  have hc : z.count u = 0 := Multiset.count_eq_zero.mpr (Multiset.mem_toFinset.not.mp hu)
  simp [hc]

lemma multFact_translateMemory (d : ℤ) {g : P.Group} (z : P.Memory g) :
    multFact (translateMemory d z) = multFact z := by
  rw [multFact_eq_prod_univ, multFact_eq_prod_univ]
  rw [← Equiv.prod_comp (translateParticle_equiv (P := P) (g := g) d)]
  apply Finset.prod_congr rfl
  intro v _
  change (((translateMemory d z).count (translateParticle d v)).factorial : ℝ) = _
  rw [translateMemory_count]

lemma groupMemoryMass_eq_div_multFact (F : FixedData) (n : ℕ) (g : P.Group) (z : P.Memory g) :
    P.groupMemoryMass F n g z =
      (z.map (fun u => tiltedMu F P n g u.1)).prod / multFact z := rfl

lemma groupMemoryMass_translateMemory (F : FixedData) (n : ℕ) (d : ℤ) (g : P.Group)
    (z : P.Memory g) :
    P.groupMemoryMass F n g (translateMemory d z) = P.groupMemoryMass F n g z := by
  rw [groupMemoryMass_eq_div_multFact, groupMemoryMass_eq_div_multFact,
    multFact_translateMemory]
  congr 1
  unfold translateMemory
  rw [Multiset.map_map]
  rfl

/-! ### Multiset factorial under cons -/

lemma multFact_cons {α : Type*} [Fintype α] [DecidableEq α] (a : α) (u : Multiset α) :
    multFact (a ::ₘ u) = ((u.count a + 1 : ℕ) : ℝ) * multFact u := by
  rw [multFact_eq_prod_univ, multFact_eq_prod_univ]
  have h1 := Finset.mul_prod_erase (Finset.univ : Finset α)
    (fun x => (((a ::ₘ u).count x).factorial : ℝ)) (Finset.mem_univ a)
  have h2 := Finset.mul_prod_erase (Finset.univ : Finset α)
    (fun x => ((u.count x).factorial : ℝ)) (Finset.mem_univ a)
  rw [← h1, ← h2]
  have hca : (((a ::ₘ u).count a).factorial : ℝ) =
      ((u.count a + 1 : ℕ) : ℝ) * ((u.count a).factorial : ℝ) := by
    rw [Multiset.count_cons_self, Nat.factorial_succ, Nat.cast_mul]
  have hrest : (∏ x ∈ Finset.univ.erase a, (((a ::ₘ u).count x).factorial : ℝ)) =
      ∏ x ∈ Finset.univ.erase a, ((u.count x).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hne : x ≠ a := Finset.ne_of_mem_erase hx
    rw [Multiset.count_cons_of_ne hne]
  rw [hca, hrest]
  ring

/-! ### Index filter count and retrieval fibres -/

lemma count_eq_card_filter {g : P.Group} (z : P.Memory g) (v : P.Particle g) :
    z.count v = (Finset.univ.filter (fun i : Fin z.card => memoryEntry z i = v)).card := by
  conv_lhs => rw [← memoryEntry_enumeration z]
  rw [Multiset.count_map]
  have hflt : ((Finset.univ : Finset (Fin z.card)).val.filter (fun i => v = memoryEntry z i)) =
      (Finset.univ.filter (fun i : Fin z.card => memoryEntry z i = v)).val := by
    rw [Finset.filter_val]
    apply Multiset.filter_congr
    intro i _
    exact eq_comm
  rw [hflt, Finset.card_def]

/-- Injective index selections matching prescribed particles on `S`. -/
def retrievalFibre {M : ℕ} {g : P.Group} (z : P.Memory g)
    (S : Finset (Fin M)) (w : Fin M → P.Particle g) :
    Finset ({idx : Fin M // idx ∈ S} → Fin z.card) :=
  Finset.univ.filter (fun f =>
    Function.Injective f ∧ ∀ idx : {idx : Fin M // idx ∈ S}, memoryEntry z (f idx) = w idx.val)

lemma retrievalFibre_empty_card {M : ℕ} {g : P.Group} (z : P.Memory g)
    (w : Fin M → P.Particle g) :
    (retrievalFibre z (∅ : Finset (Fin M)) w).card = 1 := by
  have heq : retrievalFibre z (∅ : Finset (Fin M)) w = Finset.univ := by
    ext f
    simp only [retrievalFibre, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact ⟨fun idx _ _ => False.elim (Finset.notMem_empty idx.1 idx.2),
      fun idx => False.elim (Finset.notMem_empty idx.1 idx.2)⟩
  have hempty : Fintype.card {idx : Fin M // idx ∈ (∅ : Finset (Fin M))} = 0 := by simp
  rw [heq, Finset.card_univ, Fintype.card_fun, hempty, Nat.pow_zero]

lemma finset_filter_card_eq_map_count {M : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin M)) (w : Fin M → α) (v : α) :
    (Finset.univ.filter (fun idx : {idx : Fin M // idx ∈ S} => w idx.val = v)).card =
      (S.val.map w).count v := by
  rw [Multiset.count_map]
  have h1 : ((S.val.filter (fun idx => v = w idx)).card) =
      (S.filter (fun idx => w idx = v)).card := by
    rw [Finset.card_def, Finset.filter_val]
    congr 1
    apply Multiset.filter_congr
    intro idx _
    exact eq_comm
  rw [h1]
  apply Finset.card_bij (fun (idx : {idx : Fin M // idx ∈ S}) _ => idx.val)
  · intro idx hidx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hidx ⊢
    exact ⟨idx.2, hidx⟩
  · intro i₁ _ i₂ _ h
    exact Subtype.ext h
  · intro idx hidx
    simp only [Finset.mem_filter] at hidx
    exact ⟨⟨idx, hidx.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hidx.2⟩, rfl⟩

lemma retrievalFibre_insert_card {M : ℕ} {g : P.Group} (z : P.Memory g)
    (S : Finset (Fin M)) (a : Fin M) (ha : a ∉ S) (w : Fin M → P.Particle g) :
    (retrievalFibre z (insert a S) w).card =
      (retrievalFibre z S w).card * (z.count (w a) - (S.val.map w).count (w a)) := by
  classical
  let restrict (f : {idx : Fin M // idx ∈ insert a S} → Fin z.card) :
      {idx : Fin M // idx ∈ S} → Fin z.card :=
    fun idx => f ⟨idx.1, Finset.mem_insert_of_mem idx.2⟩
  let extFibre (f' : {idx : Fin M // idx ∈ S} → Fin z.card) :
      Finset ({idx : Fin M // idx ∈ insert a S} → Fin z.card) :=
    (retrievalFibre z (insert a S) w).filter (fun f => restrict f = f')
  have hrestrict_mem : ∀ f ∈ retrievalFibre z (insert a S) w,
      restrict f ∈ retrievalFibre z S w := by
    intro f hf
    simp only [retrievalFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    refine ⟨fun i₁ i₂ heq => ?_, fun idx => hf.2 ⟨idx.1, Finset.mem_insert_of_mem idx.2⟩⟩
    have hinj := hf.1 heq
    exact Subtype.ext (Subtype.mk.inj hinj)
  have hbiUnion : retrievalFibre z (insert a S) w =
      (retrievalFibre z S w).biUnion extFibre := by
    ext f
    simp only [Finset.mem_biUnion, extFibre, Finset.mem_filter]
    constructor
    · intro hf
      exact ⟨restrict f, hrestrict_mem f hf, hf, rfl⟩
    · rintro ⟨_, _, hf, _⟩
      exact hf
  have hdisj : Set.PairwiseDisjoint (↑(retrievalFibre z S w)) extFibre := by
    intro f₁ _ f₂ _ hne
    apply Finset.disjoint_filter.mpr
    intro f _ h₁ h₂
    exact hne (h₁.symm.trans h₂)
  rw [hbiUnion, Finset.card_biUnion hdisj]
  let Z_a : Finset (Fin z.card) := Finset.univ.filter (fun j => memoryEntry z j = w a)
  have hZa_card : Z_a.card = z.count (w a) := (count_eq_card_filter z (w a)).symm
  have hfibre_card : ∀ f' ∈ retrievalFibre z S w,
      (extFibre f').card = z.count (w a) - (S.val.map w).count (w a) := by
    intro f' hf'
    have hf'_prop : Function.Injective f' ∧
        ∀ idx : {idx : Fin M // idx ∈ S}, memoryEntry z (f' idx) = w idx.val := by
      simpa only [retrievalFibre, Finset.mem_filter, Finset.mem_univ, true_and] using hf'
    let I_f' : Finset (Fin z.card) := Finset.univ.image f'
    let avail : Finset (Fin z.card) := Z_a \ I_f'
    have hbij : (extFibre f').card = avail.card := by
      apply Finset.card_bij (fun f _ => f ⟨a, Finset.mem_insert_self a S⟩)
      · intro f hf
        simp only [extFibre, retrievalFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        obtain ⟨⟨hfinj, hfval⟩, hres⟩ := hf
        simp only [avail, Z_a, I_f', Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_image, not_exists]
        refine ⟨hfval ⟨a, Finset.mem_insert_self a S⟩, fun idx hcon => ?_⟩
        have hres_idx : f ⟨idx.1, Finset.mem_insert_of_mem idx.2⟩ = f' idx :=
          congrFun hres idx
        rw [← hres_idx] at hcon
        have heq := hfinj hcon
        have hval_eq : idx.1 = a := Subtype.mk.inj heq
        exact ha (hval_eq ▸ idx.2)
      · intro f₁ hf₁ f₂ hf₂ heq_a
        simp only [extFibre, Finset.mem_filter] at hf₁ hf₂
        funext idx
        by_cases hia : idx.1 = a
        · have hidx_eq : idx = ⟨a, Finset.mem_insert_self a S⟩ := Subtype.ext hia
          rw [hidx_eq, heq_a]
        · have his : idx.1 ∈ S := Finset.mem_of_mem_insert_of_ne idx.2 hia
          have hidx_eq : idx = ⟨idx.1, Finset.mem_insert_of_mem his⟩ := Subtype.ext rfl
          rw [hidx_eq]
          have h1 : restrict f₁ ⟨idx.1, his⟩ = f' ⟨idx.1, his⟩ := congrFun hf₁.2 ⟨idx.1, his⟩
          have h2 : restrict f₂ ⟨idx.1, his⟩ = f' ⟨idx.1, his⟩ := congrFun hf₂.2 ⟨idx.1, his⟩
          exact h1.trans h2.symm
      · intro j₀ hj₀
        simp only [avail, Z_a, I_f', Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.mem_image, not_exists] at hj₀
        let f : {idx : Fin M // idx ∈ insert a S} → Fin z.card :=
          fun idx => if h : idx.1 = a then j₀
            else f' ⟨idx.1, Finset.mem_of_mem_insert_of_ne idx.2 h⟩
        have hfa : f ⟨a, Finset.mem_insert_self a S⟩ = j₀ := dif_pos rfl
        have hres : restrict f = f' := by
          funext idx
          have hne : idx.1 ≠ a := fun h => ha (h ▸ idx.2)
          exact dif_neg hne
        have hfval : ∀ idx : {idx : Fin M // idx ∈ insert a S},
            memoryEntry z (f idx) = w idx.val := by
          intro idx
          by_cases h : idx.1 = a
          · dsimp [f]
            rw [dif_pos h, hj₀.1, h]
          · dsimp [f]
            rw [dif_neg h]
            exact hf'_prop.2 ⟨idx.1, Finset.mem_of_mem_insert_of_ne idx.2 h⟩
        have hfinj : Function.Injective f := by
          intro i₁ i₂ heq
          dsimp [f] at heq
          by_cases h₁ : i₁.1 = a <;> by_cases h₂ : i₂.1 = a
          · exact Subtype.ext (h₁.trans h₂.symm)
          · rw [dif_pos h₁, dif_neg h₂] at heq
            exact False.elim (hj₀.2 _ heq.symm)
          · rw [dif_neg h₁, dif_pos h₂] at heq
            exact False.elim (hj₀.2 _ heq)
          · rw [dif_neg h₁, dif_neg h₂] at heq
            have hinj := hf'_prop.1 heq
            exact Subtype.ext (Subtype.mk.inj hinj)
        refine ⟨f, ?_, hfa⟩
        simp only [extFibre, retrievalFibre, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hfinj, hfval⟩, hres⟩
    rw [hbij]
    have hinter_eq : I_f' ∩ Z_a =
        (Finset.univ.filter (fun idx : {idx : Fin M // idx ∈ S} => w idx.val = w a)).image f' := by
      ext j
      simp only [I_f', Z_a, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨idx, rfl⟩, hj⟩
        exact ⟨idx, (hf'_prop.2 idx).symm.trans hj, rfl⟩
      · rintro ⟨idx, hidx, rfl⟩
        exact ⟨⟨idx, rfl⟩, (hf'_prop.2 idx).trans hidx⟩
    have hinter_card : (I_f' ∩ Z_a).card = (S.val.map w).count (w a) := by
      rw [hinter_eq, Finset.card_image_of_injective _ hf'_prop.1]
      exact finset_filter_card_eq_map_count S w (w a)
    dsimp [avail]
    rw [Finset.card_sdiff, hinter_card, hZa_card]
  rw [Finset.sum_congr rfl hfibre_card, Finset.sum_const, smul_eq_mul]

/-- Fundamental factorial identity for `retrievalFibre`:
`card (retrievalFibre (u + S.map w) S w) * multFact u = multFact (u + S.map w)`. -/
lemma retrievalFibre_card_mul_multFact {M : ℕ} {g : P.Group}
    (u : P.Memory g) (S : Finset (Fin M)) (w : Fin M → P.Particle g) :
    ((retrievalFibre (u + S.val.map w) S w).card : ℝ) * multFact u =
      multFact (u + S.val.map w) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty =>
    have hmap : (∅ : Finset (Fin M)).val.map w = 0 := rfl
    have hcard : (retrievalFibre (u + (∅ : Finset (Fin M)).val.map w) ∅ w).card = 1 :=
      retrievalFibre_empty_card _ w
    rw [hcard, hmap, add_zero, Nat.cast_one, one_mul]
  | @insert a S ha ih =>
    set z := u + (insert a S).val.map w
    have hcard := retrievalFibre_insert_card z S a ha w
    have hz_eq : z = (w a ::ₘ u) + S.val.map w := by
      change u + (insert a S).val.map w = (w a ::ₘ u) + S.val.map w
      rw [Finset.insert_val_of_notMem ha, Multiset.map_cons, add_comm u _,
        Multiset.cons_add, add_comm (S.val.map w) u, ← Multiset.cons_add]
    have hcount : z.count (w a) - (S.val.map w).count (w a) = u.count (w a) + 1 := by
      rw [hz_eq, Multiset.count_add, Multiset.count_cons_self, Nat.add_sub_cancel]
    have hcard_z : (retrievalFibre z S w).card =
        (retrievalFibre ((w a ::ₘ u) + S.val.map w) S w).card :=
      congrArg (fun m => (retrievalFibre m S w).card) hz_eq
    rw [hcount, hcard_z] at hcard
    have hcast : ((retrievalFibre z (insert a S) w).card : ℝ) =
        ((retrievalFibre ((w a ::ₘ u) + S.val.map w) S w).card : ℝ) *
          ((u.count (w a) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [hcast, mul_assoc, ← multFact_cons (w a) u, ih (w a ::ₘ u), ← hz_eq]

lemma groupMemoryMass_add_map (F : FixedData) (n : ℕ) {M : ℕ} {g : P.Group}
    (u : P.Memory g) (S : Finset (Fin M)) (w : Fin M → P.Particle g) :
    ((u + S.val.map w).map (fun p => tiltedMu F P n g p.1)).prod =
      (u.map (fun p => tiltedMu F P n g p.1)).prod *
        ∏ idx ∈ S, tiltedMu F P n g (w idx).1 := by
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map]
  congr 1

/-- Weighted factorial identity: multiplying `retrievalFibre.card` by `groupMemoryMass`
extracts the product of `tiltedMu` over `S` and leaves `groupMemoryMass u`. -/
lemma retrievalFibre_card_mul_groupMemoryMass (F : FixedData) (n : ℕ)
    {M : ℕ} {g : P.Group} (u : P.Memory g)
    (S : Finset (Fin M)) (w : Fin M → P.Particle g) :
    ((retrievalFibre (u + S.val.map w) S w).card : ℝ) *
      P.groupMemoryMass F n g (u + S.val.map w) =
    P.groupMemoryMass F n g u *
      ∏ idx ∈ S, tiltedMu F P n g (w idx).1 := by
  set z := u + S.val.map w
  rw [groupMemoryMass_eq_div_multFact, groupMemoryMass_eq_div_multFact]
  have hprod := groupMemoryMass_add_map F n u S w
  have hfact := retrievalFibre_card_mul_multFact u S w
  have hfu : multFact u ≠ 0 := ne_of_gt (multFact_pos u)
  have hfz : multFact z ≠ 0 := ne_of_gt (multFact_pos z)
  change ((retrievalFibre z S w).card : ℝ) *
      ((z.map (fun p => tiltedMu F P n g p.1)).prod / multFact z) =
    ((u.map (fun p => tiltedMu F P n g p.1)).prod / multFact u) *
      ∏ idx ∈ S, tiltedMu F P n g (w idx).1
  rw [hprod, mul_div_assoc', div_mul_eq_mul_div, div_eq_div_iff hfz hfu]
  calc ((retrievalFibre z S w).card : ℝ) *
        ((u.map (fun p => tiltedMu F P n g p.1)).prod *
          ∏ idx ∈ S, tiltedMu F P n g (w idx).1) * multFact u
      = (((retrievalFibre z S w).card : ℝ) * multFact u) *
          ((u.map (fun p => tiltedMu F P n g p.1)).prod *
            ∏ idx ∈ S, tiltedMu F P n g (w idx).1) := by ring
    _ = (u.map (fun p => tiltedMu F P n g p.1)).prod *
          (∏ idx ∈ S, tiltedMu F P n g (w idx).1) * multFact z := by
        rw [hfact]
        ring

/-! ### Per-big-group reversal and active-label swap -/

lemma storedMemory_eq_val_map {M : ℕ} {g : P.Group} (a : Fin M → P.Prime g)
    (B : Finset (Fin M)) :
    storedMemory a B = B.val.map (fun i => (⟨a i, 0⟩ : P.Particle g)) := by
  unfold storedMemory
  rw [← Multiset.map_coe, Finset.coe_toList]

lemma translateMemory_storedMemory (delta : ℤ) {M : ℕ} {g : P.Group}
    (a : Fin M → P.Prime g) (B : Finset (Fin M)) :
    translateMemory delta (storedMemory a B) =
      B.val.map (fun i => (⟨a i, (delta : ZMod (a i).val)⟩ : P.Particle g)) := by
  rw [storedMemory_eq_val_map]
  unfold translateMemory
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  dsimp [translateParticle]
  rw [zero_add]

lemma subtype_univ_map_eq {M : ℕ} {α : Type*} (S : Finset (Fin M)) (w : Fin M → α) :
    (Finset.univ : Finset {idx : Fin M // idx ∈ S}).val.map (fun idx => w idx.val) =
      S.val.map w := by
  have h := congrArg (fun t : Finset (Fin M) => t.val.map w) (Finset.attach_map_val (s := S))
  simpa [Finset.map_val, Multiset.map_map] using h

lemma sdiff_val_add_val {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) :
    (Finset.univ \ B).val + B.val = (Finset.univ : Finset α).val := by
  ext x
  rw [Multiset.count_add,
    Multiset.count_eq_one_of_mem (Finset.univ : Finset α).nodup (Finset.mem_univ x)]
  by_cases hx : x ∈ B
  · have hnot : x ∉ Finset.univ \ B := by simp [hx]
    rw [Multiset.count_eq_zero.mpr hnot, Multiset.count_eq_one_of_mem B.nodup hx]
  · have hmem : x ∈ Finset.univ \ B := by simp [hx]
    rw [Multiset.count_eq_one_of_mem (Finset.univ \ B).nodup hmem,
      Multiset.count_eq_zero.mpr hx]

lemma deleteMemoryIndices_add_selected {M : ℕ} {g : P.Group} (z : P.Memory g)
    (S : Finset (Fin M)) (f : {idx : Fin M // idx ∈ S} → Fin z.card)
    (hf : Function.Injective f) :
    deleteMemoryIndices z (Finset.univ.image f) +
      (Finset.univ : Finset {idx : Fin M // idx ∈ S}).val.map
        (fun idx => memoryEntry z (f idx)) = z := by
  rw [deleteMemoryIndices_eq_map]
  have himg : (Finset.univ : Finset {idx : Fin M // idx ∈ S}).val.map f =
      (Finset.univ.image f).val := by
    symm
    exact Finset.image_val_of_injOn hf.injOn
  have hmap : (Finset.univ : Finset {idx : Fin M // idx ∈ S}).val.map
      (fun idx => memoryEntry z (f idx)) =
      (Finset.univ.image f).val.map (memoryEntry z) := by
    rw [← himg, Multiset.map_map]
    rfl
  rw [hmap, ← Multiset.map_add, sdiff_val_add_val, memoryEntry_enumeration]

/-- If a valid retrieval map `f_g` exists for `(s_g, t_g)`, then `s_g` and `t_g` decompose
over the surviving multiset `u_g = deleteMemoryIndices s_g (image f_g)` and `s_g` is
uniquely determined by `(t_g, delta, a_g, b_g, B_g, A_g)`. -/
lemma valid_bigGroup_decomp (delta : ℤ) (g : P.BigGroup)
    (a_g b_g : Fin (J + F.ell) → P.Prime g.val)
    (s_g t_g : P.Memory g.val)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (f_g : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin s_g.card)
    (hinj : Function.Injective f_g)
    (hret : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g},
      (memoryEntry s_g (f_g idx)).1 = b_g idx.val ∧
      (memoryEntry s_g (f_g idx)).2 + (delta : ZMod (memoryEntry s_g (f_g idx)).1.val) = 0)
    (ht_eq : t_g = translateMemory delta
      (deleteMemoryIndices s_g (Finset.univ.image f_g) + storedMemory a_g B_g)) :
    let u_g := deleteMemoryIndices s_g (Finset.univ.image f_g)
    let w_A : Fin (J + F.ell) → P.Particle g.val :=
      fun idx => ⟨b_g idx, -(delta : ZMod (b_g idx).val)⟩
    let w_B : Fin (J + F.ell) → P.Particle g.val :=
      fun idx => ⟨a_g idx, (delta : ZMod (a_g idx).val)⟩
    f_g ∈ retrievalFibre s_g A_g w_A ∧
    s_g = u_g + A_g.val.map w_A ∧
    t_g = translateMemory delta u_g + B_g.val.map w_B ∧
    u_g = translateMemory (-delta) t_g - storedMemory a_g B_g ∧
    s_g = (translateMemory (-delta) t_g - storedMemory a_g B_g) + A_g.val.map w_A := by
  intro u_g w_A w_B
  have hentry : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g},
      memoryEntry s_g (f_g idx) = w_A idx.val := by
    intro idx
    rcases hret idx with ⟨h1, h2⟩
    rcases hp : memoryEntry s_g (f_g idx) with ⟨p, r⟩
    rw [hp] at h1 h2
    dsimp only [] at h1 h2
    subst h1
    have hr : r = -(delta : ZMod (b_g idx.val).val) := eq_neg_of_add_eq_zero_left h2
    subst hr
    rfl
  have hf_mem : f_g ∈ retrievalFibre s_g A_g w_A := by
    simp only [retrievalFibre, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hinj, hentry⟩
  have hs_eq : s_g = u_g + A_g.val.map w_A := by
    have hdel := deleteMemoryIndices_add_selected s_g A_g f_g hinj
    have hmap : (Finset.univ : Finset {idx : Fin (J + F.ell) // idx ∈ A_g}).val.map
        (fun idx => memoryEntry s_g (f_g idx)) = A_g.val.map w_A := by
      rw [Multiset.map_congr rfl (fun idx _ => hentry idx)]
      exact subtype_univ_map_eq A_g w_A
    rw [hmap] at hdel
    exact hdel.symm
  have ht_decomp : t_g = translateMemory delta u_g + B_g.val.map w_B := by
    rw [ht_eq, translateMemory_add, translateMemory_storedMemory]
  have hu_eq : u_g = translateMemory (-delta) t_g - storedMemory a_g B_g := by
    have h1 := congrArg (translateMemory (-delta)) ht_eq
    rw [translateMemory_neg_cancel] at h1
    rw [h1, Multiset.add_sub_cancel_right]
  refine ⟨hf_mem, hs_eq, ht_decomp, hu_eq, ?_⟩
  rw [← hu_eq, hs_eq]

/-- Active-label product identity when `a_g` and `b_g` agree on shared slots and
`A_g, B_g` avoid shared slots. -/
lemma active_fresh_prod_swap (F : FixedData) (n : ℕ)
    (ν : Pattern P J F.ell m) (g : P.BigGroup)
    (a_g b_g : Fin (J + F.ell) → P.Prime g.val)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (hB : ∀ idx ∈ B_g, ¬ ν.shared g.val idx)
    (hA : ∀ idx ∈ A_g, ¬ ν.shared g.val idx)
    (hsh : ∀ idx : Fin (J + F.ell), ν.shared g.val idx → a_g idx = b_g idx) :
    (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (a_g idx)) *
      (∏ idx ∈ A_g, tiltedMu F P n g.val (b_g idx)) *
      (∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx)) =
    (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
      (∏ idx ∈ B_g, tiltedMu F P n g.val (a_g idx)) *
      (∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) := by
  have hcombine : ∀ (c_g : Fin (J + F.ell) → P.Prime g.val) (S_g : Finset (Fin (J + F.ell))),
      (∀ idx ∈ S_g, ¬ ν.shared g.val idx) →
      (∏ idx ∈ S_g, tiltedMu F P n g.val (c_g idx)) *
        (∏ idx : Fin (J + F.ell),
          if ν.shared g.val idx ∨ idx ∈ S_g then 1 else tiltedMu F P n g.val (c_g idx)) =
      ∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx then 1 else tiltedMu F P n g.val (c_g idx) := by
    intro c_g S_g hS
    have hprod_S : (∏ idx ∈ S_g, tiltedMu F P n g.val (c_g idx)) =
        ∏ idx : Fin (J + F.ell), if idx ∈ S_g then tiltedMu F P n g.val (c_g idx) else 1 := by
      rw [← Finset.prod_filter, Finset.filter_univ_mem]
    rw [hprod_S, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro idx _
    by_cases hm : idx ∈ S_g
    · have hnsh : ¬ ν.shared g.val idx := hS idx hm
      simp [hm, hnsh]
    · by_cases hsh_idx : ν.shared g.val idx <;> simp [hm, hsh_idx]
  rw [mul_assoc, hcombine b_g A_g hA, mul_assoc, hcombine a_g B_g hB,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro idx _
  by_cases hsh_idx : ν.shared g.val idx
  · simp [hsh_idx, hsh idx hsh_idx]
  · simp [hsh_idx, mul_comm]

/-- Ratio bound between `(P.V g.val) ^ (-(A_g.card : ℤ))` and `(P.V g.val) ^ (-(B_g.card : ℤ))`. -/
def colRevConst (F : FixedData) (m : ℕ) : ℝ :=
  max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * max 1 ((F.vMax) ^ (F.ell + m))

lemma colRevConst_ge_one (F : FixedData) (m : ℕ) : 1 ≤ colRevConst F m := by
  unfold colRevConst
  have h1 : 1 ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) := le_max_left _ _
  have h2 : 1 ≤ max 1 ((F.vMax) ^ (F.ell + m)) := le_max_left _ _
  calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) * max 1 ((F.vMax) ^ (F.ell + m)) :=
      mul_le_mul h1 h2 zero_le_one (le_trans zero_le_one h1)

lemma colRevConst_pos (F : FixedData) (m : ℕ) : 0 < colRevConst F m :=
  lt_of_lt_of_le zero_lt_one (colRevConst_ge_one F m)

lemma groupMemoryMass_nonneg (F : FixedData) (n : ℕ) {g : P.Group}
    (htilted : ∀ p : P.Prime g, 0 ≤ tiltedMu F P n g p) (z : P.Memory g) :
    0 ≤ P.groupMemoryMass F n g z := by
  rw [groupMemoryMass_eq_div_multFact]
  apply div_nonneg _ (multFact_pos z).le
  refine Multiset.prod_nonneg ?_
  intro r hr
  rcases Multiset.mem_map.mp hr with ⟨p, _, rfl⟩
  exact htilted p.1

lemma V_zpow_swap_le (ν : Pattern P J F.ell m) (g : P.BigGroup)
    (hVlo : F.vMin ≤ P.V g.val) (hVhi : P.V g.val ≤ F.vMax)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (hB : ∀ idx ∈ B_g, ¬ ν.shared g.val idx)
    (hA : ∀ idx ∈ A_g, ¬ ν.shared g.val idx) :
    (P.V g.val) ^ (-(A_g.card : ℤ)) ≤
      colRevConst F m * (P.V g.val) ^ (-(B_g.card : ℤ)) := by
  have hVpos : 0 < P.V g.val := lt_of_lt_of_le F.vMin_pos hVlo
  have hB_card : B_g.card ≤ F.ell + m := prom_card_le ν g B_g hB
  have hA_card : A_g.card ≤ F.ell + m := prom_card_le ν g A_g hA
  have hA_le : (P.V g.val) ^ (-(A_g.card : ℤ)) ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) := by
    calc (P.V g.val) ^ (-(A_g.card : ℤ))
        ≤ ((P.V g.val)⁻¹) ^ A_g.card := by rw [zpow_neg, zpow_natCast, inv_pow]
      _ ≤ (F.vMin⁻¹) ^ A_g.card :=
          pow_le_pow_left₀ (inv_nonneg.mpr hVpos.le) (inv_anti₀ F.vMin_pos hVlo) _
      _ ≤ max 1 ((F.vMin⁻¹) ^ (F.ell + m)) := by
          rcases le_or_gt (F.vMin⁻¹) 1 with hle1 | hgt1
          · exact le_trans (pow_le_one₀ (inv_nonneg.mpr F.vMin_pos.le) hle1) (le_max_left _ _)
          · exact le_trans (pow_le_pow_right₀ hgt1.le hA_card) (le_max_right _ _)
  have hB_le : (P.V g.val) ^ (B_g.card : ℤ) ≤ max 1 ((F.vMax) ^ (F.ell + m)) := by
    rw [zpow_natCast]
    calc (P.V g.val) ^ B_g.card
        ≤ (F.vMax) ^ B_g.card := pow_le_pow_left₀ hVpos.le hVhi _
      _ ≤ max 1 ((F.vMax) ^ (F.ell + m)) := by
          rcases le_or_gt F.vMax 1 with hle1 | hgt1
          · exact le_trans (pow_le_one₀ (le_trans hVpos.le hVhi) hle1) (le_max_left _ _)
          · exact le_trans (pow_le_pow_right₀ hgt1.le hB_card) (le_max_right _ _)
  have hB_pos : 0 < (P.V g.val) ^ (-(B_g.card : ℤ)) := zpow_pos hVpos _
  have hB_cancel : (P.V g.val) ^ (B_g.card : ℤ) * (P.V g.val) ^ (-(B_g.card : ℤ)) = 1 := by
    rw [← zpow_add₀ (ne_of_gt hVpos), add_neg_cancel, zpow_zero]
  calc (P.V g.val) ^ (-(A_g.card : ℤ))
      = (P.V g.val) ^ (-(A_g.card : ℤ)) *
          ((P.V g.val) ^ (B_g.card : ℤ) * (P.V g.val) ^ (-(B_g.card : ℤ))) := by
        rw [hB_cancel, mul_one]
    _ = ((P.V g.val) ^ (-(A_g.card : ℤ)) * (P.V g.val) ^ (B_g.card : ℤ)) *
          (P.V g.val) ^ (-(B_g.card : ℤ)) := by ring
    _ ≤ colRevConst F m * (P.V g.val) ^ (-(B_g.card : ℤ)) := by
        apply mul_le_mul_of_nonneg_right _ hB_pos.le
        unfold colRevConst
        exact mul_le_mul hA_le hB_le (zpow_nonneg hVpos.le _)
          (le_trans zero_le_one (le_max_left _ _))

/-- Per-big-group factorial reversal inequality:
when a valid retrieval map `f₀` exists for `(s_g, t_g)`, multiplying `(retrievalFibre s_g A_g w_A).card`
by the source big-group mass and forward big-group edge weight is bounded by `colRevConst F m`
times the target big-group mass times the sum over reversed retrieval maps `f'_g` of
`bigGroupWeight F r n ν (-delta) g b_g t_g A_g B_g f'_g a_g`. -/
lemma col_bigGroup_reversal_le (F : FixedData) (r : MemoryParameters F) (n : ℕ)
    (ν : Pattern P J F.ell m) (delta : ℤ) (g : P.BigGroup)
    (hVlo : F.vMin ≤ P.V g.val) (hVhi : P.V g.val ≤ F.vMax)
    (htilted_nn : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p)
    (a_g b_g : Fin (J + F.ell) → P.Prime g.val)
    (s_g t_g : P.Memory g.val)
    (B_g A_g : Finset (Fin (J + F.ell)))
    (f₀ : {idx : Fin (J + F.ell) // idx ∈ A_g} → Fin s_g.card)
    (hB : ∀ idx ∈ B_g, ¬ ν.shared g.val idx)
    (hA : ∀ idx ∈ A_g, ¬ ν.shared g.val idx)
    (hsh : ∀ idx : Fin (J + F.ell), ν.shared g.val idx → a_g idx = b_g idx)
    (hinj : Function.Injective f₀)
    (hret : ∀ idx : {idx : Fin (J + F.ell) // idx ∈ A_g},
      (memoryEntry s_g (f₀ idx)).1 = b_g idx.val ∧
      (memoryEntry s_g (f₀ idx)).2 + (delta : ZMod (memoryEntry s_g (f₀ idx)).1.val) = 0)
    (ht_eq : t_g = translateMemory delta
      (deleteMemoryIndices s_g (Finset.univ.image f₀) + storedMemory a_g B_g)) :
    let w_A : Fin (J + F.ell) → P.Particle g.val :=
      fun idx => ⟨b_g idx, -(delta : ZMod (b_g idx).val)⟩
    ((retrievalFibre s_g A_g w_A).card : ℝ) *
      (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (a_g idx)) *
      P.groupMemoryMass F n g.val s_g *
      (∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx)) *
      (P.V g.val) ^ (-(A_g.card : ℤ)) *
      r.rho ^ (zeroMemoryIndices s_g).card *
      (r.v ^ A_g.card / r.v ^ B_g.card) ≤
    colRevConst F m *
      (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
      P.groupMemoryMass F n g.val t_g *
      ∑ f'_g : {idx : Fin (J + F.ell) // idx ∈ B_g} → Fin t_g.card,
        if bigGroupValid ν (-delta) g b_g t_g A_g B_g f'_g a_g then
          bigGroupWeight F r n ν (-delta) g b_g t_g A_g B_g f'_g a_g
        else 0 := by
  intro w_A
  set u_g := deleteMemoryIndices s_g (Finset.univ.image f₀)
  let w_B : Fin (J + F.ell) → P.Particle g.val :=
    fun idx => ⟨a_g idx, (delta : ZMod (a_g idx).val)⟩
  obtain ⟨_, hs_eq, ht_decomp, _, _⟩ :=
    valid_bigGroup_decomp delta g a_g b_g s_g t_g B_g A_g f₀ hinj hret ht_eq
  have hVpos : 0 < P.V g.val := lt_of_lt_of_le F.vMin_pos hVlo
  have hrev_s : ((retrievalFibre s_g A_g w_A).card : ℝ) * P.groupMemoryMass F n g.val s_g =
      P.groupMemoryMass F n g.val u_g * ∏ idx ∈ A_g, tiltedMu F P n g.val (b_g idx) := by
    have h := retrievalFibre_card_mul_groupMemoryMass F n u_g A_g w_A
    have h1 : (retrievalFibre s_g A_g w_A).card =
        (retrievalFibre (u_g + A_g.val.map w_A) A_g w_A).card :=
      congrArg (fun m => (retrievalFibre m A_g w_A).card) hs_eq
    rw [h1]
    conv_lhs => rw [hs_eq]
    exact h
  have hrev_t : ((retrievalFibre t_g B_g w_B).card : ℝ) * P.groupMemoryMass F n g.val t_g =
      P.groupMemoryMass F n g.val u_g * ∏ idx ∈ B_g, tiltedMu F P n g.val (a_g idx) := by
    have h := retrievalFibre_card_mul_groupMemoryMass F n (translateMemory delta u_g) B_g w_B
    have h1 : (retrievalFibre t_g B_g w_B).card =
        (retrievalFibre (translateMemory delta u_g + B_g.val.map w_B) B_g w_B).card :=
      congrArg (fun m => (retrievalFibre m B_g w_B).card) ht_decomp
    rw [h1]
    conv_lhs => rw [ht_decomp]
    rw [h, groupMemoryMass_translateMemory]
  have hswap := active_fresh_prod_swap F n ν g a_g b_g B_g A_g hB hA hsh
  have hmass_eq : ((retrievalFibre s_g A_g w_A).card : ℝ) *
      (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (a_g idx)) *
      P.groupMemoryMass F n g.val s_g *
      (∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx)) =
      (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
      P.groupMemoryMass F n g.val t_g *
      ((retrievalFibre t_g B_g w_B).card : ℝ) *
      (∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) := by
    calc ((retrievalFibre s_g A_g w_A).card : ℝ) *
          (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (a_g idx)) *
          P.groupMemoryMass F n g.val s_g *
          (∏ idx : Fin (J + F.ell),
            if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))
        = (((retrievalFibre s_g A_g w_A).card : ℝ) * P.groupMemoryMass F n g.val s_g) *
          (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (a_g idx)) *
          (∏ idx : Fin (J + F.ell),
            if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx)) := by ring
      _ = P.groupMemoryMass F n g.val u_g *
          ((∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (a_g idx)) *
            (∏ idx ∈ A_g, tiltedMu F P n g.val (b_g idx)) *
            (∏ idx : Fin (J + F.ell),
              if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx))) := by
        rw [hrev_s]
        ring
      _ = (P.groupMemoryMass F n g.val u_g * ∏ idx ∈ B_g, tiltedMu F P n g.val (a_g idx)) *
          (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
          (∏ idx : Fin (J + F.ell),
            if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) := by
        rw [hswap]
        ring
      _ = (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
          P.groupMemoryMass F n g.val t_g *
          ((retrievalFibre t_g B_g w_B).card : ℝ) *
          (∏ idx : Fin (J + F.ell),
            if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) := by
        rw [← hrev_t]
        ring
  have hV_swap := V_zpow_swap_le ν g hVlo hVhi B_g A_g hB hA
  have hfibre_term : ∀ f'_g ∈ retrievalFibre t_g B_g w_B,
      bigGroupValid ν (-delta) g b_g t_g A_g B_g f'_g a_g ∧
      (∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) *
      (P.V g.val) ^ (-(B_g.card : ℤ)) *
      r.rho ^ (zeroMemoryIndices s_g).card *
      (r.v ^ A_g.card / r.v ^ B_g.card) =
      bigGroupWeight F r n ν (-delta) g b_g t_g A_g B_g f'_g a_g := by
    intro f'_g hf'_g
    simp only [retrievalFibre, Finset.mem_filter, Finset.mem_univ, true_and] at hf'_g
    obtain ⟨hf'_inj, hf'_val⟩ := hf'_g
    have hval : bigGroupValid ν (-delta) g b_g t_g A_g B_g f'_g a_g := by
      refine ⟨hA, hB, fun j hj => hsh (ν.slot j) ⟨j, rfl, hj⟩, fun idx => ?_⟩
      have he := hf'_val idx
      rw [he]
      dsimp [w_B]
      refine ⟨rfl, ?_⟩
      push_cast
      exact add_neg_cancel _
    have hdel_t : deleteMemoryIndices t_g (Finset.univ.image f'_g) =
        translateMemory delta u_g := by
      have h1 := deleteMemoryIndices_add_selected t_g B_g f'_g hf'_inj
      have hmap : (Finset.univ : Finset {idx : Fin (J + F.ell) // idx ∈ B_g}).val.map
          (fun idx => memoryEntry t_g (f'_g idx)) = B_g.val.map w_B := by
        rw [Multiset.map_congr rfl (fun idx _ => hf'_val idx)]
        exact subtype_univ_map_eq B_g w_B
      rw [hmap] at h1
      exact add_right_cancel (h1.trans ht_decomp)
    have hmem_s : translateMemory (-delta)
        (deleteMemoryIndices t_g (Finset.univ.image f'_g) + storedMemory b_g A_g) = s_g := by
      rw [hdel_t, translateMemory_add, translateMemory_neg_cancel,
        translateMemory_storedMemory]
      simp only [Int.cast_neg]
      exact hs_eq.symm
    refine ⟨hval, ?_⟩
    unfold bigGroupWeight
    rw [hmem_s]
  have hfibre_sum_le : ((retrievalFibre t_g B_g w_B).card : ℝ) *
      ((∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) *
      (P.V g.val) ^ (-(B_g.card : ℤ)) *
      r.rho ^ (zeroMemoryIndices s_g).card *
      (r.v ^ A_g.card / r.v ^ B_g.card)) ≤
      ∑ f'_g : {idx : Fin (J + F.ell) // idx ∈ B_g} → Fin t_g.card,
        if bigGroupValid ν (-delta) g b_g t_g A_g B_g f'_g a_g then
          bigGroupWeight F r n ν (-delta) g b_g t_g A_g B_g f'_g a_g
        else 0 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    have hsub_eq : (∑ f'_g ∈ retrievalFibre t_g B_g w_B,
        ((∏ idx : Fin (J + F.ell),
          if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) *
        (P.V g.val) ^ (-(B_g.card : ℤ)) *
        r.rho ^ (zeroMemoryIndices s_g).card *
        (r.v ^ A_g.card / r.v ^ B_g.card))) =
        ∑ f'_g ∈ retrievalFibre t_g B_g w_B,
          if bigGroupValid ν (-delta) g b_g t_g A_g B_g f'_g a_g then
            bigGroupWeight F r n ν (-delta) g b_g t_g A_g B_g f'_g a_g
          else 0 := by
      apply Finset.sum_congr rfl
      intro f'_g hf'_g
      obtain ⟨hval, hwt⟩ := hfibre_term f'_g hf'_g
      rw [if_pos hval, hwt]
    rw [hsub_eq]
    apply Finset.sum_le_univ_sum_of_nonneg
    intro f'_g
    split_ifs
    · exact bigGroupWeight_nonneg F r n ν (-delta) g hVpos htilted_nn _ _ _ _ _ _
    · exact le_refl 0
  have hvpos : 0 < r.v := lt_trans zero_lt_one r.v_gt
  have hP_t_nn : 0 ≤ (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
      P.groupMemoryMass F n g.val t_g :=
    mul_nonneg (Finset.prod_nonneg (fun idx _ => htilted_nn _))
      (groupMemoryMass_nonneg F n htilted_nn t_g)
  have hrest_nn : 0 ≤ ((retrievalFibre t_g B_g w_B).card : ℝ) *
      (∏ idx : Fin (J + F.ell),
        if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) *
      r.rho ^ (zeroMemoryIndices s_g).card *
      (r.v ^ A_g.card / r.v ^ B_g.card) := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (Nat.cast_nonneg _)
        apply Finset.prod_nonneg (fun idx _ => ?_)
        split_ifs
        · exact zero_le_one
        · exact htilted_nn _
      · exact pow_nonneg r.rho_pos.le _
    · exact div_nonneg (pow_nonneg hvpos.le _) (pow_nonneg hvpos.le _)
  calc ((retrievalFibre s_g A_g w_A).card : ℝ) *
        (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (a_g idx)) *
        P.groupMemoryMass F n g.val s_g *
        (∏ idx : Fin (J + F.ell),
          if ν.shared g.val idx ∨ idx ∈ A_g then 1 else tiltedMu F P n g.val (b_g idx)) *
        (P.V g.val) ^ (-(A_g.card : ℤ)) *
        r.rho ^ (zeroMemoryIndices s_g).card *
        (r.v ^ A_g.card / r.v ^ B_g.card)
      = ((∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
          P.groupMemoryMass F n g.val t_g) *
        ((((retrievalFibre t_g B_g w_B).card : ℝ) *
          (∏ idx : Fin (J + F.ell),
            if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) *
          r.rho ^ (zeroMemoryIndices s_g).card *
          (r.v ^ A_g.card / r.v ^ B_g.card)) *
          (P.V g.val) ^ (-(A_g.card : ℤ))) := by
        rw [hmass_eq]
        ring
    _ ≤ ((∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
          P.groupMemoryMass F n g.val t_g) *
        ((((retrievalFibre t_g B_g w_B).card : ℝ) *
          (∏ idx : Fin (J + F.ell),
            if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) *
          r.rho ^ (zeroMemoryIndices s_g).card *
          (r.v ^ A_g.card / r.v ^ B_g.card)) *
          (colRevConst F m * (P.V g.val) ^ (-(B_g.card : ℤ)))) := by
        apply mul_le_mul_of_nonneg_left _ hP_t_nn
        exact mul_le_mul_of_nonneg_left hV_swap hrest_nn
    _ = colRevConst F m *
          (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
          P.groupMemoryMass F n g.val t_g *
          (((retrievalFibre t_g B_g w_B).card : ℝ) *
            ((∏ idx : Fin (J + F.ell),
              if ν.shared g.val idx ∨ idx ∈ B_g then 1 else tiltedMu F P n g.val (a_g idx)) *
            (P.V g.val) ^ (-(B_g.card : ℤ)) *
            r.rho ^ (zeroMemoryIndices s_g).card *
            (r.v ^ A_g.card / r.v ^ B_g.card))) := by ring
    _ ≤ colRevConst F m *
          (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
          P.groupMemoryMass F n g.val t_g *
          ∑ f'_g : {idx : Fin (J + F.ell) // idx ∈ B_g} → Fin t_g.card,
            if bigGroupValid ν (-delta) g b_g t_g A_g B_g f'_g a_g then
              bigGroupWeight F r n ν (-delta) g b_g t_g A_g B_g f'_g a_g
            else 0 := by
        apply mul_le_mul_of_nonneg_left hfibre_sum_le
        have h1 : colRevConst F m *
            (∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
            P.groupMemoryMass F n g.val t_g =
            colRevConst F m *
            ((∏ idx : Fin (J + F.ell), tiltedMu F P n g.val (b_g idx)) *
              P.groupMemoryMass F n g.val t_g) := by ring
        rw [h1]
        exact mul_nonneg (colRevConst_pos F m).le hP_t_nn

end Erdos821.P3Edge
