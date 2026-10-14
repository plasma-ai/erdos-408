import Erdos821.P3LowRank.Fourier
import Erdos821.P3LowRank.HistorySum

/-! The low-rank equality contribution on literal valid truncated histories.

The birth event is an average of products of local multipliers (`Fourier.lean`).  Each
multiplier at a potential address depends only on the operation containing that birth:
initial slots on the initial boundary state, ghost addresses on their ghost choice, fresh
addresses on their birth-edge choice and target.  Edges without a fresh address in the
support keep the unmodified signed kernel; at most `2 * rank` edges are affected. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Lowrank

open Erdos821.Blueprint.Graph Erdos821.S2Core

attribute [local instance] bmsFintype ghostChoiceFintype edgeChoiceFintype

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Which local operation contains a potential birth address. -/
def addrLoc {M n B : ℕ} : BirthAddress P M n B → Unit ⊕ (Fin n ⊕ Fin (n + 1))
  | .inl _ => .inl ()
  | .inr (.inl (i, _, _)) => .inr (.inl i)
  | .inr (.inr (i, _, _)) => .inr (.inr i)

def initVal {M n B : ℕ} : BirthAddress P M n B → P.MemoryState M → ℕ
  | .inl (g, h), s => (s.2.1 g.val h).val
  | _, _ => 0

def ghostPerf {M n B : ℕ} (x : BirthAddress P M n B) {s t : P.MemoryState M}
    (c : GhostChoice s t) : Prop :=
  match x with
  | .inr (.inr (_, g, h)) => h.val < (c.2.1 g).val
  | _ => False

def ghostVal {M n B : ℕ} (x : BirthAddress P M n B) {s t : P.MemoryState M}
    (c : GhostChoice s t) : ℕ :=
  match x with
  | .inr (.inr (_, g, h)) =>
      if hh : h.val < (c.2.1 g).val then (c.2.2 g ⟨h.val, hh⟩).val else 0
  | _ => 0

def edgePerf (A : Model F P J m) {n B : ℕ} (x : BirthAddress P (J + F.ell) n B)
    {s : P.MemoryState (J + F.ell)} (c : EdgeChoice A s) : Prop :=
  match x with
  | .inr (.inl (_, g, h)) =>
      h ∈ Finset.univ.filter (fun h => ¬ (A.pattern c.2.2.1).shared g.val h ∧
        h ∉ c.2.2.2.2.2.1 g)
  | _ => False

def edgeVal (A : Model F P J m) {n B : ℕ} (x : BirthAddress P (J + F.ell) n B)
    {s : P.MemoryState (J + F.ell)} (t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) : ℕ :=
  match x with
  | .inr (.inl (_, g, h)) => ((permuteActive c.2.1 t).2.1 g.val h).val
  | _ => 0

/-- The enumeration of addresses used by `performedFin` and `valueFin`. -/
def addrIdx (P : PrimeGroups) (M n B : ℕ) :
    Fin (Fintype.card (BirthAddress P M n B)) → BirthAddress P M n B :=
  (Fintype.equivFin _).symm

section Local

variable {A : Model F P J m} {n : ℕ} (H : MemoryHistory A n) (B : ℕ)

theorem loc_init (x : BirthAddress P (J + F.ell) n B) (hx : addrLoc x = .inl ()) :
    H.addressPerformed B x ∧ H.addressValue B x = initVal x (H.before 0) := by
  rcases x with ⟨g, h⟩ | ⟨i, g, h⟩ | ⟨i, g, h⟩
  · exact ⟨trivial, rfl⟩
  · simp [addrLoc] at hx
  · simp [addrLoc] at hx

theorem loc_ghost (x : BirthAddress P (J + F.ell) n B) (i : Fin (n + 1))
    (hx : addrLoc x = .inr (.inr i)) :
    (H.addressPerformed B x ↔ ghostPerf x (H.ghost i)) ∧
      H.addressValue B x = ghostVal x (H.ghost i) := by
  rcases x with ⟨g, h⟩ | ⟨i', g, h⟩ | ⟨i', g, h⟩
  · simp [addrLoc] at hx
  · simp [addrLoc] at hx
  · simp only [addrLoc, Sum.inr.injEq] at hx
    subst hx
    exact ⟨Iff.rfl, rfl⟩

theorem loc_edge (x : BirthAddress P (J + F.ell) n B) (i : Fin n)
    (hx : addrLoc x = .inr (.inl i)) :
    (H.addressPerformed B x ↔ edgePerf A x (H.edge i)) ∧
      H.addressValue B x = edgeVal A x (H.before i.succ) (H.edge i) := by
  rcases x with ⟨g, h⟩ | ⟨i', g, h⟩ | ⟨i', g, h⟩
  · simp [addrLoc] at hx
  · simp only [addrLoc, Sum.inr.injEq, Sum.inl.injEq] at hx
    subst hx
    refine ⟨?_, rfl⟩
    simp only [MemoryHistory.addressPerformed, MemoryHistory.freshTargetSlots, edgePerf]
  · simp [addrLoc] at hx

end Local

variable (A : Model F P J m) (n B : ℕ)

/-- Initial-slot multipliers: a function of the initial boundary state. -/
def initF (w : Fin (Fintype.card (BirthAddress P (J + F.ell) n B)) → Prop → ℕ → ℂ)
    (U : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))
    (s : P.MemoryState (J + F.ell)) : ℂ :=
  ∏ j ∈ U.filter (fun j => addrLoc (addrIdx P (J + F.ell) n B j) = .inl ()),
    w j True (initVal (addrIdx P (J + F.ell) n B j) s)

/-- Ghost-address multipliers: a function of the original ghost choice. -/
def ghostF (w : Fin (Fintype.card (BirthAddress P (J + F.ell) n B)) → Prop → ℕ → ℂ)
    (U : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))
    (i : Fin (n + 1)) (s t : P.MemoryState (J + F.ell)) (c : GhostChoice s t) : ℂ :=
  ∏ j ∈ U.filter (fun j => addrLoc (addrIdx P (J + F.ell) n B j) = .inr (.inr i)),
    w j (ghostPerf (addrIdx P (J + F.ell) n B j) c) (ghostVal (addrIdx P (J + F.ell) n B j) c)

/-- Fresh-address multipliers: a function of the birth edge's choice and target. -/
def edgeF (w : Fin (Fintype.card (BirthAddress P (J + F.ell) n B)) → Prop → ℕ → ℂ)
    (U : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))
    (i : Fin n) (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) : ℂ :=
  ∏ j ∈ U.filter (fun j => addrLoc (addrIdx P (J + F.ell) n B j) = .inr (.inl i)),
    w j (edgePerf A (addrIdx P (J + F.ell) n B j) c)
      (edgeVal A (addrIdx P (J + F.ell) n B j) t c)

theorem mem_performedFin (H : MemoryHistory A n)
    (j : Fin (Fintype.card (BirthAddress P (J + F.ell) n B))) :
    j ∈ H.performedFin B ↔ H.addressPerformed B (addrIdx P (J + F.ell) n B j) := by
  simp [MemoryHistory.performedFin, addrIdx]

/-- The product over the support factors through the local operations. -/
theorem phi_factor (w : Fin (Fintype.card (BirthAddress P (J + F.ell) n B)) → Prop → ℕ → ℂ)
    (U : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B))))
    (H : MemoryHistory A n) :
    ∏ j ∈ U, w j (j ∈ H.performedFin B) (H.valueFin B j) =
      localFactor A n (initF n B w U) (ghostF n B w U) (edgeF A n B w U) H := by
  rw [← Finset.prod_fiberwise U (fun j => addrLoc (addrIdx P (J + F.ell) n B j)),
    Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_unique]
  have h1 : (∏ j ∈ U.filter (fun j => addrLoc (addrIdx P (J + F.ell) n B j) = .inl default),
      w j (j ∈ H.performedFin B) (H.valueFin B j)) = initF n B w U (H.before 0) := by
    unfold initF
    apply Finset.prod_congr (Finset.filter_congr (fun _ _ => Iff.rfl))
    intro j hj
    have hl := (Finset.mem_filter.mp hj).2
    have hloc := loc_init H B _ hl
    have hp : (j ∈ H.performedFin B) = True :=
      propext ⟨fun _ => trivial, fun _ => (mem_performedFin A n B H j).mpr hloc.1⟩
    rw [hp]
    exact congrArg _ hloc.2
  have h2 : ∀ i : Fin (n + 1),
      (∏ j ∈ U.filter (fun j => addrLoc (addrIdx P (J + F.ell) n B j) = .inr (.inr i)),
        w j (j ∈ H.performedFin B) (H.valueFin B j)) =
        ghostF n B w U i (H.before i) (H.after i) (H.ghost i) := by
    intro i
    unfold ghostF
    apply Finset.prod_congr (Finset.filter_congr (fun _ _ => Iff.rfl))
    intro j hj
    have hl := (Finset.mem_filter.mp hj).2
    have hloc := loc_ghost H B _ i hl
    have hp : (j ∈ H.performedFin B) = ghostPerf (addrIdx P (J + F.ell) n B j) (H.ghost i) :=
      propext ((mem_performedFin A n B H j).trans hloc.1)
    rw [hp]
    exact congrArg _ hloc.2
  have h3 : ∀ i : Fin n,
      (∏ j ∈ U.filter (fun j => addrLoc (addrIdx P (J + F.ell) n B j) = .inr (.inl i)),
        w j (j ∈ H.performedFin B) (H.valueFin B j)) =
        edgeF A n B w U i (H.after i.castSucc) (H.before i.succ) (H.edge i) := by
    intro i
    unfold edgeF
    apply Finset.prod_congr (Finset.filter_congr (fun _ _ => Iff.rfl))
    intro j hj
    have hl := (Finset.mem_filter.mp hj).2
    have hloc := loc_edge H B _ i hl
    have hp : (j ∈ H.performedFin B) = edgePerf A (addrIdx P (J + F.ell) n B j) (H.edge i) :=
      propext ((mem_performedFin A n B H j).trans hloc.1)
    rw [hp]
    exact congrArg _ hloc.2
  rw [h1]
  simp only [h2, h3, localFactor]
  ring

theorem addressValue_lt (H : MemoryHistory A n) (x : BirthAddress P (J + F.ell) n B) :
    H.addressValue B x < P.allPrimes.sup id + 1 := by
  have hp : ∀ (g : P.Group) (p : P.Prime g), p.val < P.allPrimes.sup id + 1 := fun g p =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) (group_prime_mem_all g p))
  rcases x with ⟨g, h⟩ | ⟨i, g, h⟩ | ⟨i, g, h⟩
  · exact hp _ _
  · exact hp _ _
  · simp only [MemoryHistory.addressValue]
    split_ifs
    · exact hp _ _
    · omega

/-- Edges carrying a fresh address of the support. -/
def affected (U : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B)))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ j ∈ U, addrLoc (addrIdx P (J + F.ell) n B j) = .inr (.inl i))

theorem card_affected_le (U : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B)))) :
    (affected (F := F) (J := J) n B U).card ≤ U.card := by
  let emb : Fin n ↪ Unit ⊕ (Fin n ⊕ Fin (n + 1)) :=
    ⟨fun i => .inr (.inl i), fun a b h => by simpa using h⟩
  calc (affected (F := F) (J := J) n B U).card
      = ((affected (F := F) (J := J) n B U).map emb).card := (Finset.card_map _).symm
    _ ≤ (U.image (fun j => addrLoc (addrIdx P (J + F.ell) n B j))).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨j, hj, hl⟩ := (Finset.mem_filter.mp hi).2
        exact Finset.mem_image.mpr ⟨j, hj, hl⟩
    _ ≤ U.card := Finset.card_image_le

theorem edgeF_unaffected (w : Fin (Fintype.card (BirthAddress P (J + F.ell) n B)) → Prop → ℕ → ℂ)
    (U : Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B)))) (i : Fin n)
    (hi : i ∉ affected (F := F) (J := J) n B U) :
    edgeF A n B w U i = fun _ _ _ => 1 := by
  funext s t c
  unfold edgeF
  rw [Finset.filter_eq_empty_iff.mpr, Finset.prod_empty]
  intro j hj hl
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, hl⟩)

theorem norm_prod_le_one {ι : Type*} (S : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ S, ‖f i‖ ≤ 1) :
    ‖∏ i ∈ S, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) hf

end Erdos821.P3Lowrank

open Erdos821.Blueprint.Graph Erdos821.S2Core Erdos821.P3Lowrank in
attribute [local instance] bmsFintype ghostChoiceFintype edgeChoiceFintype in
theorem Erdos821.S2Core.LowRankMemoryTask_proof : Erdos821.S2Core.LowRankMemoryTask := by
  intro F P J m n B A rho theta CG CE CA hCG hCE hCEA hmass hG hEA hE pi hpi
  obtain ⟨Ξ, hΞ, mm, hnorm, hcard, hrep⟩ :=
    exists_represents (P.allPrimes.sup id + 1) (Nat.succ_pos _) pi hpi
  let U := pi.biUnion id
  let Aff := affected (F := F) (J := J) n B U
  let c : Fin n → ℝ := fun i => if i ∈ Aff then CA else CE
  let LF : Ξ → MemoryHistory A n → ℂ := fun ξ =>
    localFactor A n (initF n B (mm ξ) U) (ghostF n B (mm ξ) U) (edgeF A n B (mm ξ) U)
  have hcardC : (Fintype.card Ξ : ℂ) ≠ 0 := by exact_mod_cast hcard.ne'
  -- Step 1: the frozen expression is an average of local-multiplier history sums.
  have hexpr : lowRankHistoryExpression A n B rho theta pi =
      (Fintype.card Ξ : ℂ)⁻¹ * ∑ ξ, ∑ d : BoundedHistoryData A n B,
        (if (mkH d).Valid then (mkH d).Weight rho theta * LF ξ (mkH d) else 0) := by
    unfold lowRankHistoryExpression
    rw [tsum_trunc A n B _ (fun H hH => if_neg (fun h => hH h.2.1))]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    have hT := mkH_truncated d
    have hr := hrep ((mkH d).performedFin B) ((mkH d).valueFin B)
      (fun j => addressValue_lt A n B (mkH d) _)
    have key : (Fintype.card Ξ : ℂ)⁻¹ * ∑ ξ, LF ξ (mkH d) =
        if birthEvent ((mkH d).performedFin B) ((mkH d).valueFin B) pi then 1 else 0 := by
      rw [hr]
      congr 1
      apply Finset.sum_congr rfl
      intro ξ _
      exact (phi_factor A n B (mm ξ) U (mkH d)).symm
    by_cases hV : (mkH d).Valid
    · simp only [if_pos hV]
      calc (if (mkH d).Valid ∧ (mkH d).Truncated B ∧
            birthEvent ((mkH d).performedFin B) ((mkH d).valueFin B) pi then
            (mkH d).Weight rho theta else 0)
          = (mkH d).Weight rho theta *
              (if birthEvent ((mkH d).performedFin B) ((mkH d).valueFin B) pi then 1 else 0) := by
            by_cases hev : birthEvent ((mkH d).performedFin B) ((mkH d).valueFin B) pi
            · rw [if_pos ⟨hV, hT, hev⟩, if_pos hev, mul_one]
            · rw [if_neg (fun h => hev h.2.2), if_neg hev, mul_zero]
        _ = (mkH d).Weight rho theta * ((Fintype.card Ξ : ℂ)⁻¹ * ∑ ξ, LF ξ (mkH d)) := by
            rw [key]
        _ = _ := by
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ξ _
            ring
    · rw [if_neg (fun h => hV h.1)]
      simp only [if_neg hV, Finset.sum_const_zero, mul_zero]
  -- Step 2: each local-multiplier sum is a finite kernel chain.
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    simp only [c]
    split_ifs <;> linarith
  have hloc : ∀ ξ, ‖∑ d : BoundedHistoryData A n B,
      (if (mkH d).Valid then (mkH d).Weight rho theta * LF ξ (mkH d) else 0)‖ ≤
        initialMemoryBoundaryMass A n * CG ^ (n + 1) * ∏ i, c i := by
    intro ξ
    apply local_history_bound A n B rho theta CG c _ _ _ hmass hCG hc
    · intro s
      exact norm_prod_le_one _ _ fun j _ => hnorm _ _ _ _
    · intro i
      exact hG i _ (fun s t c' => norm_prod_le_one _ _ fun j _ => hnorm _ _ _ _)
    · intro i
      by_cases hi : i ∈ Aff
      · have hci : c i = CA := if_pos hi
        rw [hci]
        exact hEA i _ (fun s t c' => norm_prod_le_one _ _ fun j _ => hnorm _ _ _ _)
      · have hci : c i = CE := if_neg hi
        rw [hci, edgeF_unaffected A n B (mm ξ) U i hi]
        exact hE i
  -- Step 3: the affected-edge count.
  have hk : Aff.card ≤ 2 * birthRank pi :=
    (card_affected_le n B U).trans (birth_support_le pi hpi)
  have hratio : 1 ≤ CA / CE := (one_le_div hCE).mpr hCEA
  have hprod : ∏ i, c i = CE ^ n * (CA / CE) ^ Aff.card := by
    have hci : ∀ i, c i = CE * (if i ∈ Aff then CA / CE else 1) := by
      intro i
      simp only [c]
      split_ifs
      · field_simp
      · ring
    simp only [hci]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prod_ite_mem_univ, Finset.prod_const]
  have hM : 0 ≤ initialMemoryBoundaryMass A n :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hfinal : initialMemoryBoundaryMass A n * CG ^ (n + 1) * ∏ i, c i ≤
      initialMemoryBoundaryMass A n * CG ^ (n + 1) * CE ^ n * (CA / CE) ^ (2 * birthRank pi) := by
    rw [hprod, ← mul_assoc]
    apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hratio hk)
    exact mul_nonneg (mul_nonneg hM (pow_nonneg hCG _)) (pow_nonneg hCE.le _)
  rw [hexpr]
  calc ‖(Fintype.card Ξ : ℂ)⁻¹ * ∑ ξ, ∑ d : BoundedHistoryData A n B,
        (if (mkH d).Valid then (mkH d).Weight rho theta * LF ξ (mkH d) else 0)‖
      ≤ (Fintype.card Ξ : ℝ)⁻¹ * ∑ ξ : Ξ,
          (initialMemoryBoundaryMass A n * CG ^ (n + 1) * ∏ i, c i) := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => hloc ξ)
    _ = initialMemoryBoundaryMass A n * CG ^ (n + 1) * ∏ i, c i := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (by exact_mod_cast hcard.ne'), one_mul]
    _ ≤ _ := hfinal

