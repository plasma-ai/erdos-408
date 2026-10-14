import Erdos821.S2.GhostTasks

noncomputable section
open scoped BigOperators

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph
attribute [local instance] Classical.propDecidable

universe u v

private def PiProdSummableProp (ι : Type u) [Fintype ι] : Prop :=
  ∀ (β : ι → Type v) (f : (i : ι) → β i → ℝ),
    (∀ i x, 0 ≤ f i x) → (∀ i, Summable (f i)) →
      Summable (fun x : (i : ι) → β i => ∏ i, f i (x i))

set_option maxHeartbeats 1000000 in
private theorem piProdSummable {ι : Type u} [Fintype ι]
    (β : ι → Type v) (f : (i : ι) → β i → ℝ)
    (h0 : ∀ i x, 0 ≤ f i x) (hs : ∀ i, Summable (f i)) :
    Summable (fun x : (i : ι) → β i => ∏ i, f i (x i)) := by
  classical
  refine Fintype.induction_empty_option
    (P := PiProdSummableProp) ?_ ?_ ?_ ι β f h0 hs
  · intro α γ _ e h γfam g hg0 hgs
    letI : Fintype α := Fintype.ofEquiv γ e.symm
    let αfam : α → Type v := fun a => γfam (e a)
    let g' : (a : α) → αfam a → ℝ := fun a x => g (e a) x
    have hα := h αfam g' (by intro a x; exact hg0 (e a) x)
      (by intro a; exact hgs (e a))
    let E : ((b : γ) → γfam b) ≃ ((a : α) → αfam a) :=
      Equiv.piCongrLeft' γfam e.symm
    have hcomp : Summable (fun x : (b : γ) → γfam b =>
        ∏ a : α, g' a (E x a)) := (E.summable_iff).2 hα
    have hterm (x : (b : γ) → γfam b) :
        (∏ a : α, g' a (E x a)) = ∏ b : γ, g b (x b) := by
      apply Fintype.prod_equiv e
      intro a
      simp [g', E, Equiv.piCongrLeft']
    convert hcomp using 1
    funext x
    exact (hterm x).symm
  · intro β f h0 hs
    exact summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
  · intro α _ ih β f h0 hs
    let β' : α → Type v := fun a => β (some a)
    let f' : (a : α) → β' a → ℝ := fun a x => f (some a) x
    have hrest : Summable (fun y : (a : α) → β' a => ∏ a, f' a (y a)) :=
      ih β' f' (by intro a x; exact h0 (some a) x)
        (by intro a; exact hs (some a))
    let E : ((o : Option α) → β o) ≃ β none × ((a : α) → β (some a)) :=
      Equiv.piOptionEquivProd
    have hnonneg : ∀ p : β none × ((a : α) → β (some a)),
        0 ≤ f none p.1 * ∏ a, f' a (p.2 a) := by
      intro p
      exact mul_nonneg (h0 none p.1)
        (Finset.prod_nonneg fun a _ => h0 (some a) (p.2 a))
    have hrows : ∀ x : β none, Summable (fun y : (a : α) → β (some a) =>
        f none x * ∏ a, f' a (y a)) := by
      intro x
      exact hrest.mul_left (f none x)
    have houter : Summable (fun x : β none =>
        ∑' y : (a : α) → β (some a), f none x * ∏ a, f' a (y a)) := by
      have heq (x : β none) :
          (∑' y : (a : α) → β (some a), f none x * ∏ a, f' a (y a)) =
            f none x * ∑' y : (a : α) → β (some a), ∏ a, f' a (y a) :=
        hrest.tsum_mul_left (f none x)
      simpa only [heq] using
        (hs none).mul_right (∑' y : (a : α) → β (some a), ∏ a, f' a (y a))
    have hprod : Summable (fun p : β none × ((a : α) → β (some a)) =>
        f none p.1 * ∏ a, f' a (p.2 a)) :=
      (summable_prod_of_nonneg hnonneg).2 ⟨hrows, houter⟩
    have hcomp : Summable (fun x : (o : Option α) → β o =>
        f none (x none) * ∏ a, f' a (x (some a))) := (E.summable_iff).2 hprod
    have hterm (x : (o : Option α) → β o) :
        (∏ o : Option α, f o (x o)) = f none (x none) * ∏ a : α, f' a (x (some a)) := by
      simp [f']
    convert hcomp using 1
    funext x
    exact hterm x

private def PiProdTsumProp (ι : Type u) [Fintype ι] : Prop :=
  ∀ (β : ι → Type v) (f : (i : ι) → β i → ℝ),
    (∀ i x, 0 ≤ f i x) → (∀ i, Summable (f i)) →
      Summable (fun x : (i : ι) → β i => ∏ i, f i (x i)) ∧
        (∑' x : (i : ι) → β i, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x

set_option maxHeartbeats 1000000 in
private theorem piProdTsum {ι : Type u} [Fintype ι]
    (β : ι → Type v) (f : (i : ι) → β i → ℝ)
    (h0 : ∀ i x, 0 ≤ f i x) (hs : ∀ i, Summable (f i)) :
    Summable (fun x : (i : ι) → β i => ∏ i, f i (x i)) ∧
      (∑' x : (i : ι) → β i, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x := by
  classical
  refine Fintype.induction_empty_option
    (P := PiProdTsumProp) ?_ ?_ ?_ ι β f h0 hs
  · intro α γ _ e h γfam g hg0 hgs
    letI : Fintype α := Fintype.ofEquiv γ e.symm
    let αfam : α → Type v := fun a => γfam (e a)
    let g' : (a : α) → αfam a → ℝ := fun a x => g (e a) x
    have hα := h αfam g' (by intro a x; exact hg0 (e a) x)
      (by intro a; exact hgs (e a))
    let E : ((b : γ) → γfam b) ≃ ((a : α) → αfam a) :=
      Equiv.piCongrLeft' γfam e.symm
    have hcomp : Summable (fun x : (b : γ) → γfam b =>
        ∏ a : α, g' a (E x a)) := (E.summable_iff).2 hα.1
    have hterm (x : (b : γ) → γfam b) :
        (∏ a : α, g' a (E x a)) = ∏ b : γ, g b (x b) := by
      apply Fintype.prod_equiv e
      intro a
      simp [g', E, Equiv.piCongrLeft']
    constructor
    · convert hcomp using 1
      funext x
      exact (hterm x).symm
    · calc
        (∑' x : (b : γ) → γfam b, ∏ b : γ, g b (x b)) =
            ∑' x : (b : γ) → γfam b, ∏ a : α, g' a (E x a) := by
              apply tsum_congr
              intro x
              exact (hterm x).symm
        _ = ∑' y : (a : α) → αfam a, ∏ a : α, g' a (y a) :=
              E.tsum_eq (fun y : (a : α) → αfam a => ∏ a : α, g' a (y a))
        _ = ∏ a : α, ∑' x : αfam a, g' a x := hα.2
        _ = ∏ b : γ, ∑' x : γfam b, g b x := by
              apply Fintype.prod_equiv e
              intro a
              rfl
  · intro β f h0 hs
    have hfin : Summable (fun x : (i : PEmpty) → β i => ∏ i, f i (x i)) :=
      summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
    constructor
    · exact hfin
    · simp [tsum_fintype]
  · intro α _ ih β f h0 hs
    let β' : α → Type v := fun a => β (some a)
    let f' : (a : α) → β' a → ℝ := fun a x => f (some a) x
    have hrest := ih β' f' (by intro a x; exact h0 (some a) x)
      (by intro a; exact hs (some a))
    let rest : ((a : α) → β (some a)) → ℝ := fun y => ∏ a, f' a (y a)
    let E : ((o : Option α) → β o) ≃ β none × ((a : α) → β (some a)) :=
      Equiv.piOptionEquivProd
    have hnonneg : ∀ p : β none × ((a : α) → β (some a)),
        0 ≤ f none p.1 * rest p.2 := by
      intro p
      exact mul_nonneg (h0 none p.1)
        (Finset.prod_nonneg fun a _ => h0 (some a) (p.2 a))
    have hrows : ∀ x : β none, Summable (fun y : (a : α) → β (some a) => f none x * rest y) := by
      intro x
      exact hrest.1.mul_left (f none x)
    have houter : Summable (fun x : β none => ∑' y : (a : α) → β (some a), f none x * rest y) := by
      have heq (x : β none) :
          (∑' y : (a : α) → β (some a), f none x * rest y) =
            f none x * ∑' y : (a : α) → β (some a), rest y :=
        hrest.1.tsum_mul_left (f none x)
      simpa only [heq] using
        (hs none).mul_right (∑' y : (a : α) → β (some a), rest y)
    have hprod : Summable (fun p : β none × ((a : α) → β (some a)) =>
        f none p.1 * rest p.2) :=
      (summable_prod_of_nonneg hnonneg).2 ⟨hrows, houter⟩
    have hcomp : Summable (fun x : (o : Option α) → β o =>
        f none (x none) * rest (fun a => x (some a))) := (E.summable_iff).2 hprod
    have hterm (x : (o : Option α) → β o) :
        (∏ o : Option α, f o (x o)) = f none (x none) * rest (fun a => x (some a)) := by
      simp [rest, f']
    constructor
    · convert hcomp using 1
      funext x
      exact hterm x
    · calc
        (∑' x : (o : Option α) → β o, ∏ o, f o (x o)) =
            ∑' x : (o : Option α) → β o, f none (x none) * rest (fun a => x (some a)) := by
              apply tsum_congr
              intro x
              exact hterm x
        _ = ∑' p : β none × ((a : α) → β (some a)), f none p.1 * rest p.2 :=
              E.tsum_eq (fun p : β none × ((a : α) → β (some a)) => f none p.1 * rest p.2)
        _ = ∑' x : β none, ∑' y : (a : α) → β (some a), f none x * rest y :=
              hprod.tsum_prod
        _ = (∑' x : β none, f none x) * (∑' y : (a : α) → β (some a), rest y) := by
              calc
                _ = ∑' x : β none, f none x * ∑' y : (a : α) → β (some a), rest y := by
                      apply tsum_congr
                      intro x
                      exact hrest.1.tsum_mul_left (f none x)
                _ = _ := (hs none).tsum_mul_right _
        _ = ∏ o : Option α, ∑' y, f o y := by
              have hrest' :
                  (∑' y : (a : α) → β (some a), rest y) =
                    ∏ a : α, ∑' y : β (some a), f (some a) y := by
                simpa [rest, f'] using hrest.2
              rw [hrest']
              simp

private theorem ghostBirthSeries_bound {α : Type*} [Fintype α]
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hμsum : (∑ a, μ a) ≤ 2)
    (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun c : Σ b : ℕ, Fin b → α =>
        x ^ c.1 / (c.1.factorial : ℝ) * ∏ i, μ (c.2 i)) ∧
      (∑' c : Σ b : ℕ, Fin b → α,
        x ^ c.1 / (c.1.factorial : ℝ) * ∏ i, μ (c.2 i)) ≤ Real.exp (2 * x) := by
  classical
  let f : (c : Σ b : ℕ, Fin b → α) → ℝ := fun c =>
    x ^ c.1 / (c.1.factorial : ℝ) * ∏ i, μ (c.2 i)
  have hf0 : ∀ c, 0 ≤ f c := by
    intro c
    apply mul_nonneg
    · exact div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg fun i _ => hμ (c.2 i)
  have hfiber (b : ℕ) : Summable (fun p : Fin b → α => f ⟨b, p⟩) :=
    summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
  let S : ℝ := ∑ a, μ a
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => hμ a
  have hS : S ≤ 2 := hμsum
  have hsum (b : ℕ) :
      (∑' p : Fin b → α, f ⟨b, p⟩) = (x * S) ^ b / (b.factorial : ℝ) := by
    rw [tsum_fintype]
    simp only [f]
    calc
      (∑ p : Fin b → α, x ^ b / (b.factorial : ℝ) * ∏ i, μ (p i)) =
          (x ^ b / (b.factorial : ℝ)) * ∑ p : Fin b → α, ∏ i, μ (p i) := by
            rw [Finset.mul_sum]
      _ = (x * S) ^ b / (b.factorial : ℝ) := by
            rw [← Fintype.sum_pow μ b]
            dsimp [S]
            ring
  have houter : Summable (fun b : ℕ => ∑' p : Fin b → α, f ⟨b, p⟩) := by
    simpa only [hsum] using Real.summable_pow_div_factorial (x * S)
  have hsumma : Summable f :=
    (summable_sigma_of_nonneg hf0).2 ⟨hfiber, houter⟩
  have htotal :
      (∑' c : Σ b : ℕ, Fin b → α, f c) = Real.exp (x * S) := by
    calc
      (∑' c : Σ b : ℕ, Fin b → α, f c) =
          ∑' b : ℕ, ∑' p : Fin b → α, f ⟨b, p⟩ :=
            Summable.tsum_sigma' hfiber hsumma
      _ = ∑' b : ℕ, (x * S) ^ b / (b.factorial : ℝ) := by
            apply tsum_congr
            exact hsum
      _ = Real.exp (x * S) := by
            rw [Real.exp_eq_exp_ℝ]
            exact (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) (x * S)).symm
  refine ⟨hsumma, ?_⟩
  rw [htotal]
  apply Real.exp_le_exp.mpr
  calc
    x * S ≤ x * 2 := mul_le_mul_of_nonneg_left hS hx
    _ = 2 * x := by ring

private theorem ghostDeletedPowerSum {α : Type*} [Fintype α] [DecidableEq α]
    (Z : Finset α) (a b : ℝ) :
    (∑ A : {A : Finset α // A ⊆ Z},
      b ^ A.1.card * a ^ (Z.card - A.1.card)) = (a + b) ^ Z.card := by
  classical
  let e : {A : Finset α // A ⊆ Z} ≃ {A : Finset α // A ∈ Z.powerset} :=
    Equiv.subtypeEquivRight (fun A => (Finset.mem_powerset (s := A) (t := Z)).symm)

  calc
    _ = ∑ A : {A : Finset α // A ∈ Z.powerset},
        b ^ A.1.card * a ^ (Z.card - A.1.card) := by
          apply Fintype.sum_equiv e
          intro A
          rfl
    _ = ∑ A ∈ Z.powerset, b ^ A.card * a ^ (Z.card - A.card) := by
          simpa using Finset.sum_attach Z.powerset
            (fun A : Finset α => b ^ A.card * a ^ (Z.card - A.card))
    _ = (a + b) ^ Z.card := by
          simpa [add_comm] using Finset.sum_pow_mul_eq_add_pow b a Z

private theorem ghostDeletionFactor_bound {α : Type*} [Fintype α] [DecidableEq α]
    (Z : Finset α) (N : ℕ) (hZN : Z.card ≤ N) (a b v : ℝ)
    (hv : 0 < v) (hx0 : 0 ≤ a + b / v) (hx1 : a + b / v ≤ 1) :
    (∑' A : {A : Finset α // A ⊆ Z},
      a ^ (Z.card - A.1.card) * b ^ A.1.card * v ^ (N - A.1.card)) ≤ v ^ N := by
  classical
  have hsum : Summable (fun A : {A : Finset α // A ⊆ Z} =>
      a ^ (Z.card - A.1.card) * b ^ A.1.card * v ^ (N - A.1.card)) :=
    summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
  rw [tsum_fintype]
  calc
    (∑ A : {A : Finset α // A ⊆ Z},
        a ^ (Z.card - A.1.card) * b ^ A.1.card * v ^ (N - A.1.card)) =
        v ^ N * ∑ A : {A : Finset α // A ⊆ Z},
          (b / v) ^ A.1.card * a ^ (Z.card - A.1.card) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro A hA
            have hAle : A.1.card ≤ N := (Finset.card_le_card A.2).trans hZN
            have hvpow : v ^ (N - A.1.card) = v ^ N * (v ^ A.1.card)⁻¹ :=
              pow_sub₀ v (ne_of_gt hv) hAle
            rw [hvpow]
            ring_nf
    _ = v ^ N * (a + b / v) ^ Z.card := by
          rw [ghostDeletedPowerSum]
    _ ≤ v ^ N * 1 := by
          have hpown : ∀ n : ℕ, (a + b / v) ^ n ≤ 1 := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
                rw [pow_succ]
                calc
                  (a + b / v) ^ n * (a + b / v) ≤
                      (a + b / v) ^ n * 1 :=
                        mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0 n)
                  _ ≤ 1 := by simpa using ih
          exact mul_le_mul_of_nonneg_left (hpown Z.card) (pow_nonneg hv.le N)
    _ = v ^ N := by ring

lemma visitQ_eq_q_or_sqrt (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    visitQ F.q n i = F.q ∨ visitQ F.q n i = Real.sqrt F.q := by
  unfold visitQ
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma visitQ_pos (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    0 < visitQ F.q n i := by
  rcases visitQ_eq_q_or_sqrt F n i with h | h
  · rw [h]; exact F.q_pos
  · rw [h]; exact Real.sqrt_pos.2 F.q_pos

lemma visitQ_lt_one (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    visitQ F.q n i < 1 := by
  rcases visitQ_eq_q_or_sqrt F n i with h | h
  · rw [h]; exact F.q_lt
  · rw [h]
    by_contra hnot
    have hge : (1 : ℝ) ≤ Real.sqrt F.q := le_of_not_gt hnot
    have hs := Real.sq_sqrt (le_of_lt F.q_pos)
    have hp := mul_nonneg (Real.sqrt_nonneg F.q) (sub_nonneg.mpr hge)
    nlinarith [F.q_lt]

lemma eta_pos (F : FixedData) (n : ℕ) (i : Fin (n + 1)) :
    0 < eta F n i := by
  unfold eta
  linarith [visitQ_lt_one F n i]

lemma visitQ_memory_damping (F : FixedData) (r : MemoryParameters F)
    (n : ℕ) (i : Fin (n + 1)) :
    visitQ F.q n i / r.rho ^ (2 : ℕ) +
      2 * max 1 F.vMax * eta F n i / (r.rho * r.v) < 1 := by
  rcases visitQ_eq_q_or_sqrt F n i with h | h
  · simpa [eta, h] using r.damping F.q (Or.inl rfl)
  · simpa [eta, h] using r.damping (Real.sqrt F.q) (Or.inr rfl)

lemma rowsDeleteMemoryIndices_card {P : PrimeGroups} {g : P.Group}
    (z : P.Memory g) (A : Finset (Fin z.card)) :
    (deleteMemoryIndices z A).card = z.card - A.card := by
  classical
  unfold deleteMemoryIndices
  rw [Multiset.coe_card, List.length_map, Finset.length_toList]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
  simp

lemma rowsZeroBirthBatch_card {P : PrimeGroups} {g : P.Group} {b : ℕ}
    (p : Fin b → P.Prime g) : (zeroBirthBatch p).card = b := by
  simp [zeroBirthBatch]


variable {P : PrimeGroups}

abbrev GhostBirthBatch (g : P.BigGroup) := Σ b : ℕ, Fin b → P.Prime g.val

abbrev GhostDeletedChoice {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup) :=
  {A : Finset (Fin ((s.2.2 g).card)) // A ⊆ zeroMemoryIndices (s.2.2 g)}

abbrev GhostGroupTransition {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup) :=
  GhostDeletedChoice s g × GhostBirthBatch g

/-- A row transition before its target memory is grouped with other choices. -/
abbrev GhostTransition {M : ℕ} (s : P.MemoryState M) :=
  (g : P.BigGroup) → GhostGroupTransition s g

def ghostTransitionDeleted {M : ℕ} {s : P.MemoryState M}
    (c : GhostTransition s) (g : P.BigGroup) := (c g).1.1

def ghostTransitionBirths {M : ℕ} {s : P.MemoryState M}
    (c : GhostTransition s) (g : P.BigGroup) := (c g).2

def ghostTransitionTarget {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : P.MemoryState M :=
  (s.1, s.2.1, fun g =>
    deleteMemoryIndices (s.2.2 g) (ghostTransitionDeleted c g) +
      zeroBirthBatch (ghostTransitionBirths c g).2)

lemma ghostTransitionTarget_card {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) (g : P.BigGroup) :
    ((ghostTransitionTarget s c).2.2 g).card =
      (s.2.2 g).card - (ghostTransitionDeleted c g).card +
        (ghostTransitionBirths c g).1 := by
  simp [ghostTransitionTarget, ghostTransitionDeleted, ghostTransitionBirths,
    rowsDeleteMemoryIndices_card, rowsZeroBirthBatch_card, Multiset.card_add]

def ghostTransitionAsChoice {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : GhostChoice s (ghostTransitionTarget s c) := by
  classical
  refine Prod.mk (fun g : P.BigGroup => ghostTransitionDeleted c g)
    (Sigma.mk (fun g : P.BigGroup =>
      (⟨(ghostTransitionBirths c g).1, ?_⟩ :
        Fin (((ghostTransitionTarget s c).2.2 g).card + 1)))
      (fun g : P.BigGroup => (ghostTransitionBirths c g).2))
  have hc := ghostTransitionTarget_card s c g
  have hdel : (ghostTransitionDeleted c g).card ≤ (s.2.2 g).card := by
    simpa using Finset.card_le_card (Finset.subset_univ (ghostTransitionDeleted c g))
  omega

lemma ghostTransitionAsChoice_valid {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) :
    ghostChoiceValid (ghostTransitionAsChoice s c) := by
  intro g
  change ghostTransitionDeleted c g ⊆ zeroMemoryIndices (s.2.2 g) ∧
    deleteMemoryIndices (s.2.2 g) (ghostTransitionDeleted c g) +
      zeroBirthBatch (ghostTransitionBirths c g).2 =
        (ghostTransitionTarget s c).2.2 g
  constructor
  · exact (c g).1.2
  · rfl

def ghostGroupRowFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) : ℝ :=
  let A := c.1.1
  let b := (c.2).1
  ((visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - A.card) *
    (eta F n i / rho) ^ A.card *
    v ^ ((s.2.2 g).card - A.card)) *
    (((d * eta F n i * P.V g.val * v / rho) ^ b /
        (b.factorial : ℝ)) *
      ∏ j : Fin b, tiltedMu F P n g.val ((c.2).2 j))

def ghostGroupRevFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) : ℝ :=
  let A := c.1.1
  let b := (c.2).1
  ((visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - A.card) *
    (eta F n i / rho) ^ A.card *
    (d * P.V g.val) ^ A.card *
    v ^ ((s.2.2 g).card - A.card)) *
    (((eta F n i * v / rho) ^ b /
        (b.factorial : ℝ)) *
      ∏ j : Fin b, tiltedMu F P n g.val ((c.2).2 j))

private theorem ghostGroupRowFactor_summable_bound
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (hV : 0 < P.V g.val ∧ P.V g.val ≤ F.vMax)
    (hbase : ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2) :
    Summable (fun c : GhostGroupTransition s g =>
      ghostGroupRowFactor F n r.rho d r.v i s g c) ∧
    (∑' c : GhostGroupTransition s g,
      ghostGroupRowFactor F n r.rho d r.v i s g c) ≤
      r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
  classical
  let Z := zeroMemoryIndices (s.2.2 g)
  let α : ℝ := visitQ F.q n i / r.rho ^ (2 : ℕ)
  let δ : ℝ := eta F n i / r.rho
  let X : ℝ := d * eta F n i * P.V g.val * r.v / r.rho
  let D : GhostDeletedChoice s g → ℝ := fun A =>
    α ^ (Z.card - A.1.card) * δ ^ A.1.card * r.v ^ ((s.2.2 g).card - A.1.card)
  let B : GhostBirthBatch g → ℝ := fun b =>
    X ^ b.1 / (b.1.factorial : ℝ) * ∏ j : Fin b.1, tiltedMu F P n g.val (b.2 j)
  have hEta : 0 < eta F n i := eta_pos F n i
  have hEta1 : eta F n i ≤ 1 := by
    unfold eta
    linarith [visitQ_pos F n i]
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hdle : d ≤ 2 := by rcases hd with rfl | rfl <;> norm_num
  have hmu0 : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p := by
    intro p
    have hp : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos (P.prime g.val p.val p.property))
    unfold tiltedMu
    exact le_of_lt (inv_pos.mpr (mul_pos (mul_pos hV.1 hp) (hbase p)))
  have hXpos : 0 < X := by
    dsimp [X]
    positivity [hEta, hV.1, r.v_gt, r.rho_pos, hdpos]
  have hbirth := ghostBirthSeries_bound (fun p : P.Prime g.val =>
      tiltedMu F P n g.val p) hmu0 hmu X hXpos.le
  have hD_nonneg : ∀ A : GhostDeletedChoice s g, 0 ≤ D A := by
    intro A
    dsimp [D, α, δ]
    positivity [visitQ_pos F n i, hEta, r.rho_pos, r.v_gt]
  have hB_nonneg : ∀ b : GhostBirthBatch g, 0 ≤ B b := by
    intro b
    dsimp [B]
    apply mul_nonneg
    · exact div_nonneg (pow_nonneg hXpos.le _) (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg fun j _ => hmu0 (b.2 j)
  have hnonneg : ∀ c : GhostGroupTransition s g, 0 ≤ D c.1 * B c.2 := by
    intro c
    exact mul_nonneg (hD_nonneg c.1) (hB_nonneg c.2)
  have hrows : ∀ A : GhostDeletedChoice s g,
      Summable (fun b : GhostBirthBatch g => D A * B b) := by
    intro A
    exact hbirth.1.mul_left (D A)
  have houter : Summable (fun A : GhostDeletedChoice s g =>
      ∑' b : GhostBirthBatch g, D A * B b) :=
    summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
  have hlocal : Summable (fun c : GhostGroupTransition s g => D c.1 * B c.2) :=
    (summable_prod_of_nonneg hnonneg).2 ⟨hrows, houter⟩
  have hlocal_eq :
      (∑' c : GhostGroupTransition s g, D c.1 * B c.2) =
        (∑' A : GhostDeletedChoice s g, D A) *
          (∑' b : GhostBirthBatch g, B b) := by
    rw [hlocal.tsum_prod]
    calc
      (∑' A : GhostDeletedChoice s g, ∑' b : GhostBirthBatch g, D A * B b) =
          ∑' A : GhostDeletedChoice s g, D A * ∑' b : GhostBirthBatch g, B b := by
            apply tsum_congr
            intro A
            exact hbirth.1.tsum_mul_left (D A)
      _ = (∑' A : GhostDeletedChoice s g, D A) *
            (∑' b : GhostBirthBatch g, B b) := by
              simpa only [tsum_fintype] using
                (Finset.sum_mul (Finset.univ : Finset (GhostDeletedChoice s g)) D
                  (∑' b : GhostBirthBatch g, B b)).symm
  have hZle : Z.card ≤ (s.2.2 g).card := by
    have hcard := Finset.card_le_card (Finset.subset_univ Z)
    simpa [Z] using hcard
  have hdiv : (eta F n i / r.rho) / r.v = eta F n i / (r.rho * r.v) := by
    field_simp
  have hfactor : 1 ≤ 2 * max 1 F.vMax := by
    have := le_max_left (1 : ℝ) F.vMax
    nlinarith
  have hdelrate :
      0 ≤ α + δ / r.v ∧ α + δ / r.v ≤ 1 := by
    constructor
    · dsimp [α, δ]
      positivity [visitQ_pos F n i, hEta, r.rho_pos, r.v_gt]
    · rw [hdiv]
      have hle : eta F n i / (r.rho * r.v) ≤
          2 * max 1 F.vMax * eta F n i / (r.rho * r.v) := by
        calc
          eta F n i / (r.rho * r.v) =
              1 * (eta F n i / (r.rho * r.v)) := by ring
          _ ≤ 2 * max 1 F.vMax * (eta F n i / (r.rho * r.v)) :=
            mul_le_mul_of_nonneg_right hfactor (by positivity [hEta, r.rho_pos, r.v_gt])
          _ = 2 * max 1 F.vMax * eta F n i / (r.rho * r.v) := by ring
      have hdam := visitQ_memory_damping F r n i
      dsimp [α, δ] at *
      nlinarith
  have hrv : 0 < r.v := by linarith [r.v_gt]
  have hdel := ghostDeletionFactor_bound Z (s.2.2 g).card hZle α δ r.v
    hrv hdelrate.1 hdelrate.2
  have hdel_nonneg : 0 ≤ ∑' A : GhostDeletedChoice s g, D A := by
    apply tsum_nonneg
    exact hD_nonneg
  have hBtsum : (∑' b : GhostBirthBatch g, B b) ≤ Real.exp (2 * X) := by
    exact hbirth.2
  have hBnonneg : 0 ≤ ∑' b : GhostBirthBatch g, B b := by
    apply tsum_nonneg
    exact hB_nonneg
  have hVmax : P.V g.val ≤ max 1 F.vMax :=
    hV.2.trans (le_max_right 1 F.vMax)
  have hsmall : d * eta F n i * P.V g.val ≤ 2 * max 1 F.vMax := by
    calc
      d * eta F n i * P.V g.val ≤ d * P.V g.val := by
        have hde : d * eta F n i ≤ d := by
          calc
            d * eta F n i ≤ d * 1 := mul_le_mul_of_nonneg_left hEta1 hdpos.le
            _ = d := by ring
        exact mul_le_mul_of_nonneg_right hde hV.1.le
      _ ≤ 2 * P.V g.val := mul_le_mul_of_nonneg_right hdle hV.1.le
      _ ≤ 2 * max 1 F.vMax := by
        exact mul_le_mul_of_nonneg_left hVmax (by norm_num)
  have hXle : X ≤ 2 * max 1 F.vMax * r.v / r.rho := by
    dsimp [X]
    calc
      d * eta F n i * P.V g.val * r.v / r.rho ≤
          (2 * max 1 F.vMax) * r.v / r.rho := by
            apply div_le_div_of_nonneg_right _ r.rho_pos.le
            exact mul_le_mul_of_nonneg_right hsmall (le_trans (by norm_num) r.v_gt.le)
      _ = 2 * max 1 F.vMax * r.v / r.rho := by ring
  have hExp : Real.exp (2 * X) ≤ Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
    apply Real.exp_le_exp.mpr
    calc
      2 * X ≤ 2 * (2 * max 1 F.vMax * r.v / r.rho) :=
        mul_le_mul_of_nonneg_left hXle (by norm_num)
      _ = 4 * max 1 F.vMax * r.v / r.rho := by ring
  have hbound : (∑' c : GhostGroupTransition s g, D c.1 * B c.2) ≤
      r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
    rw [hlocal_eq]
    calc
      (∑' A : GhostDeletedChoice s g, D A) *
          (∑' b : GhostBirthBatch g, B b) ≤
        r.v ^ (s.2.2 g).card * Real.exp (2 * X) := by
          calc
            _ ≤ r.v ^ (s.2.2 g).card * (∑' b : GhostBirthBatch g, B b) :=
              mul_le_mul_of_nonneg_right hdel hBnonneg
            _ ≤ _ := mul_le_mul_of_nonneg_left hBtsum
              (pow_nonneg (le_trans (by norm_num) r.v_gt.le) _)
      _ ≤ r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho) :=
          mul_le_mul_of_nonneg_left hExp
            (pow_nonneg (le_trans (by norm_num) r.v_gt.le) _)
  refine ⟨?_, hbound⟩
  simpa [ghostGroupRowFactor, D, B, X, δ, α] using hlocal

private theorem ghostGroupRevFactor_summable_bound
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (hV : 0 < P.V g.val ∧ P.V g.val ≤ F.vMax)
    (hbase : ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2) :
    Summable (fun c : GhostGroupTransition s g =>
      ghostGroupRevFactor F n r.rho d r.v i s g c) ∧
    (∑' c : GhostGroupTransition s g,
      ghostGroupRevFactor F n r.rho d r.v i s g c) ≤
      r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
  classical
  let Z := zeroMemoryIndices (s.2.2 g)
  let α : ℝ := visitQ F.q n i / r.rho ^ (2 : ℕ)
  let δ : ℝ := eta F n i / r.rho * (d * P.V g.val)
  let X : ℝ := eta F n i * r.v / r.rho
  let D : GhostDeletedChoice s g → ℝ := fun A =>
    α ^ (Z.card - A.1.card) * δ ^ A.1.card * r.v ^ ((s.2.2 g).card - A.1.card)
  let B : GhostBirthBatch g → ℝ := fun b =>
    X ^ b.1 / (b.1.factorial : ℝ) * ∏ j : Fin b.1, tiltedMu F P n g.val (b.2 j)
  have hEta : 0 < eta F n i := eta_pos F n i
  have hEta1 : eta F n i ≤ 1 := by
    unfold eta
    linarith [visitQ_pos F n i]
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hdle : d ≤ 2 := by rcases hd with rfl | rfl <;> norm_num
  have hmu0 : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p := by
    intro p
    have hp : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos (P.prime g.val p.val p.property))
    unfold tiltedMu
    exact le_of_lt (inv_pos.mpr (mul_pos (mul_pos hV.1 hp) (hbase p)))
  have hXpos : 0 < X := by
    dsimp [X]
    positivity [eta_pos F n i, r.v_gt, r.rho_pos]
  have hbirth := ghostBirthSeries_bound (fun p : P.Prime g.val =>
      tiltedMu F P n g.val p) hmu0 hmu X hXpos.le
  have hD_nonneg : ∀ A : GhostDeletedChoice s g, 0 ≤ D A := by
    intro A
    dsimp [D, α, δ]
    positivity [visitQ_pos F n i, hEta, hV.1, hdpos, r.rho_pos, r.v_gt]
  have hB_nonneg : ∀ b : GhostBirthBatch g, 0 ≤ B b := by
    intro b
    dsimp [B]
    apply mul_nonneg
    · exact div_nonneg (pow_nonneg hXpos.le _) (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg fun j _ => hmu0 (b.2 j)
  have hnonneg : ∀ c : GhostGroupTransition s g, 0 ≤ D c.1 * B c.2 := by
    intro c
    exact mul_nonneg (hD_nonneg c.1) (hB_nonneg c.2)
  have hrows : ∀ A : GhostDeletedChoice s g,
      Summable (fun b : GhostBirthBatch g => D A * B b) := by
    intro A
    exact hbirth.1.mul_left (D A)
  have houter : Summable (fun A : GhostDeletedChoice s g =>
      ∑' b : GhostBirthBatch g, D A * B b) :=
    summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
  have hlocal : Summable (fun c : GhostGroupTransition s g => D c.1 * B c.2) :=
    (summable_prod_of_nonneg hnonneg).2 ⟨hrows, houter⟩
  have hlocal_eq :
      (∑' c : GhostGroupTransition s g, D c.1 * B c.2) =
        (∑' A : GhostDeletedChoice s g, D A) *
          (∑' b : GhostBirthBatch g, B b) := by
    rw [hlocal.tsum_prod]
    calc
      (∑' A : GhostDeletedChoice s g, ∑' b : GhostBirthBatch g, D A * B b) =
          ∑' A : GhostDeletedChoice s g, D A * ∑' b : GhostBirthBatch g, B b := by
            apply tsum_congr
            intro A
            exact hbirth.1.tsum_mul_left (D A)
      _ = (∑' A : GhostDeletedChoice s g, D A) *
            (∑' b : GhostBirthBatch g, B b) := by
              simpa only [tsum_fintype] using
                (Finset.sum_mul (Finset.univ : Finset (GhostDeletedChoice s g)) D
                  (∑' b : GhostBirthBatch g, B b)).symm
  have hZle : Z.card ≤ (s.2.2 g).card := by
    have hcard := Finset.card_le_card (Finset.subset_univ Z)
    simpa [Z] using hcard
  have hrv : 0 < r.v := by linarith [r.v_gt]
  have hdiv : (eta F n i / r.rho * (d * P.V g.val)) / r.v =
      (d * P.V g.val) * (eta F n i / (r.rho * r.v)) := by
    field_simp
  have hfactor : 1 ≤ 2 * max 1 F.vMax := by
    have := le_max_left (1 : ℝ) F.vMax
    nlinarith
  have hdelrate :
      0 ≤ α + δ / r.v ∧ α + δ / r.v ≤ 1 := by
    constructor
    · dsimp [α, δ]
      positivity [visitQ_pos F n i, hEta, hV.1, hdpos, r.rho_pos, hrv]
    · rw [hdiv]
      have hDV : d * P.V g.val ≤ 2 * max 1 F.vMax := by
        calc
          d * P.V g.val ≤ 2 * P.V g.val := mul_le_mul_of_nonneg_right hdle hV.1.le
          _ ≤ 2 * max 1 F.vMax :=
            mul_le_mul_of_nonneg_left (hV.2.trans (le_max_right 1 F.vMax)) (by norm_num)
      have hle : (d * P.V g.val) * (eta F n i / (r.rho * r.v)) ≤
          2 * max 1 F.vMax * eta F n i / (r.rho * r.v) := by
        calc
          (d * P.V g.val) * (eta F n i / (r.rho * r.v)) ≤
              (2 * max 1 F.vMax) * (eta F n i / (r.rho * r.v)) :=
            mul_le_mul_of_nonneg_right hDV (by positivity [hEta, r.rho_pos, hrv])
          _ = 2 * max 1 F.vMax * eta F n i / (r.rho * r.v) := by ring
      have hdam := visitQ_memory_damping F r n i
      dsimp [α, δ] at *
      nlinarith
  have hdel := ghostDeletionFactor_bound Z (s.2.2 g).card hZle α δ r.v
    hrv hdelrate.1 hdelrate.2
  have hBtsum : (∑' b : GhostBirthBatch g, B b) ≤ Real.exp (2 * X) := hbirth.2
  have hBnonneg : 0 ≤ ∑' b : GhostBirthBatch g, B b := by
    apply tsum_nonneg
    exact hB_nonneg
  have hXle : X ≤ max 1 F.vMax * r.v / r.rho := by
    dsimp [X]
    calc
      eta F n i * r.v / r.rho ≤ r.v / r.rho := by
        apply div_le_div_of_nonneg_right _ r.rho_pos.le
        simpa using mul_le_mul_of_nonneg_right hEta1 hrv.le
      _ ≤ max 1 F.vMax * r.v / r.rho := by
        apply div_le_div_of_nonneg_right _ r.rho_pos.le
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left 1 F.vMax) hrv.le
  have hExp : Real.exp (2 * X) ≤ Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
    apply Real.exp_le_exp.mpr
    calc
      2 * X ≤ 2 * (max 1 F.vMax * r.v / r.rho) :=
        mul_le_mul_of_nonneg_left hXle (by norm_num)
      _ ≤ 4 * max 1 F.vMax * r.v / r.rho := by
        let K := max 1 F.vMax
        have hcoef : 2 * K ≤ 4 * K := by
          have hK : 0 ≤ K := le_max_of_le_left (by norm_num)
          nlinarith [hK]
        have hvR : 0 ≤ r.v / r.rho := div_nonneg hrv.le r.rho_pos.le
        calc
          2 * (K * r.v / r.rho) = (2 * K) * (r.v / r.rho) := by ring
          _ ≤ (4 * K) * (r.v / r.rho) := mul_le_mul_of_nonneg_right hcoef hvR
          _ = 4 * max 1 F.vMax * r.v / r.rho := by dsimp [K]; ring
  have hbound : (∑' c : GhostGroupTransition s g, D c.1 * B c.2) ≤
      r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho) := by
    rw [hlocal_eq]
    calc
      (∑' A : GhostDeletedChoice s g, D A) *
          (∑' b : GhostBirthBatch g, B b) ≤
        r.v ^ (s.2.2 g).card * Real.exp (2 * X) := by
          calc
            _ ≤ r.v ^ (s.2.2 g).card * (∑' b : GhostBirthBatch g, B b) :=
              mul_le_mul_of_nonneg_right hdel hBnonneg
            _ ≤ _ := mul_le_mul_of_nonneg_left hBtsum
              (pow_nonneg (le_trans (by norm_num) r.v_gt.le) _)
      _ ≤ r.v ^ (s.2.2 g).card * Real.exp (4 * max 1 F.vMax * r.v / r.rho) :=
          mul_le_mul_of_nonneg_left hExp
            (pow_nonneg (le_trans (by norm_num) r.v_gt.le) _)
  have heq (c : GhostGroupTransition s g) :
      ghostGroupRevFactor F n r.rho d r.v i s g c = D c.1 * B c.2 := by
    dsimp [ghostGroupRevFactor, D, B, X, δ, α, Z]
    rw [mul_pow]
    ring
  have hfun : (fun c : GhostGroupTransition s g =>
      ghostGroupRevFactor F n r.rho d r.v i s g c) = (fun c => D c.1 * B c.2) :=
    funext heq
  constructor
  · simpa only [hfun] using hlocal
  · rw [hfun]
    exact hbound

def ghostTransitionRowFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : ℝ :=
  ∏ g : P.BigGroup, ghostGroupRowFactor F n rho d v i s g (c g)

def ghostTransitionRevFactor (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) : ℝ :=
  ∏ g : P.BigGroup, ghostGroupRevFactor F n rho d v i s g (c g)

def ghostTransitionGroupRawWeight (F : FixedData) (n : ℕ) (rho : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g) : ℝ :=
  let A := c.1.1
  let b := c.2.1
  (-(eta F n i / rho)) ^ A.card *
    (visitQ F.q n i / rho ^ (2 : ℕ)) ^
      ((zeroMemoryIndices (s.2.2 g)).card - A.card) *
    ((b.factorial : ℝ)⁻¹) *
    (-(eta F n i * P.V g.val / rho)) ^ b *
    ∏ j : Fin b, tiltedMu F P n g.val (c.2.2 j)

private theorem ghostTransitionGroupRawWeight_abs
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (c : GhostGroupTransition s g)
    (hV : 0 < P.V g.val)
    (hbase : ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    |ghostTransitionGroupRawWeight F n r.rho i s g c| =
      (eta F n i / r.rho) ^ c.1.1.card *
      (visitQ F.q n i / r.rho ^ (2 : ℕ)) ^
        ((zeroMemoryIndices (s.2.2 g)).card - c.1.1.card) *
      ((c.2.1.factorial : ℝ)⁻¹) *
      (eta F n i * P.V g.val / r.rho) ^ c.2.1 *
      ∏ j : Fin c.2.1, tiltedMu F P n g.val (c.2.2 j) := by
  classical
  have hμ : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p := by
    intro p
    have hp : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos (P.prime g.val p.val p.property))
    unfold tiltedMu
    exact le_of_lt (inv_pos.mpr (mul_pos (mul_pos hV hp) (hbase p)))
  have heta : 0 ≤ eta F n i / r.rho := div_nonneg (eta_pos F n i).le r.rho_pos.le
  have hq : 0 ≤ visitQ F.q n i / r.rho ^ (2 : ℕ) :=
    div_nonneg (visitQ_pos F n i).le (pow_nonneg r.rho_pos.le _)
  have hb : 0 ≤ eta F n i * P.V g.val / r.rho :=
    div_nonneg (mul_nonneg (eta_pos F n i).le hV.le) r.rho_pos.le
  have hf : 0 ≤ ((c.2.1.factorial : ℝ)⁻¹) := by positivity
  have hμp : 0 ≤ ∏ j : Fin c.2.1, tiltedMu F P n g.val (c.2.2 j) :=
    Finset.prod_nonneg fun j _ => hμ _
  have hnegA : |(-(eta F n i / r.rho))| = eta F n i / r.rho := by
    rw [abs_neg, abs_of_nonneg heta]
  have hnegB : |(-(eta F n i * P.V g.val / r.rho))| =
      eta F n i * P.V g.val / r.rho := by
    rw [abs_neg, abs_of_nonneg hb]
  simp [ghostTransitionGroupRawWeight, abs_mul, abs_pow, hnegA, hnegB,
    abs_of_nonneg hq, abs_of_nonneg hf, abs_of_nonneg hμp]

private theorem ghostChoiceWeight_transition_eq_prod
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (rho : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s : P.MemoryState M)
    (c : GhostTransition s) :
    ghostChoiceWeight F n rho i (ghostTransitionAsChoice s c) =
      ∏ g : P.BigGroup, ghostTransitionGroupRawWeight F n rho i s g (c g) := by
  classical
  simp [ghostChoiceWeight, ghostTransitionAsChoice, ghostTransitionGroupRawWeight,
    ghostTransitionDeleted, ghostTransitionBirths, div_neg, neg_div]
  rfl

private theorem ghostTransitionRowFactor_eq_kernelWeight
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostTransition s) :
    ghostTransitionRowFactor F n r.rho d r.v i s c =
      |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
        d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
          P.memoryWeight r.v (ghostTransitionTarget s c) := by
  classical
  let t := ghostTransitionTarget s c
  let ch := ghostTransitionAsChoice s c
  have hraw := ghostChoiceWeight_transition_eq_prod F P n r.rho i s c
  have habs : |ghostChoiceWeight F n r.rho i ch| =
      ∏ g : P.BigGroup, |ghostTransitionGroupRawWeight F n r.rho i s g (c g)| := by
    change |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| = _
    rw [hraw, Finset.abs_prod]
  have hgroup : ∀ g : P.BigGroup,
      ghostGroupRowFactor F n r.rho d r.v i s g (c g) =
        |ghostTransitionGroupRawWeight F n r.rho i s g (c g)| *
          d ^ (ghostTransitionBirths c g).1 * r.v ^ (t.2.2 g).card := by
    intro g
    have hrawg := ghostTransitionGroupRawWeight_abs F P n r i s g (c g)
      (hV g.val) (hbase g)
    rw [ghostGroupRowFactor, hrawg, ghostTransitionTarget_card]
    have hbpow :
        (d * eta F n i * P.V g.val * r.v / r.rho) ^ (c g).2.1 =
          (eta F n i * P.V g.val / r.rho) ^ (c g).2.1 *
            d ^ (c g).2.1 * r.v ^ (c g).2.1 := by
      rw [show d * eta F n i * P.V g.val * r.v / r.rho =
        (eta F n i * P.V g.val / r.rho) * d * r.v by ring, mul_pow, mul_pow]
    rw [ghostTransitionBirths, ghostTransitionDeleted]
    rw [pow_add]
    rw [hbpow]
    ring_nf
  have hBcount : ghostBirthCount ch = ∑ g : P.BigGroup, (ghostTransitionBirths c g).1 := by
    simp [ghostBirthCount, ch, ghostTransitionAsChoice, ghostTransitionBirths]
  have hdPow : d ^ ghostBirthCount ch =
      ∏ g : P.BigGroup, d ^ (ghostTransitionBirths c g).1 := by
    rw [hBcount]
    exact (Finset.prod_pow_eq_pow_sum Finset.univ
      (fun g : P.BigGroup => (ghostTransitionBirths c g).1) d).symm
  have hvPow : P.memoryWeight r.v t =
      ∏ g : P.BigGroup, r.v ^ (t.2.2 g).card := by
    change r.v ^ (∑ g : P.BigGroup, (t.2.2 g).card) = _
    exact (Finset.prod_pow_eq_pow_sum Finset.univ
      (fun g : P.BigGroup => (t.2.2 g).card) r.v).symm
  calc
    ghostTransitionRowFactor F n r.rho d r.v i s c =
        ∏ g : P.BigGroup,
          (|ghostTransitionGroupRawWeight F n r.rho i s g (c g)| *
            d ^ (ghostTransitionBirths c g).1 * r.v ^ (t.2.2 g).card) := by
          unfold ghostTransitionRowFactor
          exact Finset.prod_congr rfl (fun g _ => hgroup g)
    _ = (∏ g : P.BigGroup, |ghostTransitionGroupRawWeight F n r.rho i s g (c g)|) *
          (∏ g : P.BigGroup, d ^ (ghostTransitionBirths c g).1) *
          (∏ g : P.BigGroup, r.v ^ (t.2.2 g).card) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = |ghostChoiceWeight F n r.rho i ch| * d ^ ghostBirthCount ch *
          P.memoryWeight r.v t := by
            rw [← habs, ← hdPow, ← hvPow]

private theorem ghostGroupRevFactor_eq_reversal_mul_row
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M) (c : GhostTransition s) (g : P.BigGroup)
    (hV : 0 < P.V g.val) :
    ghostGroupRevFactor F n r.rho d r.v i s g (c g) =
      (d * P.V g.val) ^ (((s.2.2 g).card : ℤ) -
        (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
        ghostGroupRowFactor F n r.rho d r.v i s g (c g) := by
  classical
  let a := (c g).1.1.card
  let b := (c g).2.1
  let V := P.V g.val
  let qpart := visitQ F.q n i / r.rho ^ (2 : ℕ)
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hDV : 0 < d * V := mul_pos hdpos hV
  have htarget : ((ghostTransitionTarget s c).2.2 g).card =
      (s.2.2 g).card - a + b := by
    simpa [ghostTransitionTarget, ghostTransitionDeleted, ghostTransitionBirths, a, b,
      rowsDeleteMemoryIndices_card, rowsZeroBirthBatch_card, Multiset.card_add]
  have hExp : ((s.2.2 g).card : ℤ) -
      (((ghostTransitionTarget s c).2.2 g).card : ℤ) = (a : ℤ) - (b : ℤ) := by
    rw [htarget]
    have hZle : (zeroMemoryIndices (s.2.2 g)).card ≤ (s.2.2 g).card := by
      simpa using Finset.card_le_card
        (Finset.subset_univ (zeroMemoryIndices (s.2.2 g)))
    have hdel : a ≤ (s.2.2 g).card := by
      dsimp [a]
      exact (Finset.card_le_card (c g).1.2).trans hZle
    omega
  have hpow :
      (d * V) ^ (((s.2.2 g).card : ℤ) -
        (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
        (d * V) ^ b = (d * V) ^ a := by
    rw [hExp, zpow_sub₀ (ne_of_gt hDV)]
    simp only [zpow_natCast]
    field_simp [ne_of_gt hDV]
  have hbirth : d * eta F n i * V * r.v / r.rho =
      (d * V) * (eta F n i * r.v / r.rho) := by ring
  have hbirthpow : ((d * V) * (eta F n i * r.v / r.rho)) ^ b =
      (d * V) ^ b * (eta F n i * r.v / r.rho) ^ b := mul_pow _ _ _
  let hμprod : ℝ := ∏ j : Fin b, tiltedMu F P n g.val ((c g).2.2 j)
  have hrowFac :
      ghostGroupRowFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * r.v ^ ((s.2.2 g).card - a) *
            ((d * eta F n i * V * r.v / r.rho) ^ b /
              (b.factorial : ℝ) * hμprod) := by
    simp [ghostGroupRowFactor, ghostTransitionDeleted, ghostTransitionBirths,
      a, b, V, qpart, hμprod]
  have hrevFac :
      ghostGroupRevFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * (d * V) ^ a *
            r.v ^ ((s.2.2 g).card - a) *
              ((eta F n i * r.v / r.rho) ^ b /
                (b.factorial : ℝ) * hμprod) := by
    simp [ghostGroupRevFactor, ghostTransitionDeleted, ghostTransitionBirths,
      a, b, V, qpart, hμprod]
  have hbirthEq :
      (d * eta F n i * V * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod =
        (d * V) ^ b *
          ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod) := by
    rw [hbirth, hbirthpow]
    ring
  have hrowToRev :
      ghostGroupRowFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * r.v ^ ((s.2.2 g).card - a) *
            ((d * V) ^ b *
              ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod)) := by
    rw [hrowFac, hbirthEq]
  calc
    ghostGroupRevFactor F n r.rho d r.v i s g (c g) =
        qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * (d * V) ^ a *
            r.v ^ ((s.2.2 g).card - a) *
              ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod) := hrevFac
    _ = (d * V) ^ (((s.2.2 g).card : ℤ) -
          (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
        (qpart ^ ((zeroMemoryIndices (s.2.2 g)).card - a) *
          (eta F n i / r.rho) ^ a * r.v ^ ((s.2.2 g).card - a) *
            ((d * V) ^ b *
              ((eta F n i * r.v / r.rho) ^ b / (b.factorial : ℝ) * hμprod))) := by
          rw [← hpow]
          ring
    _ = (d * V) ^ (((s.2.2 g).card : ℤ) -
          (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
          ghostGroupRowFactor F n r.rho d r.v i s g (c g) := by
            rw [hrowToRev]

private theorem ghostTransitionRevFactor_eq_reversal_kernelWeight
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostTransition s) :
    ghostTransitionRevFactor F n r.rho d r.v i s c =
      ghostReversalFactor d s (ghostTransitionTarget s c) *
        |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
        d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
        P.memoryWeight r.v (ghostTransitionTarget s c) := by
  classical
  calc
    ghostTransitionRevFactor F n r.rho d r.v i s c =
        ∏ g : P.BigGroup,
          ((d * P.V g.val) ^ (((s.2.2 g).card : ℤ) -
              (((ghostTransitionTarget s c).2.2 g).card : ℤ)) *
            ghostGroupRowFactor F n r.rho d r.v i s g (c g)) := by
          unfold ghostTransitionRevFactor
          apply Finset.prod_congr rfl
          intro g hg
          exact ghostGroupRevFactor_eq_reversal_mul_row F P n r d hd i s c g
            (hV g.val)
    _ = (∏ g : P.BigGroup, (d * P.V g.val) ^
            (((s.2.2 g).card : ℤ) -
              (((ghostTransitionTarget s c).2.2 g).card : ℤ))) *
          ghostTransitionRowFactor F n r.rho d r.v i s c := by
          rw [Finset.prod_mul_distrib]
          rfl
    _ = ghostReversalFactor d s (ghostTransitionTarget s c) *
          ghostTransitionRowFactor F n r.rho d r.v i s c := rfl
    _ = ghostReversalFactor d s (ghostTransitionTarget s c) *
          (|ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
            d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
            P.memoryWeight r.v (ghostTransitionTarget s c)) := by
          exact congrArg (fun x : ℝ => ghostReversalFactor d s
            (ghostTransitionTarget s c) * x)
            (ghostTransitionRowFactor_eq_kernelWeight F P n r d hd i s hV hbase c)
    _ = ghostReversalFactor d s (ghostTransitionTarget s c) *
          |ghostChoiceWeight F n r.rho i (ghostTransitionAsChoice s c)| *
            d ^ ghostBirthCount (ghostTransitionAsChoice s c) *
            P.memoryWeight r.v (ghostTransitionTarget s c) := by ring

/-- Reconstruct the unrestricted per-group transition from a valid literal choice. -/
def ghostTransitionOfChoice {M : ℕ} (s t : P.MemoryState M)
    (c : GhostChoice s t) (hc : ghostChoiceValid c) : GhostTransition s :=
  fun g => (⟨c.1 g, (hc g).1⟩,
    ⟨(c.2.1 g).val, c.2.2 g⟩)

lemma ghostTransitionOfChoice_target {M : ℕ} (s t : P.MemoryState M)
    (hsides : s.1 = t.1 ∧ s.2.1 = t.2.1)
    (c : GhostChoice s t) (hc : ghostChoiceValid c) :
    ghostTransitionTarget s (ghostTransitionOfChoice s t c hc) = t := by
  apply Prod.ext
  · exact hsides.1
  · apply Prod.ext
    · exact hsides.2
    · funext g
      exact (hc g).2

private theorem ghostChoiceWeight_ofChoice
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (rho : ℝ) (i : Fin (n + 1))
    {M : ℕ} (s t : P.MemoryState M) (c : GhostChoice s t)
    (hc : ghostChoiceValid c) :
    ghostChoiceWeight F n rho i c =
      ghostChoiceWeight F n rho i
        (ghostTransitionAsChoice s (ghostTransitionOfChoice s t c hc)) := by
  classical
  unfold ghostChoiceWeight
  apply Finset.prod_congr rfl
  intro g hg
  dsimp [ghostTransitionAsChoice, ghostTransitionOfChoice,
    ghostTransitionDeleted, ghostTransitionBirths]
  rfl

private theorem ghostBirthCount_ofChoice
    {P : PrimeGroups} {M : ℕ} (s t : P.MemoryState M) (c : GhostChoice s t)
    (hc : ghostChoiceValid c) :
    ghostBirthCount c = ghostBirthCount
      (ghostTransitionAsChoice s (ghostTransitionOfChoice s t c hc)) := by
  classical
  simp [ghostBirthCount, ghostTransitionAsChoice, ghostTransitionOfChoice,
    ghostTransitionDeleted, ghostTransitionBirths]

structure GhostSupportedChoice {M : ℕ} (s : P.MemoryState M) where
  target : P.MemoryState M
  choice : GhostChoice s target
  valid : ghostChoiceValid choice
  sides : s.1 = target.1 ∧ s.2.1 = target.2.1

abbrev GhostSupportedChoiceAt {M : ℕ} (s t : P.MemoryState M) :=
  {c : GhostChoice s t // ghostChoiceValid c ∧
    s.1 = t.1 ∧ s.2.1 = t.2.1}

def ghostRowsChoiceTerm (F : FixedData) (n : ℕ) (rho d v : ℝ)
    (i : Fin (n + 1)) {M : ℕ} (s t : P.MemoryState M)
    (c : GhostChoice s t) : ℝ :=
  |ghostChoiceWeight F n rho i c| * d ^ ghostBirthCount c * P.memoryWeight v t

private theorem sum_ite_eq_subtype_sum {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (f : α → ℝ) :
    (∑ x : α, if p x then f x else 0) = ∑ x : {x // p x}, f x.1 := by
  classical
  calc
    (∑ x : α, if p x then f x else 0) =
        ∑ x ∈ Finset.univ with p x, f x := by
          symm
          rw [Finset.sum_filter]
    _ = ∑ x : {x // p x}, f x.1 :=
      Finset.sum_subtype (Finset.univ.filter p) (by intro x; simp) f

lemma ghostRowTerm_eq_supportedChoiceSum
    (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (i : Fin (n + 1)) (s t : P.MemoryState (J + F.ell)) :
    absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t =
      ∑ c : GhostSupportedChoiceAt s t,
        ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 := by
  classical
  by_cases hside : s.1 = t.1 ∧ s.2.1 = t.2.1
  · simp only [absoluteScaledMemoryGhostKernel, if_pos hside]
    have hmul :
        (∑ c : GhostChoice s t,
          if ghostChoiceValid c then
            |ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c else 0) *
            P.memoryWeight r.v t =
          ∑ c : GhostChoice s t,
            if ghostChoiceValid c then
              (|ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c) *
                P.memoryWeight r.v t else 0 := by
      calc
        _ = ∑ c : GhostChoice s t,
            (if ghostChoiceValid c then
              |ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c else 0) *
              P.memoryWeight r.v t :=
                Finset.sum_mul Finset.univ
                  (fun c : GhostChoice s t =>
                    if ghostChoiceValid c then
                      |ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c else 0)
                  (P.memoryWeight r.v t)
        _ = _ := by simp
    rw [hmul]
    calc
      _ = ∑ c : {c : GhostChoice s t // ghostChoiceValid c},
          (|ghostChoiceWeight F n r.rho i c.1| * d ^ ghostBirthCount c.1) *
            P.memoryWeight r.v t :=
          sum_ite_eq_subtype_sum (ghostChoiceValid (s := s) (t := t))
            (fun c => (|ghostChoiceWeight F n r.rho i c| * d ^ ghostBirthCount c) *
              P.memoryWeight r.v t)
      _ = ∑ c : GhostSupportedChoiceAt s t,
          ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 := by
          let e : {c : GhostChoice s t // ghostChoiceValid c} ≃ GhostSupportedChoiceAt s t :=
            Equiv.subtypeEquivRight (fun c => by simp [GhostSupportedChoiceAt, hside])
          simpa [e, GhostSupportedChoiceAt, ghostRowsChoiceTerm] using
            (Fintype.sum_equiv e
              (fun c : {c : GhostChoice s t // ghostChoiceValid c} =>
                (|ghostChoiceWeight F n r.rho i c.1| * d ^ ghostBirthCount c.1) *
                  P.memoryWeight r.v t)
              (fun c : GhostSupportedChoiceAt s t =>
                ghostRowsChoiceTerm F n r.rho d r.v i s t c.1)
              (by intro c; rfl))
  · have hempty : IsEmpty (GhostSupportedChoiceAt s t) :=
      ⟨fun c => hside c.2.2⟩
    letI := hempty
    simp [absoluteScaledMemoryGhostKernel, hside, ghostRowsChoiceTerm]

def ghostSupportedChoiceTransition {M : ℕ} {s : P.MemoryState M}
    (e : GhostSupportedChoice s) : GhostTransition s :=
  ghostTransitionOfChoice s e.target e.choice e.valid

def ghostSupportedChoiceAtPackage {M : ℕ} {s t : P.MemoryState M}
    (c : GhostSupportedChoiceAt s t) : GhostSupportedChoice s :=
  ⟨t, c.1, c.2.1, c.2.2⟩

def ghostSupportedChoiceAtTransition {M : ℕ} {s t : P.MemoryState M}
    (c : GhostSupportedChoiceAt s t) : GhostTransition s :=
  ghostSupportedChoiceTransition (ghostSupportedChoiceAtPackage c)

private theorem ghostRowsChoiceTerm_eq_transitionRowFactor
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s t : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostSupportedChoiceAt s t) :
    ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 =
      ghostTransitionRowFactor F n r.rho d r.v i s
        (ghostSupportedChoiceAtTransition c) := by
  classical
  have hc := c.2.1
  have hs := c.2.2
  have htarget := ghostTransitionOfChoice_target s t hs c.1 hc
  have hweight := ghostChoiceWeight_ofChoice F P n r.rho i s t c.1 hc
  have hcount := ghostBirthCount_ofChoice s t c.1 hc
  change ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 =
    ghostTransitionRowFactor F n r.rho d r.v i s
      (ghostTransitionOfChoice s t c.1 hc)
  rw [ghostTransitionRowFactor_eq_kernelWeight F P n r d hd i s hV hbase]
  unfold ghostRowsChoiceTerm
  rw [← hweight, ← hcount, htarget]

private theorem ghostRowsPartial_eq_transitionPartial
    (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1)) (s : P.MemoryState (J + F.ell))
    (S : Finset (P.MemoryState (J + F.ell)))
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    (∑ t ∈ S,
      absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) =
      ∑ x ∈ S.attach.sigma (fun t : {t : P.MemoryState (J + F.ell) // t ∈ S} =>
        (Finset.univ : Finset (GhostSupportedChoiceAt s t.val))),
        ghostTransitionRowFactor F n r.rho d r.v i s
          (ghostSupportedChoiceAtTransition x.2) := by
  classical
  let τ : (t : {t : P.MemoryState (J + F.ell) // t ∈ S}) →
      Finset (GhostSupportedChoiceAt s t.val) := fun _ => Finset.univ
  calc
    (∑ t ∈ S,
        absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) =
        ∑ t ∈ S.attach,
          absoluteScaledMemoryGhostKernel F J n r.rho d i s t.val * P.memoryWeight r.v t.val :=
      (Finset.sum_attach S
        (fun t : P.MemoryState (J + F.ell) =>
          absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t)).symm
    _ = ∑ t ∈ S.attach, ∑ c : GhostSupportedChoiceAt s t.val,
          ghostRowsChoiceTerm F n r.rho d r.v i s t.val c.1 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact ghostRowTerm_eq_supportedChoiceSum F P J n r d i s t.val
    _ = ∑ x ∈ S.attach.sigma τ,
          ghostRowsChoiceTerm F n r.rho d r.v i s x.1.val x.2.1 := by
      simpa [τ] using
        (Finset.sum_sigma' S.attach τ
          (fun t c => ghostRowsChoiceTerm F n r.rho d r.v i s t.val c.1))
    _ = ∑ x ∈ S.attach.sigma τ,
          ghostTransitionRowFactor F n r.rho d r.v i s
            (ghostSupportedChoiceAtTransition x.2) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ghostRowsChoiceTerm_eq_transitionRowFactor F P n r d hd i s x.1.val
        hV hbase x.2

private theorem ghostReverseSupportedChoiceTerm_eq_transitionRevFactor
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s t : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostSupportedChoiceAt s t) :
    ghostReversalFactor d s t *
      ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 =
    ghostTransitionRevFactor F n r.rho d r.v i s
      (ghostSupportedChoiceAtTransition c) := by
  classical
  have hc := c.2.1
  have hs := c.2.2
  have htarget := ghostTransitionOfChoice_target s t hs c.1 hc
  have hweight := ghostChoiceWeight_ofChoice F P n r.rho i s t c.1 hc
  have hcount := ghostBirthCount_ofChoice s t c.1 hc
  change ghostReversalFactor d s t *
      (|ghostChoiceWeight F n r.rho i c.1| * d ^ ghostBirthCount c.1 *
        P.memoryWeight r.v t) =
    ghostTransitionRevFactor F n r.rho d r.v i s
      (ghostTransitionOfChoice s t c.1 hc)
  rw [ghostTransitionRevFactor_eq_reversal_kernelWeight F P n r d hd i s
    (fun g => hV g) hbase (ghostTransitionOfChoice s t c.1 hc)]
  rw [← hweight, ← hcount, htarget]
  ring

private theorem ghostTransitionOfChoice_injective_on_fixed_target
    {M : ℕ} (s t : P.MemoryState M)
    (c₁ c₂ : GhostChoice s t) (hc₁ : ghostChoiceValid c₁) (hc₂ : ghostChoiceValid c₂)
    (h : ghostTransitionOfChoice s t c₁ hc₁ = ghostTransitionOfChoice s t c₂ hc₂) :
    c₁ = c₂ := by
  classical
  rcases c₁ with ⟨del₁, ⟨b₁, p₁⟩⟩
  rcases c₂ with ⟨del₂, ⟨b₂, p₂⟩⟩
  have hfun : (fun g : P.BigGroup =>
      ((⟨del₁ g, (hc₁ g).1⟩,
        (⟨(b₁ g).val, p₁ g⟩ : GhostBirthBatch g)) : GhostGroupTransition s g)) =
      (fun g : P.BigGroup =>
      ((⟨del₂ g, (hc₂ g).1⟩,
        (⟨(b₂ g).val, p₂ g⟩ : GhostBirthBatch g)) : GhostGroupTransition s g)) := by
    change (fun g : P.BigGroup => (ghostTransitionOfChoice s t (del₁, ⟨b₁, p₁⟩) hc₁) g) =
      (fun g : P.BigGroup => (ghostTransitionOfChoice s t (del₂, ⟨b₂, p₂⟩) hc₂) g)
    exact h
  have hpoint (g : P.BigGroup) := congrFun hfun g
  have hdel : del₁ = del₂ := by
    funext g
    exact congrArg (fun q : GhostGroupTransition s g => q.1.1) (hpoint g)
  have hbatch (g : P.BigGroup) :
      (⟨(b₁ g).val, p₁ g⟩ : GhostBirthBatch g) =
        (⟨(b₂ g).val, p₂ g⟩ : GhostBirthBatch g) := by
    exact congrArg (fun q : GhostGroupTransition s g => q.2) (hpoint g)
  have hb : b₁ = b₂ := by
    funext g
    apply Fin.ext
    exact congrArg Sigma.fst (hbatch g)
  cases hb
  have hp : p₁ = p₂ := by
    funext g j
    have hseq := (Sigma.mk.inj_iff.mp (hbatch g)).2
    exact congrFun (eq_of_heq hseq) j
  cases hdel
  cases hp
  rfl

private theorem ghostSupportedChoiceTransition_injective
    {M : ℕ} (s : P.MemoryState M) :
    Function.Injective (ghostSupportedChoiceTransition (s := s)) := by
  classical
  intro e₁ e₂ h
  cases e₁ with
  | mk t c hc hs =>
    cases e₂ with
    | mk u c' hc' hs' =>
      have htu : t = u := by
        calc
          t = ghostTransitionTarget s (ghostTransitionOfChoice s t c hc) :=
            (ghostTransitionOfChoice_target s t hs c hc).symm
          _ = ghostTransitionTarget s (ghostTransitionOfChoice s u c' hc') :=
            congrArg (ghostTransitionTarget s) h
          _ = u := ghostTransitionOfChoice_target s u hs' c' hc'
      subst u
      have hcc := ghostTransitionOfChoice_injective_on_fixed_target s t c c' hc hc' h
      subst c'
      have hproof : hc = hc' := Subsingleton.elim _ _
      subst hc'
      have hsproof : hs = hs' := Subsingleton.elim _ _
      subst hs'
      rfl

private theorem ghostSupportedChoiceAtTransition_injective_on_sigma
    {M : ℕ} (S : Finset (P.MemoryState M)) (s : P.MemoryState M) :
    Function.Injective (fun e : Σ t : (↑S : Type), GhostSupportedChoiceAt s t.val =>
      ghostSupportedChoiceAtTransition e.2) := by
  classical
  intro x y h
  rcases x with ⟨tx, cx⟩
  rcases y with ⟨ty, cy⟩
  change ghostSupportedChoiceAtTransition cx = ghostSupportedChoiceAtTransition cy at h
  have htx : tx.val =
      ghostTransitionTarget s (ghostSupportedChoiceAtTransition cx) := by
    exact (ghostTransitionOfChoice_target s tx.val cx.2.2 cx.1 cx.2.1).symm
  have hty : ghostTransitionTarget s (ghostSupportedChoiceAtTransition cy) = ty.val :=
    ghostTransitionOfChoice_target s ty.val cy.2.2 cy.1 cy.2.1
  have hval : tx.val = ty.val := htx.trans ((congrArg (ghostTransitionTarget s) h).trans hty)
  have hsub : tx = ty := Subtype.ext hval
  cases hsub
  have hchoice : cx.1 = cy.1 := by
    apply ghostTransitionOfChoice_injective_on_fixed_target s tx.val cx.1 cy.1
      cx.2.1 cy.2.1
    simpa [ghostSupportedChoiceAtTransition, ghostSupportedChoiceAtPackage,
      ghostSupportedChoiceTransition] using h
  have hcx : cx = cy := Subtype.ext hchoice
  cases hcx
  rfl

private theorem ghostGroupRowFactor_nonneg
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (hV : 0 < P.V g.val ∧ P.V g.val ≤ F.vMax)
    (hbase : ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    ∀ c : GhostGroupTransition s g,
      0 ≤ ghostGroupRowFactor F n r.rho d r.v i s g c := by
  classical
  intro c
  have hEta : 0 < eta F n i := eta_pos F n i
  have hμ : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p := by
    intro p
    have hp : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos (P.prime g.val p.val p.property))
    unfold tiltedMu
    exact le_of_lt (inv_pos.mpr (mul_pos (mul_pos hV.1 hp) (hbase p)))
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  unfold ghostGroupRowFactor
  dsimp
  apply mul_nonneg
  · positivity [visitQ_pos F n i, eta_pos F n i, r.rho_pos, r.v_gt]
  · apply mul_nonneg
    · exact div_nonneg (pow_nonneg (by positivity [eta_pos F n i, hV.1, hdpos, r.v_gt, r.rho_pos]) _)
        (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg fun j _ => hμ _

private theorem ghostGroupRevFactor_nonneg
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M) (g : P.BigGroup)
    (hV : 0 < P.V g.val ∧ P.V g.val ≤ F.vMax)
    (hbase : ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) :
    ∀ c : GhostGroupTransition s g,
      0 ≤ ghostGroupRevFactor F n r.rho d r.v i s g c := by
  classical
  intro c
  have hEta : 0 < eta F n i := eta_pos F n i
  have hμ : ∀ p : P.Prime g.val, 0 ≤ tiltedMu F P n g.val p := by
    intro p
    have hp : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos (P.prime g.val p.val p.property))
    unfold tiltedMu
    exact le_of_lt (inv_pos.mpr (mul_pos (mul_pos hV.1 hp) (hbase p)))
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  unfold ghostGroupRevFactor
  dsimp
  apply mul_nonneg
  · positivity [visitQ_pos F n i, eta_pos F n i, r.rho_pos, r.v_gt, hV.1, hdpos]
  · apply mul_nonneg
    · exact div_nonneg (pow_nonneg (by positivity [eta_pos F n i, r.v_gt, r.rho_pos]) _)
        (Nat.cast_nonneg _)
    · exact Finset.prod_nonneg fun j _ => hμ _

private theorem ghostTransitionRowFactor_summable_bound
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup,
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2) :
    Summable (fun c : GhostTransition s => ghostTransitionRowFactor F n r.rho d r.v i s c) ∧
    (∑' c : GhostTransition s, ghostTransitionRowFactor F n r.rho d r.v i s c) ≤
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
        P.memoryWeight r.v s := by
  classical
  let E : ℝ := Real.exp (4 * max 1 F.vMax * r.v / r.rho)
  have hlocalSummable : ∀ g : P.BigGroup,
      Summable (fun c : GhostGroupTransition s g =>
        ghostGroupRowFactor F n r.rho d r.v i s g c) := by
    intro g
    exact (ghostGroupRowFactor_summable_bound F P n r d hd i s g
      (hV g.val) (hbase g) (hmu g)).1
  have hlocalBound : ∀ g : P.BigGroup,
      (∑' c : GhostGroupTransition s g,
        ghostGroupRowFactor F n r.rho d r.v i s g c) ≤
        r.v ^ (s.2.2 g).card * E := by
    intro g
    simpa [E] using (ghostGroupRowFactor_summable_bound F P n r d hd i s g
      (hV g.val) (hbase g) (hmu g)).2
  have hnonneg : ∀ g : P.BigGroup, ∀ c : GhostGroupTransition s g,
      0 ≤ ghostGroupRowFactor F n r.rho d r.v i s g c := by
    intro g c
    exact ghostGroupRowFactor_nonneg F P n r d hd i s g
      (hV g.val) (hbase g) c
  have hPi := piProdTsum (fun g : P.BigGroup => GhostGroupTransition s g)
    (fun g c => ghostGroupRowFactor F n r.rho d r.v i s g c) hnonneg hlocalSummable
  have hprod :
      (∏ g : P.BigGroup,
        ∑' c : GhostGroupTransition s g, ghostGroupRowFactor F n r.rho d r.v i s g c) ≤
      ∏ g : P.BigGroup, (r.v ^ (s.2.2 g).card * E) := by
    apply Finset.prod_le_prod₀
    · intro g hg
      apply tsum_nonneg
      exact hnonneg g
    · intro g hg
      exact hlocalBound g
  have hcard : Fintype.card P.BigGroup = P.bigGroups.card := by
    let e : P.BigGroup ≃ (↑P.bigGroups : Type) :=
      Equiv.subtypeEquivRight (fun g : P.Group => by
        simp [PrimeGroups.bigGroups, PrimeGroups.BigGroup])
    calc
      Fintype.card P.BigGroup = Fintype.card (↑P.bigGroups : Type) := Fintype.card_congr e
      _ = P.bigGroups.card := Fintype.card_coe P.bigGroups
  have hprodEq :
      (∏ g : P.BigGroup, r.v ^ (s.2.2 g).card * E) =
        E ^ P.bigGroups.card * P.memoryWeight r.v s := by
    calc
      (∏ g : P.BigGroup, r.v ^ (s.2.2 g).card * E) =
          (∏ g : P.BigGroup, r.v ^ (s.2.2 g).card) *
            (∏ g : P.BigGroup, E) := Finset.prod_mul_distrib
      _ = r.v ^ (∑ g : P.BigGroup, (s.2.2 g).card) *
            E ^ Fintype.card P.BigGroup := by
              rw [Finset.prod_pow_eq_pow_sum]
              simp
      _ = E ^ P.bigGroups.card * P.memoryWeight r.v s := by
              rw [hcard]
              simp [PrimeGroups.memoryWeight, PrimeGroups.memorySize]
              ring
  constructor
  · simpa [ghostTransitionRowFactor] using hPi.1
  · have hsum :
        (∑' c : GhostTransition s, ghostTransitionRowFactor F n r.rho d r.v i s c) =
          ∏ g : P.BigGroup, ∑' c : GhostGroupTransition s g,
            ghostGroupRowFactor F n r.rho d r.v i s g c := by
      simpa [ghostTransitionRowFactor] using hPi.2
    rw [hsum]
    exact hprod.trans hprodEq.le

private theorem ghostTransitionRevFactor_summable_bound
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup,
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2) :
    Summable (fun c : GhostTransition s => ghostTransitionRevFactor F n r.rho d r.v i s c) ∧
    (∑' c : GhostTransition s, ghostTransitionRevFactor F n r.rho d r.v i s c) ≤
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
        P.memoryWeight r.v s := by
  classical
  let E : ℝ := Real.exp (4 * max 1 F.vMax * r.v / r.rho)
  have hlocalSummable : ∀ g : P.BigGroup,
      Summable (fun c : GhostGroupTransition s g =>
        ghostGroupRevFactor F n r.rho d r.v i s g c) := by
    intro g
    exact (ghostGroupRevFactor_summable_bound F P n r d hd i s g
      (hV g.val) (hbase g) (hmu g)).1
  have hlocalBound : ∀ g : P.BigGroup,
      (∑' c : GhostGroupTransition s g,
        ghostGroupRevFactor F n r.rho d r.v i s g c) ≤
        r.v ^ (s.2.2 g).card * E := by
    intro g
    simpa [E] using (ghostGroupRevFactor_summable_bound F P n r d hd i s g
      (hV g.val) (hbase g) (hmu g)).2
  have hnonneg : ∀ g : P.BigGroup, ∀ c : GhostGroupTransition s g,
      0 ≤ ghostGroupRevFactor F n r.rho d r.v i s g c := by
    intro g c
    exact ghostGroupRevFactor_nonneg F P n r d hd i s g
      (hV g.val) (hbase g) c
  have hPi := piProdTsum (fun g : P.BigGroup => GhostGroupTransition s g)
    (fun g c => ghostGroupRevFactor F n r.rho d r.v i s g c) hnonneg hlocalSummable
  have hprod :
      (∏ g : P.BigGroup,
        ∑' c : GhostGroupTransition s g, ghostGroupRevFactor F n r.rho d r.v i s g c) ≤
      ∏ g : P.BigGroup, (r.v ^ (s.2.2 g).card * E) := by
    apply Finset.prod_le_prod₀
    · intro g hg
      apply tsum_nonneg
      exact hnonneg g
    · intro g hg
      exact hlocalBound g
  have hcard : Fintype.card P.BigGroup = P.bigGroups.card := by
    let e : P.BigGroup ≃ (↑P.bigGroups : Type) :=
      Equiv.subtypeEquivRight (fun g : P.Group => by
        simp [PrimeGroups.bigGroups, PrimeGroups.BigGroup])
    calc
      Fintype.card P.BigGroup = Fintype.card (↑P.bigGroups : Type) := Fintype.card_congr e
      _ = P.bigGroups.card := Fintype.card_coe P.bigGroups
  have hprodEq :
      (∏ g : P.BigGroup, r.v ^ (s.2.2 g).card * E) =
        E ^ P.bigGroups.card * P.memoryWeight r.v s := by
    calc
      (∏ g : P.BigGroup, r.v ^ (s.2.2 g).card * E) =
          (∏ g : P.BigGroup, r.v ^ (s.2.2 g).card) *
            (∏ g : P.BigGroup, E) := Finset.prod_mul_distrib
      _ = r.v ^ (∑ g : P.BigGroup, (s.2.2 g).card) *
            E ^ Fintype.card P.BigGroup := by
              rw [Finset.prod_pow_eq_pow_sum]
              simp
      _ = E ^ P.bigGroups.card * P.memoryWeight r.v s := by
              rw [hcard]
              simp [PrimeGroups.memoryWeight, PrimeGroups.memorySize]
              ring
  constructor
  · simpa [ghostTransitionRevFactor] using hPi.1
  · have hsum :
        (∑' c : GhostTransition s, ghostTransitionRevFactor F n r.rho d r.v i s c) =
          ∏ g : P.BigGroup, ∑' c : GhostGroupTransition s g,
            ghostGroupRevFactor F n r.rho d r.v i s g c := by
      simpa [ghostTransitionRevFactor] using hPi.2
    rw [hsum]
    exact hprod.trans hprodEq.le

private theorem ghostTransitionRowFactor_nonneg
    (F : FixedData) (P : PrimeGroups) (n : ℕ) (r : MemoryParameters F)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    {M : ℕ} (s : P.MemoryState M)
    (hV : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (c : GhostTransition s) :
    0 ≤ ghostTransitionRowFactor F n r.rho d r.v i s c := by
  classical
  unfold ghostTransitionRowFactor
  apply Finset.prod_nonneg
  intro g hg
  exact ghostGroupRowFactor_nonneg F P n r d hd i s g (hV g.val) (hbase g) (c g)

private theorem ghostRows_forward_bound
    (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F)
    (hV : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup,
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    (s : P.MemoryState (J + F.ell)) :
    Summable (fun t => absoluteScaledMemoryGhostKernel F J n r.rho d i s t *
      P.memoryWeight r.v t) ∧
    (∑' t, absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ≤
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
        P.memoryWeight r.v s := by
  classical
  have hglobal := ghostTransitionRowFactor_summable_bound F P n r d hd i s hV hbase hmu
  have htrans0 : ∀ c : GhostTransition s,
      0 ≤ ghostTransitionRowFactor F n r.rho d r.v i s c := by
    intro c
    exact ghostTransitionRowFactor_nonneg F P n r d hd i s hV hbase c
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have hrow0 : ∀ t : P.MemoryState (J + F.ell),
      0 ≤ absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t := by
    intro t
    by_cases hsides : s.1 = t.1 ∧ s.2.1 = t.2.1
    · simp only [absoluteScaledMemoryGhostKernel, if_pos hsides]
      apply mul_nonneg
      · apply Finset.sum_nonneg
        intro c hc
        split_ifs with hvalid
        · exact mul_nonneg (abs_nonneg _) (pow_nonneg hdpos.le _)
        · simp
      · exact pow_nonneg (le_trans (by norm_num) r.v_gt.le) _
    · simp [absoluteScaledMemoryGhostKernel, hsides]
  have hpartial : ∀ S : Finset (P.MemoryState (J + F.ell)),
      (∑ t ∈ S, absoluteScaledMemoryGhostKernel F J n r.rho d i s t *
        P.memoryWeight r.v t) ≤
        (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
          P.memoryWeight r.v s := by
    intro S
    let τ : (t : {t : P.MemoryState (J + F.ell) // t ∈ S}) →
        Finset (GhostSupportedChoiceAt s t.val) := fun _ => Finset.univ
    let U := S.attach.sigma τ
    let mapRaw : (x : (t : {t : P.MemoryState (J + F.ell) // t ∈ S}) ×
        GhostSupportedChoiceAt s t.val) → GhostTransition s :=
      fun x => ghostSupportedChoiceAtTransition x.2
    let mapU : (x : U) → GhostTransition s := fun x => mapRaw x.1
    have hsum :
        (∑ t ∈ S, absoluteScaledMemoryGhostKernel F J n r.rho d i s t *
          P.memoryWeight r.v t) =
        ∑ x ∈ U, ghostTransitionRowFactor F n r.rho d r.v i s (mapRaw x) := by
      simpa [U, τ, mapRaw, mapU] using
        ghostRowsPartial_eq_transitionPartial F P J n r d hd i s S
          (fun g => (hV g).1) (fun g p => hbase g p)
    have hinjRaw := ghostSupportedChoiceAtTransition_injective_on_sigma S s
    have hinjU : Function.Injective mapU := by
      intro x y h
      apply Subtype.ext
      exact hinjRaw h
    have hsource : Summable (fun x : U =>
        ghostTransitionRowFactor F n r.rho d r.v i s (mapU x)) :=
      summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
    have hle :
        (∑' x : U, ghostTransitionRowFactor F n r.rho d r.v i s (mapU x)) ≤
          ∑' c : GhostTransition s, ghostTransitionRowFactor F n r.rho d r.v i s c := by
      exact hsource.tsum_le_tsum_of_inj (fun x : U => mapU x) hinjU
        (fun c hc => htrans0 c) (fun x => le_rfl) hglobal.1
    calc
      (∑ t ∈ S, absoluteScaledMemoryGhostKernel F J n r.rho d i s t *
          P.memoryWeight r.v t) =
        ∑ x ∈ U, ghostTransitionRowFactor F n r.rho d r.v i s (mapRaw x) := hsum
      _ = ∑' x : U, ghostTransitionRowFactor F n r.rho d r.v i s (mapU x) := by
        simpa [mapU] using (Finset.tsum_subtype U (fun x =>
          ghostTransitionRowFactor F n r.rho d r.v i s (mapRaw x))).symm
      _ ≤ ∑' c : GhostTransition s, ghostTransitionRowFactor F n r.rho d r.v i s c := hle
      _ ≤ _ := hglobal.2
  exact ⟨summable_of_sum_le hrow0 hpartial,
    Real.tsum_le_of_sum_le hrow0 hpartial⟩

private theorem ghostRows_reversed_bound
    (F : FixedData) (P : PrimeGroups) (J n : ℕ) (r : MemoryParameters F)
    (hV : ∀ g : P.Group, 0 < P.V g ∧ P.V g ≤ F.vMax)
    (hbase : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hmu : ∀ g : P.BigGroup,
      (∑ p : P.Prime g.val, tiltedMu F P n g.val p) ≤ 2)
    (d : ℝ) (hd : d = 1 ∨ d = 2) (i : Fin (n + 1))
    (s : P.MemoryState (J + F.ell)) :
    Summable (fun t => ghostReversalFactor d s t *
      absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ∧
    (∑' t, ghostReversalFactor d s t *
      absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ≤
      (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
        P.memoryWeight r.v s := by
  classical
  have hglobal := ghostTransitionRevFactor_summable_bound F P n r d hd i s hV hbase hmu
  have hdpos : 0 < d := by rcases hd with rfl | rfl <;> norm_num
  have htrans0 : ∀ c : GhostTransition s,
      0 ≤ ghostTransitionRevFactor F n r.rho d r.v i s c := by
    intro c
    unfold ghostTransitionRevFactor
    apply Finset.prod_nonneg
    intro g hg
    exact ghostGroupRevFactor_nonneg F P n r d hd i s g
      (hV g.val) (hbase g) (c g)
  have hkernel0 : ∀ t : P.MemoryState (J + F.ell),
      0 ≤ absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t := by
    intro t
    by_cases hsides : s.1 = t.1 ∧ s.2.1 = t.2.1
    · simp only [absoluteScaledMemoryGhostKernel, if_pos hsides]
      apply mul_nonneg
      · apply Finset.sum_nonneg
        intro c hc
        split_ifs with hvalid
        · exact mul_nonneg (abs_nonneg _) (pow_nonneg hdpos.le _)
        · simp
      · exact pow_nonneg (le_trans (by norm_num) r.v_gt.le) _
    · simp [absoluteScaledMemoryGhostKernel, hsides]
  have hrow0 : ∀ t : P.MemoryState (J + F.ell),
      0 ≤ ghostReversalFactor d s t *
        absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t := by
    intro t
    have hfactor : 0 ≤ ghostReversalFactor d s t := by
      unfold ghostReversalFactor
      apply Finset.prod_nonneg
      intro g hg
      have hbasePos : 0 < d * P.V g.val := mul_pos hdpos (hV g.val).1
      exact zpow_nonneg hbasePos.le _
    calc
      0 ≤ ghostReversalFactor d s t *
          (absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) :=
        mul_nonneg hfactor (hkernel0 t)
      _ = _ := by ring
  have hpartial : ∀ S : Finset (P.MemoryState (J + F.ell)),
      (∑ t ∈ S, ghostReversalFactor d s t *
        absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) ≤
        (Real.exp (4 * max 1 F.vMax * r.v / r.rho)) ^ P.bigGroups.card *
          P.memoryWeight r.v s := by
    intro S
    let τ : (t : {t : P.MemoryState (J + F.ell) // t ∈ S}) →
        Finset (GhostSupportedChoiceAt s t.val) := fun _ => Finset.univ
    let U := S.attach.sigma τ
    let mapRaw : (x : (t : {t : P.MemoryState (J + F.ell) // t ∈ S}) ×
        GhostSupportedChoiceAt s t.val) → GhostTransition s :=
      fun x => ghostSupportedChoiceAtTransition x.2
    let mapU : (x : U) → GhostTransition s := fun x => mapRaw x.1
    have hsum :
        (∑ t ∈ S, ghostReversalFactor d s t *
          absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) =
        ∑ x ∈ U, ghostTransitionRevFactor F n r.rho d r.v i s (mapRaw x) := by
      calc
        (∑ t ∈ S, ghostReversalFactor d s t *
            absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) =
            ∑ t ∈ S, ghostReversalFactor d s t *
              (absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) := by
                apply Finset.sum_congr rfl
                intro t ht
                ring
        _ = ∑ t ∈ S, ∑ c : GhostSupportedChoiceAt s t,
              ghostReversalFactor d s t *
                ghostRowsChoiceTerm F n r.rho d r.v i s t c.1 := by
                apply Finset.sum_congr rfl
                intro t ht
                rw [ghostRowTerm_eq_supportedChoiceSum F P J n r d i s t]
                exact Finset.mul_sum Finset.univ
                  (fun c : GhostSupportedChoiceAt s t =>
                    ghostRowsChoiceTerm F n r.rho d r.v i s t c.1)
                  (ghostReversalFactor d s t)
        _ = ∑ t ∈ S.attach, ∑ c : GhostSupportedChoiceAt s t.val,
              ghostReversalFactor d s t.val *
                ghostRowsChoiceTerm F n r.rho d r.v i s t.val c.1 := by
                exact (Finset.sum_attach S (fun t =>
                  ∑ c : GhostSupportedChoiceAt s t,
                    ghostReversalFactor d s t *
                      ghostRowsChoiceTerm F n r.rho d r.v i s t c.1)).symm
        _ = ∑ x ∈ U, ghostReversalFactor d s x.1.val *
              ghostRowsChoiceTerm F n r.rho d r.v i s x.1.val x.2.1 := by
                simpa [U, τ] using
                  (Finset.sum_sigma' S.attach τ
                    (fun t c => ghostReversalFactor d s t.val *
                      ghostRowsChoiceTerm F n r.rho d r.v i s t.val c.1))
        _ = ∑ x ∈ U, ghostTransitionRevFactor F n r.rho d r.v i s (mapRaw x) := by
                apply Finset.sum_congr rfl
                intro x hx
                exact (ghostReverseSupportedChoiceTerm_eq_transitionRevFactor
                  F P n r d hd i s x.1.val (fun g : P.Group => (hV g).1) hbase x.2)
    have hinjRaw := ghostSupportedChoiceAtTransition_injective_on_sigma S s
    have hinjU : Function.Injective mapU := by
      intro x y h
      apply Subtype.ext
      exact hinjRaw h
    have hsource : Summable (fun x : U =>
        ghostTransitionRevFactor F n r.rho d r.v i s (mapU x)) :=
      summable_of_hasFiniteSupport (Set.finite_univ.subset (Set.subset_univ _))
    have hle :
        (∑' x : U, ghostTransitionRevFactor F n r.rho d r.v i s (mapU x)) ≤
          ∑' c : GhostTransition s, ghostTransitionRevFactor F n r.rho d r.v i s c := by
      exact hsource.tsum_le_tsum_of_inj (fun x : U => mapU x) hinjU
        (fun c hc => htrans0 c) (fun x => le_rfl) hglobal.1
    calc
      (∑ t ∈ S, ghostReversalFactor d s t *
          absoluteScaledMemoryGhostKernel F J n r.rho d i s t * P.memoryWeight r.v t) =
        ∑ x ∈ U, ghostTransitionRevFactor F n r.rho d r.v i s (mapRaw x) := hsum
      _ = ∑' x : U, ghostTransitionRevFactor F n r.rho d r.v i s (mapU x) := by
        simpa [mapU] using (Finset.tsum_subtype U (fun x =>
          ghostTransitionRevFactor F n r.rho d r.v i s (mapRaw x))).symm
      _ ≤ ∑' c : GhostTransition s, ghostTransitionRevFactor F n r.rho d r.v i s c := hle
      _ ≤ _ := hglobal.2
  exact ⟨summable_of_sum_le hrow0 hpartial,
    Real.tsum_le_of_sum_le hrow0 hpartial⟩

theorem GhostRowsTask_proof : GhostRowsTask := by
  intro F P J n r hV hbase hmu d hd i s
  have hforward := ghostRows_forward_bound F P J n r hV hbase hmu d hd i s
  have hreverse := ghostRows_reversed_bound F P J n r hV hbase hmu d hd i s
  exact ⟨hforward.1, hforward.2, hreverse.1, hreverse.2⟩


instance ghostGroupTransition_countable {M : ℕ} (s : P.MemoryState M)
    (g : P.BigGroup) : Countable (GhostGroupTransition s g) := by
  classical
  infer_instance

instance ghostTransition_countable {M : ℕ} (s : P.MemoryState M) :
    Countable (GhostTransition s) := by
  classical
  infer_instance

end Erdos821.S2Core
