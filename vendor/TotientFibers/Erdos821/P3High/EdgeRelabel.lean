import Erdos821.P3High.RelabelState
import Erdos821.S2High.AllowedMass
import Erdos821.S2High.Majorant

/-! Conditional edge rows: constraining fresh target slots to prescribed values costs one
tilted point mass (times two, for the free-label ban) per slot.  The constrained slots are
filled after stores, promotions and the step are fixed; the coefficient is replaced by its
pattern supremum (the majorant model has the same pattern mass). -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3High

open Erdos821.Blueprint.Graph hiding BirthAddress EdgeChoice GhostChoice MemoryHistory
  TransferChoice TransferMode absoluteMemoryEdgeKernel absoluteMemoryGhostKernel
  absoluteScaledMemoryGhostKernel deleteMemoryIndices distinctMemoryExpression
  edgeChoiceCoefficient edgeChoiceValid edgeDelta edgeForward edgeSymmetryFactor freshBigFactor
  ghostBirthCount ghostChoiceValid ghostChoiceWeight ghostReversalFactor memoryEdgeKernel
  memoryEntry memoryGhostKernel permuteActive rawEdgeValid rawEdgeWeight retrievedIndices
  smallDamping smallOmega smallTargetFactor storedMemory transferModeAccept translateMemory
  translateParticle translateSmallResidues zeroBirthBatch zeroMemoryIndices
open Erdos821.S2Core Erdos821.S2High Erdos821.P3Lowrank

attribute [local instance] bmsFintype

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

/-- Tilted point mass of a natural value in a big group; zero outside the group. -/
def muHat (F : FixedData) (P : PrimeGroups) (n : ℕ) (g : P.BigGroup) (v : ℕ) : ℝ :=
  if hv : v ∈ P.primes g.val then tiltedMu F P n g.val ⟨v, hv⟩ else 0

theorem muHat_nonneg (F : FixedData) (P : PrimeGroups) (n : ℕ)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (g : P.BigGroup) (v : ℕ) : 0 ≤ muHat F P n g v := by
  unfold muHat
  split_ifs with hv
  · exact (hμ g ⟨v, hv⟩).le
  · exact le_rfl

theorem muHat_of_mem (F : FixedData) (P : PrimeGroups) (n : ℕ) (g : P.BigGroup)
    (p : P.Prime g.val) : muHat F P n g p.val = tiltedMu F P n g.val p := by
  unfold muHat
  rw [dif_pos p.property]

def edgeFresh (A : Model F P J m) {s : P.MemoryState (J + F.ell)} (c : EdgeChoice A s)
    (x : P.BigGroup × Fin (J + F.ell)) : Prop :=
  ¬ (A.pattern c.2.2.1).shared x.1.val x.2 ∧ x.2 ∉ c.2.2.2.2.2.1 x.1

def edgeSlotCond (A : Model F P J m) {s : P.MemoryState (J + F.ell)}
    (vals : P.BigGroup × Fin (J + F.ell) → ℕ) (t : P.MemoryState (J + F.ell))
    (c : EdgeChoice A s) (x : P.BigGroup × Fin (J + F.ell)) : Prop :=
  edgeFresh A c x ∧ ((permuteActive c.2.1 t).2.1 x.1.val x.2).val = vals x

/-- Indicator multiplier constraining the fresh slots `Sl` of one edge. -/
def edgeMult (A : Model F P J m) (Sl : Finset (P.BigGroup × Fin (J + F.ell)))
    (vals : P.BigGroup × Fin (J + F.ell) → ℕ) :
    (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℝ :=
  fun _ t c => if ∀ x ∈ Sl, edgeSlotCond A vals t c x then 1 else 0

theorem norm_imaginaryPower (k : ℕ) (ζ : ℝ) : ‖imaginaryPower k ζ‖ = 1 := by
  unfold imaginaryPower
  rw [show (ζ : ℂ) * (Real.log k : ℂ) * Complex.I = ((ζ * Real.log k : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem coefficient_le_sup {ell : ℕ} (ν : Pattern P J ell m) (a b : P.BigLabels (J + ell))
    (u : P.BigAux J) : ‖ν.coefficient a b u‖ ≤ coefficientSup ν := by
  unfold coefficientSup
  exact le_csSup (Set.finite_range _).bddAbove ⟨(a, b, u), rfl⟩

theorem norm_coef_major (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    ‖edgeChoiceCoefficient (majorantModel A) n rho theta i s t c‖ =
      |rawEdgeWeight A n rho (A.pattern c.2.2.1) c.2.2.2.1 (permuteActive c.1 s)
        (permuteActive c.2.1 t) c.2.2.2.2| * coefficientSup (A.pattern c.2.2.1) := by
  have hsup := coefficientSup_nonneg (A.pattern c.2.2.1)
  simp only [edgeChoiceCoefficient]
  rw [norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  congr 1
  split_ifs
  · rw [norm_mul, norm_imaginaryPower, mul_one]
    change ‖((coefficientSup (A.pattern c.2.2.1) : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsup]
  · rw [norm_star, norm_mul, norm_imaginaryPower, mul_one]
    change ‖((coefficientSup (A.pattern c.2.2.1) : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsup]

theorem norm_coef_le_major (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) :
    ‖edgeChoiceCoefficient A n rho theta i s t c‖ ≤
      ‖edgeChoiceCoefficient (majorantModel A) n rho theta i s t c‖ := by
  rw [norm_coef_major]
  simp only [edgeChoiceCoefficient]
  rw [norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  split_ifs
  · rw [norm_mul, norm_imaginaryPower, mul_one]
    exact coefficient_le_sup _ _ _ _
  · rw [norm_star, norm_mul, norm_imaginaryPower, mul_one]
    exact coefficient_le_sup _ _ _ _

/-- Replacing a fresh target label by a label outside the ban keeps the raw edge valid. -/
theorem rawEdgeValid_relabel (A : Model F P J m) (ν : Pattern P J F.ell m) (fwd : Bool)
    (u : P.Aux J) (ss tt : P.MemoryState (J + F.ell)) (tr : TransferChoice ss)
    (g : P.BigGroup) (h : Fin (J + F.ell)) (p : P.Prime g.val)
    (hv : rawEdgeValid A ν fwd u ss tt tr) (hsh : ¬ ν.shared g.val h) (hpr : h ∉ tr.2.1 g)
    (hban : ∀ i ∈ ν.changed g.val, u g.val i ≠ p) :
    rawEdgeValid A ν fwd u ss (relabelState g h p tt) tr := by
  dsimp only [rawEdgeValid] at hv ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  refine ⟨h1, ?_, ?_, ?_, h5, ?_⟩
  · intro g'
    have hne : g'.val ≠ g.val := by
      intro he
      have h1' := g'.property
      have h2' := g.property
      rw [he] at h1'
      rw [h1'] at h2'
      exact Bool.false_ne_true h2'
    change Function.Injective (relabelLabels tt.2.1 g h p g'.val) ∧
      ∀ i, tt.1 g' (relabelLabels tt.2.1 g h p g'.val i) = 0
    rw [relabelLabels_ne_group _ g h p _ hne]
    exact h2 g'
  · intro g' i hsh'
    change ss.2.1 g' i = relabelLabels tt.2.1 g h p g' i
    by_cases hg : g' = g.val
    · subst hg
      have hi : i ≠ h := fun hi => hsh (hi ▸ hsh')
      rw [relabelLabels_ne_slot _ g h p i hi]
      exact h3 _ i hsh'
    · rw [relabelLabels_ne_group _ g h p g' hg]
      exact h3 g' i hsh'
  · intro g' i hi j
    refine ⟨(h4 g' i hi j).1, ?_⟩
    change u g' i ≠ relabelLabels tt.2.1 g h p g' j
    by_cases hg : g' = g.val
    · subst hg
      by_cases hj : j = h
      · subst hj
        rw [relabelLabels_self]
        exact hban i hi
      · rw [relabelLabels_ne_slot _ g h p j hj]
        exact (h4 _ i hi j).2
    · rw [relabelLabels_ne_group _ g h p g' hg]
      exact (h4 g' i hi j).2
  · intro g'
    obtain ⟨a1, a2, a3, a4, a5⟩ := h6 g'
    refine ⟨a1, a2, a3, ?_, a5⟩
    intro i
    obtain ⟨b1, b2, b3⟩ := a4 i
    refine ⟨?_, b2, b3⟩
    change _ = relabelLabels tt.2.1 g h p g'.val i.val
    have hx : (g', i.val) ≠ (g, h) := by
      intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, hih⟩ := he
      exact hpr (hih ▸ i.property)
    rw [relabelLabels_of_ne _ g h p g' i.val hx]
    exact b1

/-- The edge weight apart from its fresh tilted masses. -/
def edgeRest (n : ℕ) (rho : ℝ) (ν : Pattern P J F.ell m) (u : P.Aux J)
    (ss tt : P.MemoryState (J + F.ell)) (tr : TransferChoice ss) : ℝ :=
  ν.auxMass u * (∏ g : P.BigGroup, (P.V g.val) ^ (-((tr.2.1 g).card : ℤ))) *
    smallTargetFactor (P := P) F * smallDamping F J ss.1 * smallDamping F J tt.1 *
    rho ^ ((∑ g : P.BigGroup, (zeroMemoryIndices (ss.2.2 g)).card) +
      (∑ g : P.BigGroup, (zeroMemoryIndices (tt.2.2 g)).card))

theorem rawEdgeWeight_eq (A : Model F P J m) (n : ℕ) (rho : ℝ) (ν : Pattern P J F.ell m)
    (u : P.Aux J) (ss tt : P.MemoryState (J + F.ell)) (tr : TransferChoice ss) :
    rawEdgeWeight A n rho ν u ss tt tr =
      freshBigFactor F n ν tr.2.1 tt.2.1 * edgeRest n rho ν u ss tt tr := by
  unfold rawEdgeWeight edgeRest
  ring

theorem freshBigFactor_relabel (n : ℕ) (ν : Pattern P J F.ell m)
    (prom : P.BigGroup → Finset (Fin (J + F.ell))) (a : P.Labels (J + F.ell))
    (g : P.BigGroup) (h : Fin (J + F.ell)) (p : P.Prime g.val)
    (hsh : ¬ ν.shared g.val h) (hpr : h ∉ prom g) :
    freshBigFactor F n ν prom (relabelLabels a g h p) * tiltedMu F P n g.val (a g.val h) =
      freshBigFactor F n ν prom a * tiltedMu F P n g.val p := by
  have key := tilted_prod_relabel F n
    (fun x : P.BigGroup × Fin (J + F.ell) => ν.shared x.1.val x.2 ∨ x.2 ∈ prom x.1)
    a g h p (by simp only [not_or]; exact ⟨hsh, hpr⟩)
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type] at key
  unfold freshBigFactor
  convert key

theorem rawEdgeWeight_relabel (A : Model F P J m) (n : ℕ) (rho : ℝ) (ν : Pattern P J F.ell m)
    (u : P.Aux J) (ss tt : P.MemoryState (J + F.ell)) (tr : TransferChoice ss)
    (g : P.BigGroup) (h : Fin (J + F.ell)) (p : P.Prime g.val)
    (hsh : ¬ ν.shared g.val h) (hpr : h ∉ tr.2.1 g) :
    rawEdgeWeight A n rho ν u ss (relabelState g h p tt) tr *
        tiltedMu F P n g.val (tt.2.1 g.val h) =
      rawEdgeWeight A n rho ν u ss tt tr * tiltedMu F P n g.val p := by
  rw [rawEdgeWeight_eq, rawEdgeWeight_eq]
  have hR : edgeRest n rho ν u ss (relabelState g h p tt) tr = edgeRest n rho ν u ss tt tr := rfl
  have hF := freshBigFactor_relabel n ν tr.2.1 tt.2.1 g h p hsh hpr
  change freshBigFactor F n ν tr.2.1 (relabelLabels tt.2.1 g h p) *
      edgeRest n rho ν u ss (relabelState g h p tt) tr * tiltedMu F P n g.val (tt.2.1 g.val h) = _
  rw [hR]
  calc freshBigFactor F n ν tr.2.1 (relabelLabels tt.2.1 g h p) *
        edgeRest n rho ν u ss tt tr * tiltedMu F P n g.val (tt.2.1 g.val h)
      = (freshBigFactor F n ν tr.2.1 (relabelLabels tt.2.1 g h p) *
          tiltedMu F P n g.val (tt.2.1 g.val h)) * edgeRest n rho ν u ss tt tr := by ring
    _ = (freshBigFactor F n ν tr.2.1 tt.2.1 * tiltedMu F P n g.val p) *
          edgeRest n rho ν u ss tt tr := by rw [hF]
    _ = _ := by ring

/-- One literal choice term of the majorant absolute edge kernel. -/
def eterm (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) (t : P.MemoryState (J + F.ell)) : ℝ :=
  if edgeChoiceValid (majorantModel A) .all i s t c then
    ‖edgeChoiceCoefficient (majorantModel A) n rho theta i s t c‖ else 0

theorem eterm_nonneg (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) (t : P.MemoryState (J + F.ell)) :
    0 ≤ eterm A n rho theta i s c t := by
  unfold eterm
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

theorem eterm_relabel (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) (t : P.MemoryState (J + F.ell))
    (x : P.BigGroup × Fin (J + F.ell)) (p : P.Prime x.1.val) (hfr : edgeFresh A c x)
    (hval : edgeChoiceValid (majorantModel A) .all i s t c)
    (hban : ∀ j ∈ (A.pattern c.2.2.1).changed x.1.val, c.2.2.2.1 x.1.val j ≠ p) :
    edgeChoiceValid (majorantModel A) .all i s (relabelState x.1 (c.2.1 x.1.val x.2) p t) c ∧
    eterm A n rho theta i s c t * tiltedMu F P n x.1.val p =
      eterm A n rho theta i s c (relabelState x.1 (c.2.1 x.1.val x.2) p t) *
        tiltedMu F P n x.1.val (t.2.1 x.1.val (c.2.1 x.1.val x.2)) := by
  have hval' : edgeChoiceValid (majorantModel A) .all i s
      (relabelState x.1 (c.2.1 x.1.val x.2) p t) c := by
    refine ⟨?_, trivial⟩
    have hv1 := hval.1
    change rawEdgeValid (majorantModel A) ((majorantModel A).pattern c.2.2.1) (edgeForward i)
      c.2.2.2.1 (permuteActive c.1 s)
      (permuteActive c.2.1 (relabelState x.1 (c.2.1 x.1.val x.2) p t)) c.2.2.2.2
    rw [permuteActive_relabel]
    exact rawEdgeValid_relabel _ _ _ _ _ _ _ x.1 x.2 p hv1 hfr.1 hfr.2 hban
  refine ⟨hval', ?_⟩
  unfold eterm
  rw [if_pos hval, if_pos hval', norm_coef_major, norm_coef_major, permuteActive_relabel]
  have hW := rawEdgeWeight_relabel A n rho (A.pattern c.2.2.1) c.2.2.2.1 (permuteActive c.1 s)
    (permuteActive c.2.1 t) c.2.2.2.2 x.1 x.2 p hfr.1 hfr.2
  have hW' := congrArg abs hW
  rw [abs_mul, abs_mul, abs_of_pos (hμ _ _), abs_of_pos (hμ _ _)] at hW'
  change _ * tiltedMu F P n x.1.val (t.2.1 x.1.val (c.2.1 x.1.val x.2)) = _ at hW'
  calc |rawEdgeWeight A n rho (A.pattern c.2.2.1) c.2.2.2.1 (permuteActive c.1 s)
          (permuteActive c.2.1 t) c.2.2.2.2| * coefficientSup (A.pattern c.2.2.1) *
        tiltedMu F P n x.1.val p
      = (|rawEdgeWeight A n rho (A.pattern c.2.2.1) c.2.2.2.1 (permuteActive c.1 s)
          (permuteActive c.2.1 t) c.2.2.2.2| * tiltedMu F P n x.1.val p) *
          coefficientSup (A.pattern c.2.2.1) := by ring
    _ = _ := by rw [← hW']; ring

/-- Constraining one more fresh slot, uniformly in a relabelling-invariant constraint `Q`. -/
theorem edge_single (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n) (B : ℕ) (v : ℝ)
    (hv : 0 ≤ v)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmassJ : ∀ (g : P.BigGroup) (forb : Finset (P.Prime g.val)), forb.card ≤ J →
      (1 / 2 : ℝ) ≤ ∑ p ∈ Finset.univ.filter (fun p => p ∉ forb), tiltedMu F P n g.val p)
    (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (Q : P.MemoryState (J + F.ell) → Prop) (x : P.BigGroup × Fin (J + F.ell))
    (hQ : ∀ p t, Q (relabelState x.1 (c.2.1 x.1.val x.2) p t) ↔ Q t) (vx : ℕ) :
    ∑ t : BoundedMemoryState P (J + F.ell) B,
        (if Q t.val ∧ (edgeFresh A c x ∧ ((permuteActive c.2.1 t.val).2.1 x.1.val x.2).val = vx)
          then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) ≤
      2 * muHat F P n x.1 vx * ∑ t : BoundedMemoryState P (J + F.ell) B,
        (if Q t.val then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) := by
  have hf0 : ∀ t : BoundedMemoryState P (J + F.ell) B,
      0 ≤ eterm A n rho theta i s c t.val * P.memoryWeight v t.val :=
    fun t => mul_nonneg (eterm_nonneg _ _ _ _ _ _ _ _) (pow_nonneg hv _)
  have hR0 : 0 ≤ ∑ t : BoundedMemoryState P (J + F.ell) B,
      (if Q t.val then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) :=
    Finset.sum_nonneg fun t _ => by
      split_ifs
      · exact hf0 t
      · exact le_rfl
  have hRHS0 : 0 ≤ 2 * muHat F P n x.1 vx * ∑ t : BoundedMemoryState P (J + F.ell) B,
      (if Q t.val then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) :=
    mul_nonneg (mul_nonneg two_pos.le (muHat_nonneg F P n hμ _ _)) hR0
  by_cases hfr : edgeFresh A c x
  swap
  · rw [Finset.sum_eq_zero fun t _ => if_neg (fun h => hfr h.2.1)]
    exact hRHS0
  by_cases hvx : vx ∈ P.primes x.1.val
  swap
  · have hz : ∀ t : BoundedMemoryState P (J + F.ell) B, ¬ (Q t.val ∧ (edgeFresh A c x ∧
        ((permuteActive c.2.1 t.val).2.1 x.1.val x.2).val = vx)) := by
      intro t h
      apply hvx
      rw [← h.2.2]
      exact ((permuteActive c.2.1 t.val).2.1 x.1.val x.2).property
    rw [Finset.sum_eq_zero fun t _ => if_neg (hz t)]
    exact hRHS0
  let α : P.Prime x.1.val := ⟨vx, hvx⟩
  have hmu : muHat F P n x.1 vx = tiltedMu F P n x.1.val α := muHat_of_mem F P n x.1 α
  let k := c.2.1 x.1.val x.2
  let T := Finset.univ.filter (fun t : BoundedMemoryState P (J + F.ell) B =>
    Q t.val ∧ edgeChoiceValid (majorantModel A) .all i s t.val c ∧ t.val.2.1 x.1.val k = α)
  let S := Finset.univ.filter (fun t : BoundedMemoryState P (J + F.ell) B => Q t.val)
  let forb : Finset (P.Prime x.1.val) :=
    ((A.pattern c.2.2.1).changed x.1.val).image (c.2.2.2.1 x.1.val)
  let Q' := Finset.univ.filter (fun p : P.Prime x.1.val => p ∉ forb)
  have hforb : forb.card ≤ J := Finset.card_image_le.trans
    ((Finset.card_le_univ _).trans (Fintype.card_fin J).le)
  have hLHS : (∑ t : BoundedMemoryState P (J + F.ell) B,
      (if Q t.val ∧ (edgeFresh A c x ∧ ((permuteActive c.2.1 t.val).2.1 x.1.val x.2).val = vx)
        then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0)) =
      ∑ t ∈ T, eterm A n rho theta i s c t.val * P.memoryWeight v t.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hval : edgeChoiceValid (majorantModel A) .all i s t.val c
    · by_cases hc : Q t.val ∧ t.val.2.1 x.1.val k = α
      · rw [if_pos ⟨hc.1, hfr, congrArg Subtype.val hc.2⟩, if_pos ⟨hc.1, hval, hc.2⟩]
      · rw [if_neg, if_neg]
        · exact fun h => hc ⟨h.1, h.2.2⟩
        · exact fun h => hc ⟨h.1, Subtype.ext h.2.2⟩
    · have hf : eterm A n rho theta i s c t.val = 0 := by
        unfold eterm
        rw [if_neg hval]
      rw [hf, zero_mul]
      split_ifs <;> rfl
  have hS : (∑ t : BoundedMemoryState P (J + F.ell) B,
      (if Q t.val then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0)) =
      ∑ t ∈ S, eterm A n rho theta i s c t.val * P.memoryWeight v t.val :=
    (Finset.sum_filter _ _).symm
  have key := relabel_sum_le
    (fun t : BoundedMemoryState P (J + F.ell) B =>
      eterm A n rho theta i s c t.val * P.memoryWeight v t.val) T S Q'
    (fun t p => relabelB x.1 k p t) (tiltedMu F P n x.1.val) (tiltedMu F P n x.1.val α) (1 / 2)
    (fun t _ => hf0 t) (fun t _ => hf0 t) (hμ _ _).le (by norm_num) (hmassJ x.1 forb hforb)
    (by
      intro t ht p _
      rw [Finset.mem_filter] at ht ⊢
      exact ⟨Finset.mem_univ _, (hQ p t.val).mpr ht.2.1⟩)
    (by
      intro t1 ht1 p1 _ t2 ht2 p2 _ he
      have he' : relabelState x.1 k p1 t1.val = relabelState x.1 k p2 t2.val :=
        congrArg Subtype.val he
      have hp : p1 = p2 := by
        have h3 := congrArg (fun z : P.MemoryState (J + F.ell) => z.2.1 x.1.val k) he'
        change relabelLabels t1.val.2.1 x.1 k p1 x.1.val k =
          relabelLabels t2.val.2.1 x.1 k p2 x.1.val k at h3
        rwa [relabelLabels_self, relabelLabels_self] at h3
      refine ⟨?_, hp⟩
      apply Subtype.ext
      have h1 : t1.val.2.1 x.1.val k = α := (Finset.mem_filter.1 ht1).2.2.2
      have h2 : t2.val.2.1 x.1.val k = α := (Finset.mem_filter.1 ht2).2.2.2
      calc t1.val = relabelState x.1 k α (relabelState x.1 k p1 t1.val) := by
            rw [relabelState_relabel, ← h1, relabelState_eq_self]
        _ = relabelState x.1 k α (relabelState x.1 k p2 t2.val) := by rw [he']
        _ = t2.val := by rw [relabelState_relabel, ← h2, relabelState_eq_self])
    (by
      intro t ht p hp
      obtain ⟨-, -, hval, hlab⟩ := Finset.mem_filter.1 ht
      have hpf : p ∉ forb := (Finset.mem_filter.1 hp).2
      have hban : ∀ j ∈ (A.pattern c.2.2.1).changed x.1.val, c.2.2.2.1 x.1.val j ≠ p :=
        fun j hj he => hpf (Finset.mem_image.2 ⟨j, hj, he⟩)
      have hr := (eterm_relabel A n rho theta i hμ s c t.val x p hfr hval hban).2
      change eterm A n rho theta i s c t.val * P.memoryWeight v t.val * tiltedMu F P n x.1.val p =
        eterm A n rho theta i s c (relabelState x.1 k p t.val) *
          P.memoryWeight v (relabelState x.1 k p t.val) * tiltedMu F P n x.1.val α
      rw [memoryWeight_relabelState, ← hlab]
      calc eterm A n rho theta i s c t.val * P.memoryWeight v t.val * tiltedMu F P n x.1.val p
          = (eterm A n rho theta i s c t.val * tiltedMu F P n x.1.val p) *
              P.memoryWeight v t.val := by ring
        _ = _ := by rw [hr]; ring)
  rw [hLHS, hS, hmu]
  calc _ ≤ tiltedMu F P n x.1.val α / (1 / 2) *
        ∑ t ∈ S, eterm A n rho theta i s c t.val * P.memoryWeight v t.val := key
    _ = _ := by ring

/-- All constrained fresh slots of one edge choice. -/
theorem edge_slots (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n) (B : ℕ) (v : ℝ)
    (hv : 0 ≤ v)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmassJ : ∀ (g : P.BigGroup) (forb : Finset (P.Prime g.val)), forb.card ≤ J →
      (1 / 2 : ℝ) ≤ ∑ p ∈ Finset.univ.filter (fun p => p ∉ forb), tiltedMu F P n g.val p)
    (s : P.MemoryState (J + F.ell)) (c : EdgeChoice A s)
    (vals : P.BigGroup × Fin (J + F.ell) → ℕ) :
    ∀ Sl : Finset (P.BigGroup × Fin (J + F.ell)),
    ∑ t : BoundedMemoryState P (J + F.ell) B,
        (if ∀ x ∈ Sl, edgeSlotCond A vals t.val c x
          then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) ≤
      (∏ x ∈ Sl, 2 * muHat F P n x.1 (vals x)) * ∑ t : BoundedMemoryState P (J + F.ell) B,
        eterm A n rho theta i s c t.val * P.memoryWeight v t.val := by
  intro Sl
  induction Sl using Finset.induction_on with
  | empty => simp
  | insert y S hy ih =>
      have hrw : ∀ t : BoundedMemoryState P (J + F.ell) B,
          (if ∀ x ∈ insert y S, edgeSlotCond A vals t.val c x
            then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) =
          (if (∀ x ∈ S, edgeSlotCond A vals t.val c x) ∧ (edgeFresh A c y ∧
              ((permuteActive c.2.1 t.val).2.1 y.1.val y.2).val = vals y)
            then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) := by
        intro t
        by_cases h1 : ∀ x ∈ insert y S, edgeSlotCond A vals t.val c x
        · rw [if_pos h1, if_pos ⟨fun x hx => h1 x (Finset.mem_insert_of_mem hx),
            h1 y (Finset.mem_insert_self y S)⟩]
        · rw [if_neg h1, if_neg]
          rintro ⟨h2, h3⟩
          apply h1
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact h3
          · exact h2 x hx
      rw [Finset.sum_congr rfl (fun t _ => hrw t)]
      have hQ : ∀ (p : P.Prime y.1.val) (t : P.MemoryState (J + F.ell)),
          (∀ x ∈ S, edgeSlotCond A vals (relabelState y.1 (c.2.1 y.1.val y.2) p t) c x) ↔
            (∀ x ∈ S, edgeSlotCond A vals t c x) := by
        intro p t
        have hx : ∀ x ∈ S, edgeSlotCond A vals (relabelState y.1 (c.2.1 y.1.val y.2) p t) c x ↔
            edgeSlotCond A vals t c x := by
          intro x hxS
          have hne : (x.1, x.2) ≠ (y.1, y.2) := by
            rw [Prod.mk.eta, Prod.mk.eta]
            rintro rfl
            exact hy hxS
          unfold edgeSlotCond
          rw [permuteActive_relabel]
          change edgeFresh A c x ∧
              (relabelLabels (permuteActive c.2.1 t).2.1 y.1 y.2 p x.1.val x.2).val = vals x ↔ _
          rw [relabelLabels_of_ne _ y.1 y.2 p x.1 x.2 hne]
        exact ⟨fun h x hxS => (hx x hxS).mp (h x hxS), fun h x hxS => (hx x hxS).mpr (h x hxS)⟩
      have hstep := edge_single A n rho theta i B v hv hμ hmassJ s c
        (fun t => ∀ x ∈ S, edgeSlotCond A vals t c x) y hQ (vals y)
      have hm0 : 0 ≤ 2 * muHat F P n y.1 (vals y) :=
        mul_nonneg two_pos.le (muHat_nonneg F P n hμ _ _)
      calc _ ≤ 2 * muHat F P n y.1 (vals y) * ∑ t : BoundedMemoryState P (J + F.ell) B,
              (if ∀ x ∈ S, edgeSlotCond A vals t.val c x
                then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) := by
            convert hstep
        _ ≤ 2 * muHat F P n y.1 (vals y) * ((∏ x ∈ S, 2 * muHat F P n x.1 (vals x)) *
              ∑ t : BoundedMemoryState P (J + F.ell) B,
                eterm A n rho theta i s c t.val * P.memoryWeight v t.val) :=
            mul_le_mul_of_nonneg_left ih hm0
        _ = _ := by rw [Finset.prod_insert hy]; ring

theorem absEdge_eq_eterm (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) :
    absoluteMemoryEdgeKernel (majorantModel A) n rho theta i .all s t =
      edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s, eterm A n rho theta i s c t :=
  rfl

/-- The conditional weighted edge row: the constrained slots each cost a tilted point mass. -/
theorem edge_row_constrained (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n) (B : ℕ)
    (v : ℝ) (hv : 0 ≤ v)
    (hμ : ∀ (g : P.BigGroup) (p : P.Prime g.val), 0 < tiltedMu F P n g.val p)
    (hmassJ : ∀ (g : P.BigGroup) (forb : Finset (P.Prime g.val)), forb.card ≤ J →
      (1 / 2 : ℝ) ≤ ∑ p ∈ Finset.univ.filter (fun p => p ∉ forb), tiltedMu F P n g.val p)
    (Sl : Finset (P.BigGroup × Fin (J + F.ell))) (vals : P.BigGroup × Fin (J + F.ell) → ℕ)
    (s : P.MemoryState (J + F.ell)) :
    ∑ t : BoundedMemoryState P (J + F.ell) B,
        edgeK A n rho theta i (edgeMult A Sl vals) s t.val * P.memoryWeight v t.val ≤
      (∏ x ∈ Sl, 2 * muHat F P n x.1 (vals x)) * ∑ t : BoundedMemoryState P (J + F.ell) B,
        absoluteMemoryEdgeKernel (majorantModel A) n rho theta i .all s t.val *
          P.memoryWeight v t.val := by
  have hsym := edgeSymmetryFactor_nonneg P (J + F.ell)
  have hw : ∀ t : P.MemoryState (J + F.ell), 0 ≤ P.memoryWeight v t := fun t => pow_nonneg hv _
  have hle : ∀ t, edgeK A n rho theta i (edgeMult A Sl vals) s t ≤
      edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
        (if ∀ x ∈ Sl, edgeSlotCond A vals t c x then eterm A n rho theta i s c t else 0) := by
    intro t
    unfold edgeK
    apply mul_le_mul_of_nonneg_left _ hsym
    apply Finset.sum_le_sum
    intro c _
    unfold edgeMult
    by_cases hval : edgeChoiceValid A .all i s t c
    · have hval' : edgeChoiceValid (majorantModel A) .all i s t c := hval
      rw [if_pos hval]
      by_cases hS : ∀ x ∈ Sl, edgeSlotCond A vals t c x
      · rw [if_pos hS, if_pos hS, mul_one]
        unfold eterm
        rw [if_pos hval']
        exact norm_coef_le_major A n rho theta i s t c
      · rw [if_neg hS, if_neg hS, mul_zero]
    · rw [if_neg hval]
      split_ifs
      · exact eterm_nonneg _ _ _ _ _ _ _ _
      · exact le_rfl
  calc ∑ t : BoundedMemoryState P (J + F.ell) B,
        edgeK A n rho theta i (edgeMult A Sl vals) s t.val * P.memoryWeight v t.val
      ≤ ∑ t : BoundedMemoryState P (J + F.ell) B,
          (edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
            (if ∀ x ∈ Sl, edgeSlotCond A vals t.val c x then eterm A n rho theta i s c t.val
              else 0)) * P.memoryWeight v t.val :=
        Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (hle t.val) (hw t.val)
    _ = edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
          ∑ t : BoundedMemoryState P (J + F.ell) B,
            (if ∀ x ∈ Sl, edgeSlotCond A vals t.val c x
              then eterm A n rho theta i s c t.val * P.memoryWeight v t.val else 0) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_lhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
    _ ≤ edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
          (∏ x ∈ Sl, 2 * muHat F P n x.1 (vals x)) * ∑ t : BoundedMemoryState P (J + F.ell) B,
            eterm A n rho theta i s c t.val * P.memoryWeight v t.val :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ =>
          edge_slots A n rho theta i B v hv hμ hmassJ s c vals Sl) hsym
    _ = _ := by
        simp_rw [absEdge_eq_eterm]
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_lhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro c _
        ring

end Erdos821.P3High
