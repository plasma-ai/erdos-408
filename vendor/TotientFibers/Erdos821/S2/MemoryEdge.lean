import Erdos821.S2.MemoryGhost

/-! The literal edge choices for active lists and pending memory. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

inductive TransferMode where
  | all
  | clean
  | dirty
  deriving DecidableEq

def translateParticle (delta : ℤ) {g : P.Group} (z : P.Particle g) : P.Particle g :=
  ⟨z.1, z.2 + (delta : ZMod z.1.val)⟩

def translateMemory (delta : ℤ) {g : P.Group} (z : P.Memory g) : P.Memory g :=
  z.map (translateParticle delta)

def translateSmallResidues (delta : ℤ) (y : P.SmallResidues) : P.SmallResidues :=
  fun g p => y g p + (delta : ZMod p.val)

def permuteActive {M : ℕ} (π : P.Permutations M) (s : P.MemoryState M) : P.MemoryState M :=
  (s.1, P.act π s.2.1, s.2.2)

abbrev TransferChoice {M : ℕ} (s : P.MemoryState M) :=
  ((g : P.BigGroup) → Finset (Fin M)) ×
    ((A : (g : P.BigGroup) → Finset (Fin M)) ×
      ((g : P.BigGroup) → (i : {i : Fin M // i ∈ A g}) → Fin (s.2.2 g).card))

/-- Both endpoint permutations, pattern/free labels and canonical transfer choices. -/
abbrev EdgeChoice (A : Model F P J m) (s : P.MemoryState (J + F.ell)) :=
  P.Permutations (J + F.ell) × P.Permutations (J + F.ell) ×
    Fin A.patternCount × P.Aux J × TransferChoice s

def transferModeAccept {M : ℕ} {s : P.MemoryState M} (mode : TransferMode)
    (c : TransferChoice s) : Prop :=
  match mode with
  | .all => True
  | .clean => ∀ g, c.1 g = ∅ ∧ c.2.1 g = ∅
  | .dirty => ∃ g, c.1 g ≠ ∅ ∨ c.2.1 g ≠ ∅

def storedMemory {M : ℕ} {g : P.Group} (a : Fin M → P.Prime g)
    (B : Finset (Fin M)) : P.Memory g :=
  (B.toList.map (fun i => (⟨a i, 0⟩ : P.Particle g)) : List (P.Particle g))

def retrievedIndices {M : ℕ} {s : P.MemoryState M} (c : TransferChoice s) (g : P.BigGroup) :
    Finset (Fin (s.2.2 g).card) := Finset.univ.image (c.2.2 g)

def edgeForward {n : ℕ} (i : Fin n) : Bool := i.val % 2 == 0

def edgeDelta (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (a : P.Labels (J + F.ell)) (u : P.Aux J) : ℤ :=
  if forward then A.k * (ν.D a u : ℤ) else -(A.k * (ν.D a u : ℤ))

def smallOmega (y : P.SmallResidues) : ℕ :=
  ∑ g : P.SmallGroup, (Finset.univ.filter (fun p : P.Prime g.val => y g p = 0)).card

def smallDamping (F : FixedData) (J : ℕ) (y : P.SmallResidues) : ℝ :=
  F.q ^ (((smallOmega y : ℝ) - (J + F.ell) * Fintype.card P.SmallGroup) / 2)

def smallTargetFactor (F : FixedData) : ℝ :=
  ∏ g : P.SmallGroup, (P.V g.val) ^ (-(F.ell : ℤ))

def freshBigFactor (F : FixedData) (n : ℕ) (ν : Pattern P J F.ell m)
    (prom : P.BigGroup → Finset (Fin (J + F.ell)))
    (a : P.Labels (J + F.ell)) : ℝ :=
  ∏ g : P.BigGroup, ∏ i : Fin (J + F.ell),
    if ν.shared g.val i ∨ i ∈ prom g then 1 else tiltedMu F P n g.val (a g.val i)

/-- Retrievals refer only to old source indices; stores cannot be promoted here. -/
def rawEdgeValid (A : Model F P J m) (ν : Pattern P J F.ell m) (forward : Bool)
    (u : P.Aux J) (s t : P.MemoryState (J + F.ell)) (c : TransferChoice s) : Prop :=
  let delta := edgeDelta A ν forward s.2.1 u
  P.smallPhysical s.1 s.2.1 ∧ P.smallPhysical t.1 t.2.1 ∧
  ν.compatible s.2.1 t.2.1 ∧ ν.ban s.2.1 t.2.1 u ∧
  t.1 = translateSmallResidues delta s.1 ∧
  ∀ g : P.BigGroup,
    (∀ i ∈ c.1 g, ¬ ν.shared g.val i ∧ ¬ (s.2.1 g.val i).val ∣ ν.D s.2.1 u) ∧
    (∀ i ∈ c.2.1 g, ¬ ν.shared g.val i) ∧
    Function.Injective (c.2.2 g) ∧
    (∀ i : {i : Fin (J + F.ell) // i ∈ c.2.1 g},
      let z := memoryEntry (s.2.2 g) (c.2.2 g i)
      z.1 = t.2.1 g.val i.val ∧ z.2 + (delta : ZMod z.1.val) = 0 ∧
      ¬ z.1.val ∣ ν.D s.2.1 u) ∧
    t.2.2 g = translateMemory delta
      (deleteMemoryIndices (s.2.2 g) (retrievedIndices c g) + storedMemory (s.2.1 g.val) (c.1 g))

/-- Small endpoints stay physical; big endpoints use fresh/promoted birth weights. -/
def rawEdgeWeight (A : Model F P J m) (n : ℕ) (rho : ℝ)
    (ν : Pattern P J F.ell m) (u : P.Aux J)
    (s t : P.MemoryState (J + F.ell)) (c : TransferChoice s) : ℝ :=
  ν.auxMass u * freshBigFactor F n ν c.2.1 t.2.1 *
    (∏ g : P.BigGroup, (P.V g.val) ^ (-((c.2.1 g).card : ℤ))) *
    smallTargetFactor (P := P) F * smallDamping F J s.1 * smallDamping F J t.1 *
    rho ^ ((∑ g : P.BigGroup, (zeroMemoryIndices (s.2.2 g)).card) +
      (∑ g : P.BigGroup, (zeroMemoryIndices (t.2.2 g)).card))

def edgeChoiceCoefficient (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) : ℂ :=
  let ss := permuteActive c.1 s
  let tt := permuteActive c.2.1 t
  let ν := A.pattern c.2.2.1
  let u := c.2.2.2.1
  let transfers := c.2.2.2.2
  let forward := edgeForward i
  let D := ν.D ss.2.1 u
  let z := ν.coefficient (P.restrictBig ss.2.1) (P.restrictBig tt.2.1) (fun g => u g.val) *
    imaginaryPower D A.zeta
  let zr := star (ν.coefficient (P.restrictBig tt.2.1) (P.restrictBig ss.2.1) (fun g => u g.val) *
    imaginaryPower D A.zeta)
  (rawEdgeWeight A n rho ν u ss tt transfers : ℂ) * (if forward then z else zr) *
    phase (theta * (edgeDelta A ν forward ss.2.1 u : ℝ))

def edgeChoiceValid (A : Model F P J m) (mode : TransferMode) {n : ℕ} (i : Fin n)
    (s t : P.MemoryState (J + F.ell)) (c : EdgeChoice A s) : Prop :=
  rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
    (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2 ∧
  transferModeAccept mode c.2.2.2.2

def edgeSymmetryFactor (P : PrimeGroups) (M : ℕ) : ℝ :=
  ((Fintype.card (P.Permutations M) : ℝ) ^ (2 : ℕ))⁻¹

def memoryEdgeKernel (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n) (mode : TransferMode)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (s t : P.MemoryState (J + F.ell)) : ℂ :=
  (edgeSymmetryFactor P (J + F.ell) : ℂ) * ∑ c : EdgeChoice A s,
    if edgeChoiceValid A mode i s t c then edgeChoiceCoefficient A n rho theta i s t c * phi s t c else 0

def absoluteMemoryEdgeKernel (A : Model F P J m) (n : ℕ) (rho theta : ℝ) (i : Fin n)
    (mode : TransferMode) (s t : P.MemoryState (J + F.ell)) : ℝ :=
  edgeSymmetryFactor P (J + F.ell) * ∑ c : EdgeChoice A s,
    if edgeChoiceValid A mode i s t c then ‖edgeChoiceCoefficient A n rho theta i s t c‖ else 0

theorem edgeSymmetryFactor_nonneg (P : PrimeGroups) (M : ℕ) :
    0 ≤ edgeSymmetryFactor P M := by
  unfold edgeSymmetryFactor
  positivity

theorem translateMemory_card (delta : ℤ) {g : P.Group} (z : P.Memory g) :
    (translateMemory delta z).card = z.card := Multiset.card_map _ _

theorem deleteMemoryIndices_card {g : P.Group} (z : P.Memory g)
    (B : Finset (Fin z.card)) :
    (deleteMemoryIndices z B).card = z.card - B.card := by
  simp [deleteMemoryIndices, Finset.card_sdiff_of_subset (Finset.subset_univ B)]

theorem storedMemory_card {M : ℕ} {g : P.Group} (a : Fin M → P.Prime g)
    (B : Finset (Fin M)) : (storedMemory a B).card = B.card := by
  simp [storedMemory]

theorem retrievedIndices_card {M : ℕ} {s : P.MemoryState M}
    (c : TransferChoice s) (g : P.BigGroup) (hc : Function.Injective (c.2.2 g)) :
    (retrievedIndices c g).card = (c.2.1 g).card := by
  simp [retrievedIndices, Finset.card_image_of_injective _ hc]

theorem rawEdgeValid_memory_card (A : Model F P J m) (ν : Pattern P J F.ell m)
    (forward : Bool) (u : P.Aux J) (s t : P.MemoryState (J + F.ell))
    (c : TransferChoice s) (hc : rawEdgeValid A ν forward u s t c) (g : P.BigGroup) :
    (t.2.2 g).card = (s.2.2 g).card - (c.2.1 g).card + (c.1 g).card := by
  obtain ⟨_, _, _, _, _, hg⟩ := hc
  obtain ⟨_, _, hi, _, ht⟩ := hg g
  rw [ht, translateMemory_card, Multiset.card_add, deleteMemoryIndices_card,
    storedMemory_card, retrievedIndices_card c g hi]

theorem transferModeAccept_dirty_iff {M : ℕ} {s : P.MemoryState M}
    (c : TransferChoice s) :
    transferModeAccept .dirty c ↔ ¬ transferModeAccept .clean c := by
  change (∃ g, c.1 g ≠ ∅ ∨ c.2.1 g ≠ ∅) ↔ ¬ (∀ g, c.1 g = ∅ ∧ c.2.1 g = ∅)
  simp only [not_forall, not_and_or]

/-- Every individual multiplier is dominated before the edge choices are summed. -/
theorem memoryEdgeKernel_norm_le (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n) (mode : TransferMode)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (hphi : ∀ s t c, ‖phi s t c‖ ≤ 1) (s t : P.MemoryState (J + F.ell)) :
    ‖memoryEdgeKernel A n rho theta i mode phi s t‖ ≤
      absoluteMemoryEdgeKernel A n rho theta i mode s t := by
  simp only [memoryEdgeKernel, absoluteMemoryEdgeKernel, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (edgeSymmetryFactor_nonneg P (J + F.ell))]
  apply mul_le_mul_of_nonneg_left _ (edgeSymmetryFactor_nonneg P (J + F.ell))
  calc
    _ ≤ ∑ c : EdgeChoice A s,
        ‖if edgeChoiceValid A mode i s t c then
          edgeChoiceCoefficient A n rho theta i s t c * phi s t c else 0‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : edgeChoiceValid A mode i s t c
      · simp only [if_pos hc, norm_mul]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hphi s t c)
          (norm_nonneg (edgeChoiceCoefficient A n rho theta i s t c))
      · simp only [if_neg hc, norm_zero, le_refl]

theorem memoryEdgeKernel_all (A : Model F P J m) (n : ℕ) (rho theta : ℝ)
    (i : Fin n)
    (phi : (s t : P.MemoryState (J + F.ell)) → EdgeChoice A s → ℂ)
    (s t : P.MemoryState (J + F.ell)) :
    memoryEdgeKernel A n rho theta i .all phi s t =
      memoryEdgeKernel A n rho theta i .clean phi s t +
        memoryEdgeKernel A n rho theta i .dirty phi s t := by
  simp only [memoryEdgeKernel, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  simp only [edgeChoiceValid, transferModeAccept, and_true]
  by_cases hv : rawEdgeValid A (A.pattern c.2.2.1) (edgeForward i) c.2.2.2.1
    (permuteActive c.1 s) (permuteActive c.2.1 t) c.2.2.2.2
  · have hd := transferModeAccept_dirty_iff c.2.2.2.2
    change (∃ g, c.2.2.2.2.1 g ≠ ∅ ∨ c.2.2.2.2.2.1 g ≠ ∅) ↔
      ¬ (∀ g, c.2.2.2.2.1 g = ∅ ∧ c.2.2.2.2.2.1 g = ∅) at hd
    by_cases hclean : ∀ g, c.2.2.2.2.1 g = ∅ ∧ c.2.2.2.2.2.1 g = ∅
    · have hdirty := hd.not.mpr (not_not.mpr hclean)
      simp only [hv, ite_true, true_and, if_pos hclean, if_neg hdirty, add_zero]
    · have hdirty := hd.mpr hclean
      simp only [hv, ite_true, true_and, if_neg hclean, if_pos hdirty, zero_add]
  · simp [hv]


end Erdos821.S2Core
