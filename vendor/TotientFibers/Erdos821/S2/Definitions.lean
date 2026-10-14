import Mathlib

/-! Finite data for §2 of Weighted dilation graphs. No placeholder proofs. -/

noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2

/-- §1 logarithmic scales. -/
def L (x : ℝ) : ℝ := Real.log x
def T (x : ℝ) : ℝ := Real.log (L x)
def W (x : ℝ) : ℝ := Real.exp (Real.sqrt (L x))
def phase (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)
def imaginaryPower (n : ℕ) (ζ : ℝ) : ℂ := Complex.exp (ζ * Real.log n * Complex.I)

structure FixedData where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  c₀ : ℝ
  C₀ : ℝ
  vMin : ℝ
  vMax : ℝ
  q : ℝ
  ell : ℕ
  a_pos : 0 < a
  ab : a < b
  bc : b < c
  cd : c < d
  d_lt : d < (47 : ℝ) / 100
  c₀_pos : 0 < c₀
  C₀_pos : 0 < C₀
  vMin_pos : 0 < vMin
  vMax_pos : 0 < vMax
  q_pos : 0 < q
  q_lt : q < 1

/-- def:prime-groups. Small and big groups are separated by a Boolean flag. -/
structure PrimeGroups where
  count : ℕ
  primes : Fin count → Finset ℕ
  big : Fin count → Bool
  prime : ∀ g p, p ∈ primes g → Nat.Prime p
  disjoint : ∀ g h, g ≠ h → Disjoint (primes g) (primes h)

namespace PrimeGroups
variable (P : PrimeGroups)
abbrev Group := Fin P.count
abbrev Prime (g : P.Group) := {p : ℕ // p ∈ P.primes g}
def smallGroups : Finset P.Group := Finset.univ.filter (fun g => P.big g = false)
def bigGroups : Finset P.Group := Finset.univ.filter (fun g => P.big g = true)
def allPrimes : Finset ℕ := Finset.univ.biUnion P.primes
def V (g : P.Group) : ℝ := ∑ p ∈ P.primes g, (p : ℝ)⁻¹
def mu (g : P.Group) (p : P.Prime g) : ℝ := (P.V g * p.val)⁻¹
def omegaGroup (g : P.Group) (n : ℤ) : ℕ := (P.primes g |>.filter (fun p : ℕ => (p : ℤ) ∣ n)).card
def omega (n : ℤ) : ℕ := ∑ g, P.omegaGroup g n

def Admissible (F : FixedData) (x : ℝ) : Prop :=
  F.c₀ * T x ≤ (P.smallGroups.card : ℝ) ∧
  (P.smallGroups.card : ℝ) ≤ F.C₀ * T x ∧
  F.c₀ * T x ≤ (P.bigGroups.card : ℝ) ∧
  (P.bigGroups.card : ℝ) ≤ F.C₀ * T x ∧
  (∀ g, F.vMin ≤ P.V g ∧ P.V g ≤ F.vMax) ∧
  (∀ g p, p ∈ P.primes g →
    if P.big g then Real.exp ((L x) ^ F.c) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp ((L x) ^ F.d)
    else Real.exp ((L x) ^ F.a) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp ((L x) ^ F.b))

abbrev Labels (M : ℕ) := (g : P.Group) → Fin M → P.Prime g
abbrev BigGroup := {g : P.Group // P.big g = true}
abbrev BigLabels (M : ℕ) := (g : P.BigGroup) → Fin M → P.Prime g.val
abbrev Aux (J : ℕ) := (g : P.Group) → Fin J → P.Prime g
abbrev BigAux (J : ℕ) := (g : P.BigGroup) → Fin J → P.Prime g.val
abbrev Permutations (M : ℕ) := P.Group → Equiv.Perm (Fin M)
abbrev BigPermutations (M : ℕ) := P.BigGroup → Equiv.Perm (Fin M)

def restrictBig {M : ℕ} (a : P.Labels M) : P.BigLabels M := fun g => a g.val

def physical (M : ℕ) (n : ℤ) (a : P.Labels M) : Prop :=
  ∀ g, Function.Injective (a g) ∧ ∀ i, ((a g i).val : ℤ) ∣ n

def markMass (M : ℕ) : ℝ := ∏ g, (P.V g) ^ (-(M : ℤ))
def idealMass {M : ℕ} (a : P.BigLabels M) : ℝ := ∏ g, ∏ i, P.mu g.val (a g i)

def act {M : ℕ} (π : P.Permutations M) (a : P.Labels M) : P.Labels M :=
  fun g i => a g (π g i)
def actBig {M : ℕ} (π : P.BigPermutations M) (a : P.BigLabels M) : P.BigLabels M :=
  fun g i => a g (π g i)
end PrimeGroups

/-- Patterns and coefficients; K has only big-label arguments. -/
structure Pattern (P : PrimeGroups) (J ell m : ℕ) where
  changed : P.Group → Finset (Fin J)
  small : ∀ g, P.big g = false → changed g = ∅
  bound : ∀ g, (changed g).card ≤ m
  coefficient : P.BigLabels (J + ell) → P.BigLabels (J + ell) → P.BigAux J → ℂ
  coefficient_aux_ext : ∀ a b u v,
    (∀ g i, i ∈ changed g.val → u g i = v g i) → coefficient a b u = coefficient a b v

namespace Pattern
variable {P : PrimeGroups} {J ell m : ℕ} (ν : Pattern P J ell m)
def slot (_ν : Pattern P J ell m) (i : Fin J) : Fin (J + ell) := ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_add_right J ell)⟩
def shared (g : P.Group) (i : Fin (J + ell)) : Prop :=
  ∃ j : Fin J, ν.slot j = i ∧ j ∉ ν.changed g
def t (g : P.Group) : ℕ := ell + (ν.changed g).card

def D (a : P.Labels (J + ell)) (u : P.Aux J) : ℕ :=
  ∏ g, ∏ i : Fin J, if i ∈ ν.changed g then (u g i).val else (a g (ν.slot i)).val

def DBig (a : P.BigLabels (J + ell)) (u : P.BigAux J) : ℕ :=
  ∏ g, ∏ i : Fin J, if i ∈ ν.changed g.val then (u g i).val else (a g (ν.slot i)).val

def compatible (a b : P.Labels (J + ell)) : Prop :=
  ∀ g i, ν.shared g i → a g i = b g i

def matchesBig (a b : P.BigLabels (J + ell)) : Prop :=
  ∀ g i, ν.shared g.val i → a g i = b g i

def ban (a b : P.Labels (J + ell)) (u : P.Aux J) : Prop :=
  ∀ g i, i ∈ ν.changed g → ∀ j, u g i ≠ a g j ∧ u g i ≠ b g j

def auxMass (_ν : Pattern P J ell m) (u : P.Aux J) : ℝ := ∏ g, ∏ i, P.mu g (u g i)
def bigAuxMass (_ν : Pattern P J ell m) (u : P.BigAux J) : ℝ := ∏ g, ∏ i, P.mu g.val (u g i)
def freshMass (b : P.BigLabels (J + ell)) : ℝ :=
  ∏ g, ∏ i, if ν.shared g.val i then 1 else P.mu g.val (b g i)
def physicalTargetMass : ℝ := ∏ g, (P.V g) ^ (-(ν.t g : ℤ))
end Pattern

/-- Finite family; supremum is a finite maximum including zero. -/
structure Model (F : FixedData) (P : PrimeGroups) (J m : ℕ) where
  patternCount : ℕ
  pattern : Fin patternCount → Pattern P J F.ell m
  k : ℤ
  zeta : ℝ

namespace Model
variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m)
abbrev Labels (_A : Model F P J m) := P.Labels (J + F.ell)
abbrev BigLabels (_A : Model F P J m) := P.BigLabels (J + F.ell)
abbrev State := ℤ × A.Labels

/-- def:ideal-operator, before both symmetrizing projections. -/
def idealRaw (θ : ℝ) (a b : A.BigLabels) : ℂ :=
  ∑ v, ∑ u : P.BigAux J,
    if (A.pattern v).matchesBig a b then
      ((A.pattern v).bigAuxMass u * (A.pattern v).freshMass b : ℝ) *
      (A.pattern v).coefficient a b u * imaginaryPower ((A.pattern v).DBig a u) A.zeta *
      phase (θ * (A.pattern v).DBig a u)
    else 0

def idealKernel (θ : ℝ) (a b : A.BigLabels) : ℂ :=
  ((Fintype.card (P.BigPermutations (J + F.ell)) : ℂ) ^ 2)⁻¹ *
    ∑ π : P.BigPermutations (J + F.ell), ∑ τ : P.BigPermutations (J + F.ell),
      A.idealRaw θ (P.actBig π a) (P.actBig τ b)

def damping (_A : Model F P J m) (n : ℤ) : ℝ := F.q ^ (((P.omega n : ℝ) - (J + F.ell) * P.count) / 2)

/-- def:physical-operator. Unused auxiliary coordinates integrate to one. -/
def physicalRaw (absolute : Bool) (z z' : A.State) : ℂ :=
  if P.physical (J + F.ell) z.1 z.2 ∧ P.physical (J + F.ell) z'.1 z'.2 then
    ∑ v, ∑ u : P.Aux J,
      if (A.pattern v).compatible z.2 z'.2 ∧ (A.pattern v).ban z.2 z'.2 u ∧
          z'.1 = z.1 + A.k * ((A.pattern v).D z.2 u : ℤ) then
        let c := (A.pattern v).coefficient (P.restrictBig z.2) (P.restrictBig z'.2)
          (fun g => u g.val) * imaginaryPower ((A.pattern v).D z.2 u) A.zeta
        ((A.pattern v).auxMass u * (A.pattern v).physicalTargetMass *
          A.damping z.1 * A.damping z'.1 : ℝ) * (if absolute then (‖c‖ : ℂ) else c)
      else 0
  else 0

def physicalKernel (absolute : Bool) (z z' : A.State) : ℂ :=
  ((Fintype.card (P.Permutations (J + F.ell)) : ℂ) ^ 2)⁻¹ *
    ∑ π : P.Permutations (J + F.ell), ∑ τ : P.Permutations (J + F.ell),
      A.physicalRaw absolute (z.1, P.act π z.2) (z'.1, P.act τ z'.2)

def stateMass (z : A.State) : ℝ :=
  if P.physical (J + F.ell) z.1 z.2 then P.markMass (J + F.ell) else 0

-- The maximum does not require a nonempty label space when evaluated via `sSup`.
def patternMass : ℝ := ∑ v, sSup (Set.range (fun (z : A.BigLabels × A.BigLabels × P.BigAux J) =>
  ‖(A.pattern v).coefficient z.1 z.2.1 z.2.2‖))
end Model

/-- Finite integer dyad: integer n satisfies X ≤ n < 2X exactly. -/
def dyad (X : ℝ) : Finset ℤ := Finset.Ico ⌈X⌉ ⌈2 * X⌉
def R (x : ℝ) : ℕ := ⌈(L x) ^ ((52 : ℝ) / 100)⌉₊
def N (x : ℝ) : ℕ := 2 * R x

def kernelComp {α : Type*} (K H : α → α → ℂ) (a b : α) : ℂ := ∑' z, K a z * H z b

def kernelPower {α : Type*} (K : α → α → ℂ) : ℕ → α → α → ℂ
  | 0, a, b => if a = b then 1 else 0
  | n + 1, a, b => kernelComp K (kernelPower K n) a b

namespace Model
variable {F : FixedData} {P : PrimeGroups} {J m : ℕ} (A : Model F P J m)
def adjointKernel (a b : A.State) : ℂ := star (A.physicalKernel false b a)
def rootMoment (r : ℕ) (n : ℤ) : ℝ :=
  (∑ a : A.Labels, ∑ b : A.Labels, (A.stateMass (n, a) : ℂ) *
    kernelPower (kernelComp (A.physicalKernel false) A.adjointKernel) r (n, a) (n, b)).re

def averageMoment (x X : ℝ) : ℝ :=
  ((dyad X).card : ℝ)⁻¹ * ∑ n ∈ dyad X, A.rootMoment (R x) n

/-- Finite-support functions suffice since I contains finitely many mark lists. -/
def pair (s t : Finset A.State) (f g : A.State → ℂ) : ℂ :=
  ∑ a ∈ s, ∑ b ∈ t, (A.stateMass a : ℂ) * star (f a) * A.physicalKernel false a b * g b

def normSq (s : Finset A.State) (f : A.State → ℂ) : ℝ :=
  ∑ z ∈ s, A.stateMass z * ‖f z‖ ^ 2
end Model

namespace PrimeGroups
variable (P : PrimeGroups)
abbrev GroupPrime := {p : ℕ // p ∈ P.allPrimes}
abbrev Residues := (p : P.GroupPrime) → Fin p.val

def pathFactor (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (z : ℤ) : ℝ :=
  ∏ p ∈ P.allPrimes, ∏ i : Fin (n + 1),
    if p ∈ active i then (if (p : ℤ) ∣ z + h i then 1 else 0)
    else if (p : ℤ) ∣ z + h i then q i else 1

def residuePathFactor (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) (y : P.Residues) : ℝ :=
  ∏ p : P.GroupPrime, ∏ i : Fin (n + 1),
    if p.val ∈ active i then (if (p.val : ℤ) ∣ (y p).val + h i then 1 else 0)
    else if (p.val : ℤ) ∣ (y p).val + h i then q i else 1

def residueExpectation (n : ℕ) (q : Fin (n + 1) → ℝ) (h : Fin (n + 1) → ℤ)
    (active : Fin (n + 1) → Finset ℕ) : ℝ :=
  (Fintype.card P.Residues : ℝ)⁻¹ * ∑ y : P.Residues, P.residuePathFactor n q h active y
end PrimeGroups

def visitQ (q : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i.val = 0 ∨ i.val = n then Real.sqrt q else q

/-- Dual finite-support formulation of the L² norm, valid also for countable states.
K already includes target integration. Positive masses are the inner-product measure. -/
def NormBound {α : Type*} (mass : α → ℝ) (K : α → α → ℂ) (C : ℝ) : Prop :=
  ∀ (s t : Finset α) (f g : α → ℂ),
    ‖∑ a ∈ s, ∑ b ∈ t, (mass a : ℂ) * star (f a) * K a b * g b‖ ≤
      C * Real.sqrt (∑ a ∈ s, mass a * ‖f a‖ ^ 2) *
        Real.sqrt (∑ b ∈ t, mass b * ‖g b‖ ^ 2)

/-- eq:lifespan-baseline and its tilted label weights. -/
def eta (F : FixedData) (n : ℕ) (i : Fin (n + 1)) : ℝ := 1 - visitQ F.q n i
def baselinePrime (F : FixedData) (n p : ℕ) : ℝ :=
  1 - (p : ℝ)⁻¹ * ∑ i : Fin (n + 1), eta F n i

def tiltedMu (F : FixedData) (P : PrimeGroups) (n : ℕ) (g : P.Group) (p : P.Prime g) : ℝ :=
  (P.V g * p.val * baselinePrime F n p.val)⁻¹

def bigBaseline (F : FixedData) (P : PrimeGroups) (n : ℕ) : ℝ :=
  ∏ g ∈ P.bigGroups, ∏ p ∈ P.primes g, baselinePrime F n p

def omissionNumber (F : FixedData) (P : PrimeGroups) (J : ℕ) : ℕ :=
  Nat.choose (J + F.ell) F.ell ^ P.smallGroups.card

def memoryCutoff (x : ℝ) : ℕ := ⌈(L x) ^ (2 : ℕ)⌉₊

namespace PrimeGroups
variable (P : PrimeGroups)
abbrev SmallGroup := {g : P.Group // P.big g = false}
instance primeNeZero (g : P.Group) (p : P.Prime g) : NeZero p.val :=
  ⟨(P.prime g p.val p.property).ne_zero⟩
abbrev SmallResidues := (g : P.SmallGroup) → (p : P.Prime g.val) → ZMod p.val
abbrev Particle (g : P.Group) := (p : P.Prime g) × ZMod p.val
abbrev Memory (g : P.Group) := Multiset (P.Particle g)
abbrev MemoryState (M : ℕ) := P.SmallResidues × P.Labels M × ((g : P.BigGroup) → P.Memory g.val)

def smallPhysical {M : ℕ} (y : P.SmallResidues) (a : P.Labels M) : Prop :=
  ∀ g : P.SmallGroup, Function.Injective (a g.val) ∧ ∀ i, y g (a g.val i) = 0

def memorySize {M : ℕ} (z : P.MemoryState M) : ℕ := ∑ g, (z.2.2 g).card
def memoryWeight {M : ℕ} (v : ℝ) (z : P.MemoryState M) : ℝ := v ^ P.memorySize z

def emptyBoundary {M : ℕ} (z : P.MemoryState M) : ℂ :=
  if ∀ g, z.2.2 g = 0 then 1 else 0

/-- Pushforward of λ^j/j! from ordered particles to their multiset.
The denominator keeps the index multiplicities of coincident particles. -/
def groupMemoryMass (F : FixedData) (n : ℕ) (g : P.Group) (z : P.Memory g) : ℝ :=
  (z.map (fun u => tiltedMu F P n g u.1)).prod /
    ∏ u ∈ z.toFinset, ((z.count u).factorial : ℝ)

def memoryMass (F : FixedData) (J n : ℕ) (z : P.MemoryState (J + F.ell)) : ℝ :=
  if P.smallPhysical z.1 z.2.1 then
    (Fintype.card P.SmallResidues : ℝ)⁻¹ *
      (∏ g : P.SmallGroup, (P.V g.val) ^ (-(J + F.ell : ℕ) : ℤ)) *
      (∏ g : P.BigGroup, ∏ i, tiltedMu F P n g.val (z.2.1 g.val i)) *
      ∏ g : P.BigGroup, P.groupMemoryMass F n g.val (z.2.2 g)
  else 0
end PrimeGroups

/-- Absolute row and column certificates require convergence of their sums. -/
def WeightedBounds {α : Type*} (mass w : α → ℝ) (K : α → α → ℂ) (C : ℝ) : Prop :=
  (∀ a, Summable (fun b => ‖K a b‖ * w b) ∧
    ∑' b, ‖K a b‖ * w b ≤ C * w a) ∧
  (∀ b, Summable (fun a => mass a * ‖K a b‖ * w a) ∧
    ∑' a, mass a * ‖K a b‖ * w a ≤ C * mass b * w b)

def projectKernel {α : Type*} (keep : α → Prop) (K : α → α → ℂ) (a b : α) : ℂ :=
  if keep a ∧ keep b then K a b else 0

/-- Birth collections are disjoint nonsingleton blocks of potential addresses. -/
def BirthCollection {a : ℕ} (π : Finset (Finset (Fin a))) : Prop :=
  (∀ B ∈ π, 2 ≤ B.card) ∧ (π : Set (Finset (Fin a))).Pairwise Disjoint

/-- Equality rank adds |B|-1 separately for each block. -/
def birthRank {a : ℕ} (π : Finset (Finset (Fin a))) : ℕ := ∑ B ∈ π, (B.card - 1)

def birthMobius {a : ℕ} (π : Finset (Finset (Fin a))) : ℤ :=
  ∏ B ∈ π, (-1 : ℤ) ^ (B.card - 1) * (Nat.factorial (B.card - 1) : ℤ)

def birthEvent {a : ℕ} (performed : Finset (Fin a)) (value : Fin a → ℕ)
    (π : Finset (Finset (Fin a))) : Prop :=
  ∀ B ∈ π, B ⊆ performed ∧ ∀ i ∈ B, ∀ j ∈ B, value i = value j


end Erdos821.S2
