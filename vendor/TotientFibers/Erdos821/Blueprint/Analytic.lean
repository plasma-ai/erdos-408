import Mathlib

/-! Planning interfaces for §§3–4. These declarations are deliberately not an
acceptance artifact: lemma proofs are placeholders, definitions are complete.
All divisions in analytic quantities take place in ℝ or ℂ. -/

open scoped BigOperators ContDiff
open Filter MeasureTheory

namespace Erdos821.Blueprint.Analytic

noncomputable section
attribute [local instance] Classical.propDecidable

def L (x : ℝ) : ℝ := Real.log x
def T (x : ℝ) : ℝ := Real.log (L x)
def W (x : ℝ) : ℝ := Real.exp (Real.sqrt (L x))
def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)
def mellin (n t : ℝ) : ℂ := Complex.exp (Complex.I * t * Real.log n)
def rough (y : ℝ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → y < (p : ℝ)

def dp (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, c n * mellin n t

def sqNorm (s : Finset ℕ) (c : ℕ → ℂ) : ℝ := ∑ n ∈ s, ‖c n‖ ^ 2

structure Geometry where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  c₀ : ℝ
  C₀ : ℝ
  vmin : ℝ
  vmax : ℝ
  q : ℝ
  ell : ℕ
  ordered : 0 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < 0.47
  positive : 0 < c₀ ∧ 0 < C₀ ∧ 0 < vmin ∧ vmin ≤ vmax
  damping : 0 < q ∧ q < 1
  marks : 1 ≤ ell

structure PrimeGroups where
  size : ℕ
  primes : Fin size → Finset ℕ
  small : Finset (Fin size)
  prime : ∀ g p, p ∈ primes g → p.Prime
  disjoint : ∀ g h, g ≠ h → Disjoint (primes g) (primes h)

def PrimeGroups.big (G : PrimeGroups) : Finset (Fin G.size) := Finset.univ \ G.small
def mass (G : PrimeGroups) (g : Fin G.size) : ℝ := ∑ p ∈ G.primes g, 1 / (p : ℝ)
def mu (G : PrimeGroups) (g : Fin G.size) (p : ℕ) : ℝ := 1 / (mass G g * p)

def Admissible (P : Geometry) (x : ℝ) (G : PrimeGroups) : Prop :=
  (P.c₀ * T x ≤ G.small.card ∧ (G.small.card : ℝ) ≤ P.C₀ * T x) ∧
  (P.c₀ * T x ≤ G.big.card ∧ (G.big.card : ℝ) ≤ P.C₀ * T x) ∧
  (∀ g, P.vmin ≤ mass G g ∧ mass G g ≤ P.vmax) ∧
  (∀ g p, p ∈ G.primes g →
    if g ∈ G.small then Real.exp (L x ^ P.a) ≤ p ∧ (p : ℝ) ≤ Real.exp (L x ^ P.b)
    else Real.exp (L x ^ P.c) ≤ p ∧ (p : ℝ) ≤ Real.exp (L x ^ P.d)) ∧
  (∀ g, g ∈ G.big → ∃ lo hi : ℝ, ∀ p : ℕ,
    p ∈ G.primes g ↔ p.Prime ∧ lo ≤ (p : ℝ) ∧ (p : ℝ) ≤ hi)

abbrev Label (G : PrimeGroups) (g : Fin G.size) := {p : ℕ // p ∈ G.primes g}
abbrev Tuple (G : PrimeGroups) (k : Fin G.size → ℕ) := ∀ g, Fin (k g) → Label G g

def product (G : PrimeGroups) (k : Fin G.size → ℕ) (z : Tuple G k) : ℕ :=
  ∏ g, ∏ j, (z g j).val

def tupleWeight (G : PrimeGroups) (k : Fin G.size → ℕ) (z : Tuple G k) : ℝ :=
  ∏ g, ∏ j, mu G g (z g j).val

def expect (G : PrimeGroups) (k : Fin G.size → ℕ) (f : Tuple G k → ℂ) : ℂ :=
  ∑ z, (tupleWeight G k z : ℂ) * f z

def tupleNorm (G : PrimeGroups) (k : Fin G.size → ℕ) (f : Tuple G k → ℂ) : ℝ :=
  Real.sqrt (∑ z, tupleWeight G k z * ‖f z‖ ^ 2)

def rho (G : PrimeGroups) (k : Fin G.size → ℕ) (n : ℕ) : ℝ :=
  ∑ z, if product G k z = n then tupleWeight G k z else 0

def collapse (G : PrimeGroups) (k : Fin G.size → ℕ)
    (f : Tuple G k → ℂ) (n : ℕ) : ℂ :=
  expect G k (fun z => if product G k z = n then f z else 0)

def bigSlots (G : PrimeGroups) (k : Fin G.size → ℕ) (m : ℕ) : Prop :=
  (∑ g, k g) > 0 ∧ ∀ g, k g ≤ m ∧ (g ∈ G.small → k g = 0)

abbrev CharacterIndex (Q : ℕ) := (r : Fin Q) × DirichletCharacter ℂ (r.val + 1)

def primitiveCharacters (Q : ℕ) : Finset (CharacterIndex Q) :=
  Finset.univ.filter fun χ => χ.2.IsPrimitive

def charValue {Q : ℕ} (χ : CharacterIndex Q) (n : ℕ) : ℂ := χ.2 (n : ZMod (χ.1.val + 1))

def cell (h : ℝ) (n : ℕ) : ℤ := ⌊Real.log n / h⌋
def cellMass (G : PrimeGroups) (k : Fin G.size → ℕ) (h : ℝ) (j : ℤ) : ℝ :=
  ∑ z, if cell h (product G k z) = j then tupleWeight G k z else 0

def cellKernel (G : PrimeGroups) (k : Fin G.size → ℕ) (Q : ℕ) (h ξ : ℝ)
    (D X : ℕ) : ℂ :=
  if cell h D = cell h X ∧ ξ ≤ cellMass G k h (cell h X) then
    (cellMass G k h (cell h X) : ℂ)⁻¹ *
      ∑ χ ∈ primitiveCharacters Q, star (charValue χ D) * charValue χ X
  else 0

/-- §3, eq. ideal-product-atom, including all zero-probability fibers. -/
abbrev product_atom_bound_statement : Prop :=
  ∀ (P : Geometry) (m : ℕ),
    ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
      ∀ k, bigSlots G k m → ∀ n : ℕ, 0 < n →
      rho G k n ≤ L x ^
        (P.C₀ * (Real.log (Nat.factorial m) + m * Real.log (max 1 P.vmin⁻¹))) / n
/-- §3, eq. ideal-collapse; tests retain their ordered tuple dependence. -/
abbrev collapse_l2_statement : Prop :=
  ∀ (G : PrimeGroups) (k : Fin G.size → ℕ)
    (f : Tuple G k → ℂ) (s : Finset ℕ) (R : ℝ)
    (hR : 0 ≤ R) (hρ : ∀ n ∈ s, rho G k n ≤ R),
    sqNorm s (collapse G k f) ≤ R * (tupleNorm G k f) ^ 2
/-- §3, Lemma integer bilinear estimate. Origins N and M are unrestricted. -/
abbrev integer_bilinear_statement : Prop :=
  ∀ (C : ℝ) (hC : 0 < C),
    ∃ K : ℝ, 0 < K ∧ ∀ (U V N M α β : ℝ) (u : ℤ) (r : ℕ)
      (s t : Finset ℤ) (a b : ℤ → ℂ),
      1 ≤ U → 1 ≤ V → 1 ≤ r → Nat.Coprime u.natAbs r →
      α = (u : ℝ) / r + β → |β| ≤ (r : ℝ) ^ (-2 : ℤ) →
      (∀ n ∈ s, N ≤ (n : ℝ) ∧ (n : ℝ) ≤ N + C * U) →
      (∀ n ∈ t, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ M + C * V) →
      ‖∑ n ∈ s, ∑ v ∈ t, a n * b v * e (α * n * v)‖ ≤
        K * Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) * Real.sqrt (∑ v ∈ t, ‖b v‖ ^ 2) *
          Real.sqrt (U + (1 + V / r) * (U + r * Real.log (2 * r)))
abbrev cell_kernel_sup_statement : Prop :=
  ∀ (G : PrimeGroups) (k : Fin G.size → ℕ)
    (Q : ℕ) (h ξ : ℝ) (hξ : 0 < ξ) (D X : ℕ),
    ‖cellKernel G k Q h ξ D X‖ ≤ (Q : ℝ) ^ 2 / ξ
def comparisonError (G : PrimeGroups) (a b : Fin G.size → ℕ)
    (Q : ℕ) (h ξ α ζ : ℝ) (f : Tuple G b → ℂ) (g : Tuple G a → ℂ) : ℂ :=
  expect G b fun XB => expect G a fun XA =>
    star (f XB) * g XA *
      (mellin (product G a XA * product G b XB) ζ * e (α * product G a XA * product G b XB) -
      expect G a fun DA => expect G b fun DB =>
        cellKernel G a Q h ξ (product G a DA) (product G a XA) *
        cellKernel G b Q h ξ (product G b DB) (product G b XB) *
        mellin (product G a DA * product G b DB) ζ * e (α * product G a DA * product G b DB))

/-- §3 comparison kernel; Q is rounded down, h and ξ are exact real powers. -/
abbrev comparison_kernel_statement : Prop :=
  ∀ (P : Geometry) (m : ℕ) (A C₄ : ℝ)
    (hA : 0 < A) (hC₄ : 0 ≤ C₄),
    ∃ qexp hexp ξexp : ℝ, 0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ᶠ x in atTop, ∀ G : PrimeGroups, Admissible P x G →
        ∀ a b, bigSlots G a m → bigSlots G b m →
        ∀ (α ζ : ℝ) (f : Tuple G b → ℂ) (g : Tuple G a → ℂ),
        |ζ| ≤ L x ^ C₄ →
        ‖comparisonError G a b ⌊L x ^ qexp⌋₊ (L x ^ (-hexp))
            (L x ^ (-ξexp)) α ζ f g‖ ≤ L x ^ (-A) * tupleNorm G b f * tupleNorm G a g
/-- §3 Hoeffding fraction; cast BEFORE division, and require feasible cardinalities. -/
abbrev hoeffding_fraction_statement : Prop :=
  ∀ (M m ell j : ℕ) (hml : m + ell ≤ M)
    (hmj : m ≤ j) (hje : j + ell ≤ M),
    (Nat.choose (M - m - ell) (j - m) : ℝ) / Nat.choose M j =
      ((Nat.descFactorial j m : ℝ) * Nat.descFactorial (M - j) ell) /
        Nat.descFactorial M (m + ell)
abbrev hoeffding_fraction_bound_statement : Prop :=
  ∀ (M m ell j : ℕ) (hm : 1 ≤ m) (he : 1 ≤ ell)
    (hM : (m + ell) * (m + ell - 1) ≤ M) (hj : j ≤ M),
    ((Nat.descFactorial j m : ℝ) * Nat.descFactorial (M - j) ell) /
      Nat.descFactorial M (m + ell) ≤ 2 * (ell : ℝ) ^ ell / (m : ℝ) ^ ell
-- `inclusion_exclusion` is proved in `Erdos821/Leaves/`.

def omegaGroup (G : PrimeGroups) (g : Fin G.size) (n : ℕ) : ℕ :=
  ((G.primes g).filter fun p => p ∣ n).card
def omega (G : PrimeGroups) (n : ℕ) : ℕ := ∑ g, omegaGroup G g n

def groupFreePart (G : PrimeGroups) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors \ (Finset.univ.biUnion G.primes), p ^ n.factorization p

def markWeight (G : PrimeGroups) (q : ℝ) (t : Fin G.size → ℕ) (n : ℕ) : ℝ :=
  q ^ ((omega G n : ℤ) - ∑ g, (t g : ℤ)) *
    ∏ g, (Nat.descFactorial (omegaGroup G g n) (t g) : ℝ) / mass G g ^ t g

def admissibleMarks (G : PrimeGroups) (t : Fin G.size → ℕ)
    (n : ℕ) (z : Tuple G t) : Prop :=
  ∀ g, Function.Injective (z g) ∧ ∀ j, (z g j).val ∣ n

def weightedMarks (G : PrimeGroups) (q : ℝ) (t : Fin G.size → ℕ)
    (b : Tuple G t → ℂ) (n : ℕ) : ℂ :=
  (q ^ ((omega G n : ℤ) - ∑ g, (t g : ℤ)) * ∏ g, (mass G g)⁻¹ ^ t g : ℝ) *
    ∑ z, if admissibleMarks G t n z then b z else 0

-- `mark_sup` is proved in `Erdos821/Leaves/`.

structure Endpoint where
  alpha : ℕ → ℂ
  residual : ℕ → ℂ
  modulus : ℕ
  positive : 0 < modulus
  chi : DirichletCharacter ℂ modulus
  sigma₀ : ℝ
  sigma₁ : ℝ
  lo : ℝ
  hi : ℝ

def endpoint (G : PrimeGroups) (x : ℝ) (E : Endpoint) (n : ℕ) : ℂ :=
  let N := groupFreePart G n
  ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 N,
    if m * p * r = N ∧ E.lo ≤ p ∧ (p : ℝ) ≤ E.hi ∧ rough (W x) p then
      E.alpha m * E.chi (m : ZMod E.modulus) * mellin m E.sigma₀ *
        mellin p E.sigma₁ * E.residual r else 0

def EndpointBound (x C τ η : ℝ) (E : Endpoint) : Prop :=
  0 < τ ∧ τ < η ∧ η < 1 / 4 ∧
  (∀ n, ‖E.alpha n‖ ≤ L x ^ C ∧ ‖E.residual n‖ ≤ L x ^ C) ∧
  (∀ n, E.alpha n ≠ 0 → rough (W x) n) ∧
  (E.modulus : ℝ) ≤ L x ^ C ∧ |E.sigma₀| ≤ L x ^ C ∧ |E.sigma₁| ≤ L x ^ C ∧
  x ^ τ ≤ E.lo ∧ E.lo ≤ E.hi ∧ E.hi ≤ x ^ η

def discrepancy (x B : ℝ) (a : ℕ → ℂ) : Prop :=
  ∀ (lo hi u : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r),
    1 ≤ lo → lo ≤ hi → hi ≤ x ^ (2 : ℕ) → 1 ≤ r → (r : ℝ) ≤ L x ^ B →
    |u| ≤ L x ^ B →
    ‖∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
      a n * χ (n : ZMod r) * mellin n u / (n : ℂ)‖ ≤ L x ^ (-B)

def CutoffBound (x C lo hi : ℝ) (Ψ : ℝ → ℂ) (bounds : ℕ → ℝ) : Prop :=
  ContDiff ℝ ∞ Ψ ∧ Function.support Ψ ⊆ Set.Icc lo hi ∧
  ∀ j y, ‖iteratedDeriv j Ψ y‖ ≤ bounds j * L x ^ (C * (j + 1))

def shiftCorrelation (P : Geometry) (G : PrimeGroups) (x Z a₁ a₂ : ℝ)
    (k : ℤ) (F H : Endpoint) (Ψ : ℝ → ℂ) (lo hi : ℝ) : ℂ :=
  ∑ z ∈ Finset.Icc ⌈lo * Z⌉₊ ⌊hi * Z⌋₊,
    if 0 < z ∧ 0 < (z : ℤ) + k then
      Ψ (z / Z) / (z : ℂ) * mellin z a₁ * mellin ((z : ℤ) + k) a₂ *
      star (endpoint G x F z) * endpoint G x H ((z : ℤ) + k).toNat *
      markWeight G P.q (fun _ => P.ell) z *
      markWeight G P.q (fun _ => P.ell) ((z : ℤ) + k).toNat else 0

abbrev lifted_shift_statement : Prop :=
  ∀ (P : Geometry) (D C τ η lo hi : ℝ) (bounds : ℕ → ℝ)
    (hD : 0 < D) (hC : 0 < C) (hI : 0 < lo ∧ lo < hi),
    ∃ B K : ℝ, 0 < B ∧ 0 < K ∧ ∀ᶠ x in atTop,
      ∀ (G : PrimeGroups) (F H : Endpoint) (k : ℤ) (Z a₁ a₂ : ℝ) (Ψ : ℝ → ℂ),
      Admissible P x G → EndpointBound x C τ η F → EndpointBound x C τ η H →
      k ≠ 0 → |(k : ℝ)| ≤ L x ^ C → x * L x ^ (-C) ≤ Z → Z ≤ x * L x ^ C →
      |a₁| ≤ L x ^ C → |a₂| ≤ L x ^ C → CutoffBound x C lo hi Ψ bounds →
      discrepancy x B F.alpha →
      ‖shiftCorrelation P G x Z a₁ a₂ k F H Ψ lo hi‖ ≤ K * L x ^ (-D)
def primePolynomial (s : Finset ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  dp s (fun p => b p / (p : ℂ)) t
def occupied (s : Finset ℕ) (b : ℕ → ℂ) (threshold Tmax : ℝ) : Set ℤ :=
  {j | ∃ t : ℝ, (j : ℝ) ≤ t ∧ t ≤ (j : ℝ) + 1 ∧
    |t| ≤ Tmax ∧ threshold < ‖primePolynomial s b t‖}

-- `exceptional_times` is proved in `Erdos821/P5/ExceptionalTheorem.lean`.

/-- §4 sparse residual estimate with quantitative slack in cardinality and length. -/
abbrev sparse_residual_statement : Prop :=
  ∃ K Y₀ : ℝ, 0 < K ∧ 1 < Y₀ ∧
    ∀ (Y U A : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (E : Finset ℤ),
      Y₀ ≤ Y → Y ^ (0.6 : ℝ) ≤ U → U ≤ Y → 0 ≤ A →
      (∀ n ∈ s, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * U) →
      sqNorm s c ≤ A / U → (E.card : ℝ) ≤ Y ^ (0.05 : ℝ) →
      (∀ j ∈ E, |(j : ℝ)| ≤ Y) →
      ∑ j ∈ E, ⨆ t : Set.Icc (j : ℝ) ((j : ℝ) + 1), ‖dp s c t‖ ^ 2 ≤
        K * A * Real.log (2 * Y)
/-- §4 long rough-integer polynomial. The variable n ranges over integers, not primes. -/
abbrev long_rough_polynomial_statement : Prop :=
  ∀ (τ η C A : ℝ) (hτ : 0 < τ) (hη : η < 1 / 4)
    (hC : 0 < C) (hA : 0 < A),
    ∃ B₀ K : ℝ, 0 < B₀ ∧ 0 < K ∧ ∀ᶠ x in atTop,
      ∀ (P lo hi σ t : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r),
      x ^ τ / 2 ≤ P → P ≤ x ^ η → P ≤ lo → lo ≤ hi → hi ≤ 2 * P →
      1 ≤ r → (r : ℝ) ≤ L x ^ C → |σ| ≤ L x ^ C →
      L x ^ B₀ ≤ |t| → |t + σ| ≤ x ^ (2 : ℕ) →
      ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough (W x)),
        χ (n : ZMod r) * mellin n (t + σ) / (n : ℂ)‖ ≤ K * L x ^ (-A)
end
end Erdos821.Blueprint.Analytic
