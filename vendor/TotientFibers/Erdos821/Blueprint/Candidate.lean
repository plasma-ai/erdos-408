import Erdos821.Blueprint.Classical

/-! P7: geometric slot lists, their literal coefficient and uniform candidate bounds. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace Erdos821.Blueprint
open Analytic

structure BandData where
  geometry : Geometry
  groups : ℝ → PrimeGroups
  r₀ : ℕ
  c₁ : ℝ
  c₂ : ℝ
  s' : ℝ
  ratio : ℝ
  last : ℝ → ℕ

namespace BandData
variable (D : BandData)
def scale (x : ℝ) (j : ℕ) : ℝ := D.s' * L x / D.ratio ^ j
def band (x : ℝ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc ⌈Real.exp (D.c₁ * D.scale x j)⌉₊
    ⌊Real.exp (D.c₂ * D.scale x j)⌋₊).filter Nat.Prime

def Valid : Prop :=
  1 ≤ D.r₀ ∧ 0 < D.c₁ ∧ D.c₁ < D.c₂ ∧ 0 < D.s' ∧
  1 < D.ratio ∧ D.c₂ * D.s' < 1 / 4 ∧
  ((D.r₀ : ℝ) - 1) * D.c₁ / D.ratio ≥ D.c₂ + 1 ∧
  Tendsto D.last atTop atTop ∧
  ∃ cmin cmax : ℝ, 0 < cmin ∧ 0 < cmax ∧ ∀ᶠ x : ℝ in atTop,
    Admissible D.geometry x (D.groups x) ∧
    cmin * T x ≤ D.scale x (D.last x) ∧ D.scale x (D.last x) ≤ cmax * T x ∧
    (∀ i ≤ D.last x, ∀ j ≤ D.last x, i ≠ j → Disjoint (D.band x i) (D.band x j)) ∧
    (∀ j ≤ D.last x, ∀ g, Disjoint (D.band x j) ((D.groups x).primes g))

abbrev Slot (x : ℝ) := Fin (D.last x + 1) × Fin D.r₀

def slotValues (x : ℝ) (jstar : ℕ) (s : D.Slot x) : Finset ℕ :=
  let lo := Real.exp (D.c₁ * D.scale x s.1.val)
  let hi := Real.exp (D.c₂ * D.scale x s.1.val)
  if s.1.val = jstar ∧ s.2.val = 0 then
    (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough (W x))
  else D.band x s.1.val

abbrev SlotValue (x : ℝ) (jstar : ℕ) (s : D.Slot x) :=
  {v : ℕ // v ∈ D.slotValues x jstar s}
abbrev Lists (x : ℝ) (jstar : ℕ) := (s : D.Slot x) → D.SlotValue x jstar s

def listProduct {x : ℝ} {jstar : ℕ} (z : D.Lists x jstar) : ℕ := ∏ s, (z s).val
def aQ (x : ℝ) (jstar v : ℕ) : ℝ :=
  ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ *
    (Finset.univ.filter (fun z : D.Lists x jstar => D.listProduct z = v)).card

def weight (x : ℝ) (jstar u : ℕ) : ℝ :=
  D.aQ x jstar (groupFreePart (D.groups x) u) *
    markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) u

def harmonicQ (x : ℝ) (jstar : ℕ) : ℝ :=
  ((D.r₀.factorial : ℝ) ^ (D.last x + 1))⁻¹ *
    ∏ s : D.Slot x, ∑ v ∈ D.slotValues x jstar s, (v : ℝ)⁻¹

def harmonicP (x : ℝ) : ℝ := ∑' r : ℕ,
  if 0 < r ∧ groupFreePart (D.groups x) r = 1 then
    markWeight (D.groups x) D.geometry.q (fun _ => D.geometry.ell) r / r
  else 0
end BandData

structure CandidateData where
  bands : BandData
  j₀ : ℕ
  prefixLen : ℕ
  micro : ℕ
  theta : ℝ
  psi : ℝ → ℝ

namespace CandidateData
variable (C : CandidateData)
def Geometry (δ : ℝ) : Prop :=
  C.bands.Valid ∧ C.bands.c₁ = 1 ∧ C.bands.c₂ = 6 / 5 ∧ C.bands.ratio = 2 ∧
  C.bands.s' = 1 / ((C.bands.r₀ : ℝ) * (C.bands.c₁ + C.bands.c₂)) ∧
  C.bands.c₂ * C.bands.s' < δ ∧
  (∀ᶠ x : ℝ in atTop,
    20 * T x ≤ C.bands.c₁ * C.bands.scale x (C.bands.last x) ∧
    C.bands.c₁ * C.bands.scale x (C.bands.last x + 1) < 20 * T x) ∧
  C.prefixLen < C.j₀ ∧
  2 * C.bands.r₀ * C.bands.c₂ * C.bands.s' / 2 ^ (C.prefixLen + 1) <
    (C.bands.c₂ - C.bands.c₁) * C.bands.s' / 24 ∧
  C.bands.geometry.q = 1 / 2 ∧ C.bands.geometry.ell = 1 ∧
  C.bands.geometry.a = 1 / 10 ∧ C.bands.geometry.b = 1 / 5 ∧
  C.bands.geometry.c = 3 / 10 ∧ C.bands.geometry.d = 2 / 5 ∧
  C.micro ≤ C.j₀ ∧ C.bands.c₂ * C.bands.s' / 2 ^ C.micro < C.theta ∧
  C.theta < 2 * C.bands.c₁ * C.bands.s' / 2 ^ C.micro ∧
  10 * C.theta ≤ 1 / 20 ∧
  2 * C.bands.r₀ * C.bands.c₂ * C.bands.s' / 2 ^ C.micro ≤ 1 / 25 ∧
  ContDiff ℝ ∞ C.psi ∧ Function.support C.psi ⊆ Set.Icc 1 2 ∧
  (∀ y, 0 ≤ C.psi y) ∧
  (∃ a b c : ℝ, 1 < a ∧ a < b ∧ b < 2 ∧ 0 < c ∧
    ∀ y ∈ Set.Icc a b, c ≤ C.psi y)

def weighted (x : ℝ) (jstar u : ℕ) : ℝ := C.bands.weight x jstar u * C.psi (u / x)
def mass (x : ℝ) (jstar : ℕ) : ℝ := ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊, C.weighted x jstar u
def primeMass (x : ℝ) (jstar : ℕ) : ℝ :=
  ∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => Nat.Prime (2 * u + 1)), C.weighted x jstar u

def Bounds (δ : ℝ) : Prop :=
  ∃ K CA cmin cmax : ℝ, 0 < K ∧ 0 < cmin ∧ 0 < cmax ∧
    ∀ jstar : ℕ, C.j₀ ≤ jstar → ∀ᶠ x : ℝ in atTop,
      x * L x ^ (-CA) ≤ C.mass x jstar ∧
      cmin * (x / L x) * C.bands.harmonicQ x jstar * C.bands.harmonicP x ≤ C.mass x jstar ∧
      C.mass x jstar ≤ cmax * (x / L x) * C.bands.harmonicQ x jstar * C.bands.harmonicP x ∧
      (∀ u : ℕ, 0 ≤ C.weighted x jstar u) ∧
      (∀ u : ℕ, C.weighted x jstar u ≤ Real.exp (K * Real.sqrt (L x))) ∧
      (∀ u : ℕ, C.weighted x jstar u ≠ 0 → x ≤ (u : ℝ) ∧ (u : ℝ) ≤ 2 * x ∧
        ∀ p : ℕ, p.Prime → p ∣ u → L x ^ (20 : ℕ) ≤ (p : ℝ) ∧ (p : ℝ) ≤ x ^ δ)

def remainder (x : ℝ) (jstar d : ℕ) : ℝ :=
  (∑ u ∈ (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun u => d ∣ 2 * u + 1), C.weighted x jstar u) -
    C.mass x jstar / (Nat.totient d : ℝ)

def TypeI : Prop :=
  ∀ θ D : ℝ, θ < 1 / 2 → 0 < D →
    ∀ jstar : ℕ, C.j₀ ≤ jstar → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      (∑ d ∈ (Finset.Icc 1 ⌊x ^ θ⌋₊).filter (fun d => Odd d ∧ Squarefree d),
        |C.remainder x jstar d|) ≤
        K * (x * L x ^ (-D) + C.mass x jstar * L x ^ (-18 : ℝ))
end CandidateData

/-- P7 geometry is chosen before the gap, rough slot, accuracy and proxy precision. -/
abbrev candidate_geometry_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 4),
    ∃ C : CandidateData, C.Geometry δ
abbrev candidate_bounds_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (δ : ℝ) (C : CandidateData)
    (_hC : C.Geometry δ),
    C.Bounds δ
abbrev candidate_typeI_statement : Prop :=
  ∀ (_hc : ClassicalInputs) (δ : ℝ) (C : CandidateData)
    (_hC : C.Geometry δ) (_hb : C.Bounds δ),
    C.TypeI
end Erdos821.Blueprint
