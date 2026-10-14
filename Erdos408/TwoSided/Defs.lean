module

public import Erdos408.Extraction.Defs

/-!
# Definitions for the two-sided correlation

The objects of `blueprint/two_sided_correlation.md` §3.1, for the proof of
`TwoSidedCorrelation` from `GraphTransference` (PD §6). Groups are indexed by a `Fintype ι`
with `P : ι → Finset ℕ` and `big : Finset ι`, as in `GraphTransference`; the assembly
reindexes `TwoSidedCorrelation`'s groups once, with `ι = ↥(Sg ∪ Bg)`.

* The admissibility predicates of the varying data: the groups of PD (6.1), the inert
  bands, the clipped core and the cutoff class.
* The centered core `F = 𝒲 (f_B - C_B)` and the raw correlation `twoSidedSum`.
* The represented lists `slotLists` and the marked list weight `W_t^b` of PD (6.2).
* The stripped comparison correlation of one pattern, PD (6.15), and the comparison patterns
  of `GraphTransference`'s family.
* The first endpoint `endpointCoeff` of a comparison at scale `Y`, PD (6.28).
-/

@[expose] public section

namespace Erdos408.TwoSided

/-- PD (6.1) for groups indexed by `ι`; the hypotheses of `GraphTransference`. -/
def GroupAdmissible (c₀ C₀ vlo vhi x : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (big : Finset ι) : Prop :=
  (∀ g h, g ≠ h → Disjoint (P g) (P h)) ∧
  c₀ * Real.log (Real.log x) ≤ (Finset.univ \ big).card ∧
  ((Finset.univ \ big).card : ℝ) ≤ C₀ * Real.log (Real.log x) ∧
  c₀ * Real.log (Real.log x) ≤ big.card ∧ (big.card : ℝ) ≤ C₀ * Real.log (Real.log x) ∧
  (∀ g, vlo ≤ harmonicMass (P g) ∧ harmonicMass (P g) ≤ vhi) ∧
  (∀ g ∉ big, P g ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
    (Real.exp (Real.log x ^ (0.36 : ℝ)))) ∧
  (∀ g ∈ big, P g ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
    (Real.exp (Real.log x ^ (0.46 : ℝ)))) ∧
  ∀ g ∈ big, ∃ y z : ℝ, P g = primesIcc y z

/-- At most `K₀ + C_N s` disjoint inert bands with exponents in the window. -/
def InertAdmissible (K₀ : ℕ) (CN alo ahi x : ℝ) {r : ℕ} (a : Fin r → ℝ) : Prop :=
  (r : ℝ) ≤ K₀ + CN * Real.log (Real.log (Real.log x)) ∧ (∀ i, alo ≤ a i ∧ a i ≤ ahi) ∧
    ∀ i j, i ≠ j → Disjoint (band x (a i)) (band x (a j))

/-- The clipped invariant core. -/
def CoreAdmissible (B₀ x : ℝ) {ι : Type} [Fintype ι] (P : ι → Finset ℕ) (G : ℕ → ℝ) :
    Prop :=
  (∀ n, G n = G (stripPrimes (Finset.univ.biUnion P) n)) ∧
    ∀ n, 0 ≤ G n ∧ G n ≤ Real.log x ^ B₀

/-- The cutoff class of `TwoSidedCorrelation` (signed; `IsCutoff` in `Extraction/Defs` also
asks `0 ≤ Φ`). -/
def CutoffAdmissible (κ CΨ : ℝ) (M : ℕ → ℝ) (x : ℝ) (Ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧ (∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) ∧
    ∀ (k : ℕ) (y : ℝ), |iteratedDeriv k Ψ y| ≤ M k * Real.log (Real.log x) ^ (CΨ * k)

/-- `F_x = 𝒲 (f_B − C_B)`, PD (6.4) with the spare slot (X1). -/
noncomputable def centeredCore (x q : ℝ) {r d : ℕ} (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ)
    (Bc : (Fin d → ℕ) → ℝ) (n : ℕ) : ℝ :=
  markedWeight Finset.univ q (fun i => band x (a i)) n *
    (slotCount x u v Bc n - slotMean x u v Bc)

/-- The raw correlation, the sum in `TwoSidedCorrelation` in the `ι` encoding. -/
noncomputable def twoSidedSum (x q q₀ κ : ℝ) {r d : ℕ} (a : Fin r → ℝ)
    (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ) {ι : Type} [Fintype ι]
    (P : ι → Finset ℕ) (G : ℕ → ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  ∑ w ∈ Finset.Icc 1 ⌊κ * x⌋₊, Ψ (w / x) / w * centeredCore x q a u v Bc w * G (w + 1) *
    markedWeight Finset.univ q₀ P w * markedWeight Finset.univ q₀ P (w + 1)

/-- The unshared slots of group `g` after stripping: its free slots and the final one. -/
def unsharedSlots {ι : Type} {J : ℕ} (C : ι → Finset (Fin J)) (g : ι) :
    Finset (Fin (J + 1)) :=
  insert (Fin.last J) ((C g).map Fin.castSuccEmb)

/-- Represented lists at `n`, as in PD (6.2): in each slot of `S g` a prime of `P g` dividing
`n`, distinct within the group, and `1` in every other slot. -/
noncomputable def slotLists {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    {M : ℕ} (S : ι → Finset (Fin M)) (n : ℕ) : Finset (ι → Fin M → ℕ) :=
  (Fintype.piFinset fun g => Fintype.piFinset fun i => if i ∈ S g then P g else {1}).filter
    fun p => ∀ g, Set.InjOn (p g) (S g) ∧ ∀ i ∈ S g, p g i ∣ n

/-- `W_t^b(n)` of PD (6.2), with `t_g = |S g|` (zero allowed). -/
noncomputable def markedListWeight {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (q₀ : ℝ) {M : ℕ} (S : ι → Finset (Fin M))
    (b : (ι → Fin M → ℕ) → ℂ) (n : ℕ) : ℂ :=
  ((q₀ ^ ((groupPrimeCount P n : ℤ) - ∑ g, ((S g).card : ℤ)) *
      ∏ g, (harmonicMass (P g))⁻¹ ^ (S g).card : ℝ) : ℂ) * ∑ p ∈ slotLists P S n, b p

/-- The stripped comparison correlation of one pattern, PD (6.15): free labels `a` with law
`∏ μ_g`, free products `D_A, D_B`, shift `D_C = D_A D_B`, source test `ψ'(X_B)`, target test
`ψ(X_A)`; no restrictions between labels. -/
noncomputable def strippedComparison (x q₀ : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) {J : ℕ} (A B : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ)
    (F G : ℕ → ℝ) (Ψ : ℝ → ℝ) : ℂ :=
  ∑ a ∈ auxLabels P (fun g => A g ∪ B g),
    ((∏ g, ∏ i ∈ A g ∪ B g, (harmonicMass (P g) * a g i)⁻¹ : ℝ) : ℂ) *
      φ (slotProduct A a) * φ' (slotProduct B a) *
      ∑ w ∈ Finset.Icc 1 ⌊x ^ 2⌋₊,
        ((Ψ (w / (x * slotProduct (fun g => A g ∪ B g) a)) / w * F w *
            G (w + slotProduct (fun g => A g ∪ B g) a) : ℝ) : ℂ) *
          markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
            (fun p => ψ' (slotProduct B fun g i => p g i.castSucc)) w *
          markedListWeight P q₀ (unsharedSlots fun g => A g ∪ B g)
            (fun p => ψ (slotProduct A fun g i => p g i.castSucc))
            (w + slotProduct (fun g => A g ∪ B g) a)

/-- One comparison pattern of `GraphTransference`'s family. -/
def ComparisonPattern (m₀ : ℕ) {ι : Type} [Fintype ι] (big : Finset ι) {J : ℕ}
    (A B : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ) (U U' : ℝ) : Prop :=
  (∀ g, Disjoint (A g) (B g) ∧ (A g ∪ B g).card ≤ m₀) ∧ (∀ g ∉ big, A g = ∅ ∧ B g = ∅) ∧
    ((∃ g, (A g).Nonempty) ∧ ∃ g, (B g).Nonempty) ∧
    (∀ n, ‖φ n‖ ≤ 1 ∧ ‖φ' n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖ψ' n‖ ≤ 1) ∧
    (∀ n, φ n ≠ 0 → U ≤ n ∧ n ≤ Real.exp 1 * U) ∧
    ∀ n, φ' n ≠ 0 → U' ≤ n ∧ n ≤ Real.exp 1 * U'

/-- The first endpoint of a comparison at scale `Y`, PD (6.28). -/
noncomputable def endpointCoeff (x q q₀ : ℝ) {r d : ℕ} (a : Fin r → ℝ)
    (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) {J : ℕ} (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ)
    (ψ₁ : ℝ → ℂ) (Y σ : ℝ) (w : ℕ) : ℂ :=
  ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (centeredCore x q a u v Bc w : ℂ) *
    markedListWeight P q₀ (unsharedSlots C) b w

end Erdos408.TwoSided
