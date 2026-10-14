module

public import Erdos408.Statement
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# The graph-paper results

The results of *The Poisson–Dirichlet law for prime predecessors* (PD)
and *Weighted dilation graphs, smooth shifted primes and totient fibers* (WD)
from which the rectangle statistic is derived. Put `L = log x`, `T = log L`,
`s = log T` and `W = exp(L^{0.24})`; an integer is *rough* if it has no
prime factor at most `W`.

* `OneSidedTypeII` is PD Theorem 3.1 for every coefficient `α` with the
  properties its proof uses: support in `[H_m, 2H_m]`, roughness, a
  logarithmic size bound, and the twisted cancellation of PD Lemma 5.2. The
  scales may shrink to `x^γ` with `γ ≥ L^{-1/100}`, and the band exponents
  may vary in a fixed window with a fixed gap. The integer-kernel bound that
  PD's Lemma 5.3 derives at fixed scales is a premise. It is proved as
  `oneSidedTypeII` in `Erdos408.OneSided`, so it is no longer a hypothesis.
* `TwoSidedCorrelation` is PD Theorem 6.1 with a bounded joint coefficient
  on all slots but the last, slot margins `x^{cT^{-20}}`, a clipped
  invariant core, up to `O(s)` varying inert bands, and cutoffs with
  `T^{O(1)}` derivatives. The two analytic estimates its proof needs at
  those margins, replacing PD (6.37) and (6.38), are premises. It is proved
  as `twoSidedCorrelation_of_graphTransference` in `Erdos408.TwoSided`,
  following PD §6.
* `GraphTransference` is PD Propositions 6.2 and 6.3 composed: WD's local
  transference and residual ideal family, for endpoints that depend on the
  position alone. It is proved as `graphTransference` in `Erdos408.Graph`,
  from the vendored formalization of WD (`vendor/TotientFibers/`).
* `BlockSieve` is WD Lemma 2.9 (PD Lemma 2.6) as printed, with the implicit
  `z ≥ 1`. It is proved as `blockSieve` in `Erdos408.BlockSieve`, so it is no
  longer a hypothesis.

`OneSidedTypeII` and `TwoSidedCorrelation` are *not* the printed theorems.
The printed statements fix the scale, the margin, the bands and the proxy,
and give no rate, so they do not imply the rectangle statistic. These are
the extensions that the extraction of *The normal order of the number of
iterations of Euler's function* (Plasma AI, 2026), §6, uses and argues the
printed proofs support; both are proved here.

No statement here uses a zero-free region: every analytic estimate is a
premise, proved separately from the vendored zero-free half-plane. See
`blueprint/rectangle_input.md` for the statements and their justification.

None of these definitions appears in `Challenge.lean`, whose theorems have no
hypotheses.
-/

@[expose] public section

open Filter

namespace Erdos408

/-- The roughness level `W = exp(L^{0.24})`. -/
noncomputable def roughLevel (x : ℝ) : ℝ :=
  Real.exp (Real.log x ^ (0.24 : ℝ))

/-- `n` is rough: every prime factor exceeds `W`. -/
def IsRough (x : ℝ) (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, roughLevel x < p

/-- The band of primes `exp(L^a) ≤ p ≤ exp(2 L^a)`. -/
noncomputable def band (x a : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈Real.exp (Real.log x ^ a)⌉₊ ⌊Real.exp (2 * Real.log x ^ a)⌋₊).filter Nat.Prime

/-- The number of primes of `S` dividing `n`. -/
def primeCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  (S.filter (· ∣ n)).card

/-- The harmonic mass `∑_{p ∈ S} 1 / p`. -/
noncomputable def harmonicMass (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, (1 : ℝ) / p

/-- The marked weight `q^{ω(n) - |s|} ∏_{i ∈ s} ω_i(n) / V_i` of a family of
prime groups, where `ω_i(n)` counts the primes of group `i` dividing `n` and
`ω = ∑ ω_i`. This is PD (3.4) for the bands and the weight `W₁` of PD
(6.2) for the active groups. -/
noncomputable def markedWeight {ι : Type*} (s : Finset ι) (q : ℝ) (G : ι → Finset ℕ)
    (n : ℕ) : ℝ :=
  q ^ ((∑ i ∈ s, primeCount (G i) n : ℕ) - s.card : ℤ) *
    ∏ i ∈ s, (primeCount (G i) n : ℝ) / harmonicMass (G i)

/-- `n_*`: `n` with its prime factors in `P` removed, with multiplicity. -/
noncomputable def stripPrimes (P : Finset ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors with p ∉ P, p ^ n.factorization p

/-- The primes in `[a, b]`. -/
noncomputable def primesIcc (a b : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter Nat.Prime

/-- The analytic premise replacing PD (6.38): twisted prime sums over
intervals `I ⊂ [H, 2H]` with `exp(L / T²²) ≤ H ≤ x`, for characters of
modulus at most `L^{C_m}` and `L^E ≤ |u| ≤ x³`, are at most `κ L^{-A}`. -/
def PrimeTwistBound (x A E Cm κ : ℝ) : Prop :=
  ∀ H lo hi : ℝ, Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤ H → H ≤ x →
    H ≤ lo → hi ≤ 2 * H →
    ∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm → ∀ (χ : DirichletCharacter ℂ k) (u : ℝ),
      Real.log x ^ E ≤ |u| → |u| ≤ x ^ 3 →
      ‖∑ p ∈ (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime,
          χ p * (p : ℂ) ^ ((-1 : ℂ) + (u : ℂ) * Complex.I)‖ ≤
        κ * Real.log x ^ (-A)

/-- The analytic premise replacing PD (6.37): over intervals `I ⊂ [H, 2H]`
with `exp(L / T²²) ≤ H ≤ x`, residue classes of modulus at most `L^{C_m}`, and
`1 ≤ |u| ≤ x³`, the integer kernel satisfies
`H⁻¹ |∑_{n ∈ I, n ≡ a} n^{iu}| ≤ κ ((1 + |u|)⁻¹ + exp(-L^{0.95}))`. -/
def IntegerKernelBound (x Cm κ : ℝ) : Prop :=
  ∀ H lo hi : ℝ, Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤ H → H ≤ x →
    H ≤ lo → hi ≤ 2 * H →
    ∀ (k a : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm → ∀ u : ℝ, 1 ≤ |u| → |u| ≤ x ^ 3 →
      H⁻¹ * ‖∑ n ∈ (Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter (· ≡ a [MOD k]),
          (n : ℂ) ^ ((u : ℂ) * Complex.I)‖ ≤
        κ * ((1 + |u|)⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ)))

/-- The extended two-sided marked correlation (PD Theorem 6.1).

The fixed data are: `q, q₀ ∈ (0, 1)`; active-group constants
`c₀, C₀, v₋, v₊`; an inert window `[a₋, a₊] ⊂ (0.1, 0.2)` with `K₀, C_N`;
a margin constant `c > 0`; `d ≤ 2` weighted slots; a core exponent `B₀`; a
cutoff class `κ > 1, C_Ψ, (M_r)`; and a target `A`. There are a premise
precision `A'` and modulus exponent `C_m` such that, for every frequency
threshold `E` and premise constant `κ'`, the following holds for large `x`
satisfying the premises. Take active groups as in PD (6.1); at most
`K₀ + C_N s` disjoint inert bands; `d + 1` slots `(x^{u_i}, x^{v_i}]` with
`u_i ≥ c / T²⁰` and `∑ v_i ≤ 1 - c / T²⁰`, the last a spare; a coefficient
`|B| ≤ 1` on the first `d` slots; a core with `G(n) = G(n_*)` and
`0 ≤ G ≤ L^{B₀}`; and a cutoff `Ψ` supported in `[κ⁻¹, κ]` with
`|Ψ^{(r)}| ≤ M_r T^{C_Ψ r}`. Then
`|∑_w Ψ(w/x) w⁻¹ 𝒲(w) (f_B(w) - C_B) G(w+1) W₁(w) W₁(w+1)| ≤ C* L^{-A}`. -/
def TwoSidedCorrelation : Prop :=
  ∀ (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ)
    (M : ℕ → ℝ) (A : ℝ),
    0 < q → q < 1 → 0 < q₀ → q₀ < 1 → 0 < c₀ → 0 < vlo → 1 / 10 < alo → alo ≤ ahi →
    ahi < 1 / 5 → 0 < c → d ≤ 2 → 1 < κ →
    ∃ A' Cm : ℝ, ∀ E κ' : ℝ, ∃ Cstar : ℝ, ∀ᶠ x : ℝ in atTop,
      PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
      ∀ (Sg Bg : Finset (Finset ℕ)) (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ)
        (Bc : (Fin d → ℕ) → ℝ) (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
        -- active groups as in PD (6.1)
        Disjoint Sg Bg → (Sg ∪ Bg : Set (Finset ℕ)).PairwiseDisjoint id →
        c₀ * Real.log (Real.log x) ≤ Sg.card → (Sg.card : ℝ) ≤ C₀ * Real.log (Real.log x) →
        c₀ * Real.log (Real.log x) ≤ Bg.card → (Bg.card : ℝ) ≤ C₀ * Real.log (Real.log x) →
        (∀ P ∈ Sg ∪ Bg, vlo ≤ harmonicMass P ∧ harmonicMass P ≤ vhi) →
        (∀ P ∈ Sg, P ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
          (Real.exp (Real.log x ^ (0.36 : ℝ)))) →
        (∀ P ∈ Bg, P ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
          (Real.exp (Real.log x ^ (0.46 : ℝ)))) →
        (∀ P ∈ Bg, ∃ y z : ℝ, P = primesIcc y z) →
        -- inert bands
        (r : ℝ) ≤ K₀ + CN * Real.log (Real.log (Real.log x)) →
        (∀ i, alo ≤ a i ∧ a i ≤ ahi) →
        (∀ i j, i ≠ j → Disjoint (band x (a i)) (band x (a j))) →
        -- slots, the last one spare
        (∀ i, c / Real.log (Real.log x) ^ 20 ≤ u i) →
        ∑ i, v i ≤ 1 - c / Real.log (Real.log x) ^ 20 →
        (∀ Q, |Bc Q| ≤ 1) →
        -- the clipped invariant core
        (∀ n, G n = G (stripPrimes ((Sg ∪ Bg).biUnion id) n)) →
        (∀ n, 0 ≤ G n ∧ G n ≤ Real.log x ^ B₀) →
        -- the cutoff
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ → (∀ y, Ψ y ≠ 0 → κ⁻¹ ≤ y ∧ y ≤ κ) →
        (∀ (k : ℕ) (y : ℝ), |iteratedDeriv k Ψ y| ≤ M k * Real.log (Real.log x) ^ (CΨ * k)) →
        |∑ w ∈ Finset.Icc 1 ⌊κ * x⌋₊,
            Ψ (w / x) / w *
              (markedWeight Finset.univ q (fun i => band x (a i)) w *
                ((∑ Q ∈ slotTuples x u v with ∏ i, Q i ∣ w, Bc (Fin.init Q)) -
                  ∑ Q ∈ slotTuples x u v, Bc (Fin.init Q) / ∏ i, (Q i : ℝ))) *
              G (w + 1) * markedWeight (Sg ∪ Bg) q₀ id w *
              markedWeight (Sg ∪ Bg) q₀ id (w + 1)| ≤
          Cstar * Real.log x ^ (-A)

/-- The extended one-sided marked Type II estimate (PD Theorem 3.1).

For fixed `q ∈ (0, 1)`, `C, D_* > 0`, `C_X ≥ 1` and a window
`[a₋, a₊] ⊂ (0.1, 0.2)`, there are `K₀` and exponents `A₀, B, A` such that,
for every `K ≥ K₀`, every gap `g > 0` and all constants `c₄, c_G`, the
following holds for large `x`. The gap comes after `K₀`: `K` bands spaced
`g` apart must fit in the window, so a gap fixed first would let `K₀` make
the hypotheses unsatisfiable. Let `K` bands have exponents in the window,
spaced at least `g` apart, and let `γ ≥ L^{-1/100}`, `H_m, H_n ≥ x^γ` with
`X = H_m H_n ≍ x`. Let `|F| ≤ 1` be invariant under the band primes; let
`α` be supported on rough `m ∈ [H_m, 2H_m]` with `|α| ≤ L^C` and
`|H_m⁻¹ ∑ α_m χ(m) m^{it}| ≤ c₄ L^{-A}` for characters of modulus at most
`L^{A₀}` and `|t| ≤ 2 X L^B`; let `β` be supported on rough
`n ∈ [H_n, 2H_n]` with `|β| ≤ L^C`; and let the integer kernel satisfy
`H_n⁻¹ |∑_{H_n ≤ n ≤ 2H_n} n^{iΔ}| ≤ c_G (|Δ|⁻¹ + exp(-L^{0.95}))` for
`1 ≤ |Δ| ≤ 4 X L^B + 2`. Then
`|∑ α_m β_n F(mn - 1) 𝒲(mn - 1)| ≤ C₁ X L^{-D_*}`. -/
def OneSidedTypeII : Prop :=
  ∀ (q C Dstar CX alo ahi : ℝ), 0 < q → q < 1 → 0 < C → 0 < Dstar → 1 ≤ CX →
    1 / 10 < alo → alo ≤ ahi → ahi < 1 / 5 →
    ∃ (K₀ : ℕ) (A₀ B A : ℝ), ∀ K : ℕ, K₀ ≤ K → ∀ g c₄ cG : ℝ, 0 < g → ∃ C₁ : ℝ,
      ∀ᶠ x : ℝ in atTop,
        ∀ (a : Fin K → ℝ) (γ Hm Hn : ℝ) (F : ℕ → ℂ) (α β : ℕ → ℂ),
          (∀ i, alo ≤ a i ∧ a i ≤ ahi) → (∀ i j : Fin K, i < j → a i + g ≤ a j) →
          Real.log x ^ (-(1 / 100 : ℝ)) ≤ γ → x ^ γ ≤ Hm → x ^ γ ≤ Hn →
          x / CX ≤ Hm * Hn → Hm * Hn ≤ CX * x →
          (∀ h, ‖F h‖ ≤ 1) → (∀ i h, ∀ p ∈ band x (a i), F (p * h) = F h) →
          (∀ m, α m ≠ 0 →
            Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm ∧ IsRough x m ∧ ‖α m‖ ≤ Real.log x ^ C) →
          (∀ (k : ℕ), 1 ≤ k → (k : ℝ) ≤ Real.log x ^ A₀ → ∀ (χ : DirichletCharacter ℂ k)
            (t : ℝ), |t| ≤ 2 * (Hm * Hn) * Real.log x ^ B →
            ‖(Hm : ℂ)⁻¹ * ∑ m ∈ Finset.Icc ⌈Hm⌉₊ ⌊2 * Hm⌋₊,
                α m * χ m * (m : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ c₄ * Real.log x ^ (-A)) →
          (∀ n, β n ≠ 0 →
            Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough x n ∧ ‖β n‖ ≤ Real.log x ^ C) →
          (∀ Δ : ℝ, 1 ≤ |Δ| → |Δ| ≤ 4 * (Hm * Hn) * Real.log x ^ B + 2 →
            Hn⁻¹ * ‖∑ n ∈ Finset.Icc ⌈Hn⌉₊ ⌊2 * Hn⌋₊, (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ ≤
              cG * (|Δ|⁻¹ + Real.exp (-Real.log x ^ (0.95 : ℝ)))) →
          ‖∑ m ∈ Finset.Icc ⌈Hm⌉₊ ⌊2 * Hm⌋₊, ∑ n ∈ Finset.Icc ⌈Hn⌉₊ ⌊2 * Hn⌋₊,
              α m * β n * F (m * n - 1) *
                markedWeight Finset.univ q (fun i => band x (a i)) (m * n - 1)‖ ≤
            C₁ * (Hm * Hn) * Real.log x ^ (-Dstar)

/-- The number `ω(n)` of group primes dividing `n`. -/
def groupPrimeCount {ι : Type*} [Fintype ι] (P : ι → Finset ℕ) (n : ℕ) : ℕ :=
  ∑ g, primeCount (P g) n

/-- The marks of the physical states at `n` (WD Definition 3.3): ordered lists
of `M` distinct primes of each group `P g`, all dividing `n`. -/
noncomputable def physicalLists {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (M n : ℕ) : Finset (ι → Fin M → ℕ) :=
  (Fintype.piFinset fun g => Fintype.piFinset fun _ : Fin M => P g).filter fun p =>
    ∀ g, Function.Injective (p g) ∧ ∀ i, p g i ∣ n

/-- The squared physical norm `∑_n |f(n)|² · #lists(n) · ∏_g V_g^{-M}` of a
function of the position alone, over positions in `S`. -/
noncomputable def physicalNormSq {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (M : ℕ) (S : Finset ℕ) (f : ℕ → ℂ) : ℝ :=
  ∑ n ∈ S, ‖f n‖ ^ 2 * (physicalLists P M n).card * ∏ g, (harmonicMass (P g))⁻¹ ^ M

/-- The auxiliary free labels of a pattern with free slots `C g ⊆ Fin J`: a
prime of `P g` in each slot of `C g`, and `1` in every other slot. -/
noncomputable def auxLabels {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) {J : ℕ}
    (C : ι → Finset (Fin J)) : Finset (ι → Fin J → ℕ) :=
  Fintype.piFinset fun g => Fintype.piFinset fun i => if i ∈ C g then P g else {1}

/-- The edge product `D = D_R D_C`: the shared source labels in the first `J`
slots outside `C g`, and the auxiliary labels in the slots of `C g`. -/
def edgeProduct {ι : Type*} [Fintype ι] {J : ℕ} (C : ι → Finset (Fin J))
    (p : ι → Fin (J + 1) → ℕ) (a : ι → Fin J → ℕ) : ℕ :=
  ∏ g, ∏ i, if i ∈ C g then a g i else p g i.castSucc

/-- The product of the labels of `a` in the slots `A g`. -/
def slotProduct {ι : Type*} [Fintype ι] {J : ℕ} (A : ι → Finset (Fin J))
    (a : ι → Fin J → ℕ) : ℕ :=
  ∏ g, ∏ i ∈ A g, a g i

/-- The pairing `⟨f, 𝒜_ν g⟩` of one pattern of the physical operator (WD
Definition 3.3, PD (6.6)), with `ℓ = 1` final slot and shift `k = 1`, between
endpoints `f, g` that depend on the position alone. The source is a physical
state `(n, p)` with `n ∈ S`, of mass `∏_g V_g^{-M}`, `M = J + 1`. The pattern
frees the slots `C g` of the first `J`. Auxiliary labels `a` in these slots have
law `∏ μ_g`, `μ_g(p) = 1 / (V_g p)`, and must avoid both endpoint lists. The
target is every physical state `(n + D, p')` sharing the source labels in the
other first `J` slots, with coefficient `∏_g V_g^{-t_g}`, `t_g = |C g| + 1`.
The multiplier is `K(p, p', a) D^{iζ} q₀^{(ω(n) - Ms)/2} q₀^{(ω(n + D) - Ms)/2}`,
with `s` the number of groups. For such endpoints the slot symmetrizations of
the printed operator drop out. -/
noncomputable def patternPairing {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    (q₀ : ℝ) {J : ℕ} (C : ι → Finset (Fin J))
    (K : (ι → Fin (J + 1) → ℕ) → (ι → Fin (J + 1) → ℕ) → (ι → Fin J → ℕ) → ℂ) (ζ : ℝ)
    (S : Finset ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ n ∈ S, ∑ p ∈ physicalLists P (J + 1) n, ∑ a ∈ auxLabels P C,
    ∑ p' ∈ (physicalLists P (J + 1) (n + edgeProduct C p a)).filter (fun p' =>
        ∀ h, (∀ i, i ∉ C h → p' h i.castSucc = p h i.castSucc) ∧
          ∀ i ∈ C h, ∀ j, a h i ≠ p h j ∧ a h i ≠ p' h j),
      ((∏ h, (harmonicMass (P h))⁻¹ ^ (J + 1) *
          (∏ i ∈ C h, (harmonicMass (P h) * a h i)⁻¹) *
          (harmonicMass (P h))⁻¹ ^ ((C h).card + 1) : ℝ) : ℂ) *
        starRingEnd ℂ (f n) * K p p' a *
        ((edgeProduct C p a : ℂ) ^ ((ζ : ℂ) * Complex.I)) *
        ((Real.sqrt q₀ ^ (groupPrimeCount P n - (J + 1) * Fintype.card ι) *
          Real.sqrt q₀ ^ (groupPrimeCount P (n + edgeProduct C p a) -
            (J + 1) * Fintype.card ι) : ℝ) : ℂ) *
        g (n + edgeProduct C p a)

/-- The graph transference input: PD Propositions 6.2 and 6.3, composed (WD
Theorem 3.5, Corollary 3.11, Theorem 4.1 and Lemma 4.3), with `ℓ = k = 1` and
the group exponents of PD (6.1), for endpoints that depend on the position
alone.

For fixed `q₀ ∈ (0, 1)` and group constants `c₀, C₀, v₋, v₊`, and every
transfer saving `E`, endpoint exponent `C₃` and frequency exponent `C₄`, there
are a probe bound `m₀`, a number `J` of shared slots, a pattern-mass exponent
`C₁` and a constant `C` with the following property for large `x`. Take active
groups as in PD (6.1), small and big. There is a family of comparison patterns:
each frees disjoint nonempty sets `A, B` of at most `m₀` slots among the first
`J` of the big groups, and has coefficient `β φ(D_A) φ'(D_B) ψ(X_A) ψ'(X_B)`.
Here `D_A, D_B` are the products of the auxiliary labels in `A, B`, `X_A` is
the product of the target labels in `A` and `X_B` of the source labels in `B`;
`|φ|, |φ'|, |ψ|, |ψ'| ≤ 1`, `φ` and `φ'` are supported in log cells
`[U, eU]`, and `∑ |β| ≤ L^{C₁}`. The pairing of the raw pattern (no free
slots, coefficient one) plus all comparison patterns, at any `|ζ| ≤ L^{C₄}`,
between `f` supported on `[X, 2X)` with `x^{1/2} ≤ X ≤ x²`, `|f| ≤ 1`, and any
`g`, with both physical norms at most `X^{1/2} L^{C₃}`, is at most
`C X L^{-E + 2C₃}`.

WD's family has this form after expanding its kernels: each term of PD (6.10)
is a cell indicator times a character value, with weight at most `ξ⁻¹`. -/
def GraphTransference : Prop :=
  ∀ (q₀ c₀ C₀ vlo vhi : ℝ), 0 < q₀ → q₀ < 1 → 0 < c₀ → 0 < vlo →
    ∀ E C₃ C₄ : ℝ, ∃ (m₀ J : ℕ) (C₁ C : ℝ), ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        -- active groups as in PD (6.1)
        (∀ g h, g ≠ h → Disjoint (P g) (P h)) →
        c₀ * Real.log (Real.log x) ≤ (Finset.univ \ big).card →
        ((Finset.univ \ big).card : ℝ) ≤ C₀ * Real.log (Real.log x) →
        c₀ * Real.log (Real.log x) ≤ big.card → (big.card : ℝ) ≤ C₀ * Real.log (Real.log x) →
        (∀ g, vlo ≤ harmonicMass (P g) ∧ harmonicMass (P g) ≤ vhi) →
        (∀ g ∉ big, P g ⊆ primesIcc (Real.exp (Real.log x ^ (0.27 : ℝ)))
          (Real.exp (Real.log x ^ (0.36 : ℝ)))) →
        (∀ g ∈ big, P g ⊆ primesIcc (Real.exp (Real.log x ^ (0.39 : ℝ)))
          (Real.exp (Real.log x ^ (0.46 : ℝ)))) →
        (∀ g ∈ big, ∃ y z : ℝ, P g = primesIcc y z) →
        ∃ (N : ℕ) (A B : Fin N → ι → Finset (Fin J)) (β : Fin N → ℂ)
          (φ φ' ψ ψ' : Fin N → ℕ → ℂ) (U U' : Fin N → ℝ),
          -- the comparison patterns
          (∀ ν g, Disjoint (A ν g) (B ν g) ∧ (A ν g ∪ B ν g).card ≤ m₀) ∧
          (∀ ν, ∀ g ∉ big, A ν g = ∅ ∧ B ν g = ∅) ∧
          (∀ ν, (∃ g, (A ν g).Nonempty) ∧ ∃ g, (B ν g).Nonempty) ∧
          (∀ ν n, ‖φ ν n‖ ≤ 1 ∧ ‖φ' ν n‖ ≤ 1 ∧ ‖ψ ν n‖ ≤ 1 ∧ ‖ψ' ν n‖ ≤ 1) ∧
          (∀ ν n, φ ν n ≠ 0 → U ν ≤ n ∧ n ≤ Real.exp 1 * U ν) ∧
          (∀ ν n, φ' ν n ≠ 0 → U' ν ≤ n ∧ n ≤ Real.exp 1 * U' ν) ∧
          ∑ ν, ‖β ν‖ ≤ Real.log x ^ C₁ ∧
          -- the transferred pairing
          ∀ ζ : ℝ, |ζ| ≤ Real.log x ^ C₄ → ∀ X : ℝ, √x ≤ X → X ≤ x ^ 2 →
            ∀ (S S' : Finset ℕ) (f g : ℕ → ℂ), (∀ n ∈ S, X ≤ n ∧ (n : ℝ) < 2 * X) →
              (∀ n, ‖f n‖ ≤ 1) → (∀ n ∉ S', g n = 0) →
              physicalNormSq P (J + 1) S f ≤ X * Real.log x ^ (2 * C₃) →
              physicalNormSq P (J + 1) S' g ≤ X * Real.log x ^ (2 * C₃) →
              ‖patternPairing P q₀ (fun _ => (∅ : Finset (Fin J))) (fun _ _ _ => 1) ζ S f g +
                  ∑ ν, patternPairing P q₀ (fun h => A ν h ∪ B ν h)
                    (fun p p' a => β ν * φ ν (slotProduct (A ν) a) * φ' ν (slotProduct (B ν) a) *
                      ψ ν (slotProduct (A ν) fun h i => p' h i.castSucc) *
                      ψ' ν (slotProduct (B ν) fun h i => p h i.castSucc)) ζ S f g‖ ≤
                C * X * Real.log x ^ (-E + 2 * C₃)

/-- The block sieve (WD Lemma 2.9, PD Lemma 2.6).

Nonnegatively weighted objects carry a bad condition at each designated
prime `p ≤ z`, where `z ≥ 1` (implicit in the printed lemma: for `z < 1` the
remainder sum would omit `D = ∅`, and the statement fails). Suppose the
weight on which the conditions at every prime of a set `D` hold is
`X g(D) + r(D)`, with `g(D) = ∏_{p ∈ D} g(p)`,
`0 ≤ g(p) ≤ 1 - η₀` and `∑_{w < p ≤ w²} g(p) ≤ C₀`. Then, for every large
even `h`, the weight avoiding all bad conditions is
`X ∏ (1 - g(p)) (1 + O(e^{-h})) + O(∑_{∏ D ≤ z^{4h+2}} |r(D)|)`, and for
`h = 2` it is at most a fixed constant times `X ∏ (1 - g(p))` plus the same
remainder sum. The constants depend only on `η₀, C₀`. -/
def BlockSieve : Prop :=
  ∀ η₀ C₀ : ℝ, 0 < η₀ → ∃ (h₀ : ℕ) (K : ℝ),
    ∀ {ι : Type} (objs : Finset ι) (wt : ι → ℝ) (P : Finset ℕ) (z X : ℝ)
      (bad : ℕ → ι → Prop) [∀ p i, Decidable (bad p i)] (g : ℕ → ℝ),
      (∀ i ∈ objs, 0 ≤ wt i) → 1 ≤ z → (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) → 0 ≤ X →
      (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
      (∀ w : ℝ, 1 < w → ∑ p ∈ P.filter (fun p : ℕ => w < p ∧ (p : ℝ) ≤ w ^ 2), g p ≤ C₀) →
      let S : Finset ℕ → ℝ := fun D => ∑ i ∈ objs with ∀ p ∈ D, bad p i, wt i
      let rem : Finset ℕ → ℝ := fun D => S D - X * ∏ p ∈ D, g p
      let sifted : ℝ := ∑ i ∈ objs with ∀ p ∈ P, ¬ bad p i, wt i
      let main : ℝ := X * ∏ p ∈ P, (1 - g p)
      (∀ h : ℕ, Even h → h₀ ≤ h →
        |sifted - main| ≤
          K * Real.exp (-(h : ℝ)) * main +
            K * ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ (4 * h + 2), |rem D|) ∧
      sifted ≤ K * main + K * ∑ D ∈ P.powerset with ((∏ p ∈ D, p : ℕ) : ℝ) ≤ z ^ 10, |rem D|

end Erdos408
