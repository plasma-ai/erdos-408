# Blueprint: the two-sided correlation (H2) from the graph transference input

This document records the proof of

```lean
theorem twoSidedCorrelation_of_graphTransference (hG : GraphTransference) :
    TwoSidedCorrelation
```

in `Erdos408/TwoSided.lean` and `Erdos408/TwoSided/`. Both propositions are defined in
`Erdos408/Hypotheses.lean`. `GraphTransference` is proved as `Erdos408.graphTransference`
(`Erdos408/Graph.lean`, `Erdos408/Graph/`) from the vendored WD formalization
(`vendor/TotientFibers/`), so `Solution.lean` obtains `TwoSidedCorrelation` with no hypotheses.

The proof is PD §6 with the extensions X1–X8 that `TwoSidedCorrelation` needs beyond PD
Theorem 6.1 (§7.3). This document restates PD §6 as a chain of lemmas with every quantifier
and parameter choice explicit, and says where each lemma lives in Lean. It also records:

- **O2**, every step that PD states at a fixed margin `ε`, with explicit bounds at the
  shrinking margin `ε = cT^{-20}` (§7.1);
- **O4**, the placement of the spare slot (§7.2);
- **X5**, Lemma 6.5 with `r ≤ K₀ + C_N s` inert bands (§6.1);
- **X6**, the Mellin tails for cutoffs with `T^{O(r)}` derivatives (§4.2, §5.1);
- that the premise constants `A'` and `C_m` do not depend on the frequency threshold `E`
  (§1.3).

**The one repair.** PD's S19 bounds progression sums of `n^{it}` at scales `R' = x^{1±o(1)}`.
Some of these scales are *above* `x`, where the premise `IntegerKernelBound`, which stops at
`H ≤ x`, does not apply. The unconditional `IntegerKernel.norm_sum_filter_modEq_le`
(`Erdos408/Analytic/IntegerKernel.lean`) has no upper bound on the scale, and it covers S19
completely (§6.6). The premise `IntegerKernelBound` (AP2) is used only in the sparse Gram bound
S17, where every scale is at most `x` (§6.5); the premise `PrimeTwistBound` (AP1) is used only
in S18 (§6.6). The paper *The normal order of the number of iterations of Euler's
function* (Plasma AI, 2026) notes the same point: the constant-term argument uses the
progression bound on slightly larger scales.

**Sources.** "PD" is *The Poisson–Dirichlet law for prime predecessors*, and "WD" is
*Weighted dilation graphs, smooth shifted primes and totient fibers*. Equation numbers
(6.1)–(6.42) and Lemmas 6.4–6.5 are PD's; WD's shifted correlations are its §5, with Theorem
5.1, Lemmas 5.2–5.4 and equations (5.1)–(5.12). Vendored Lean is cited by its path under
`vendor/TotientFibers/Erdos821/`, abbreviated `tf/…`.

**Step numbers.** S0–S20 number the steps of PD's proof of Theorem 6.1 in order:

| step | content | PD |
|---|---|---|
| S0 | parameter order | §6.2 |
| S1 | endpoint vectors and norms | (6.12) |
| S2 | insertion of `Ψ`, Mellin separation, dyads, transference | (6.13) |
| S3 | stripping the shared labels | (6.14)–(6.15) |
| S4 | restoring the suppressed restrictions | (6.16) |
| S5 | comparison scales and endpoint energies | (6.17)–(6.19) |
| S6–S7 | bilinear multiplier, minor and major arcs | (6.20)–(6.21) |
| S8 | reduction to the arc energy | (6.22) |
| S9 | local Mellin energy | Lemma 6.4, (6.23) |
| S10 | reduction to the Mellin mean square | (6.24) |
| S11 | truncated divisor model | Lemma 6.5, (6.25)–(6.27) |
| S12 | low Mellin frequencies | (6.28)–(6.29) |
| S13–S14 | high frequencies: factorization, the three polynomials | (6.30)–(6.34) |
| S15 | ordinary times | (6.35) |
| S16 | exceptional count | (6.36) |
| S17 | sparse Gram bound | (6.37) |
| S18 | tuple part at high times | (6.38) |
| S19 | constant part at high times | (6.39)–(6.42) |
| S20 | conclusion | end of §6.6 |

**Markers.** **[PD]** means PD's argument with nothing added. **[new]** means this document
adds content: an explicit rate, an implicit choice made explicit, or a different proof of the
same statement. **[WD]** means the step is taken from WD §5 (or its Lean) in place of PD's
text. Every **[new]** item is listed in §10.

---

## 0. Target and conventions

### 0.1 The statement in Lean terms

Fixed data:

- `q, q₀ ∈ (0,1)`;
- `c₀ > 0`, `C₀`, `vlo > 0`, `vhi`;
- `1/10 < alo ≤ ahi < 1/5`, `K₀ : ℕ`, `CN`;
- `c > 0`, `d ≤ 2`, `B₀`;
- `κ > 1`, `CΨ`, `M : ℕ → ℝ`;
- `A`.

The proof produces `A', C_m` such that, for every `E, κ'`, there is `C*` with the following
property for large `x`. Assume `PrimeTwistBound x A' E C_m κ'` (AP1) and
`IntegerKernelBound x C_m κ'` (AP2). Then for every admissible choice of the varying data,

`|S_raw| ≤ C* L^{-A}`, where
`S_raw = ∑_{1 ≤ w ≤ ⌊κx⌋} Ψ(w/x) w^{-1} F(w) G(w+1) W₁(w) W₁(w+1)`.

The varying data are:

- groups `Sg, Bg` as in PD (6.1);
- `r ≤ K₀ + CN s` disjoint bands with exponents in `[alo, ahi]`;
- slots `u, v` with `u_i ≥ c/T²⁰` and `∑ v_i ≤ 1 − c/T²⁰`;
- `|Bc| ≤ 1`;
- `G = G ∘ stripPrimes`, with `0 ≤ G ≤ L^{B₀}`;
- `Ψ` smooth, supported in `[κ⁻¹, κ]`, with `|Ψ^{(k)}| ≤ M_k T^{CΨ k}`.

The proof never uses `d ≤ 2`; it works for every fixed `d`. In the extraction
(`Erdos408/Extraction/Allocation/TwoSided.lean`) the premises AP1 and AP2 are supplied by
`eventually_primeTwistBound` and `eventually_integerKernelBound` (`Erdos408/Analytic/`).

**Notation.**

- `L = log x`, `T = log L`, `s = log T`, `ε = c/T²⁰`.
- `W₁ = markedWeight univ q₀ P`.
- `𝒲 = markedWeight univ q (band x ∘ a)`.
- `f_B = slotCount x u v Bc` and `C_B = slotMean x u v Bc` (`Erdos408/Extraction/Defs.lean`);
  these are literally the two slot sums of `TwoSidedCorrelation`.
- `F = 𝒲 · (f_B − C_B)` (`centeredCore`, §3.1).
- The spare slot is `Fin.last d`, and `Bc` reads `Fin.init Q`.

**Group encoding.** `TwoSidedCorrelation` indexes groups by the Finsets themselves
(`Sg ∪ Bg : Finset (Finset ℕ)`, weight `id`). `GraphTransference` indexes them by a
`Fintype ι` with `P : ι → Finset ℕ` and `big : Finset ι`. The packages below use the `ι`
encoding. The assembly (§3.4) reindexes once, with `ι = ↥(Sg ∪ Bg)`, `P = Subtype.val` and
`big = univ.filter (·.1 ∈ Bg)`.

For a group `g`:

- `V_g = harmonicMass (P g)`;
- `ω_g(n) = primeCount (P g) n`;
- `ω_P = groupPrimeCount P`;
- `s_P = card ι`;
- `μ_g(p) = 1/(V_g p)`.

**Thresholds.** "Eventually" means for `x ≥ x₀`. Here `x₀` may depend on the fixed data and on
every constant introduced *before* the statement in which it appears (in particular on `E, κ'`
in package E). It never depends on the varying data. Every lemma below is uniform in the
varying data.

### 0.2 The proof in one paragraph

**Package G** (S0–S4) applies `hG` to endpoint vectors built from `F` and `G`. It inserts
`Ψ(n/(xD))/n` by Mellin inversion, sums dyads, and strips the shared labels. The result is that
the raw sum plus the signed stripped comparison correlations is `O(L^{-A})`.

**Package C** (S5–S10) bounds each stripped comparison correlation by `L^{-A''}`. It proceeds
by:

- a second Mellin separation and a partition of unity;
- a bilinear multiplier on the free products and the minor arcs;
- Parseval;
- reduction of each major arc to the Mellin mean square (6.24) through the local Mellin
  energy lemma.

**Package E** (S11–S19) proves (6.24) from AP1 and AP2:

- Lemma 6.5 at low frequencies, with exact cancellation of `f_B` against `C_B`;
- at high frequencies, one small-prime factor and the Matomäki–Radziwiłł split;
- the spare-slot prime polynomial (AP1) on the exceptional set, with the sparse Gram bound
  (AP2);
- the constant part through pointwise progression bounds.

Subtracting C from G proves the theorem.

---

## 1. Parameters and their order

### 1.1 Named constants

PD fixes these only by order. The values below are those of the Lean proof; "dep." lists
everything a constant depends on. Constants given by an existential lemma are named by that
lemma.

**Package G** (`Graph/Insertion.lean`, `Graph/Restore.lean`).

| Name | Value | dep. | Role |
|---|---|---|---|
| `C_f, K_Ψ` | `exists_mellinCutoff` (§4.2) | `κ, CΨ, M` | cutoff `L^{C_f}`; `∫|a| ≤ L^{K_Ψ}` |
| `C₃` | `max(B₀, 0) + 1` | `B₀` | endpoint norm exponent (G1) |
| `C₄` | `C_f + 3` | `C_f` | frequency range `|ζ| = 2π|ξ| ≤ L^{C₄}` |
| `E_G` | `A + 2C₃ + K_Ψ + 2` | `A, B₀, K_Ψ` | transfer saving (S0) |
| `m₀, J, C₁, C_gr` | `hG q₀ c₀ C₀ vlo vhi E_G C₃ C₄` | the above | the graph family |
| `C_abs` | `exists_norm_patternPairing_le` (G2a) | `J` | absolute pattern bound |
| `A_t` | `|A| + |C₁| + |C_abs| + 4` | | Mellin tail precision in S2 |
| `C_r` | G5 | `J, m₀` | stripping error `L^{C_r} e^{-L^{0.27}}` |
| `A''` | `A + max(C₁, 0)` | `A, C₁` | per-comparison saving |

**Package C** (`Comparison.lean`, `Comparison/`).

| Name | Value | dep. | Role |
|---|---|---|---|
| `ψ_{1,m}, y_m, M₁` | `exists_partition` (§5.1) | `κ` | partition pieces, derivative bounds |
| `C_W` | U9 | `m₀, q₀, vlo, C₀` | `|W^b_S| ≤ L^{C_W}` |
| `C₅` | `exists_norm_comparisonBilinear_le` | `B₀, C_W, M₁(0)` | `|Y⁻¹ 𝔅| ≤ L^{C₅}` (6.19) |
| `C_A, C_V` | `2C_W + 3`, `2B₀ + 2C_W + 1` | | energies `Y L^{C_A}`, `Y L^{C_V}` (6.19) |
| `C₇` | `2m₀C₀ log γ`, `γ = max(1, m₀) max(1, vlo⁻¹)` | `m₀` | atoms `ρ(n) ≤ L^{C₇}/n` (C1) |
| `A_m` | `A'' + K_Ψ` | | minor-arc saving |
| `C_arc` | C2 at `(max(C₇,1), 0.38, A_m')` | `A_m', C₇` | arc exponent (PD's `C₆`) |
| `A_m'` | `|A_m| + |C_A| + |C_V| + 1` | | saving asked of C2 |
| `C_cost` | `2C_arc + C_V/2` | | cost of the arcs |
| `C_m` | `max(C_arc, C_f + 3)` | | **premise modulus exponent**; also `|σ| ≤ L^{C_m}` |
| `A_SM` | `2(A'' + K_Ψ + C_cost)` | | Mellin mean-square target (6.24), `A₀` of package E |

The decay order `j` of Lemma 6.4 is chosen from the tail precision `A_e = A_m + C_cost`
(`j − 4 ≥ C_A + 2A_e + 2`), and the Mellin tail of the separation has precision
`|A''| + |C₅| + 1`.

**Package E** (`Endpoint.lean`, `Endpoint/`), with `A₀ = A_SM`.

| Name | Value | dep. | Role |
|---|---|---|---|
| `C_U` | `C_W + d + 2` | `m₀, d` | `|c(u)| ≤ L^{C_U}`, tuple coefficient |
| `C_sep, K₁` | `exists_mellin_piece` (E6) | `M₁` | separation of `ψ₁(p_s p_l u/Y)` |
| `D` | `6C_m + 2K₁ + 2C_U + 11` | | total cost of the tuple part |
| `A_s` | `max((A₀ + D)/2, 1)` | | small-prime threshold (S15) |
| **`A'`** | `(A₀ + D − 1)/2` | | **premise precision of AP1** |
| `B_min` | `max(C_m, C_sep) + 2` | | tuple frequency floor |
| `C₈` | `2|C₀||vhi| + 2` | `C₀, vhi` | divisor-model mass (E1) |
| `B_con` | `exists_integral_const_high_le` | `A₀, d, C_W, C_m, C₈` | constant-part floor |
| `B'` | `max(B_min, B_con) + |E|` | **`E`** | low/high frequency split |
| `N` | `⌈A₀ + B' + 2⌉` | `B'` | divisor-model precision in S12 |

### 1.2 Order of choice

The order is that of PD S0, extended. It matches the Lean quantifiers
`∃ A' C_m, ∀ E κ', ∃ C*, ∀ᶠ x`:

1. Fixed data, then `A`.
2. Package G: `C_f, K_Ψ`, then `C₃, C₄, E_G`, then `hG` gives `m₀, J, C₁, C_gr` (existentials
   of a Prop, destructured before `A'` is produced), then `C_abs`, `A_t`, `C_r`. G's output is
   `m₀, J, C₁, C_G`.
3. Package C at `(m₀, A'')`: the partition, `C₅`, `C_arc, C_cost`, then `C_m` and `A_SM`.
4. Package E at `(m₀, C_m, A_SM, M₁)`: `C_U, C_sep, K₁, D, A_s`, then `A'`, `B_min`, `B_con`.
   **`(A', C_m)` is the witness.**
5. `∀ E κ'`: `B'`, then `N`, then every remaining `x`-threshold and `C*`.

### 1.3 `A'` and `C_m` do not depend on `E`

The "dep." columns are the proof:

- `C_m = max(C_arc, C_f + 3)`.
  - `C_arc` depends on `C₇` and `A_m' = |A_m| + |C_A| + |C_V| + 1`.
  - `A_m = A'' + K_Ψ`, and `C_A, C_V` depend on `B₀, C_W`.
  - `A'' = A + max(C₁, 0)`, and `C₁` comes from `hG`.
- `A' = (A_SM + D − 1)/2` depends on:
  - `A_SM = 2(A'' + K_Ψ + C_cost)`;
  - `D = 6C_m + 2K₁ + 2C_U + 11`, with `K₁` from the fixed partition pieces and `C_U` from
    `m₀, d`.

None of these involves `E` or `κ'`. Step by step through S13–S19:

- **S13.** The separation frequency `C_sep` and its cost `K₁` come from the fixed pieces. The
  moduli and twists are `≤ L^{C_m}`, and the number of boxes, classes and characters is
  `≤ 64 L^{3C_m + 3}`. None of this depends on `B'`. `E` enters only through
  `B' ≥ E + B_min`, which makes every shifted time `t' = t + σ + 2πξ` with `|t| ≥ L^{B'}`
  satisfy `|t'| ≥ L^E`, as AP1 requires.
- **S15.** The ordinary-time bound is `L^{-2A_s} L^{2C_U + 5}` (E7), with no `B'`.
- **S16.** `#𝒥 ≤ exp(L^{0.95})` eventually. The threshold depends on `A_s`, not on `B'`.
- **S17.** `∑_{𝒥} sup|R|² ≤ 9(1 + |κ'|) L^{2C_U + 4}`. `κ'` enters the constant only. The
  shifts change the time variable, not the coefficient norms of `R`.
- **S18.** On the exceptional set one box contributes
  `(2/vlo)² · 4(4κ' L^{-A'})² · 9(1 + |κ'|) L^{2C_U + 4}`. After
  the costs of the boxes, characters and separation, the saving `L^{-A_SM}` needs only `A'` as
  tabled, independent of `B'`.
- **S19.**
  - The medium range needs `B' ≥ B_con`, a *lower* bound that the max supplies.
  - The model error needs `N` after `B'`.
  - The high range has an absolute saving `x^{-1/150}`.
  - None of these feeds `A'` or `C_m`.
- **S12.** The low range `|t| ≤ L^{B'}` needs `N ≥ A₀ + B' + 2`. `N` is the precision of
  Lemma 6.5, which holds for every `N` with an `N`-dependent threshold. So `N` may depend on
  `E`; `A'` does not.

This is why `TwoSidedCorrelation` quantifies the AP1 threshold `E` universally.

---

## 2. Uniform facts (Setup)

All of these hold eventually and uniformly in the varying data. The `[ε]` items are the O2
rates (§7.1). `Erdos408/TwoSided/Setup.lean` holds R1, the crude forms of U7 and U9 and U8 in
algebraic form; the other facts are proved where they are used.

- **U1. Groups.**
  - Small-group primes lie in `[e^{L^{.27}}, e^{L^{.36}}]`, big-group primes in
    `[e^{L^{.39}}, e^{L^{.46}}]`.
  - `s_P ≤ 2C₀T`, and `#small ≥ c₀T ≥ 1`.
  - `sup_g sup_p μ_g(p) ≤ e^{-L^{.27}}/vlo`, and
    `∑_g ∑_{p ∈ P_g} p^{-2} ≤ 2C₀T e^{-L^{.27}}`.
  - [PD (6.1)]
- **U2. Bands.**
  - Band primes lie in `[e^{L^{0.1}}, e^{2L^{0.2}}]`.
  - `1/2 ≤ V_i ≤ 1`, uniformly in `a ≥ alo` (`OneSided.eventually_harmonicMass_band`,
    `Erdos408/OneSided/Bands.lean`).
  - `e^r ≤ e^{K₀} T^{max(CN,0)} ≤ L^{1/10}`.
  - [new: X5]
- **U3. Disjointness and order** (`eventually_scales`, `Endpoint/Factor/Identity.lean`).
  - Every band prime is below every active prime, since `2L^{.2} < L^{.27}`.
  - Every active prime is `≤ x^{ε}/2`, since `L^{.46} < cL/T²⁰ − 1`.
  - Every slot prime exceeds `x^ε`.
  - So bands, active groups and slots are pairwise disjoint, and every active or band prime
    exceeds `L^{C}` for every fixed `C`. In particular, it is a unit mod any `k ≤ L^{C_m}`.
- **U4. Slot geometry.** If `slotTuples x u v ≠ ∅`, then `ε ≤ u_i < v_i` for all `i`, and
  `∏ x^{v_i} ≤ x^{1−ε}`. So every `v_i ≤ 1 − ε − d·ε`. If it is empty, then `f_B = C_B = 0`
  and every package is trivial.
- **U5 [ε]. Tuple count.** `|f_B(n)| ≤ (2T²⁰/c)^{d+1}` for `1 ≤ n ≤ x²`
  (`Sieve.abs_slotCount_le`, `Erdos408/Extraction/Sieve/Basic.lean`, with `ε = c/T²⁰`).
- **U6 [ε]. Harmonic constant.**
  `|C_B| ≤ C_x ≤ (∑_{p ≤ x} 1/p)^{d+1} ≤ (T + E₀)^{d+1}` (`Sieve.sum_inv_slotTuples_le`),
  with the crude forms `|C_B| ≤ (1 + L)^{d+1}` (`Endpoint/Factor/Bounds.lean`) and
  `|C_B/V| ≤ L^{d+3}` (`Endpoint/Constant/Bounds.lean`).
- **U7. Inert weight.**
  - `0 ≤ 𝒲 ≤ (2/(1−q))^r ≤ L` (`markedWeight_bands_le`, `eventually_markedWeight_band_le`).
  - Hence `|F(n)| ≤ L` for `1 ≤ n ≤ x³` (`eventually_abs_centeredCore_le_log`, from U5).
  - Put `N_F := L`, so `|F|/N_F ≤ 1`.
  - [new: X5]
- **U8. Invariance.**
  - For `p` active and any `n`, `F(pn) = F(n)` (`Graph/Restore/Core.lean`):
    - `TypeII.primeCount_prime_mul` for the bands;
    - `TypeII.slotCount_prime_mul` for `f_B`, using `p ≤ x^{u_i}` from U3
      (both in `Erdos408/Extraction/TypeII/Bands.lean`).
  - `G(pn) = G(n)`, since `stripPrimes(pn) = stripPrimes(n)`.
  - For `p` a slot prime, `𝒲(pn) = 𝒲(n)` and `W^b_S(pn) = W^b_S(n)` (`markedWeight_congr`,
    `markedListWeight_congr`).
  - For `p` an active prime outside the slots of `𝒜_B` (always, by U3),
    `𝒜_B(pn) = 𝒜_B(n)`.
- **U9. Marked weights.** For `S g` of size `t_g ≤ m₀ + 1` and `|b| ≤ 1`,
  `|W^b_S(n)| ≤ K^{s_P} ≤ L^{C_W}` [PD (6.3); WD (5.2)] (`exists_norm_markedListWeight_le_pow`,
  `exists_norm_markedListWeight_le_rpow`, from the list count `card_slotLists_le`).
- **U10. Edge sizes.**
  - In any comparison pattern, `exp(L^{0.39}) ≤ D_C ≤ exp(L^{0.465})`
    (`eventually_slotProduct_le`, `Comparison/ArcsLabels.lean`), and `κ D_C ≤ x`.
  - In any pattern, `D ≤ e^{L^{.46} · J · 2C₀T} ≤ e^{L^{.47}}`.
  - Every factor `n_*`, `D_R` of a position `≤ x²` is of course `≤ x²`.
- **U11. Prime-factor counts.** `ω(n) ≤ log₂ n`; in particular `ω(n) ≤ 4L` for `n ≤ x²`
  (`card_primeFactors_le_four_mul_log`).

**R1. Reindexing (assembly).** For `ι = ↥(Sg ∪ Bg)` (`Setup.lean`):

- `markedWeight (Sg ∪ Bg) q₀ id = markedWeight univ q₀ Subtype.val` (`markedWeight_coe_sort`);
- `stripPrimes ((Sg ∪ Bg).biUnion id) = stripPrimes (univ.biUnion Subtype.val)`
  (`biUnion_coe_sort`);
- the (6.1) hypotheses of `TwoSidedCorrelation` imply `GroupAdmissible` (§3.1), with
  `(univ \ big).card = Sg.card` by `Disjoint Sg Bg` (`groupAdmissible_coe_sort`).

---

## 3. The interfaces

Namespace `Erdos408.TwoSided`, files under `Erdos408/TwoSided/`. These are ordinary
(non-`module`) files, because they import vendored modules.

### 3.1 Definitions (`Defs.lean`)

These definitions are internal to the proof; only the statements in `Erdos408/Hypotheses.lean`
are trusted.

- `GroupAdmissible c₀ C₀ vlo vhi x P big`: PD (6.1) for groups indexed by `ι`, the hypotheses
  of `GraphTransference` (disjoint groups, `c₀T ≤ #small, #big ≤ C₀T`,
  `vlo ≤ V_g ≤ vhi`, the small and big windows, big groups are prime intervals).
- `InertAdmissible K₀ CN alo ahi x a`: at most `K₀ + CN s` pairwise disjoint bands with
  exponents in `[alo, ahi]`.
- `CoreAdmissible B₀ x P G`: `G = G ∘ stripPrimes (univ.biUnion P)` and `0 ≤ G ≤ L^{B₀}`.
- `CutoffAdmissible κ CΨ M x Ψ`: `Ψ` smooth (signed), supported in `[κ⁻¹, κ]`, with
  `|Ψ^{(k)}| ≤ M_k T^{CΨ k}`.
- `centeredCore x q a u v Bc = 𝒲 · (f_B − C_B)`, PD (6.4) with the spare slot (X1).
- `twoSidedSum`: the sum of `TwoSidedCorrelation` in the `ι` encoding.
- `unsharedSlots C g = {Fin.last J} ∪ castSucc '' C g`: the unshared slots of group `g` after
  stripping, its free slots and the final one.
- `slotLists P S n`: the represented lists at `n` (PD (6.2)): in each slot of `S g` a prime of
  `P g` dividing `n`, distinct within the group, and `1` in every other slot.
- `markedListWeight P q₀ S b n`
  `= q₀^{ω_P(n) − ∑_g |S g|} ∏_g V_g^{-|S g|} ∑_{p ∈ slotLists P S n} b(p)`, the weight
  `W_t^b(n)` of PD (6.2) with `t_g = |S g|` (zero allowed).
- `strippedComparison x q₀ P A B φ φ' ψ ψ' F G Ψ`: the stripped comparison correlation of one
  pattern, PD (6.15). Free labels `a ∈ auxLabels P (A ∪ B)` with law `∏ μ_g`, free products
  `D_A, D_B`, shift `D_C = D_A D_B`, and
  `∑_a ∏μ(a) φ(D_A) φ'(D_B) ∑_{w ≤ x²} Ψ(w/(xD_C))/w · F(w) G(w + D_C)`
  `· W^{ψ'(X_B)}(w) W^{ψ(X_A)}(w + D_C)`,
  with both marked weights over `unsharedSlots (A ∪ B)`; no restrictions between labels.
- `ComparisonPattern m₀ big A B φ φ' ψ ψ' U U'`: one comparison pattern of `GraphTransference`'s
  family (`A g, B g` disjoint, `|A g ∪ B g| ≤ m₀`, empty off the big groups, both nonempty
  somewhere, all tests of modulus `≤ 1`, `φ, φ'` supported in `[U, eU]`, `[U', eU']`).
- `endpointCoeff … C b ψ₁ Y σ w = ψ₁(w/Y) w^{iσ} F(w) W^b_{unsh C}(w)`: the first endpoint of a
  comparison at scale `Y`, PD (6.28).

Remarks on the encoding:

- `slotProduct (A ∪ B) a = slotProduct A a * slotProduct B a` because `A g` and `B g` are
  disjoint.
- In `GraphTransference`, `p h i.castSucc` with `i ∈ A h` is exactly the argument of `ψ`
  (target) and `ψ'` (source).
- The `w`-range `Icc 1 ⌊x²⌋` is harmless: `Ψ(w/(xD_C)) = 0` for `w > κxD_C`, and
  `κ x D_C ≤ x²` eventually, by U10.

### 3.2 Package G (`Graph.lean`)

```lean
theorem eventually_raw_add_comparison_le (hG : GraphTransference)
    (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ)
    (M : ℕ → ℝ) (A : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1)
    (hc₀ : 0 < c₀) (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (_hal : alo ≤ ahi)
    (hahi : ahi < 1 / 5) (hc : 0 < c) (hκ : 1 < κ) :
    ∃ (m₀ J : ℕ) (C₁ CG : ℝ), ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∃ (N : ℕ) (Aν Bν : Fin N → ι → Finset (Fin J)) (β : Fin N → ℂ)
          (φ φ' ψ ψ' : Fin N → ℕ → ℂ) (U U' : Fin N → ℝ),
          (∀ ν, ComparisonPattern m₀ big (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν) (U ν)
            (U' ν)) ∧
          ∑ ν, ‖β ν‖ ≤ Real.log x ^ C₁ ∧
          ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
            (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
            InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
            (∀ Q, |Bc Q| ≤ 1) → CoreAdmissible B₀ x P G → CutoffAdmissible κ CΨ M x Ψ →
            ‖(twoSidedSum x q q₀ κ a u v Bc P G Ψ : ℂ) +
                ∑ ν, β ν * strippedComparison x q₀ P (Aν ν) (Bν ν) (φ ν) (φ' ν) (ψ ν) (ψ' ν)
                  (centeredCore x q a u v Bc) G Ψ‖ ≤
              CG * Real.log x ^ (-A)
```

### 3.3 Packages C and E (`Comparison.lean`, `Endpoint.lean`)

```lean
theorem exists_comparison_bound
    (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (B₀ κ CΨ : ℝ) (M : ℕ → ℝ)
    (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hc₀ : 0 < c₀)
    (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c)
    (hκ : 1 < κ) (m₀ : ℕ) (A'' : ℝ) :
    ∃ A' Cm : ℝ, ∀ E κ' : ℝ, ∃ CC : ℝ, ∀ᶠ x : ℝ in atTop,
      PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ)
          (G : ℕ → ℝ) (Ψ : ℝ → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
          CoreAdmissible B₀ x P G → CutoffAdmissible κ CΨ M x Ψ →
          ∀ (J : ℕ) (Aν Bν : ι → Finset (Fin J)) (φ φ' ψ ψ' : ℕ → ℂ) (U U' : ℝ),
            ComparisonPattern m₀ big Aν Bν φ φ' ψ ψ' U U' →
            ‖strippedComparison x q₀ P Aν Bν φ φ' ψ ψ' (centeredCore x q a u v Bc) G Ψ‖ ≤
              CC * Real.log x ^ (-A'')

theorem exists_endpoint_meanSquare
    (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ) (d : ℕ)
    (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hc₀ : 0 < c₀)
    (hvlo : 0 < vlo) (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c)
    (m₀ : ℕ) (Cm A₀ : ℝ) (M₁ : ℕ → ℝ) :
    ∃ A' : ℝ, ∀ E κ' : ℝ, ∃ CE : ℝ, ∀ᶠ x : ℝ in atTop,
      PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big →
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
        ∀ (J : ℕ) (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ),
          (∀ g, (C g).card ≤ m₀) → (∀ g ∉ big, C g = ∅) → (∀ p, ‖b p‖ ≤ 1) →
          (∀ p p', (∀ g ∈ big, p g = p' g) → b p = b p') →
        ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
          (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) → (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
        ∀ (Y σ : ℝ) (k : ℕ) (h : ℤ),
          x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y →
          Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
          |σ| ≤ Real.log x ^ Cm → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
          ∫ t in -(x * Real.log x ^ (Cm + 2))..(x * Real.log x ^ (Cm + 2)),
              ‖(Y : ℂ)⁻¹ * ∑ w ∈ Finset.Icc ⌈Y⌉₊ ⌊2 * Y⌋₊,
                  endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w *
                    Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) *
                    (w : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
            CE * Real.log x ^ (-A₀)
```

`T₀ := x L^{C_m+2}` is PD's `T₀ = xL^{C₆+1}` with one spare power for the constants `κ e²` of
the partition pieces. Package C calls E with `(m₀, C_m, A_SM, M₁)`, where `M₁` is the fixed
derivative bound of the partition pieces of §5.1. C's witness `A'` is E's, and C's `Cm` is
`C_m = max(C_arc, C_f + 3)`.

### 3.4 Assembly (`Erdos408/TwoSided.lean`)

`twoSidedCorrelation_of_graphTransference` obtains `m₀, J, C₁, C_G` from G, then `A', C_m`
from C at `(m₀, A'')` with `A'' = A + max(C₁, 0)`, and returns `(A', C_m)`. For given `E, κ'`
it takes `C* = |C_G| + |C_C|`. For large `x` it reindexes the groups by R1, applies G to get
the family, applies C to each pattern, and concludes

`|raw| ≤ ‖raw + ∑_ν β_ν cmp_ν‖ + ∑_ν ‖β_ν‖ · C_C L^{-A''} ≤ (|C_G| + |C_C|) L^{-A}`,

using `∑_ν ‖β_ν‖ ≤ L^{C₁}` and `L^{C₁} L^{-A''} ≤ L^{-A}` for `L ≥ 1`. The bound `d ≤ 2` is
unused.

---

## 4. Package G: graph reduction (PD §§6.1–6.2, S0–S4)

### 4.1 S1. Endpoint vectors and norms [PD §6.2, (6.12); new in form: clipped core]

`Graph/Endpoint.lean`, with the list counts in `Graph/BoundsLists.lean`.

Fix a dyad `X = 2^m` with `√x ≤ X ≤ x²`, `S_X = [X, 2X)`, `S'_X = [X, 3X)`, and `ξ ∈ ℝ`. Put
`M = J + 1` and `h(n) = √q₀ ^ (ω_P(n) − M s_P)` (ℕ subtraction, as in `patternPairing`).
Define

- `f_{X,ξ}(n) = conj(N_F⁻¹ F(n) (n/x)^{2πiξ} (X/n) h(n)) · 1[n ∈ S_X]`;
- `g_X(n') = G(n') h(n') · 1[n' ∈ S'_X]`.

**Lemma G1 (endpoint bounds)** (`eventually_endpoint_bounds`). Eventually:

- `‖f_{X,ξ}‖ ≤ 1` pointwise;
- `physicalNormSq P M S_X f ≤ 2X`;
- `physicalNormSq P M S'_X g_X ≤ X L^{2C₃}`, with `C₃ = max(B₀, 0) + 1`.

The exponent `C₃` does not depend on `J` or `m₀`.

*Proof.* `‖f‖ ≤ 1` follows from the crude U7 `|F| ≤ L = N_F`, `X/n ≤ 1` and `h ≤ 1`. For the
norm, `#physicalLists(n) = ∑_p 1[p ∈ physicalLists(n)]`, and `p ∈ physicalLists(n)` implies
`Π(p) | n`, where `Π(p)` is the squarefree product of the labels of `p`. So over an interval of
length `Y + 1`,

`∑_n #lists(n) ∏V^{-M} ≤ ∏V^{-M} ∑_{p injective per group} (Y/Π(p) + 2) = Y + 2 ∏_g (|P_g|/V_g)^M`.

The first part is (6.12). The list count is `exp(O(J T L^{.46})) ≤ √x/2`. The same argument
with `|g| ≤ L^{B₀}` and `|S'_X| ≤ 3X` gives the third bound.

The clipped core makes PD's divisor moments unnecessary (X4).

### 4.2 S2. Mellin insertion, dyads and transference [PD §6.2, (6.13); WD §5.2; X6]

`Graph/Insertion.lean`, `Graph/Insertion/Identity.lean`, `Graph/Insertion/MellinAdapter.lean`.

**Mellin cutoff (X6) [WD]** (`exists_mellinCutoff`). The vendored `tf/P5Mellin/MellinCutoff.lean`
`mellinCutoffTask_proof`, applied to `tf/Classical/FourierSeparation.lean`
`blueprint_lem_fourier_separation`, at `C = 1`, `lo = κ⁻¹`, `hi = κ` and
`bounds j = max (M j) 0`, to `(Ψ : ℝ → ℂ)`. Its hypothesis `CutoffBound x 1 κ⁻¹ κ Ψ bounds`
holds eventually, uniformly in `j`: for `T ≥ 1`, `T^{CΨ j} ≤ L^{j+1}` as soon as
`max(CΨ,0) log T ≤ T`. The densities on `Fin 1 → ℝ` are transported to `ℝ` along
`t ↦ (fun _ => t)`.

It gives `C_f, K_Ψ` and, for every `A_t`, a `K_A` such that eventually there is `a : ℝ → ℂ`
with:

- `∫ ‖a‖ ≤ L^{K_Ψ}`;
- `Ψ(y) = ∫ a(ξ) y^{2πiξ} dξ` for `y > 0`;
- `∫_{|ξ| > L^{C_f}} ‖a‖ ≤ K_A L^{-A_t}`.

**The cutoff exponent `C_f` is fixed before the saving `A_t`.** This is PD's remark after
(6.13) that the differentiation order can be chosen after the family is fixed, and WD's in
§5.2. The `T^{O(r)}` derivative growth is absorbed by the `L^{C(j+1)}` form. This closes X6 for
S2.

**Lemma G2 (insertion identity, exact)** (`eventually_cutoffPairing_eq`). For a pattern
`(C, K) ∈ {(∅, 1)} ∪ {(A_ν ∪ B_ν, K_ν)}`, let `Π_C^Ψ` (`cutoffPairing`) be the pattern pairing
with `f` replaced by `Ψ(n/(xD)) F(n) h(n)/n`, the target endpoint `G(n') h(n')` and `ζ = 0`.
Then, eventually,

`Π_raw^Ψ + ∑_ν Π_ν^Ψ`
`= N_F ∑_{X dyadic} X⁻¹ ∫ a(ξ) (⟨f_{X,ξ}, 𝒜_raw g_X⟩ + ∑_ν ⟨f_{X,ξ}, 𝒜_ν g_X⟩) dξ`

at `ζ = −2πξ`, with `N_F = L`.

*Proof* (`Graph/Insertion/Identity.lean`).

- Every nonzero term has `n ∈ [x/κ, x²]`, since `1 ≤ D ≤ x/κ` (U10); the dyads `[X, 2X)`
  partition this range.
- For `n ∈ S_X`, every target `n + D` of a nonzero term lies in `S'_X`.
- Exchange the finite sums with the integral against the integrable density, then apply
  Mellin inversion at `y = n/(xD)`, using `(n/x)^{2πiξ} D^{−2πiξ} = (n/(xD))^{2πiξ}`.

**Lemma G2a (absolute pattern bound) [new: replaces WD Lemma 3.4]** (`Graph/Absolute.lean`,
`exists_norm_patternPairing_le`; the generic bound `GraphBounds.norm_patternPairing_le` in
`Graph/BoundsDamping.lean`). Eventually, for every `X`, `ξ` and pattern,
`‖patternPairing P q₀ C K ζ S_X f g_X‖ ≤ sup‖K‖ · X L^{C_abs}`.

*Proof.* Bound all factors absolutely, keeping each damping with its list sum:

- `‖f‖ ≤ 1`, `‖g‖ ≤ L^{B₀}`, and the auxiliary labels have mass exactly 1 (`sum_labelMass`).
- `sup_z z^M q₀^{z/2} < ∞`, so `#lists(n) q₀^{(ω(n) − Ms)₊/2} ≤ c(M, q₀)^{s_P}` at both
  endpoints. This is PD's display after Proposition 6.2.
- `|S_X| ≤ X`.

Since `s_P ≤ 2C₀T`, the product is `L^{O_{J,m₀}(1)}`. `C_abs` may depend on `J`: it is used
only in the tail, whose precision `A_t` is chosen after `J`. WD's Lemma 3.4 gives a `J`-free
bound, which is not needed here.

**Lemma G3 (residual pairing)** (`eventually_norm_cutoffPairing_family_le`). With `m₀, J, C₁`
from `hG` at `(E_G, C₃, C₄)`, eventually `|Π^Ψ_raw + ∑_ν Π^Ψ_ν| ≤ C_res L^{-A}`.

*Proof.* By G2, split each `ξ`-integral at `|ξ| = L^{C_f}`.

- **Inner part.** Here `|ζ| = 2π|ξ| ≤ L^{C₄}`, and G1 supplies the norm hypotheses. `hG`
  bounds the integrand of the sum of all patterns by `C_gr X L^{-E_G + 2C₃}`. Integrating
  against `|a|` costs `L^{K_Ψ}`, `X⁻¹` cancels `X`, there are at most `4L` dyads, and
  `N_F = L`. With `E_G = A + 2C₃ + K_Ψ + 2` this is `O(L^{-A})`.
- **Tail.** By G2a and `∑|β| ≤ L^{C₁}`, the tail is
  `≤ 4L · N_F · K_A L^{-A_t} · (1 + L^{C₁}) L^{C_abs}`, which is `O(L^{-A})` at
  `A_t = |A| + |C₁| + |C_abs| + 4`.

**The family.** It is the one supplied by `hG` for the given `P, big`. Its properties are
exactly `∀ ν, ComparisonPattern …` and `∑ ‖β‖ ≤ L^{C₁}`. In the proof of `GraphTransference`
(`Erdos408/Graph.lean`), the weight bound comes from the pattern mass of WD's residual family
(`patternMass`): the weights sum to at most `ξ⁻² Q⁴` times it.

### 4.3 S3. Stripping shared labels [PD §6.2, (6.14)–(6.15); WD §5.2]

`Graph/Restore/Strip.lean`, `Graph/Restore/Clean.lean`, `Graph/Restore/Patterns.lean`.

For a pattern with free sets `C g` (`C g = ∅` for raw), the **shared slots** of group `g` are
`Sh_g = {i.castSucc : i ∉ C g}`, which has `J − |C g|` elements. The unshared slots are
`unsharedSlots C g`. Write a source list `p ∈ physicalLists P M n` as a pair:

- the shared labels `s ∈ auxLabels P (sharedSlots C)`: `p` on the shared slots, `1` in the
  free slots;
- the unshared part `l ∈ unsharedLists P C`: `p` on the unshared slots, `1` in the shared
  ones.

`merge C s l` recombines them. Here `D_R(s) = ∏_{g, i ∈ Sh_g} s g i` and `D = D_R · D_C`, where
`D_C = slotProduct C a`.

**Lemma G4 (stripping bijection, exact)** (`Restore.physSum_eq_sum_strip`). `merge` is a
bijection from shared labels and unshared parts onto all lists (`sum_allLists_eq`). Under it,
for `n ≥ 1`, the source lists at `n` correspond to the triples `(s, w = n/D_R(s), l)` with:

- `s` injective per group on `Sh_g`, with values in `P_g`;
- `D_R(s) | n`;
- `l ∈ slotLists P (unsharedSlots C) w`, with `l` disjoint from `s` groupwise.

The target lists `p'` with shared part `s` correspond in the same way to
`l' ∈ slotLists P (unsharedSlots C) (w + D_C)` disjoint from `s`, since `n + D = D_R(w + D_C)`.
So the cutoff pairing becomes a sum over `(a, s, l, l', w)`.

*Proof.* The labels are distinct primes in disjoint groups, so `D_R(s) | n` if and only if
every label divides `n`. A label of `l` divides `n` but not `D_R`, hence divides `w`.

**The clean summands** (`physTerm_eq_stripTerm`, `stripSum_eq_sum`). Call `(a, s, w)` *clean*
if the shared labels are distinct and divide neither `w` nor `w + D_C`, and the free labels
avoid the shared labels and do not divide `w`. At a clean `(a, s, w)` the summand of the
cutoff pairing equals the summand of the stripped correlation (`stripSum`):

- the physical conditions at `n = D_R w` are the represented-list conditions at `w` and
  `w + D_C` (`physCond_merge_iff`);
- (6.14), damping: `ω(D_R w) = ∑_g |Sh_g| + ω(w)`;
- (6.14), mass: the mass of the source lists splits as `∏ μ(s) · D_R · ∏ V^{-t}`;
- invariance: `F(D_R w) = F(w)` and `G(D_R w') = G(w')` (U8);
- cutoff: `Ψ(n/(xD))/n = D_R⁻¹ Ψ(w/(xD_C))/w`.

**The two kinds of pattern** (`Graph/Restore/Patterns.lean`).

- For the raw pattern (`C = ∅`, `K = 1`, `D_C = 1`, `t_g = 1`), `stripSum` is exactly
  `twoSidedSum` (`stripSum_raw_eq`). This uses `W₁ = markedListWeight P q₀ (unsharedSlots ∅) 1`
  (lists of one prime per group: `∑_ℓ 1 = ∏ ω_g`), and that the cutoff support `w ≤ κx` lies
  below `x²`.
- For a comparison pattern, `stripSum` is `β` times `strippedComparison`
  (`stripSum_comparison_eq`): the kernel factors as `β φ(D_A) φ'(D_B) ψ'(X_B) ψ(X_A)`, and it
  depends only on the unshared parts of the lists.

### 4.4 S4. Restoring the suppressed restrictions [PD §6.2, (6.16); WD §5.2]

`Graph/Restore.lean`, `Graph/Restore/General.lean`, `Graph/Restore/Bound.lean`,
`Graph/Restore/Mass.lean`, `Graph/Restore/Eventually.lean`, `Graph/Restore/Core.lean`.

**Lemma G5.** For every `m₀, J` there is `C_r` such that, eventually, for every comparison
pattern, `|Π^Ψ_ν − β_ν · strippedComparison_ν| ≤ ‖β_ν‖ L^{C_r} e^{-L^{.27}}`
(`exists_norm_cutoffPairing_sub_le`), and for the raw pattern
`|Π^Ψ_raw − twoSidedSum| ≤ L^{C_r} e^{-L^{.27}}` (`exists_norm_cutoffPairing_raw_sub_le`).
Both are the general pattern case `Restore.exists_eventually_norm_physSum_sub_stripSum_le`.

*Proof.* The explicit inequality is `norm_physSum_sub_stripSum_le`.

- **Absolute summand** (`Graph/Restore/Bound.lean`). In every case, collision or not, the
  summands at `(a, s, w)`, summed over `l, l'`, are at most
  `μ(s) μ(a) V_t² κ_K M₀ L_F L_G Λ(n) Λ(n') / w`, where `V_t = ∏_g V_g^{-t_g}` and
  `Λ(n) = q₀^{ω(n) − Ms} #lists(n)` keeps each damping with its list count.
- **Sizes** (`Graph/Restore/Eventually.lean`). `Λ(n) ≤ (q₀^{-M} c_q)^{s_P} ≤ L^{O(1)}`, from
  `q₀^z z^t ≤ t!/log(1/q₀)^t` (U9); `V_t ≤ max(1, 1/vlo)^{(m₀+1)s_P} ≤ L^{O(1)}`;
  `ω(n) ≤ log₂ n` (U11), `μ_g(p) ≤ e^{-L^{.27}}/vlo` (U1), `D_R D_C ≤ e^{J s_P L^{.46}}` (U10)
  and `∑_{w ≤ x²} 1/w ≤ 1 + 2L`.
- **The unclean mass** (`sum_mass_not_clean_le`) is a union bound over the suppressed
  restrictions, using the one- and two-slot marginals of the label law
  (`Graph/Restore/Mass.lean`). With `Ω` a bound for the number of prime factors:
  1. two shared labels of a group coincide: `≤ s_P J² sup μ`;
  2. a shared label divides `w(w + D_C)` or equals a free label: `≤ J(2Ω + m₀ s_P) sup μ`;
  3. a free label divides `w` (the label ban, a free label equal to an unshared endpoint
     label, which divides `D_C` and one endpoint, hence both): `≤ m₀ Ω sup μ`.

  The physical injectivity across shared and unshared slots is implied once (2) is excluded.
  With the clipped core every summand is bounded pointwise: no Cauchy, no divisor moments.

**Proof of G** (`Graph.lean`). Combine G3 and G5: with `∑ ‖β‖ ≤ L^{C₁}`, the stripping errors
are below `2L^{-A}` eventually, so
`‖twoSidedSum + ∑ β_ν strippedComparison_ν‖ ≤ C_G L^{-A}`.

---

## 5. Package C: comparison bound (PD §6.3, S5–S10)

Fix a pattern `(A, B, φ, φ', ψ, ψ', U, U')`, and put `C = A ∪ B`, `H' = UU'` and `Y₀ = xH'`.
If no `a` has `φ(D_A)φ'(D_B) ≠ 0`, the correlation is 0. Otherwise, by nonemptiness (U1,
U10), `exp(L^{.39}) ≤ D_C ≤ exp(L^{.465})` and `D_C ∈ [UU', e²UU']`. These are the scales
(6.17).

### 5.1 S5. Separation and endpoint energies [PD §6.3, (6.17)–(6.19); WD §5.3]

`Comparison/Separation.lean`.

1. **Mellin.** Apply S2's density `a` to `Ψ(w/(xD_C))`. For `w` in the support,
   `w/Y₀ ∈ [κ⁻¹, κe²]`, and
   `(w/(x D_C))^{iσ} = x^{-iσ} w^{iσ} D_A^{-iσ} D_B^{-iσ}` with `σ = 2πξ`.
   - Truncate at `|ξ| ≤ L^{C_f}`, so `|σ| ≤ L^{C_m}`.
   - The tail is bounded by the pointwise energy below and the Mellin tail at precision
     `|A''| + |C₅| + 1`.
   - The factors `D^{-iσ}` are unimodular and enter `b₁ = φ D_A^{-iσ}` and
     `b₂ = φ' D_B^{-iσ}`, which keep `|b_i| ≤ 1` and the cell supports.
2. **Partition of unity [new]** (`exists_partition`). There are finitely many fixed smooth
   pieces `ψ_{1,m}` supported in `[1, 2]`, with derivative bounds `M₁`, and points
   `y_m ∈ [(4κ)⁻¹, 2κe²]`, such that `∑_m ψ_{1,m}(z/y_m) = 1/z` for `z ∈ [κ⁻¹, κe²]`.
   Construction: with `a = κ⁻¹`, take `y_m = a/2 + m a/4` for `m < ⌈4κe²/a⌉`, the steps
   `S_m(z) = smoothTransition(4(z − y_m)/a)` and `η_m = S_m − S_{m+1}`, which is supported in
   `[y_m, y_m + a/2] ⊆ [y_m, 2y_m]`. The sum telescopes to `S_0 − S_n = 1` on `[κ⁻¹, κe²]`. Put
   `ψ_{1,m}(z) = η_m(y_m z)/(y_m z)`; the derivative bounds hold by compact support. Package E
   needs the support condition, since the local Mellin energy requires support in `[Y, 2Y]`.
3. **Form (6.18)** (`eventually_strippedComparison_eq`). With `Y_m = y_m Y₀`,
   - `𝒰_m(w) = ψ_{1,m}(w/Y_m) w^{iσ} F(w) W^{ψ'(X_B)}_{unsh C}(w)`, which is
     `endpointCoeff … C (ψ' ∘ X_B) ψ_{1,m} Y_m σ w`;
   - `𝒱(w') = G(w') W^{ψ(X_A)}_{unsh C}(w')`;
   - `𝔅_m = 𝔼_a b₁(D_A) b₂(D_B) ∑_w 𝒰_m(w) 𝒱(w + D_C)` (`comparisonBilinear`).

   Then `strippedComparison = ∫ a(ξ) x^{-iσ} ∑_m y_m Y_m⁻¹ 𝔅_m(σ) dξ`. Every `w ≤ κ x D_C ≤ x²`
   (U10). The test `ψ'(X_B)` uses only big labels, as E requires.
4. **Energies (6.19) [PD; pointwise]** (`exists_norm_comparisonBilinear_le`,
   `Comparison/ArcsCore.lean`). From the crude U7 and U9,
   `∑_{Y ≤ w ≤ 2Y} |𝒰_m|² ≤ Y L^{C_A}` with `C_A = 2C_W + 3`, and
   `∑_{0 ≤ w ≤ 3Y} |𝒱|² ≤ Y L^{C_V}` with `C_V = 2B₀ + 2C_W + 1`. Pointwise,
   `|Y_m⁻¹ 𝔅_m| ≤ L^{C₅}`. No divisor moments are needed (X4).

### 5.2 S6–S7. Bilinear multiplier and minor arcs [PD §6.3, (6.20)–(6.21); WD §5.3]

`Comparison/Multiplier.lean`, `Comparison/ArcsLabels.lean`.

Put `𝔪(θ) = 𝔼_a b₁(D_A) b₂(D_B) e(θ D_A D_B)`. The `A`- and `B`-labels are independent
(disjoint slots, `sum_auxLabels_union`), so `𝔪(θ) = ∑_{n,v} α_n β_v e(θnv)`, where
`α_n = ∑_{a_A : D_A = n} μ(a_A) b₁(n)`.

**Lemma C1 (atoms) [PD (6.20)]** (`eventually_sum_auxLabels_eq_le`). `|α_n| ≤ ρ_A(n) ≤ L^{C₇}/n`.

*Proof.* Each slot holds one of the at most `|A g|` prime factors of `n` in its group, since
each prime lies in one group. So at most `max(1, m₀)^k` labels have product `n`, with
`k = m₀ |ι|`, each of mass at most `max(1, vlo⁻¹)^k / n`; and `|ι| ≤ 2C₀T`.

Hence `∑_{n ∈ [U, 2U]} |α_n|² ≤ L^{2C₇}/U`. Grouping the labels by their products and
splitting `[U, 4U]` into `[U, 2U]` and `(2U, 4U]` writes `𝔪` as at most four box sums
(`norm_sum_bilinear_le`, `bilinearPhase`).

**Lemma C2 (minor arcs) [WD]** (`exists_minorArc_bound`). The vendored
`tf/P5Minor/MinorArcTask.lean` `minorArcTask_proof`, applied to
`tf/S34/OwnedLeafProofs.lean` `integer_bilinear_proof` (WD's `MinorArcTask`): for
`C, δ, A > 0` there are `C_arc, K > 0` such that, eventually, for `exp(L^δ) ≤ U, V` with
`UV ≤ x²`, `0 < |k| ≤ L^C`, integer coefficients on `[U, 2U]` and `[V, 2V]` with
`∑ |a_n|² ≤ L^C/U`, `∑ |b_v|² ≤ L^C/V`, and `θ` at distance `> L^{C_arc}/(UV)` from every
`u/r` with `r ≤ L^{C_arc}`, `|∑_{n,v} a_n b_v e(−kθnv)| ≤ K L^{-A}`.

It is applied with `C = max(C₇, 1)`, `δ = 0.38`, `A = A_m'` and `k = 1` to the coefficients of
C1 on the four boxes (`norm_multiplier_le`). Since `U_iV_j ≥ H'`, "off our arcs of radius
`L^{C_arc}/H'`" implies "off the box's arcs". This replaces PD (6.20)–(6.21) and its Dirichlet
step.

### 5.3 S8. Parseval and arcs [PD §6.3, (6.22); WD §5.3]

`Comparison/ArcsFourier.lean`, `Comparison/ArcsBound.lean`.

The vendored `tf/P5FourierArcProof/FourierArc.lean` `FourierArcTask_proof` supplies:

- the shift identity
  `∫₀¹ star(∑ star(f_n) e(θn)) (∑ g_m e(θm)) ∑_l c_l e(−θD_l) = ∑_l c_l ∑_n f_n g_{n + D_l}`
  (`integral_star_mul_mul_sum`);
- Parseval (`integral_norm_localAdditivePolynomial_sq`);
- the split `‖∫₀¹ star F · G · M‖ ≤ ε √A √B + #centers · √E · √B`.

`exists_norm_sum_shift_le` applies them to an abstract shifted sum with:

- `f = 𝒰_m`, `g = 𝒱`, `M = 𝔪`;
- centres `u/r` with `1 ≤ r ≤ R`, `−R ≤ u ≤ 2R`, `R = ⌊L^{C_arc}⌋`, so `#centers ≤ 4R²`;
- arcs of radius `1/H`, `H = UU'/L^{C_arc}`;
- `ε = 4K' L^{-A_m'}` from C1 and C2, and `A ≤ Y L^{C_A}`, `B ≤ Y L^{C_V}` from (6.19);
- `E` the arc energy of §5.4.

The continuity of `F, G, M` holds: they are finite trigonometric sums (`continuous_dp`).

### 5.4 S9–S10. Local Mellin energy and the tail [PD Lemma 6.4, (6.23)–(6.24); WD §5.5]

`Comparison/ArcsFourier.lean`, `Comparison/ArcsCore.lean`, `Comparison/Arcs.lean`.

**Lemma C3 (= PD Lemma 6.4, with the tail) [WD]**
(`exists_integral_norm_localAdditivePolynomial_le`). From the vendored `tf/P5Energy/Final.lean`
`LocalMellinEnergyTask_proof`, with the weighted tail split off by
`tf/P5MarkedEnergy/Weights.lean` `wj_integral_split` and bounded by
`tf/P5MarkedEnergy/WeightedMean.lean` `weighted_mean_value`. For `j ≥ 4` there is `K > 0` such
that for `10 ≤ Y`, `1 ≤ H ≤ Y/10`, `2Y ≤ T₀H` and coefficients supported in `[Y, 2Y]`, the
energy of `∑ a_n e(θn)` on the arc `|θ − c| ≤ 1/H` is at most

- `K/Y ∫_{-T₀}^{T₀} |∑ a_n e(cn) n^{it}|² dt`,
- plus `K (1 + T₀H/(2Y))^{4−j} (1/H + 2 log 4Y) ∑ |a_n|²`,
- plus `K (H/Y)² ∑ |a_n|²`.

This is PD (6.23) with the tail of (6.24), under the support condition that §5.1 step 2
arranges. The Mellin side is `Y` times the twisted polynomial of (6.24)
(`norm_sum_star_mul_cpow`), with `h = u`, `k = r ≤ L^{C_m}`.

**The arc energy (S10)** (`energy_le`). Let `Ξ₀` bound the mean square (6.24) at every centre,
and let `A_e` be a target precision for the tail. With `H ≥ 1`, `2YL ≤ T₀H` (as
`T₀ = x L^{C_m + 2}` and `Y/H ≤ 4κe² x L^{C_arc}`), `Y ≤ x exp(L^{0.47})`, `H/Y ≤ 4κ/x` and
`j − 4 ≥ C_A + 2A_e + 2`, the energy is `E ≤ K₃ Y (Ξ₀ + 2L^{-2A_e})`: the main term `K₃ Y Ξ₀`,
the weighted tail and the additive term `(H/Y)² A`.

**One bilinear form** (`exists_norm_comparisonBilinear_le_arcs`). Combining §5.2–§5.4,
`|Y⁻¹ 𝔅| ≤ K (L^{-A_m} + L^{C_cost} (√Ξ₀ + L^{-A_e}))` with `C_cost = 2C_arc + C_V/2`. The final
count is `div_le_of_arcs`: from
`𝔅 ≤ ε √(Y L^{C_A}) √(Y L^{C_V}) + 4R² √E √(Y L^{C_V})`,
`𝔅/Y ≤ (4K' + 8√K₃)(L^{-A_m} + L^{2C_arc + C_V/2}(√Ξ₀ + L^{-A_e}))`.

**Proof of C** (`Comparison.lean`). Package E gives `Ξ₀ = C_E L^{-A_SM}` at every centre, and
`A_e = A_m + C_cost`. With `A_SM = 2(A_m + C_cost)`, each `|Y_m⁻¹ 𝔅_m|` is `O(L^{-A_m})` for
`|ξ| ≤ L^{C_f}`. Integrate against `|a|` (cost `L^{K_Ψ}`, and `A_m = A'' + K_Ψ`), sum the fixed
number of pieces, and add the Mellin tail. This is `≤ C_C L^{-A''}`.

---

## 6. Package E: the endpoint mean square (PD §§6.4–6.6, S11–S19)

Fix the data of `exists_endpoint_meanSquare` and write `𝒰(w) = endpointCoeff … w`. The target
is `Ξ := ∫_{|t| ≤ T₀} |Y⁻¹ ∑_w 𝒰(w) e(hw/k) w^{it}|² dt ≤ C_E L^{-A₀}`.

Write `H_m(n) := 𝒲(n) W^b_S(n)` (the marks), with `S = unsharedSlots C`.

**Proof of E** (`Endpoint.lean`). Split `|t| ≤ T₀` at `L^{B'}`, `B' = max(B_min, B_con) + |E|`.
Pick a small group `g_s ∉ big`, which exists since `#small ≥ 1`.

- `|t| ≤ L^{B'}`: Lemma E2 with the divisor model E1 (`exists_integral_lowFrequency_le`).
- `L^{B'} ≤ |t| ≤ T₀`: `𝒰 = 𝒰_tup − 𝒰_con + (𝒰 − 𝒰_tup + 𝒰_con)`. The tuple part uses AP1 and
  AP2 (`exists_integral_tuple_high_le`), the constant part is unconditional
  (`exists_integral_const_high_le`), and the remainder lives on the exceptional positions of
  E3–E4 (`exists_integral_removal_le`).

Each part is `O(L^{-A₀})`.

### 6.1 S11. Lemma 6.5, the truncated divisor model, with `r` inert bands [PD (6.25)–(6.27); X5]

`Endpoint/DivisorModel.lean`, `Endpoint/DivisorModel/Truncation.lean`,
`Endpoint/DivisorModel/Lists.lean`.

**Lemma E1** (`exists_divisorModel`). Fix `m₀`. There is `C₈ = 2|C₀||vhi| + 2` such that for
every `N` there is `C_N` (in fact `C_N = 1`) such that, eventually, uniformly in:

- groups as in (6.1);
- `r ≤ K₀ + CN s` disjoint bands in `[alo, ahi]`;
- `S` with `|S g| ≤ m₀ + 1` (zero allowed);
- `|b| ≤ 1` (no regularity);

there is `A : ℕ → ℂ` with the following properties:

- (a) `A_{d'} ≠ 0` only for squarefree `d'` whose primes lie in the active groups or bands,
  and `d' ≤ exp(2L^{.47})`;
- (b) `∑_{d'} |A_{d'}|/d' ≤ L^{C₈}`;
- (c) for **every** `R ≥ 1`, `∑_{R < n ≤ 2R} |H_m(n) − ∑_{d' | n} A_{d'}|² ≤ C_N R L^{-N}`.

`A` does not depend on `R`. This matters in S12, where one model serves the scales `Y/l` and
`Y`.

*Proof, step by step with `r` bands.* The assembly under explicit size conditions is
`DivModel.divisorModel_of_facts`.

1. **List expansion (exact)** (`DivModel.markedWeight_eq_listForm`,
   `DivModel.markedListWeight_eq_listForm`). For pairwise disjoint bands,
   `𝒲(n) = ∑_{(p_i)_{i<r}, p_i ∈ 𝒬_i, p_i | n} ∏_i V_i⁻¹ · q^{|D(n) \ {p_i}|}`, one prime per
   band, where `D(n)` is the set of band primes dividing `n`; the damping `q^{ω(n) − r}` is
   the product over unrepresented band primes dividing `n`, because the bands are disjoint.
   Likewise `W^b_S(n)` is a sum over the lists `groupLists P S` of distinct primes in the slots
   `S g`, damped by `q₀` off the represented primes. Both are *list forms*
   `H(n) = ∑_j [R_j ⊆ D(n)] c_j ∏_{p ∈ D(n) \ R_j} w_p`, and list forms on disjoint prime sets
   multiply (`DivModel.listForm_mul`). For `r = 0`, `𝒲 = 1`.
2. **Truncation** (`Endpoint/DivisorModel/Truncation.lean`). A list form expands as
   `∑_j [R_j ⊆ D(n)] c_j ∑_{U ⊆ D(n) \ R_j} ∏_{p ∈ U} (w_p − 1)`. Keep `|U| ≤ h₀ = ⌊L^{0.01}⌋`.
   The model (`DivModel.truncModel`) is `∑_{d | n} A_d` with
   `A_d = ∑_j ∑_{U ⊆ Q \ R_j, |U| ≤ h₀, ∏(R_j ∪ U) = d} c_j ∏_{p ∈ U} (w_p − 1)`.
3. **(a) Support.** `d'` has at most `∑_g |S g| + r + h₀ ≤ (m₀+1) 2C₀T + K₀ + CN s + L^{0.01}`
   primes, each `≤ e^{L^{.46}}`. So `log d' ≤ 2L^{.47}`.
4. **(b) Mass** (`DivModel.sum_norm_truncModel_div_le`).
   `∑_d |A_d|/d ≤ (∑_j |c_j|/∏ R_j) ∏_{p ∈ Q} (1 + 1/p)`. The bracket is a product of
   `∏_i (∑_{p ∈ 𝒬_i} 1/(V_i p)) = 1` and `∏_g (∑_{p ∈ P_g} 1/(V_g p))^{|S g|} = 1`
   (repetitions only add). The last factor is
   `≤ exp(∑_g V_g + ∑_i V_i) ≤ exp(2C₀T vhi + r) ≤ L^{2C₀ vhi} L^{1/10}` (U2). **The bands enter
   only through `e^{r} ≤ L^{1/10}`**, which is the whole of X5 here.
5. **Pointwise error** (`DivModel.norm_listForm_sub_le`). For `|w_p − 1| ≤ 1` the error is at
   most `(∑_j [R_j ⊆ D(n)] |c_j|) 4^{|D(n)|} 2^{-h₀}`, where `D(n)` is now the set of group and
   band primes dividing `n`. The normalized list counts `∑_j [R_j ⊆ D(n)] |c_j|` are at most
   `C_x 2^{(m₀+1)|D(n)|}` with `C_x = L^{O(1)}` (the weight sums of both forms,
   `Endpoint/DivisorModel/Lists.lean`). So the squared error is
   `≤ C_x² 4^{-h₀} (4^{m₀+3})^{|D(n)|}`.
6. **(c) Mean square** (`DivModel.sum_pow_card_divs_le`).
   `∑_{n ≤ N} z^{|D(n)|} ≤ N ∏_{p ∈ Q} (1 + (z − 1)/p)`, which is (6.27). At `z = 4^{m₀+3}`,
   `∑_{n ≤ 2R} z^{|D(n)|} ≤ 2R exp((z − 1)(r + s_P vhi)) = 2R L^{O(1)}` (U1, U2). Hence the
   sum is `≤ 2R L^{O(1)} 4^{-⌊L^{.01}⌋} ≤ C_N R L^{-N}`.

### 6.2 S12. Low frequencies `|t| ≤ L^{B'}` [PD §6.4, (6.28)–(6.29); X1, O2]

`Endpoint/Low.lean`, `Endpoint/Low/Facts.lean`, `Endpoint/Low/Model.lean`,
`Endpoint/Low/Progression.lean`.

**Lemma E2** (`exists_norm_lowFrequency_le`). Eventually, for `|t| ≤ L^{B'}` and `τ = t + σ`,

`|Y⁻¹ ∑_w 𝒰(w) e(hw/k) w^{it}| ≤ 6M₁(0) C_N^{1/2} L^{-N/2} (T + E₀)^{d+1} + exp(−cL/(2T²⁰))`.

With `N = ⌈A₀ + B' + 2⌉`, `(T + E₀)^{d+1} ≤ L` and `exp(−cL/(2T²⁰)) ≤ L^{-(A₀ + B')/2}`, the
part of `Ξ` with `|t| ≤ L^{B'}` is `O(L^{-A₀})` (`exists_integral_lowFrequency_le`).

*Proof.*

1. **Tuple term [PD; X1]** (`LowFreq.twistedPoly_eq`). Write
   `f_B(w) H_m(w) = ∑_{Q ∈ slotTuples} Bc(init Q) ∑_{w = l_Q n} H_m(n)`, where `l_Q = ∏ Q_i` is
   squarefree, and `H_m(l_Q n) = H_m(n)` by U8. So the endpoint polynomial is
   `Y⁻¹ (∑_Q Bc(init Q) P_{l_Q} − C_B P_1)`, with the progression sums
   `P_m = ∑_{w ≤ 2Y, m | w} ψ₁(w/Y) w^{iτ} e(hw/k) H_m(w)`.
2. **Model** (`LowFreq.norm_sum_mul_sub_model_le`). Replace `H_m(n)` by `∑_{d | n} A_d` (E1 at
   scale `Y/l_Q` for the tuples, `Y` for the constant). By Cauchy and E1(c), the error is
   `≤ 2√2 M₁(0) C_N^{1/2} L^{-N/2} (∑_Q 1/l_Q + 1)`. U6 gives `∑_Q 1/l_Q ≤ (T + E₀)^{d+1}`.
3. **Progressions (6.29) [PD; new: Lean route]** (`Endpoint/Low/Progression.lean`). For `m`
   coprime to `k` and `f(0) = 0`,
   `∑_{w ≤ N, m | w} f(w) e(hw/k) = κ_{h,k} m⁻¹ ∑_{w ≤ N} f(w)` up to `k` times the total
   variation of `f` (`LowFreq.norm_sum_dvd_twist_sub_le`), where
   `κ_{h,k} = k⁻¹ ∑_{a < k} e(ha/k)` does not depend on `m`. This is the complex form
   `LowFreq.norm_sum_modEq_sub_le` of `Sieve.abs_sum_modEq_sub_le`
   (`Erdos408/Extraction/Sieve/Smooth.lean`), applied class by class. The total variation of
   `w ↦ ψ₁(w/Y) w^{iτ}` on `[1, N]` is at most `N (M₁(1) + |τ| M₁(0)) / Y`
   (`LowFreq.sum_norm_sub_le`). Since `gcd(l_Q d, k) = 1` (U3), each modulus `l_Q d` gives
   the main term `κ_{h,k} (l_Q d)⁻¹ ∑_{w ≤ 2Y} ψ₁(w/Y) w^{iτ}` with error
   `≤ k · 2(M₁(1) + |τ| M₁(0))`.
4. **Summed errors [O2].** `#slotTuples ≤ x^{∑v} ≤ x^{1−ε}` (`Sieve.card_slotTuples_le`), and
   `∑_d |A_d| ≤ e^{2L^{.47}} L^{C₈}`. So the total error, divided by `Y`, is
   `≤ L^{O(1)} e^{2L^{.47}} x^{-ε} ≤ exp(−cL/(2T²⁰))`, using `3L^{0.47} ≤ (c/2) L/T²⁰`. This
   replaces PD's `x^{-ε+o(1)}`.
5. **Cancellation [PD; X1]** (`LowFreq.norm_combine_le`). The tuple main term is
   `∑_Q Bc(init Q)/l_Q · Θ = C_B Θ`, with `Θ = κ_{h,k} ∑_d A_d/d · ∑_{w ≤ 2Y} ψ₁(w/Y) w^{iτ}`.
   It cancels the constant term exactly. This uses that `C_B = slotMean` is literally
   `∑_Q Bc(init Q)/l_Q` over the same `slotTuples`, and that one model serves all scales.
   Since the main terms cancel exactly, the full sum is never compared with an integral.

### 6.3 S13–S15. Factorization and ordinary times [PD §6.5, (6.30)–(6.35); WD §§5.4–5.5; O4, O2]

`Endpoint/Factor.lean`, `Endpoint/Factor/Identity.lean`, `Endpoint/Factor/Bounds.lean`,
`Endpoint/Tuple/Split.lean`, `Endpoint/Tuple/Energy.lean`, `Endpoint/Tuple/Mean.lean`,
`Endpoint/Constant/Boxes.lean`.

**E3. Small-prime removal (6.30) [PD; WD (5.12)]** (`markedListWeight_eq_removal`). For the
small group `g_s ∉ big`, `S g_s = {last}`. If no `p ∈ P_{g_s}` has `p² | w`, then
`W^b_S(w) = V_{g_s}⁻¹ ∑_{p_s ∈ P_{g_s}, p_s | w} W^b_{S'}(w/p_s)`, with `S' = S` except
`S' g_s = ∅`. This holds because `b` ignores small labels.

**E4. Repeated slots (O2) [PD (6.30)].** Replace `f_B` by
`f̃_B(w) = ∑_{Q ∈ ∏ slot primes} Bc(init Q) 1[∏ Q_i | w]` (all tuples, repetitions allowed). A
repeated tuple prime `q` forces `q² | w`, so they differ only on `w` with `q² | w` for a slot
prime `q > x^ε`.

**E3–E4, the exceptional positions** (`exists_integral_removal_le`). By E3–E5 the coefficient
of `𝒰 − 𝒰_tup + 𝒰_con` vanishes except on `w ∈ [Y, 2Y]` with `p_s² | w` (count
`≤ 4Y e^{-L^{.27}} vhi`, U1) or `q² | w` for a slot prime (count `≤ 4Y x^{-ε}`), where it is
`≤ L^{C}` (U7, U9, U11). The mean value theorem over `[−T₀, T₀]` with `T₀/Y ≤ L^{C_m + 2}`
(`FactorAux.integral_norm_twistedPoly_sq_le`, from `OneSided.integral_norm_dirichlet_sq_le`)
bounds its part of `Ξ` by `L^{C_R} (e^{-L^{.27}} + x^{-ε})`, with `x^{-ε} = exp(−cL/T²⁰)`.

**E5. Spare-slot factorization (O4, X1) [new: written out]** (`slotCount_eq_sum_sparePrimes`,
`eventually_endpointCoeff_eq_tuple_sub_const`). With `p_l` ranging over the spare-slot primes
`x^{u_d} < p_l ≤ x^{v_d}`, where `d = Fin.last d`:

- `f̃_B(w) = ∑_{p_l | w} 𝒜_B(w/p_l)`, where
  `𝒜_B(u) = ∑_{Q' ∈ ∏_{i<d} slot primes} Bc(Q') 1[∏ Q' | u]`;
- this is exact, with no injectivity anywhere, because `Bc` reads `Fin.init`.

Combined with E3, off the exceptional positions `𝒰 = 𝒰_tup − 𝒰_con`, where

- `𝒰_tup(w) = ψ₁(w/Y) w^{iσ} V_{g_s}⁻¹ ∑_{p_s p_l u = w} c(u)`, with
  `c(u) = 𝒲(u) W^b_{S'}(u) 𝒜_B(u)` and `|c| ≤ L^{C_U}`, `C_U = C_W + d + 2` (U7, U9 and
  `|𝒜_B(u)| ≤ ω(u)^d`, `Endpoint/Tuple/Mark.lean`). This is (6.31) with `B` and with the spare
  slot as `p_l`.
- `𝒰_con(w) = ψ₁(w/Y) w^{iσ} C_B V_{g_s}⁻¹ ∑_{p_s n = w} c'(n)`, with `c' = 𝒲 W^b_{S'}`.

Both use U8. PD takes `p_l = l_1`. Here the weighted slots are `0..d−1` and the spare is the
last, so the relabeling is `p_l = Q_{Fin.last d}`. Nothing else changes. An empty weighted slot
makes `𝒜_B = 0`; otherwise `v_d ≤ 1 − ε`.

**E6. Characters, dyads and separation (tuple part) [PD (6.32); WD §§5.4–5.5]**
(`Endpoint/Tuple/Split.lean`, `Endpoint/Tuple/Assembly.lean`, `Endpoint/Tuple/Energy.lean`).

- **Dyads and classes.** The twisted polynomial of the tuple part is a sum over
  `w = p_s p_l u` (`twistedSum_eq`). Fix the dyadic boxes `p_s ∈ (2^i, 2^{i+1}]`,
  `p_l ∈ (2^j, 2^{j+1}]`, `u ∈ (2^l, 2^{l+1}]` below `⌈3L⌉`, and the classes `p_s ≡ α`,
  `u ≡ β` mod `k`.
- **Characters.** Expand `e(hαβ p_l/k)` over the characters of `p_l` with the vendored
  `tf/P5MarkedEnergy/Factorization.lean` `e_eq_sum_cchi` (`‖cchi‖ ≤ 1`, `norm_cchi_le`). With
  `OneSided.card_dirichletCharacter_le` there are at most `64 L^{3C_m + 3}` indices in all
  (`twistedPoly_eq_sum_boxTerm`), paid for by Cauchy–Schwarz at the cost of their number
  squared.
- **Separation** (`exists_mellin_piece`, `boxSum_eq_integral`). Separate `ψ₁(p_s p_l u/Y)` by
  its Mellin density, from `mellinCutoffTask_proof` at `C = 1`, `lo = 1`, `hi = 2`,
  `bounds j = max (M₁ j) 0`: `∫ |a| ≤ L^{K₁}` and tail
  `∫_{|ξ| > L^{C_sep}} |a| ≤ K_A L^{-A_t}`. The energy of the average is
  `integral_sq_le_of_le_integral_split`, a form of `OneSided.integral_sq_le_of_le_integral`
  (`Erdos408/OneSided/Major/Energy/Average.lean`) with the tail kept apart; the tail meets the
  trivial bound `(2/vlo)² L^{2C_U + 5}` (`integral_boxPoly_le`).

This yields the time variable `t' = t + σ + 2πξ`. For `L^{B'} ≤ |t| ≤ T₀`,
`L^E ≤ |t'| ≤ 2T₀ − 2`, since `B' ≥ E + B_min` with `B_min = max(C_m, C_sep) + 2`. The box
polynomial is `G(τ) = P_s(τ) · (P/Y) P_l(τ) R(τ)` (`Endpoint/Tuple/Box.lean`), with

- `P_s(τ) = (PV)⁻¹ ∑_{p_s ∈ (P,2P], ≡α} p_s^{iτ}`;
- `P_l(τ) = ∑_{p_l ∈ (lo, hi]} χ(p_l) p_l^{iτ}`;
- `R(τ) = ∑_{u ∈ (R, 2R], ≡β} c_u u^{iτ}`;

and the scales satisfy `PNR ≤ 2Y`.

**The constant part** has no spare prime, so no characters: E6 for it is in
`Endpoint/Constant/Boxes.lean` and §6.6 (E10).

**Scales [O2]** (`Endpoint/Tuple/Asymp.lean`).

- `log P ∈ [L^{.27} − 1, L^{.36}]`.
- `N_l ∈ [x^{ε}/2, x]`.
- (6.34): the tuple residual satisfies `R ∈ [exp(L/T²²), x]`, from
  `R ≥ Y/(16 P N_l) ≥ x^{ε} e^{-L^{.36} − 4}/κ` and `D exp(L/T²²) ≤ x^ε`.
- The constant residual `R ≍ Y/P` lies in `[x^{0.99}, x²]`, and above `x` in general.

**E7. Ordinary times (S15) [PD (6.35)]** (`Endpoint/Tuple/Mean.lean`, `boxMeanValue_le`). On
the set where `|P_s| ≤ θ`, bound `|P_s Q|² ≤ θ² |Q|²`, enlarge the set to an interval and apply
the mean value theorem `OneSided.integral_norm_dirichlet_sq_le`
(`Erdos408/OneSided/Analysis/Divisor.lean`) to `Q = (P/Y) P_l R`, collapsed at scale `4NR`. Its
coefficients are `≤ (P/Y) L^{C_U} ω(n)` (U11), and over an interval of length `≤ 2T₀` its mean
value is `≤ L^{2C_U + 5}`. So the ordinary times contribute `≤ L^{-2A_s} L^{2C_U + 5}`.

### 6.4 S16. The exceptional set [PD (6.36); WD Lemma 5.2]

`Endpoint/Tuple/Exceptional.lean` (`exists_card_exceptional_le`).

The vendored `tf/P5/ExceptionalTheorem.lean` `exceptional_times`, at
`(a, b, A) = (0.27, 0.36, A + 1)`, with `coeff' p = coeff p · p/(2P)`, so that
`primePolynomial s coeff' = P⁻¹ ∑ coeff(p) p^{it}/2`. For every `A > 0` there is `K > 0` such
that, eventually, the integers `j` such that `[j, j + 1]` meets
`{|t| ≤ T_max : |P⁻¹ ∑_{p ∈ s} coeff(p) p^{it}| > L^{-A}}` number at most
`exp(K (L^{.36} + L^{.73} log L)) ≤ exp(L^{0.95})`. This is (6.36), used at `A = A_s`. For the
tuple part, `s` is
the primes of `P_{g_s} ∩ (P, 2P]` in the class `α`, rescaled by `min(1, vlo)/V`; for the
constant part, the phases `e(hpβ/k)` are absorbed into `coeff`.

### 6.5 S17. The sparse Gram bound from AP2 [PD (6.37); X2, X3]

`Endpoint/Tuple/Gram.lean`.

**Lemma E8** (`eventually_sum_sup_normSq_le`). Under `IntegerKernelBound x C_m κ'`: for
`R ∈ [exp(L/T²²), x]`, coefficients `|c_u| ≤ L^{C_U}` and a set `𝒥` of integers with
`#𝒥 e^{-L^{0.95}} ≤ 1` and `|j| ≤ 2T₀`, there are bounds `s_j` of `sup_{[j, j+1]} |R⁻¹ R|²`
with `∑_{j ∈ 𝒥} s_j ≤ 9(1 + |κ'|) L^{2C_U + 4}`.

*Proof.*

1. Choose a maximizer `τ_j ∈ [j, j + 1]` for each `j ∈ 𝒥`, by compactness
   (`IsCompact.exists_isMaxOn`).
2. By the `TT*` bound `sum_norm_sq_le_of_gram_rowSum` (as in
   `OneSided.sum_norm_unmarkedPoly_sq_le`, `Erdos408/OneSided/Major/Sparse.lean`), it suffices
   to bound the absolute row sums of the Gram matrix of `u ↦ u^{iτ_j}` on `(⌊R⌋, ⌊2R⌋]`.
3. The entries are at most `R + 1`, which is used for `|j − j'| ≤ 1`. Otherwise
   `1 ≤ |Δ| ≤ 4T₀ + 2 ≤ x³`, and AP2 at `k = 1`, `a = 0`, `H = lo = R`, `hi = 2R` bounds them
   by `|κ'| R (2|j − j'|⁻¹ + exp(−L^{0.95}))`. The row sums are at most
   `9(1 + |κ'|) R L/2`.
4. With `∑ |c_u|² ≤ 2R L^{2C_U}`, the result follows.

**Range check.**

- The tuple residual `R ∈ [exp(L/T²²), x]` by (6.34). PD's `R₀ ≥ x^{ε/2}` is replaced by
  `log R ≥ L/T²²`.
- The coefficient bound is pointwise (6.32), so the retained shifts do not change the
  exponent.
- AP2 is used only here.

WD's `sparse_residual_proof` (Lemma 5.3) needs `Y^{0.6} ≤ U`. It does not apply, because the
residual can be as small as `x^{cT^{-20}}`. This is the WD/PD difference at S17.

### 6.6 S18–S19. Tuple and constant parts at high times [PD (6.38)–(6.42); X1, X3; new: S19]

**E9. Spare prime polynomial from AP1 (S18)** (`norm_primeTwistPoly_le`,
`Endpoint/Tuple/Twist.lean`). Under `PrimeTwistBound x A' E C_m κ'`, for
`H ∈ [exp(L/T²²), x]`, an interval `(lo, hi] ⊂ [H, 2H]`, a character `χ` of modulus
`k ≤ L^{C_m}` and `L^E ≤ |u| ≤ x³`,
`|H⁻¹ ∑_{p ∈ (lo, hi]} χ(p) p^{iu}| ≤ 4κ' L^{-A'}`.

*Proof.* Abel summation with weight `p` (`sum_Ioc_natCast_mul_eq`) writes the sum through the
partial sums `S(y) = ∑_{p ∈ (lo, y]} χ(p) p^{-1+iu}`, each bounded by AP1. Here
`N_l ∈ [x^ε/2, x] ⊂ [exp(L/T²²), x]`. The spare slot carries coefficient 1 (X1), and the
character comes from E6.

**Tuple part on 𝒥** (`Endpoint/Tuple/Sparse.lean`). At an exceptional time,
`|G(t)|² ≤ (2/vlo)² · 4(4κ' L^{-A'})² s_j` by `|P_s| ≤ 2/vlo`, E9 and `PNR ≤ 2Y`
(`norm_boxPoly_sq_le_of_twist`). Summing with E8,
`∫_{𝒥} |G|² ≤ (2/vlo)² · 4(4κ' L^{-A'})² · 9(1 + |κ'|) L^{2C_U + 4}`
(`integral_exceptional_le`). With E7, one box contributes
`L^{-2A_s} L^{2C_U + 5} + (2/vlo)² · 4(4κ' L^{-A'})² · 9(1 + |κ'|) L^{2C_U + 4}`
(`eventually_integral_boxPoly_le_of_twist`). After the index count (squared) and the
separation cost, the choices `A_s = max((A₀ + D)/2, 1)`, `A' = (A₀ + D − 1)/2` and
`A_t = max(A₀ + D − K₁, 1)` give `O(L^{-A₀})` (`tupleBound_le`;
`TupleHigh.exists_integral_tupleSum_high_le`, `Endpoint/Tuple/General.lean`).

**E10. Constant part (S19) [new: replaces (6.40)–(6.42)]** (`Endpoint/Constant.lean`,
`exists_integral_const_high_le`; the pieces in `Endpoint/Constant/`).

0. **Boxes, with an elementary separation [new]** (`Endpoint/Constant/Boxes.lean`). In
   `𝒰_con(w) = ψ₁(w/Y) w^{iσ} C_B V⁻¹ ∑_{p | w} H(w/p)`, split `p` and `n = w/p` along the
   geometric grid `⌊e^{iδ}⌋`, `i < I`, with `δ = L^{-D}` and `I = ⌈3L^{1+D}⌉`. In the box
   `(j, i)` replace `ψ₁(pn/Y)` by its value at the corner `r = e^{(j+i)δ}`, at a cost
   `|ψ₁(pn/Y) − ψ₁(r/Y)| ≤ 12δM₁(1)` (`integral_boxErr_le`). The corner term factors over the
   classes `n ≡ β (mod k)` as `W ∑_β A_β(t) B_β(t)`, with a scalar `|W| ≤ 2K_c M₀`, the
   small-prime polynomial
   `A_β(t) = e^{-jδ} ∑_p e(hpβ/k) p^{iσ} p^{it}` and the residual
   `B_β(t) = e^{-iδ} ∑_{n ≡ β} H(n) n^{iσ} n^{it}`, split by the divisor model E1 as
   `B⁰ + B¹`. Cauchy–Schwarz over the `I²` boxes costs `I⁴ ≤ 256 L^{4 + 4D}`
   (`integral_twistedPoly_const_le`).
1. **Model error (6.39) [PD]** (`integral_boxResidual_error_le`). By E1(c) and the mean value
   theorem, `∫ |B¹|² ≤ (17 + 48L) C_N L^{-N}`. This is valid on the *whole* time range, before
   restricting to 𝒥.
2. **Pointwise model bound** (`eventually_norm_modelProgression_le`,
   `Endpoint/Constant/Kernel.lean`). For a model supported on `d ≤ exp(2L^{.47})` coprime to
   `k` with `∑ |A_d|/d ≤ L^{C₈}`, a scale `R ∈ [x^{0.99}, x²]`, a class `β` mod `k ≤ L^{C_m}`
   and `1 ≤ |t| ≤ x³`,
   `|R⁻¹ ∑_{n ∈ (⌊R⌋, ⌊2R⌋], n ≡ β} (∑_{d | n} A_d) n^{it}| ≤ L^{C₈} (12/|t| + x^{-1/150})`.
   Write the sum as `∑_d A_d d^{it} ∑_{v ≡ β d⁻¹} v^{it}` over `v ∈ (⌊R⌋/d, ⌊2R⌋/d]` and apply
   `IntegerKernel.norm_sum_filter_modEq_le` (`Erdos408/Analytic/IntegerKernel.lean`) with
   `H = R/d ≥ x^{0.99} e^{-2L^{.47}}`. Its hypotheses are `3^{128} ≤ H/k`, `H ≤ A + 1`,
   `B ≤ 2H` and `1 ≤ |t|`, and it gives
   `H⁻¹ |∑| ≤ 12/(1+|t|) + K e^{C√(log(k(|t|+3)))} (H/k)^{-1/128}`. In a box,
   `|B⁰(t)| ≤ L^{C₈} (24/|t| + x^{-1/150})` (`norm_boxResidual_model_le`).
3. **Medium range** `L^{B'} ≤ |t| ≤ X = x^{1/300}`: the model part is integrated as `t^{-2}`,
   giving `L^{2C₈} (2304 L^{-B'} + 4ε²X)` with `ε = x^{-1/150}`, which is small by
   `B' ≥ B_con`. This is the square integration of `1/|t|` in PD (6.41).
4. **High range** `X < |t| ≤ T₀`, only on the exceptional intervals 𝒥 of S16 (applied to
   `A_β`): `≤ #𝒥 (L^{C₈}(24/X + ε))²`, with `#𝒥 ≤ exp(L^{0.95})`.
5. Ordinary times `|A_β| ≤ θ = L^{-A_s}` are E7: `θ² (17 + 48L) 3δ H_max²`
   (`setIntegral_boxOrdinary_le`). The factor `|C_B/V| ≤ L^{d+3}` (U6) is absorbed.

One box is `integral_piece_le` (`Endpoint/Constant/Piece.lean`) and
`integral_boxSmall_mul_le`, `integral_boxSum_le` (`Endpoint/Constant/High.lean`); the
bookkeeping in powers of `L` is `Endpoint/Constant/Growth.lean` (`total_le_rpow`).

**Why the repair.** In PD, `R₀ ≍ Y/P` with `Y = xH'`, `H' ≥ e^{2L^{.39}−2}` and
`P ≤ e^{L^{.36}}`, so `R₀ > x`. For divisors `d' < H'/P` the progression scale `R' = R₀/d'`
exceeds `x`. AP2, the premise replacing PD Lemma 2.4, is stated only for `H ≤ x`. So PD's
(6.42) cannot be taken from AP2. PD's own Lemma 2.4 allows scales up to `2x⁵`. The lemma used
above is proved from the vendored zero-free half-plane (via `Erdos408/Analytic/Core.lean`). It
has no upper scale bound and needs only `H/k ≥ 3^{128}`. It is not a new hypothesis.

---

## 7. The extensions and explicit rates

### 7.1 O2: every `[ε]` step at `ε = c T^{-20}`

| step | PD | explicit bound here | where |
|---|---|---|---|
| Remark: `C_x = O_ε(1)` | `O_ε(1)` | `|C_B| ≤ C_x ≤ (T + E₀)^{d+1}` | U6 |
| S1, S5: tuple count | `O_ε(1)` | `|f_B| ≤ (2T²⁰/c)^{d+1}` on `[1, x²]`; `|F| ≤ L` | U5, U7 |
| S12: summed errors | `x^{-ε+o(1)}` | `≤ L^{O(1)} e^{2L^{.47}} x^{-ε} ≤ exp(−cL/(2T²⁰))` | E2.4 |
| S12: model error | `L^{-N}(1 + ∑ 1/l)` | `2√2 M₁(0) √C_N L^{-N/2}((T + E₀)^{d+1} + 1)` | E2.2 |
| S13 repeated slots | count `O(x^{-ε})` | count `≤ 4Yx^{-ε}`; `Ξ`-part `≤ L^{C_R} x^{-ε}` | E4 |
| S13 slot multiplicities | bounded | `≤ ω(m) ≤ 4L` for `m ≤ x²` | E7 |
| S14 (6.34) | `R₀ ≥ x^{ε−o(1)}` | `R ∈ [exp(L/T²²), x]`; `N_l ∈ [x^ε/2, x]` | §6.3 |
| S17 (6.37) | `R₀ ≥ x^{ε/2} > exp(L/(log L)²)`; Lemma 2.4 | AP2 with `H ∈ [exp(L/T²²), x]` | E8 |
| S18 (6.38) | Lemma 2.3, fixed `τ < ε` | AP1 on `N_l ∈ [x^ε/2, x] ⊂ [exp(L/T²²), x]` | E9 |
| S19 | `R' = x^{1−o(1)}` | `R/d ≥ x^{0.99} e^{-2L^{.47}}`, no upper bound; unconditional | E10 |
| Props 6.2–6.3 | `X = x^{1+o(1)}` | `n ∈ [x/κ, x²]`, dyads `X ∈ [√x, x²]` | G2 |

Every `[ε]` loss is a power of `T` or of `L`, and every saving is `exp(−cL/(2T²⁰))` or better.

### 7.2 O4: the spare slot

E5: `p_l = Q (Fin.last d)`. `Bc ∘ Fin.init` never sees it, and
`𝒜_B(u) = ∑_{Q'} Bc(Q') 1[∏Q' | u]` depends on `u` alone, not on `p_l` or `p_s`. Repeated
slots are removed (E4) before factorizing. Keeping `Q'_i ≠ p_l` inside `𝒜_B` would reintroduce
a dependence on `p_l`; the paper makes the same remark.

### 7.3 X1–X8

These are the ways `TwoSidedCorrelation` goes beyond PD Theorem 6.1.

- **X1. Joint `Bc` on all but the spare slot** (E2.5, E5, E8, E9, E10). Exact cancellation
  through `slotMean` at low times; `𝒜_B` sits in the residual, and the Gram bound is
  coefficient-free; AP1 is applied to the spare slot with coefficient 1; `C_B` is a scalar in
  the constant part.
- **X2. Margins `x^{cT^{-20}}`** (§7.1). All losses are `T^{O(1)}`, and the AP1 and AP2 ranges
  are checked.
- **X3. Analytic premises** (E8 for AP2, E9 for AP1; E10 uses a proved lemma). AP2 is used
  only at scales `≤ x`.
- **X4. Clipped core, uniform in `G`** (G1, G5, §5.1). Pointwise `L^{B₀}`; no divisor moments.
- **X5. `r ≤ K₀ + C_N s` varying bands** (U2, U7, E1). `e^r ≤ L^{1/10}`; one prime per band;
  disjointness from U3; no gap between the bands is needed.
- **X6. `x`-dependent `Ψ` with `T^{O(r)}` derivatives** (§4.2, §5.1). `MellinCutoffTask` with
  `C(j+1)` growth: the cutoff `C_f` is fixed, the tail saving arbitrary.
- **X7. `d + 1` slots, `d ≥ 0`** (throughout). `d` is fixed; `d ≤ 2` is unused.
- **X8. `L^{-A}` uniform in X1–X6** (§1). Every constant in §1 is independent of the varying
  data.

---

## 8. Vendored and repo lemmas used

`tf/` = `vendor/TotientFibers/Erdos821/`. Upstream encodes groups as `PrimeGroups`, labels as
subtypes, and endpoints as WD's `Endpoint`, so its endpoint-specific theorems do not apply to
`F = 𝒲(f_B − C_B)`. The proof uses its generic analytic lemmas only.

**Vendored WD lemmas.**

- **S2, S5, E6 (X6).** `Erdos821.P5Mellin.mellinCutoffTask_proof` (`tf/P5Mellin/MellinCutoff.lean`)
  applied to `Erdos821.Classical.blueprint_lem_fourier_separation`
  (`tf/Classical/FourierSeparation.lean`). Used in `Graph/Insertion.lean`
  (`exists_mellinCutoff`, for `Ψ`; package C reuses its density) and
  `Endpoint/Tuple/Energy.lean` (`exists_mellin_piece`, for `ψ₁`).
- **C2 (S7).** `Erdos821.P5Core.minorArcTask_proof` (`tf/P5Minor/MinorArcTask.lean`) with
  `Erdos821.Blueprint.Analytic.integer_bilinear_proof` (`tf/S34/OwnedLeafProofs.lean`). Used in
  `Comparison/Multiplier.lean`.
- **S8.** `Erdos821.P5Core.FourierArcTask_proof` (shift identity, Parseval, arc split) and
  `continuous_dp` (`tf/P5FourierArcProof/FourierArc.lean`). Used in
  `Comparison/ArcsFourier.lean` and `Comparison/ArcsBound.lean`.
- **C3 (S9).** `Erdos821.P5Core.LocalMellinEnergyTask_proof` (`tf/P5Energy/Final.lean`). Used in
  `Comparison/ArcsFourier.lean`.
- **S10 tail.** `Erdos821.P5Marked.wj_integral_split` (`tf/P5MarkedEnergy/Weights.lean`) and
  `Erdos821.P5Marked.weighted_mean_value` (`tf/P5MarkedEnergy/WeightedMean.lean`). Used in
  `Comparison/ArcsFourier.lean`.
- **E6 (S13).** `Erdos821.P5Marked.e_eq_sum_cchi`, `norm_cchi_le` and `e_periodic`
  (`tf/P5MarkedEnergy/Factorization.lean`). Used in `Endpoint/Tuple/Split.lean`,
  `Endpoint/Tuple/Assembly.lean` and `Endpoint/Tuple/General.lean`.
- **S16.** `Erdos821.Blueprint.Analytic.exceptional_times` (`tf/P5/ExceptionalTheorem.lean`).
  Used in `Endpoint/Tuple/Exceptional.lean`.

The definitions `e`, `dp`, `mellin`, `primePolynomial` and `localAdditivePolynomial` come with
them.

**Repo lemmas outside `TwoSided/`.**

- **U2.** `OneSided.eventually_harmonicMass_band` (`Erdos408/OneSided/Bands.lean`).
- **U5, U6, S12.** `Sieve.abs_slotCount_le`, `Sieve.sum_inv_slotTuples_le` and
  `Sieve.card_slotTuples_le` (`Erdos408/Extraction/Sieve/Basic.lean`).
- **U6.** `Unsmooth.abs_slotMean_le` (`Erdos408/Extraction/Unsmooth.lean`).
- **U7, U8.** `TypeII.markedWeight_eq_prod`, `TypeII.primeCount_prime_mul` and
  `TypeII.slotCount_prime_mul` (`Erdos408/Extraction/TypeII/Bands.lean`).
- **S12.** `Sieve.abs_sum_modEq_sub_le` (`Erdos408/Extraction/Sieve/Smooth.lean`), complexified
  as `LowFreq.norm_sum_modEq_sub_le`.
- **E3–E4, E7, E10.** The mean value theorem `OneSided.integral_norm_dirichlet_sq_le`
  (`Erdos408/OneSided/Analysis/Divisor.lean`).
- **E6.** `OneSided.integral_sq_le_of_le_integral` (`Erdos408/OneSided/Major/Energy/Average.lean`)
  and `OneSided.card_dirichletCharacter_le` (`Erdos408/OneSided/Major/Characters.lean`).
- **E10.** `IntegerKernel.norm_sum_filter_modEq_le` (`Erdos408/Analytic/IntegerKernel.lean`).

The `TT*` bound of E8 (`sum_norm_sq_le_of_gram_rowSum`) and the divisor-model combinatorics of
E1 (`DivModel.*`) are proved in `TwoSided/` itself.

**WD §5's endpoint versus PD's.**

- **WD**:
  - the first endpoint carries `α` with the discrepancy condition (WD (5.4)), which supplies
    the **low** times;
  - it also carries a rough factor on a fixed-exponent interval `[x^τ, x^η]`, which supplies
    the **high** times by the long rough-integer polynomial (WD Lemma 5.4).
- **PD**: the endpoint is `𝒲(f_B − C_B)`.
  - **Low** times come from Lemma 6.5 and exact centering (E2), with no discrepancy
    hypothesis.
  - **High** times come from the spare-slot prime polynomial at margin `x^{cT^{-20}}` (AP1,
    not a fixed exponent) and the constant part (E10).

So WD's `MarkedEndpointEnergyTask` and `long_rough_polynomial_proof` are not used. The S13–S17
skeleton is shared: removal, characters, boxes, exceptional set, Gram.

---

## 9. Lean layout

`Erdos408/TwoSided.lean` and `Erdos408/TwoSided/`, namespace `Erdos408.TwoSided`.

| File | Contents |
|---|---|
| `../TwoSided.lean` | `twoSidedCorrelation_of_graphTransference` (§3.4) |
| `Defs.lean` | §3.1 definitions |
| `Setup.lean` | R1; crude U7, U9; U8 (algebraic); free labels; analytic glue |
| `Graph.lean` | interface G (Proof of G) |
| `Graph/Endpoint.lean` | G1 (S1) |
| `Graph/BoundsLists.lean` | list counts for G1, G2a |
| `Graph/BoundsDamping.lean` | generic absolute bound of a pattern pairing |
| `Graph/Absolute.lean` | G2a |
| `Graph/Insertion.lean` | Mellin cutoff, G2, G3 (S2) |
| `Graph/Insertion/Identity.lean` | the insertion identity of G2 |
| `Graph/Insertion/MellinAdapter.lean` | the `CutoffBound` adapter (X6) |
| `Graph/Restore.lean` | G5, raw and comparison cases (S3–S4) |
| `Graph/Restore/Strip.lean` | G4 |
| `Graph/Restore/Clean.lean` | the clean summands |
| `Graph/Restore/Patterns.lean` | raw and comparison stripped correlations |
| `Graph/Restore/Core.lean` | U8 for `F` and `G` |
| `Graph/Restore/Bound.lean` | the absolute summand |
| `Graph/Restore/Mass.lean` | label masses |
| `Graph/Restore/General.lean` | G5 as an explicit inequality |
| `Graph/Restore/Eventually.lean` | G5 at scale `x` |
| `Comparison.lean` | interface C (Proof of C) |
| `Comparison/Separation.lean` | §5.1: Mellin, partition of unity, (6.18), (6.19) |
| `Comparison/Multiplier.lean` | C1, C2 (S6–S7) |
| `Comparison/ArcsLabels.lean` | free labels, the four boxes |
| `Comparison/ArcsFourier.lean` | shift identity, Parseval, C3 with the tail |
| `Comparison/ArcsBound.lean` | S8–S10 for abstract data |
| `Comparison/ArcsCore.lean` | energies, minor arcs, the arc energy, the final count |
| `Comparison/Arcs.lean` | one bilinear form from the mean square (S8–S10) |
| `Endpoint.lean` | interface E (Proof of E) |
| `Endpoint/DivisorModel.lean` | E1 (S11) |
| `Endpoint/DivisorModel/Truncation.lean` | list forms and their truncation |
| `Endpoint/DivisorModel/Lists.lean` | the marked weights as list forms |
| `Endpoint/Low.lean` | E2 (S12) |
| `Endpoint/Low/Facts.lean` | E2 steps 1 and 5, growth facts |
| `Endpoint/Low/Model.lean` | E2 steps 2–3 for one modulus |
| `Endpoint/Low/Progression.lean` | twisted progression sums |
| `Endpoint/Factor.lean` | E3–E5, the exceptional positions (S13–S14) |
| `Endpoint/Factor/Identity.lean` | E3, U3 |
| `Endpoint/Factor/Bounds.lean` | U6, U11, the mean value for E3–E4 |
| `Endpoint/Tuple.lean` | tuple part at high times (S13–S18) |
| `Endpoint/Tuple/Mark.lean` | `|c| ≤ L^{C_U}` |
| `Endpoint/Tuple/Split.lean` | E6: boxes, classes, characters |
| `Endpoint/Tuple/Energy.lean` | E6: separation of `ψ₁` |
| `Endpoint/Tuple/Assembly.lean` | E6 assembly and the choice of `A_s, A', A_t` |
| `Endpoint/Tuple/General.lean` | the tuple part for a general coefficient |
| `Endpoint/Tuple/Box.lean` | one box: mean value, trivial bound |
| `Endpoint/Tuple/Mean.lean` | E7 (S15) |
| `Endpoint/Tuple/Exceptional.lean` | S16 |
| `Endpoint/Tuple/Gram.lean` | E8 (S17) |
| `Endpoint/Tuple/Twist.lean` | E9 (S18) |
| `Endpoint/Tuple/Sparse.lean` | S15–S18 for one box |
| `Endpoint/Tuple/Asymp.lean` | growth facts (6.34) |
| `Endpoint/Constant.lean` | E10 (S19) |
| `Endpoint/Constant/Boxes.lean` | E10 step 0: geometric boxes and corner error |
| `Endpoint/Constant/Kernel.lean` | E10.2 |
| `Endpoint/Constant/Piece.lean` | one box, E10.3–E10.4 |
| `Endpoint/Constant/High.lean` | S19 at fixed `x` |
| `Endpoint/Constant/Bounds.lean` | U6, coprimality of the model |
| `Endpoint/Constant/Glue.lean` | elementary facts |
| `Endpoint/Constant/Growth.lean` | the exponents of S19 |

---

## 10. Deviations from PD

1. **Explicit exponents and order** (§1), including the independence of `A', C_m` from `E`.
2. **Clipped core** (X4): S1, S4 and (6.19) are pointwise, with no divisor moments.
3. **Vendored Mellin cutoff** (S2, S5, E6) instead of `N`-fold integration by parts. Same
   content: cutoff fixed, saving arbitrary.
4. **Crude absolute bound** G2a, with a `J`-dependent exponent, instead of WD Lemma 3.4.
5. **Partition of unity with supports in `[y, 2y]`** (§5.1), to meet the support hypothesis of
   the local Mellin energy.
6. **`T₀ = x L^{C_m+2}`**, decay order `j` chosen from the tail precision `A_e`, and the tail
   bounded by the weighted mean value (§5.4).
7. **S12 without a sum–integral comparison** (E2): each progression sum is compared with
   `κ_{h,k} m⁻¹` times the full sum, and the main terms cancel exactly against `C_B`.
8. **S17 range**: `log R ≥ L/T²²` with AP2, replacing `R₀ ≥ x^{ε/2}`.
9. **S19 repair** (E10): `IntegerKernel.norm_sum_filter_modEq_le` in place of (6.40)–(6.42).
   The medium/high split is at `x^{1/300}` instead of `T_mod`. AP2 is not used in S19,
   because its range `H ≤ x` misses `R' > x`. The constant part is separated along a geometric
   grid instead of by a Mellin density, and needs no characters.
10. **O4 relabeling** (E5): the spare slot is `Fin.last d`.
11. **X5** (E1): `e^r ≤ L^{1/10}` is the only band-count dependence.

None of these changes a statement that the rest of the argument consumes.

---

## 11. Dependencies

1. **Interfaces.** The proof meets the rest of the development only through the statements in
   `Erdos408/Hypotheses.lean`: `TwoSidedCorrelation`, `GraphTransference`, the premises
   `PrimeTwistBound` and `IntegerKernelBound`, and the graph objects `patternPairing` and
   `physicalLists`. The definitions of §3.1 are internal; G2 and G4 tie them to the graph
   objects.
2. **Imports.** The proof imports the vendored WD modules listed in §8 and
   `Erdos408.Analytic.IntegerKernel`. S19 therefore rests on the vendored zero-free half-plane
   through `Erdos408/Analytic/Core.lean`, which adds no hypothesis.
3. **Existential constants.** The constants inside vendored lemmas (`K` of
   `exceptional_times`, `K` of the local Mellin energy, `C_arc`) are existential. §1 uses them
   only as fixed constants, which is all the argument needs.
