# Blueprint: the one-sided Type II estimate (H1)

This document records the proof of `oneSidedTypeII : OneSidedTypeII`. The statement is in
`Erdos408/Hypotheses.lean` and the proof in `Erdos408/OneSided.lean` and
`Erdos408/OneSided/`. `OneSidedTypeII` is the extended form of PD Theorem 3.1. This
document restates PD §§3–5 as a chain of lemmas with every quantifier and every parameter
choice explicit, and says where each lemma is proved in Lean. It also closes the two
obligations that `rectangle_input.md` §1 lists for (H1):

- **O1**, the unquantified `exp(o(L))` budgets of PD Lemma 3.4 (§5.4);
- **O3**, uniformity in the band exponents (§2 and §5.3).

Sources. "PD" is *The Poisson–Dirichlet law for prime predecessors* (OpenAI, 24 September
2026). PD's §k is its TeX file `sections/0k-*.tex`. Equation numbers such as (3.9) are
PD's printed numbers. References such as `det:weak-kloosterman` or `mem:ghost-row` are
labels in PD's TeX source, used where PD's equations are cited by name.

Markers. **[PD]** means the step is PD's argument with nothing added. **[new]** means this
document adds content: an explicit rate, a choice PD leaves implicit, or a different proof
of the same statement. Every **[new]** item is listed in §9.

---

## 0. Target and conventions

**Target.** The Lean statement, in words. Fixed data are `q ∈ (0,1)`, `C, D_* > 0`,
`C_X ≥ 1`, and a window `0.1 < α₋ ≤ α₊ < 0.2`. The statement provides `K₀` and
`A₀, B, A` such that, for every `K ≥ K₀`, every gap `g > 0` and all constants `c₄, c_G`,
there is a `C₁` with the following property for all sufficiently large `x`.

For every choice of the varying data below, `|S| ≤ C₁ X L^{−D_*}`, where
`S = ∑_{m,n} α_m β_n F(mn − 1) 𝒲(mn − 1)`. The varying data are:

- exponents `α₋ ≤ a_1 < ⋯ < a_K ≤ α₊` with gaps `≥ g`;
- `γ ≥ L^{−1/100}` and scales `H_m, H_n ≥ x^γ` with `x/C_X ≤ X := H_m H_n ≤ C_X x`;
- `F` with `|F| ≤ 1` that is invariant under band primes;
- `α` satisfying P1–P4 of `rectangle_input.md` §2 (H1) with `(A₀, B, A, c₄)`: `α` is
  supported on rough `m ∈ [H_m, 2H_m]` with `|α_m| ≤ L^C` (P1–P3), and
  `|H_m^{−1} ∑_m α_m χ(m) m^{it}| ≤ c₄ L^{−A}` for every character `χ` of modulus
  `≤ L^{A₀}` and every `|t| ≤ 2XL^B` (P4);
- `β` supported on rough `n ∈ [H_n, 2H_n]` with `|β_n| ≤ L^C`;
- the kernel premise (G) with `c_G`: for `1 ≤ |Δ| ≤ 4XL^B + 2`,
  `H_n^{−1} |∑_{H_n ≤ n ≤ 2H_n} n^{iΔ}| ≤ c_G (|Δ|^{−1} + exp(−L^{0.95}))`.

In Lean (`Erdos408/OneSided/Setup.lean`), `Data K` bundles the varying data and
`Admissible` lists their hypotheses apart from P4 (`TwistBound`) and (G) (`KernelBound`).

**Notation.** `L = log x`, `W = exp(L^{0.24})`, and `m_* = min(H_m, H_n)`, so
`log m_* ≥ γL ≥ L^{0.99}`. The bands are
`𝒫_i = band x a_i = {p prime : ⌈exp(L^{a_i})⌉ ≤ p ≤ ⌊exp(2L^{a_i})⌋}`. Put
`V_i = ∑_{p ∈ 𝒫_i} 1/p` and `μ_i(p) = 1/(p V_i)`. Let `ω_i(h)` count the primes of `𝒫_i`
dividing `h`, and `ω = ∑ ω_i`. Then `𝒲 = markedWeight univ q 𝒫`. A *label product* is
`∏_i p_i` with `p_i ∈ 𝒫_i`.

**Thresholds.** "Eventually" means for `x ≥ x₀`, where `x₀` depends only on
`q, C, D_*, C_X, α±, K, g, c₄, c_G`. Constants written `C_K` depend on the same data. This
is exactly what `∃ C₁, ∀ᶠ x` permits: the threshold and constants must not depend on the
varying data. Every lemma below is uniform in the varying data in this sense. The Lean
statements have the form `∀ᶠ x in atTop, ∀ d : Data K, Admissible … x d → …`.

**Name clashes with PD.** PD uses `B` both for the memory cap `⌈L²⌉` (§4) and for the
frequency exponent. PD uses `T` both for the Bonferroni degree (proof of Lemma 3.4) and for
an interval length. Here:

- `B` is the frequency exponent of P4 and (G);
- `B_m = ⌈L²⌉` is the memory cap;
- `T_b = ⌈L^{0.76}⌉` is the Bonferroni degree.

---

## 1. Parameters

**Fixed exponents [new].** PD gives only their order. These values suffice, and they are
the definitions in `Setup.lean`:

| Name | Value | Lean | Role |
|---|---|---|---|
| `D₁` | `2D_* + 2` | `squarePrec` | precision for the Cauchy square (§3) |
| `E₀` | `D₁ + 4C + 2` | `momentPrec` | moment precision; `4C` is the endpoint loss `C₅` (§5.1) |
| `G` | `E₀ + 4` | `edgePrec` | edge contraction `‖ℰ_j‖ ≤ L^{−G}` (§5.5) |
| `A₀` | `G + 1` | `arcExp` | arc exponent and the P4 modulus exponent |
| `K₀` | `⌈200 (G + 3)⌉` | `bandThreshold` | so that `.005K ≥ G + 3` |
| `B` | `D + 13A₀ + C₄` | `freqExp` | retained frequency range, P4 and (G) (§6.4) |
| `C₄` | `4C + 4` | `meanExp` | mean-square loss in `maj:product-mean` |
| `D` | `D₁ + 1` | `majorPrec` | precision of the major term |
| `A'` | `4(D + 13A₀) + 3C₄ + B` | `energyExp` | energy precision (§6.4) |
| `A''` | `A' + 4A₀ + 4` | `isolatedExp` | isolated energy (§6.4) |
| `A_s` | `(A'' + C₄ + B + 2)/2` | `sparseExp` | sparse threshold (§6.4) |
| `A` | `(A'' + 2C + 4)/2` | `twistExp` | P4 precision (§6.4) |

All of these depend only on `(D_*, C)`. That matches the Lean order
`∃ K₀ A₀ B A, ∀ K ≥ K₀, ∀ g c₄ c_G, ∃ C₁`:

- `q` enters only constants: the bound on the weight (3.4), and the constants `C_K` of
  PD §4, which PD notes may depend on `q` (§4.1). It never enters the condition on `K`;
- `g` enters only the threshold (§2 and §5.3);
- `c₄` and `c_G` enter only `C₁`.

The lift of §4 has its own damping exponent, a free parameter that equals one at the
endpoints and so affects only the moment. `Replacement.lean` uses `1/2`.

The exponent `C_e = C(K, A₀, q)` of the crude edge bound (`mem:edge-crude`) depends on
`K`. It is never used to choose `K`: it is paid on only `o(N)` edges (§5.5, M10).

**Growing parameters [PD].**

- `J = ⌊L^{0.01}⌋` pads per group, and `M = J + 1`.
- `R = ⌈L^{0.5}/2⌉` (`momentPower`) and `N = 2R` path edges.
- `B_m = ⌈L²⌉` (`truncCap`) and `T_b = ⌈L^{0.76}⌉`.
- The rank cutoff is `r₀ = ⌈L^{9/20}⌉` **[new]**; PD uses `⌈C' N log L / L^{0.1}⌉` (§13).
- Grid side `κ = 1/⌈m_*^{1/40}⌉` **[new]** (§5.4).

**Scales.** `Y` ranges over powers of 2 with `L^{α₋} − 2 ≤ log Y ≤ 2K L^{α₊}`, giving
`O_K(L)` values. The pad dyads are `[d₀, 2d₀)` with `d₀ = 2^k`, `k ≤ L`, which covers every
pad product, since `log d₀ ≤ 2KJ L^{α₊} ≤ 2K L^{0.21}`. Put `H = d₀ Y`, `U = H H_m`,
`V = H_n`, and `Ω = [U, 16U] × [V, 2V]`. Then `min(U, V) ≥ m_*` and `log H = O_K(L^{0.21})`.

**Cutoffs [new in form].**

- Let `s` be `Real.smoothTransition (y − 1)`, which is `0` for `y ≤ 1` and `1` for `y ≥ 2`.
- `η(y) = s(y) − s(y/2)` (`dyadicBump`) is smooth, `0 ≤ η ≤ 1`, supported in `[1, 4]`, and
  `∑_{Y = 2^j, 0 ≤ j ≤ J'} η(b/Y) = 1` for `2 ≤ b ≤ 2^{J'+1}`.
- `ψ(t) = smoothTransition (5 − |t|)` (`plateau`) is smooth, real, supported in `(−5, 5)`,
  equal to `1` on `[−4, 4]`, and `0 ≤ ψ ≤ 1`.

**Arcs [PD].** `𝔐 ⊂ ℝ/ℤ` is the union of the arcs `|θ − h/k| ≤ 2L^{A₀}/Y` with
`1 ≤ k ≤ L^{A₀}` and `(h, k) = 1`. They are disjoint once `Y ≥ 8L^{3A₀}`, and
`|𝔐| ≤ 4L^{3A₀}/Y`. Put `𝓗_𝔐(t; a, b) = ψ(t/Y) ∫_𝔐 e(θ(t − b + a)) dθ`
(`arcIntegral`, `majorWeight`).

---

## 2. Uniform band facts (O3, first part)

All of these hold eventually and uniformly over `a ∈ [α₋, α₊]^K` with gaps `≥ g`.

- **B1. Disjoint and ordered.** If `a_{i+1} ≥ a_i + g`, then
  `exp(2L^{a_i}) < exp(L^{a_{i+1}})` once `L^g > 2`. So the bands are disjoint, and every
  prime of `𝒫_i` is below every prime of `𝒫_{i+1}`.
- **B2. Below the roughness level.** `exp(2L^{α₊}) < W` and
  `p_min := min ⋃𝒫_i ≥ exp(L^{α₋})`. So every band prime divides no rough integer, and
  every band prime exceeds `L^{A₀}`.
- **B3. Mass.** `1/2 ≤ V_i ≤ 1`. From `mertens_second`, `V_i` is within `E/L^{a_i}` of
  `log 2`, uniformly in `a_i ≥ α₋`. Hence `∏ V_i^{−2} ≤ 4^K`.
- **B4. Atoms and squares.** `sup_{i,p} μ_i(p) ≤ 2 e^{−L^{α₋}}`,
  `∑_{p ∈ 𝒫_i} p^{−2} ≤ 2 e^{−L^{a_i}}`, and `|𝒫_i| ≤ exp(2L^{a_i})`.
- **B5. Label products.** Every label product lies in
  `[exp(∑ L^{a_i}), exp(2 ∑ L^{a_i})] ⊆ [exp(L^{α₋}), exp(2K L^{α₊})]`. A product of `KJ`
  band primes lies in `[1, exp(2KJ L^{α₊})]`.
- **B6. Gap bound for Lemma 3.2.** For `i < i_*`,
  `∑_{i < i_*} 2L^{a_i} ≤ 2K L^{a_{i_*} − g}`.

B1–B5 are proved in `Erdos408/OneSided/Bands.lean` (`eventually_band_disjoint`,
`eventually_band_lt`, `eventually_not_dvd_of_isRough`, `eventually_rpow_lt_of_mem_band`,
`eventually_harmonicMass_band`, `sum_band_inv_sq_le`, `card_band_le`,
`labelProduct_bounds`). The lower half of B3 comes from `harmonicMass_band_ge` in
`Erdos408/Extraction/TypeII/Bands.lean`, and the expansion of `𝒲` in §3 uses
`markedWeight_eq_prod` from the same file. B6 is `card_selections_le` in
`Goodness.lean`.

The gap enters only B1 and B6. The window enters B2–B5. Nothing else in §§3–6 depends on
the individual `a_i`; §8 lists the places where the band exponents enter.

---

## 3. Interface 1: the Cauchy reduction [PD §3.1]

**Definitions.** Fix a dyadic `Y`. For label products `a, b` put
`R(a, b) = ∑_{m,n,r,s} α_m ᾱ_r β_n β̄_s · 1[∃ h ≥ 1 : mn − 1 = ah, rs − 1 = bh]`. Then
`Q_Y = ∏_i V_i^{−2} ∑_{a,b} η(a/Y) η(b/Y) R(a, b)` (`cauchySquare`, PD (3.8)). This is
real and nonnegative, since it equals `∑_h |T_h|²` below.

**Theorem 1 (Cauchy reduction; `cauchy_reduction` in `Cauchy.lean`).** Let `K ≥ 1`.
Suppose that, eventually and uniformly, `Q_Y ≤ C' X Y L^{−D₁}` for every dyadic `Y`. Then,
eventually, `|S| ≤ C₁ X L^{−D_*}`.

`K ≥ 1` is necessary, and PD leaves it implicit. With no bands the only label product is
`1`, and `η(1/Y) = 0`, so every `Q_Y` vanishes while `S` need not be small. The assembly
gets it from `K ≥ K₀ ≥ 1` (`one_le_bandThreshold`).

Theorems 1–3 quantify over every dyadic `Y`, not only those in range. Outside the range no
label product has `η(a/Y) ≠ 0`, so `Q_Y`, `Q_Y^{maj}`, `𝒯` and the moment all vanish.

Proof steps:

1. **Label expansion.** `𝒲(h') = ∑_{b₀} ∏V_i^{−1} q^{ω(h')−K} 1[b₀ ∣ h']`, summed over
   label products `b₀` (using B1). For `h' = b₀h`, invariance gives `F(h') = F(h)`.
2. **Squareful error [PD; rate new].** Always `ω(h) ≥ ω(h') − K`, with equality unless some
   `p_i² ∣ h'`. Replacing `q^{ω(h')−K}` by `q^{ω(h)}` changes the sum by at most
   `2 C(K,q) L^{2C} ∑_p 2H_m (H_n/p² + 1)`. Here `C(K,q) = sup_j (j q^{j−1})^K / ∏V_i`. By
   B4 this is `≤ C_K X L^{2C} (e^{−L^{α₋}} + exp(2KL^{α₊})/H_n) ≤ X L^{−D_*−1}`. The second
   term uses `H_n ≥ exp(L^{0.99})`.
3. **Dyadic split.** `S = ∑_Y S_Y + error`, with `S_Y = ∑_{h < 4X/Y} F(h) q^{ω(h)} T_h`,
   where `T_h = ∑_{b₀ h = mn − 1} ∏V_i^{−1} η(b₀/Y) α_m β_n`.
4. **Cauchy.** `|S_Y|² ≤ (4X/Y) ∑_h |T_h|² = (4X/Y) Q_Y`, using `|F q^{ω}| ≤ 1`.
5. **Sum over dyads.** `|S| ≤ O_K(L) · (4C')^{1/2} X L^{−D₁/2} + X L^{−D_*−1}`, which is at
   most `C₁ X L^{−D_*}` because `D₁ = 2D_* + 2`.

**Lemma 1.1 (progression divisors, (3.9)) [PD].** For `1 ≤ l ≤ 4Y` with `Y ≤ X^{1/4}`,
`∑_{1 ≤ h ≤ 4X/Y} τ(1 + lh)² ≤ C (X/Y) L³`. The proof uses `τ² ≤ τ₄` (prime by prime,
`(k+1)² ≤ C(k+3, 3)`) and `τ₄(n) ≤ 4 ∑_{d ∣ n, d ≤ n^{3/4}} τ₃(d)`. In Lean this is
`sum_card_divisors_one_add_mul_sq_le` (`Analysis/Divisor.lean`), with the explicit bound
`4 (Z + (1 + lZ)^{3/4}) (1 + log(1 + lZ))³` for `h ≤ Z`.

**Lemma 1.2 (shared labels) [PD].** Let `Q_Y^{sh}` be the part of `Q_Y` with `(a, b) > 1`.
Then `|Q_Y^{sh}| ≤ C_K X Y L^{4C+3} e^{−L^{α₋}}`. In Lean the absolute size of the pair
error is bounded in `Decomposition/Pair.lean` and `Decomposition/Count.lean`, and the
probability of a shared prime in `Decomposition/Collision.lean`.

**Lemma 1.3 (determinant form) [PD].** For coprime label products,
`[∃ h ≥ 1 : mn − 1 = ah, rs − 1 = bh] ⟺ bmn − ars = b − a`. Since `|b − a| ≤ 4Y`, the
indicator equals `ψ((bmn − ars)/Y) · 1[⋯]` (`Decomposition/Bound.lean`).

---

## 4. The lift: definitions [PD §3.2]

Fix `Y` and a pad dyad `d₀`. The Lean definitions are in `Lift.lean`.

**States.** A *physical state* is a primitive `P = (P₁, P₂) ∈ Ω ∩ ℤ²` together with, for
each `i`, an ordered list `p_i = (p_{i,1}, …, p_{i,M})` of distinct primes of `𝒫_i`, all
dividing `P₁` (`lists`). The state measure is `∏_i V_i^{−M}` times counting measure. It is
constant, so adjoints are conjugate transposes. The state space is finite.

**Operators.**

- `𝒮` (`symOp`) averages over permutations within each group's list.
- `𝒯` (`rowOp`) is the row operation. It copies slots `1..J` of each group (product `D`,
  required to lie in `[d₀, 2d₀)`). The source's slot `M` products to `b`. New target slots
  (product `a`) carry weight `V_i^{−1}` each, under the *cross-edge ban*: every new label
  differs from every source label. The edge requires `t = det(P, Q)/D ∈ ℤ` and has
  multiplier (3.15)
  `𝒦 = (d₀/D) η(b/Y) η(a/Y) ψ(t/Y) {1[t = b − a] − ∫_𝔐 e(θ(t − b + a)) dθ}
  · q^{(ω(P₁) − KM)/2 + (ω(Q₁) − KM)/2}`. Here `q` is the damping exponent of the lift
  (§1).
- `r_P` (`rootRatio`) is the first coordinate of the second column of any `SL₂(ℤ)`
  completion of `P`, divided by `P₁`, taken mod 1.
- A state is *good* when tests (i) and (ii) of PD §3.2 (`det:good-first`,
  `det:good-second`) hold. `𝒢` (`goodOp`) is the projection onto good states.
- `𝒜 = 𝒢 𝒮 𝒯 𝒮 𝒢` (`edgeOp`), and the moment `∑_P ⟨u_P, (𝒜𝒜^*)^R u_P⟩` is `detMoment`.

**Endpoint vectors.** `f̄(P) = α_{P₁/G(P₁)} β̄_{P₂}` and `g(P) = ᾱ_{P₁/G(P₁)} β_{P₂}`, where
`G(P₁)` is the band-prime part of `P₁` (PD (3.16)). They are zero unless `G(P₁)` is
squarefree with exactly `M` primes per group. Thus `g = f`, which is `endVec` in Lean, and
`rowPairing` and `pairing` are `⟨f, 𝒯 f⟩` and `⟨f, 𝒜 f⟩`.

**Lemma 4.1 (lift identity) [PD (3.17) and §4.9].** Let `E_Y` be the coprime-pair error
`∏V_i^{−2} ∑_{(a,b)=1} η η ∑ α ᾱ β β̄ (1[t = b − a] − 𝓗_𝔐(t; a, b))`, with
`t = bmn − ars`. Weight each summand by independent ordered harmonic pads
`∏_{i,h} μ_i(p_{i,h})`, which have total mass 1, and keep only pads that are distinct and
disjoint from `a, b`. The result equals `∑_{d₀} d₀^{−1} ⟨f, 𝒯 g⟩_{d₀}` exactly.

The change of variables is `P = (Dbm, s)` and `Q = (Dar, n)`, so that
`det(P, Q)/D = bmn − ars`. It uses:

- the measure identity `D^{−1} ∏V_i^{−(J+2)} = ∏ μ_i(p_{i,h}) · ∏V_i^{−2}`
  (`mem:pad-measure`);
- B2, so that `G(Dbm) = Db` and the damping is 1 at endpoints;
- automatic primitivity (PD §3.2): a common prime of `m` and `s` exceeds `W ≥ 5Y > |t|` and
  divides `t ≠ 0`;
- `𝒮 f = f` and `𝒮 g = g`.

In Lean the identity is `Decomposition/LiftSum.lean`, with the bookkeeping of pads and
lists in `Decomposition/Lists.lean`.

**Lemma 4.2 (endpoint norms) [PD (3.18)].** `‖f‖² ≤ 64 L^{4C} U V` and
`sup|f| ≤ L^{2C}`. The proof uses `∏_i V_i^{−M} ∑_{distinct ordered} ∏ 1/p ≤ 1` and
`#{P₁ = Gm ∈ [U, 16U] : α_m ≠ 0} ≤ 32U/G`. No exponent depends on `K` or `J`. In Lean this
is `Pairing/Endpoint.lean`, which also shows that `f` is constant on the lists at a
position.

---

## 5. Interface 2: the replacement

**Theorem 2 (`eventually_replacement` in `Replacement.lean`).** For `K ≥ K₀` there is `C₂`
such that, eventually, for every dyadic `Y`, `|Q_Y − Q_Y^{maj}| ≤ C₂ X Y L^{−D₁−1}`. Here
`Q_Y^{maj}` (`majorSquare`) is the major sum `maj:sum`, PD (5.1): like `Q_Y`, but with
`𝓗_𝔐(bmn − ars; a, b)` in place of the equation, and with no coprimality.

The proof is the chain §5.1 → §5.6. The decomposition is
`Q_Y − Q_Y^{maj} = Q_Y^{sh} − Q_Y^{maj,sh} + E_Y`, where `E_Y` is the coprime-pair error.
Lemma 1.2 and `mem:unshared-collisions` bound the shared parts. The proof has three parts,
called leaves in the Lean docstrings:

- **leaf A**, the lift identity and the collisions (`eventually_square_decomposition`,
  `Decomposition.lean`; Lemmas 1.2, 4.1 and §5.6), combinatorics on the physical states;
- **leaf B**, the removal of the good-state projections (`eventually_goodness_removal`;
  §5.6 and §14);
- **leaf C**, the moment bound (`eventually_detMoment`; §§5.4–5.5 and §§11–13), which
  `eventually_pairing_of_moment` (§5.1) turns into a bound on `⟨f, 𝒜 f⟩`.

### 5.1 Pairing from the moment (2b) [PD §3.3]

**Lemma 5.1 (`eventually_pairing_of_moment` in `Pairing.lean`).** If
`(UV)^{−1} ∑_{P ∈ Ω primitive} ⟨u_P, (𝒜𝒜^*)^R u_P⟩ ≤ L^{−E₀ N}`, then
`|⟨f, 𝒜 g⟩| ≤ C_K U V L^{4C − E₀}`.

Ingredients, all finite-dimensional:

- **Slope cells.** Partition positions into slope intervals of length `H/U²`. Edges join
  only cells within bounded distance, since `|det| ≤ C H`. Each cell holds `≤ C H`
  primitive positions, by the pivot argument (`Pairing/Geometry.lean`).
- **Compression.** The Gram matrix `C^{(j)}_{PQ} = ⟨u_P, B₀^R u_Q⟩` is PSD, so
  `⟨f_j, B₀^R f_j⟩ ≤ tr(C^{(j)}) ∑_P |f(P)|²`.
- **Spectral Hölder.** For PSD `B₀ = 𝒜𝒜^*`,
  `‖𝒜^* f‖² ≤ ‖f‖^{2−2/R} ⟨f, B₀^R f⟩^{1/R}`.
- **Hölder in `j`** with exponents `(2, 2R/(R−1), 2R)`.
- `H^{1/(2R)} = O(1)`, since `log H = O_K(L^{0.21})` and `R ≍ L^{0.5}`.
- **Constant.** With Lemma 4.2 the loss is `C₅ = 4C`.

The compression, spectral Hölder and Hölder steps are proved for an arbitrary complex
matrix in `Pairing/Cells.lean` (`norm_pow_le_of_cells`).

### 5.2 Root residues: PD Lemma 3.3

**Kloosterman bound (`det:weak-kloosterman`, (3.24)) [PD].** For
`K_m(h, k) = ∑_{y ∈ (ℤ/m)^×} e((hy + k y^{−1})/m)` and every `ε > 0`,
`|K_m(h, k)| ≤ C_ε m^{3/4+ε} (h, k, m)^{1/4}` (`norm_kloosterman_le`,
`Analysis/Kloosterman.lean`). The proof:

- `∑_{h,k} |K_m|⁴ = m² T_m`, where `T_m` counts unit quadruples with equal sums and equal
  inverse sums. Clearing denominators gives `m ∣ (y₁+y₂)(z₁−y₁)(z₁−y₂)`. The linear map to
  these three forms has kernel of size `≤ 2`, so `T_m ≤ 2 m² τ(m)²`.
- `K_m` is constant on the orbits `(hs, ks^{−1})`, and the stabilizer of `(h, k)` has at
  most `(h, k, m)` elements, so `φ(m) |K_m(h, k)|⁴ ≤ (h, k, m) m² T_m`.
- Finish with `m/φ(m) ≤ τ(m)` and `τ(m) ≤ C_ε m^ε`.

**Lemma 5.2 (root residues; `abs_rootCount_sub_le` in `RootResidue.lean`).** Let
`U, V ≥ 2`, let `S` be squarefree, and fix `g₀ ∈ SL₂(ℤ/S)`. Let `I₁, I₂, I₃` be intervals
in `[1,16]`, `[1,2]`, `[0,1]`. Count the primitive `(u, v)` with:

- `u/U ∈ I₁` and `v/V ∈ I₂`;
- unique completion `ud − vc = 1` with `0 ≤ c < u`, and `c/u ∈ I₃`;
- `g = (u c; v d) ≡ g₀ (mod S)`.

The count is `c₂ U V |I₁||I₂||I₃| / |SL₂(ℤ/S)| + O(U V S² min(U, V)^{−1/5})`, with an
absolute implied constant and `c₂ = ∑_l μ(l)/l²` (`primitiveDensity`). Two notes on the
form **[new]**:

- The error replaces PD's `x^{−c_δ}`; that is the whole point of the extension. The
  restriction on `S` is not needed in the lemma; the root replacement keeps
  `S² m_*^{−1/5}` small (§5.4).
- `c₂` is used instead of `1/ζ(2)`. Its value is never needed, only `c₂ ≤ 2`.

Proof [PD outline, with a different discrepancy step **[new]**]. Treat `U ≤ V`; the other
case swaps roles, as at the end of PD's proof of Lemma 3.3 (`rootCount_le_swap`,
`swap_le_rootCount`).

- Fix `u ≡ u₀ (S)` and put `S₁ = (u, S)`. The admissible `(c, v)` mod `m₁ = uS₁` lie on a
  twisted modular hyperbola, with `M(u) = u ∏_{p∣u, p∤S}(1 − 1/p)` points per period
  (PD (3.25)–(3.26); `fibreCount_eq_card`).
- **Discrepancy by completion.** This replaces PD's smooth sandwich. Count the points in a
  box by finite Fourier analysis on `(ℤ/m₁)²` (`RootResidue/Fourier.lean`). The interval
  transforms are geometric sums with `|Â(h)| ≤ m₁/(2‖hq‖)`, so the error is
  `X τ(m₁)(2 + log m₁)²` whatever the length of the `v`-range, once the hyperbola sums
  satisfy `|Ŝ(h, k)| ≤ X (k, m₁)` for `k ≠ 0`. By `det:CRT-Fourier`, (3.28), these sums are
  averages of `K_{m₁}(h + ju, k a')`, so the Kloosterman bound gives
  `X ≪ m₁^{3/4 + 1/100}` (`RootResidue/Hyperbola.lean`). Everything is a finite sum: no
  smooth bumps and no Fourier tails.
- The main term is the column count `#{c ∈ I₃u : c ≡ c₀ (S), (c, u) = 1}`, by Möbius
  inversion `|I₃| u/S · ∑_{l ∣ u, (l, S) = 1} μ(l)/l + O(τ(u))`.
- Sum over `u ≍ U` with `u ≡ u₀ (S)`, and average the Euler factor
  (`RootResidue/Progression.lean`). The main term is
  `U V |I₁||I₂||I₃| ∑_{(l, S) = 1} μ(l)/l² / S³`, with error `O(U^{4/5} V S²)`.
- The constant is identified without computing `|SL₂(ℤ/S)|`: the counts over all `g₀` add
  up to the count for `S = 1`, and comparing main terms gives
  `∑_{(l, S) = 1} μ(l)/l² / S³ = c₂ / |SL₂(ℤ/S)|` (`coprimeDensity_div_eq`).

**Lemma 5.2′ (lines) [PD].** Under the uniform measure on `SL₂(ℤ/S)`, the kernel lines of
the first row mod `p ∣ S` are independent and uniform on `ℙ¹(𝔽_p)`. Every unimodular row is
the first row of exactly `S` matrices, and by CRT each line mod `p` contains `p − 1`
nonzero rows (`Moment/RootReplacement/Lines.lean`).

### 5.3 Good states: PD Lemma 3.2 (O3, second part)

**Lemma 5.3 (`eventually_volume_not_good` in `Goodness.lean`).** Fix full unordered lists
at a position, and `d₀`. Eventually, the set of `r ∈ ℝ/ℤ` failing test (i) or test (ii)
has measure at most `e^{−L^{α₋}/4}`, uniformly in the lists and the varying data.

Proof [PD, with uniformity **[new]**]:

- **Test (i).** For a nonzero integer `n`, the `r` with `‖nr‖ ≤ δ` have measure at most
  `6δ`. There are at most `M^K · Y^{0.2}` integers `n = lD`, so the total is
  `6 M^K Y^{−0.5}`.
- **Test (ii).** Fix `I` with `i_* = max I`, and fresh draws `T_f`. The trial integers
  number at most `M^K exp(2K L^{a_{i_*} − g})`, by B6. The bad set of `r` for one `T_f` has
  measure `≤ #pairs · 600 e^{−L^{a_{i_*}}}`. Averaging over `T_f` and applying Markov's
  inequality at the threshold `exp(−¼L^{a_{i_*}})` gives at most
  `600 M^{2K} exp(4K L^{a_{i_*} − g} − ¾ L^{a_{i_*}})` for each of the `2^K` sets `I`.
- **Uniformity.** Both totals are at most `e^{−L^{α₋}/4}/2` once `L^g ≥ 32K` and
  `L^{α₋} ≥ 8(K + 2K L^{0.01} + 600)`, using `M ≤ exp(L^{0.01})`. Both thresholds depend
  only on `K, g, α₋`, which closes PD's `exp(o(L^{a_{i_*}}))`.

### 5.4 Root replacement: PD Lemma 3.4 (O1)

**The path functional.** Expand `(𝒜𝒜^*)^R` as a sum over paths of `N` edges. Write every
position as `g z` with `g` the root matrix of `P₀` and `z` primitive, so that
`z₀ = z_N = e₁`. Allow a *real* root `ϱ = (u/U, v/V, r) ∈ [1,16] × [1,2] × [0,1]`, with
`g(ϱ) = (u, ur; v, vr + 1/u)`. For `ℓ ∈ ∏_{p band} ℙ¹(𝔽_p)`, define
`Φ(ϱ, ℓ) = ∑_{paths, lists} c(path) · box(ϱ, path) · good(r, path) ·
∏_p λ_p(path, ℓ_p)`. Here:

- `c(path)` holds every root-independent factor: label weights, the edge multipliers, which
  depend only on `det(z, z')/D`, and the list restrictions.
- `box` holds the conditions `g z_j ∈ Ω`.
- `good` holds the good-state tests. These depend on the root only through `r`, since
  `r_{gz} = τ(w)/τ(z)` with `τ(z) = z₁ + r z₂` (3.31).
- The line factor is
  `λ_p = ∏_{j ∈ A_p} 1[[z_j]_p = ℓ_p] · ∏_{j ∉ A_p} (1 − η'_j 1[[z_j]_p = ℓ_p])`, where
  `A_p` is the set of visits where `p` is active, and `η'_j = 1 − q_j` with
  `q_0 = q_N = √q` and `q_j = q` otherwise.

For an integer root, let `ℓ(g)_p` be the kernel line of `(u, c) mod p`. Then **exactly**
`(UV)^{−1} ∑_P ⟨u_P, (𝒜𝒜^*)^R u_P⟩ = (UV)^{−1} ∑_{g} Φ(g, ℓ(g))`, because
`p ∣ (gz)₁ ⟺ [z]_p = ℓ(g)_p`. The *model* is
`Φ̄(ϱ) = ∑ c · box · good · ∏_p avg_{ℓ_p ∈ ℙ¹(𝔽_p)} λ_p`.

**Lemma 5.4 (root replacement; `eventually_root_replacement` in `Moment/Statements.lean`)
[statement new in form].** Let 𝒬 be the grid of cubes of side `κ` in
`[1,16] × [1,2] × [0,1]`, and `ϱ_Q` the lower corner of the cube `Q`. Eventually,
`|(UV)^{−1} ∑_g Φ(g, ℓ(g)) − c₂ ∑_{Q ∈ 𝒬} vol(Q) Φ̄(ϱ_Q)| ≤ exp(−L^{0.76})`.

The proof applies to every functional of the same shape:

- at most `N` edges;
- root-independent coefficients of total absolute mass `≤ exp(L^{0.74})`;
- box, good and line factors as above.

PD uses the one-edge and goodness-failure versions to remove the good-state projections.
The Lean proof does not need them: it counts the bad states directly (§14).

The model is a Riemann sum, not PD's integral **[new]**. The bound in §5.5 holds
pointwise in `ϱ`, so no integral is ever needed. The error is two-sided, though only an
upper bound on the nonnegative moment is used.

**Proof, with every budget explicit [new].** PD's proof of Lemma 3.4 has three steps:

1. Bonferroni at degree `T_b` on `∏_{p inactive}(1 − X_p)`, where
   `X_p = 1 − ∏_j (1 − η'_j H_j) ∈ [0, 1]`. The sandwich is pointwise, since a multilinear
   inequality that holds on `{0,1}^n` holds on `[0,1]^n`. The gap is `e_{T_b}(X)`, with
   model mean `≤ (∑_p 𝔼X_p)^{T_b} / T_b! ≤ (K (N + 1))^{T_b} / T_b!`.
2. Apply Lemma 5.2 to each monomial on each grid cube, summing over residue matrices.
3. Bound the boundary cubes absolutely.

The budgets, where "PD says" quotes the proof of Lemma 3.4:

| Quantity | PD says | Explicit bound | Reason |
|---|---|---|---|
| paths × labels × permutations | `exp(O_K(L^{.73}))` | `exp(C_K L^{0.73}) ≤ exp(L^{0.74})` | as printed, for the paths in the tube (3.30) |
| Bonferroni gap | `exp(−Ω(L^{.76} log L))` | `≤ exp(−0.25 L^{0.76} log L)` | `60 σ^{T_b}/T_b!` with `σ ≤ K (N + 1)` and `N/T_b ≤ L^{−0.26}` |
| monomials | in "`exp(o(L))`" | `≤ exp(3 L^{0.96})` | at most `T_b` primes among `≤ K exp(2L^{α₊})` |
| modulus `S` | `log S = O_K(L^{.96})` | `log S ≤ 3 L^{0.96}` | `≤ K(M + N + 1) + T_b` primes, each `≤ exp(2L^{α₊})` |
| residue matrices | in "`exp(o(L))`" | `≤ S⁴` | `\|SL₂(ℤ/S)\| ≤ S⁴` |
| good-test breakpoints in `r`, per visit | "`exp(o(L))`" | `≤ exp(C_K L^{0.21})` | `r ↦ τ(w)/τ(z)` is monotone and `256`-Lipschitz; `‖mρ‖` changes side `≤ 256\|m\| + 1` times for `\|m\| ≤ exp(C_K L^{0.21})` |
| face derivatives | "`exp(o(L))`" | `≤ exp(C_K L^{0.21})` | `∂_r (gz)₂/V = (v/V) z₂` with `\|z₂\| ≤ 2560 N H` |
| grid cubes | `x^{3ε}` | `15 κ^{−3} ≤ 120 m_*^{3/40}` | choice of `κ` |
| one root count | `UV x^{−c_δ}` | `C UV S² m_*^{−1/5}` | Lemma 5.2 |

Totals, normalized by `UV`, each multiplied by the coefficient mass `exp(L^{0.74})`
(`Moment/RootReplacement/Budget.lean`):

- **Gap.** `≤ exp(−0.25 L^{0.76} log L)`.
- **Discrepancy.** `κ^{−3} · exp(3L^{0.96}) · S⁴ · C S² m_*^{−1/5} ≤
  exp(C_K L^{0.96}) m_*^{−1/8}`.
- **Boundary.** At most `κ^{−2} exp(L^{1/2})` bad cubes (§15, RR6), each costing
  `4κ³ + C m_*^{−1/5}`, so `≤ exp(2 L^{1/2}) m_*^{−1/40}`.
- **Upper faces.** The positions with `u = 16U` or `v = 2V` cost `≤ 20/m_*`.

With `log m_* ≥ L^{0.99}` the last three are `≤ exp(C_K L^{0.96} − L^{0.99}/40)`, which is
far below `exp(−L^{0.76})`. The Bonferroni gap is the binding term, and it absorbs the
coefficient mass since `0.76 > 0.74`. The total is below `exp(−L^{0.76})`, which is
smaller than `L^{−AN} = exp(−A L^{0.5} log L)` for every fixed `A`. That is all §5.5 needs.

**O1 is closed.** Every budget PD writes as `exp(o(L))` is at most `exp(C_K L^{0.96})`.
The extension needs these budgets to be `exp(O_K(L^{0.98}))`, so that the shrinking scale
`γ L ≥ L^{0.99}` absorbs them, as *The normal order of the number of iterations of Euler's
function* (Plasma AI, 2026) states for the one-sided argument. The proof needs only
`γ L / L^{0.96} → ∞`.

### 5.5 The model bound: PD §4.1–4.8

**Theorem 5.5 (`eventually_norm_lineAverage_le` in `Moment/Memory.lean`).** Eventually,
uniformly in `ϱ` and the varying data, `|Φ̄(ϱ)| ≤ L^{−(E₀+1) N}`.

With Lemma 5.4 this gives the moment bound `eventually_detMoment`:
`(UV)^{−1} ∑_P ⟨u_P, (𝒜𝒜^*)^R u_P⟩ ≤ 15 c₂ L^{−(E₀+1)N} + exp(−L^{0.76}) ≤ L^{−E₀ N}`.

Both rank ranges of M10 give `≤ L^{−(E₀+2)N}`, so the history sum is at most
`2 L^{−(E₀+2)N}`.

The chain is stated here at PD's level. Its Lean representation is described in §10 and
§§12–13. Fix `ϱ`, and let 𝒵 be the finite set of primitive `z` in the tube `det:tube`,
(3.30), satisfying the box at `ϱ`. Put:

- `b'_p = 1 − ∑_j η'_j/(p + 1)` (`baseline`);
- `ν_i(p) = 1/(V_i (p + 1) b'_p)`;
- `s_i = ∑_{p ∈ 𝒫_i} ν_i(p)`;
- `Δ = sup ν_i(p)`.

| # | Statement | PD | Quantitative content |
|---|---|---|---|
| M0 | `ν_i/μ_i = 1 + O((N+1)/p)`, `s_i = 1 + O((N+1)/p_min)`, `Δ ≤ C_K e^{−L^{α₋}}`, `b'_p ≥ 1/2` | `mem:measure-masses` | B2–B4 |
| M1 | primewise identity: `∏_p avg λ_p = ∏_p b'_p ·` (lifespan expansion), with run charge `V_i^{−r}/((p+1) b'_p)` | `mem:orphan-identity`, `mem:prefix`, `mem:suffix`, `mem:run-charge` | exact |
| M2 | with global birth distinctness, the lifespan expansion equals `⟨𝐛, 𝒢₀ ℰ₀ 𝒢₁ ⋯ ℰ_{N−1} 𝒢_N 𝐛⟩` on the memory space `mem:hilbert-space` | `mem:operator-history`, `mem:rho-cancellation` | exact; `‖𝐛‖² ≤ 2^{KM}` |
| M3 | inserting the cap `Π_{B_m}` costs `≤ 2^{−B_m + KN} exp(O(L)) ≤ exp(−L²/2)` | `mem:truncation-error` | explicit |
| M4 | `‖𝒢_j‖ ≤ C_K` (weighted Schur, weight `v₀^{k_tot}`, `ρ² > √q`); crude edge row and column `≤ C_K B_m^K (1 + L^{3A₀}) ≤ L^{C_e}` | `mem:ghost-row`, `mem:ghost-column`, `mem:edge-crude` | `C_e = C(K, A₀, q)` |
| M5 | at a good source, the lattice block has box sides `A'B' ≤ C Y`, `A', B' ≤ Y^{0.9}` | `mem:lattice-shape` | test (i), Dirichlet approximation |
| M6 | clean edge: `‖ℰ^{clean}‖ ≤ C_K (1 + log Y)(L^{−A₀} + Y^{−0.1}) ≤ L^{−G−1/2}` | `mem:clean-bound` | `A₀ = G + 1`; Gram bound `mem:bilinear-gram`; Fourier in the product variable |
| M7 | dirty raw: `≤ C_K √ε_K`, `ε_K = C_K (B_m/M^K + B_m^K e^{−L^{0.1}/4})`, so `≤ C_K L^{1 − .005K} + o(L^{−G}) ≤ L^{−G−1}` | `mem:epsilon`, `mem:raw-dirty-norm` | test (ii); `.005K ≥ G + 3` |
| M8 | dirty comparison: `≤ (ζ_K L^{C_e})^{1/2}`, `ζ_K = C_K L^{3A₀} B_m^K (p_min^{−1} + Y^{−0.2}) ≤ e^{−L^{α₋}/2}` | `mem:comparison-small` | line count `mem:line-count` |
| M9 | `‖ℰ_j‖_{ℋ_{B_m}} ≤ L^{−G}` | `mem:signed-edge` | M6 + M7 + M8, with `4^K` pieces |
| M10 | restoring distinctness: partition identity over equality systems; rank `≥ r₀` absolute, `≤ L^{C(N+1)} (C_K Q_birth² e^{−L^{α₋}})^r` summed `≤ L^{−(E₀+2)N}`; rank `< r₀` signed, `≤ C_K^{N+1} L^{−GN + 2(C_e + G) r} 2^{KM}` summed `≤ L^{−(G−2)N}` | `mem:partition-identity`, `mem:high-rank`, `mem:low-rank` | `Q_birth ≤ L⁴`; `r₀ = o(N / log L)`; `C_K^{N+1} = L^{o(N)}` |

Since `G − 2 = E₀ + 2`, both rank ranges give `L^{−(E₀+2)N}`. In Lean: M0 enters as
`1/2 ≤ V_i ≤ 1` and `b'_p ≥ 1/2` (`Moment/Phased/Ghost.lean`, `Moment/Edge/Measure.lean`); M1 is
`Moment/PrimeFactor.lean`; M2 is S3 of §12; M3 is `Moment/Truncation.lean`; M4 is
`exists_phasedGhost_normLe` and `exists_phasedEdge_normLe` (`Moment/Phased.lean`); M5 is
`exists_lattice_box` (`Moment/Edge/Lattice.lean`); M6–M9 are §16; M10 is §13.

The uniformity in `ϱ` is PD's claim (§4.5, after `mem:lattice-shape`, and §4.8). The
proof never uses integrality of the root, only the identity `r_{gz} = τ(w)/τ(z)` and
`det g = 1`.

### 5.6 Goodness removal and pad stripping (2c) [PD §4.9]

**Lemma 5.6.** Eventually, `|E_Y| ≤ C_K X Y L^{4C + 1 − E₀} = C_K X Y L^{−D₁ − 1}`, where
`E_Y` is the coprime-pair error of §5. The pieces:

- **Goodness (`eventually_goodness_removal`).**
  `|⟨f, 𝒯 g⟩ − ⟨f, 𝒜 g⟩| ≤ C_K U V L^{4C + 3A₀} e^{−L^{α₋}/8}`, which is below every power
  of `L` times `UV`. PD derives this from Lemma 5.3, the one-edge Lemma 5.4, and
  `mem:one-edge-label-mass`. The Lean proof counts the bad states directly (§14).
- **Pad collisions.** The probability is `≤ C_K M² e^{−L^{α₋}}`, against the absolute raw
  square `≤ C_K X Y L^{4C + 3}` and the absolute comparison square
  `≤ C_K X Y L^{4C + 3 + 3A₀}` (`Decomposition/Collision.lean`).
- **Sum over pad dyads.** Use Lemma 5.1 with `U V = d₀ Y X`, over the `O(L)` dyads `d₀`.
- **Shared parts.** Lemma 1.2 and `mem:unshared-collisions`, both
  `≤ C_K X Y L^{4C + 3 + 3A₀} e^{−L^{α₋}}`.

Theorem 2 follows.

---

## 6. Interface 3: the major term [PD §5]

**Theorem 3 (`eventually_majorSquare` in `Major.lean`).** Assume P4 with
`(A₀, B, A, c₄)` and (G) with `(B, c_G)`. Then there is `C₃` such that, eventually, for
every dyadic `Y`, `|Q_Y^{maj}| ≤ C₃ X Y L^{−D}`.

§§6.1–6.3 follow PD. §6.4 describes where the Lean proof departs from PD's route.

### 6.1 Mean values: PD Lemma 2.2 [PD]

These are proved with explicit constants in `Analysis/Divisor.lean`.

- `∑_{n ≤ Y} τ(n)² ≤ Y (1 + log Y)³` (`sum_card_divisors_sq_le`).
- For `P(t) = ∑_{n ≤ Y} c_n n^{it}` and an interval `I` of length `T`:
  `∫_I |P|² ≤ (T + 8Y(1 + log Y)) ∑|c_n|²` (`integral_norm_dirichlet_sq_le`).
- For 1-separated `𝒯 ⊂ I`, the same with the extra factor `2(1 + log Y)²`, by
  one-dimensional Sobolev (`sum_norm_dirichlet_sq_le`).

The constants do not depend on the coefficients. This matters in Lemma 6.2, where the
polynomial is raised to a growing power.

### 6.2 Sparse frequencies: Lemma 5.3 from (G) [PD, with (G) for (5.13)/(5.14)]

**Lemma 6.2 (`Major/Sparse.lean`).** Let `exp(L^{α₋}) ≤ P ≤ exp(2L^{α₊})`, let 𝒫 be any
set of primes in `[P, 2P)`, let `ξ ∈ ℝ`, and let `χ` be any character. Put
`P_s(t) = P^{−1} ∑_{p ∈ 𝒫} χ(p) p^{i(t + ξ)}`. The unit intervals meeting
`{|t| ≤ 2 X L^B : |P_s(t)| > L^{−A_s}}` form a family 𝓘 with:

- `|𝓘| ≤ exp(C L^{0.91})` (`card_sparseSet_le`), by `P_s^j` with
  `j = ⌊log 4XL^B / log 2P⌋`, `∑|c_n|² ≤ j^j 3^j P^{−j}`, and §6.1 applied to the two
  parity classes of intervals, which are 1-separated;
- `∑_{I ∈ 𝓘} sup_I |N_β|² ≤ C L^{2C+1}` (`sum_norm_sq_le_of_sparse`).

For the second bound, choose `t_I` in the closure of `I`. By the `TT*` bound it suffices to
bound the absolute row sums of the Gram matrix
`G_{IJ} = ∑_{⌈H_n⌉ ≤ n ≤ ⌊2H_n⌋} n^{i(t_I − t_J)}`. Its entries are at most `H_n + 1`, which
is used for adjacent intervals. Otherwise `1 ≤ |t_I − t_J| ≤ 4 X L^B + 2`, which is
exactly (G)'s range, so `|G_{IJ}| ≤ c_G H_n (|Δ|^{−1} + e^{−L^{0.95}})`. The row sums are
`≤ C H_n L`, and `‖β‖² ≤ (H_n + 1) L^{2C}`. Both bounds are uniform in `ξ`, the characters
and the prime set.

### 6.3 Separation and assembly [PD]

1. **Arcs and characters.** `𝔐` is a disjoint union of `≤ L^{2A₀}` arcs. On the arc
   `h/k + λ/Y`, every variable is a unit mod `k` (B2 and roughness). The function
   `e(h(bmn − ars − b + a)/k)` expands into `≤ φ(k)⁶ ≤ L^{6A₀}` six-fold character products
   with coefficients of modulus `≤ 1` (`Major/Characters.lean`, `Major/Arcs.lean`).
2. **Mellin separation (`maj:Mellin-separation`, (5.15)).**
   `ψ_λ(X(w − w')) = X^{−1} ∬ F_λ(t/X, s') w^{it} w'^{i(s'−t)} dt ds'` for
   `w, w' ∈ [1, 16]`, with
   `|F_λ(v, s')| ≤ C_j (1 + |v|/L^{B₀})^{−j} (1 + |s'|/L^{B₀})^{−j}`. This is the 2-D
   Fourier inversion of `(ζ, z) ↦ ψ_λ(X e^z (e^{ζ/X} − 1))` times fixed cutoffs. Its
   derivatives of order `r + s` are `≤ C_{r,s} L^{A₀ (r+s)}`, so `B₀ = A₀ + 1` works. The
   Lean proof uses order-2 decay instead (§6.4).
3. **Normalization.** `(YX)² · X^{−1} · Y^{−1} = XY`. The pointwise bounds are `|B_λ| ≤ 4`
   and `|Q_{b'}| ≤ 8` (B3). For any interval `I` of length `Z`, `maj:product-mean`, (5.19),
   gives `∫_I |M_α N_β|² ≤ C L^{C₄}(1 + Z/X)` (`Major/Energy/Mean.lean`).
4. **Truncation.** Restrict to `|s'| ≤ L^B` and `|t| ≤ X L^B`, using `B = B₀ + 2` and the
   decay with `j` large. The Lean proof controls the tails by mean values instead (§6.4).
5. **Energy (`maj:energy`, (5.21)).** `∫_{|t| ≤ 2XL^B} |B_λ M_α N_β|² ≤ L^{−A'}` suffices.
   The total loss is `L^{9A₀}` (arcs, characters, `λ`) times `L^B` (`s'`) times
   `L^{(C₄ + B + 1)/2}` (the `Q'` mean square), which fixes `A'`.
6. **Isolated energy.** Peel one prime `p ∈ 𝒫₁`, split into `O(L)` dyads, and use the
   Mellin bound `∫ |f̂_λ| ≤ C L^{2A₀}` with Minkowski. Then `∫ |P_s M_α N_β|² ≤ L^{−A''}`
   suffices, uniformly in `ξ`. The Lean proof replaces Minkowski by Cauchy–Schwarz in `ξ`
   with the weight `|f̂_λ|`, and Fubini (`Major/Energy/Average.lean`).
7. **The split (`maj:isolated-energy`, (5.22); `Major/Energy/Isolated.lean`).**
   - On `|P_s| ≤ L^{−A_s}`, the bound is `L^{−2A_s} · C L^{C₄}(1 + 4L^B)`.
   - On 𝓘, it is `4 (c₄ L^{−A})² C L^{2C+1}`, by P4 at `|t| ≤ 2 X L^B` with modulus
     `k ≤ L^{A₀}`, and Lemma 6.2.
   - The table's `A_s` and `A` make both `≤ L^{−A''}/2`.

### 6.4 The Lean route: low-order decay and a larger `B` [new]

PD's step 4 needs decay `(1 + |s'|)^{−j}` of every order. That needs bounds on iterated
derivatives of the composite `ψ_λ(X e^z (e^{ζ/X} − 1))` of every order. H1 lets us choose
`B`, so order-2 decay suffices if the tails are controlled by mean values on dyadic
intervals instead of pointwise bounds.

**Separation lemma (`exists_plateauTwist_separation` in `Major/Mellin.lean`).** For
`|λ| ≤ Λ`, `Λ ≥ 1`, `X ≥ 2`, there is `K_λ` with
`ψ_λ(X(w − w')) = ∫∫ K_λ(τ, σ) w^{iτ} w'^{iσ} dσ dτ` for `w, w' ∈ [1, 16]` and
`|K_λ(τ, σ)| ≤ C₀ Λ⁴ X^{−1} (1 + |τ|/X)^{−2} (1 + |τ + σ|)^{−2}`.

*Proof.* Use 2-D Fourier inversion of `Φ(ζ, z) = ψ_λ(X e^z (e^{ζ/X} − 1)) ρ(z) χ(ζ)`, with
fixed cutoffs. With `y = X e^z (e^{ζ/X} − 1)` we have `∂_z y = y` and
`∂_ζ y = e^z e^{ζ/X}`, which is bounded. So the mixed partials `∂_ζ^a ∂_z^b Φ` with
`a, b ≤ 2` are `O(Λ⁴)` uniformly in `X`, which gives
`|Φ̂(v, s)| ≪ Λ⁴ (1+|v|)^{−2} (1+|s|)^{−2}`. The substitution `τ = 2πXv`, `σ = 2πs − τ`
gives `K_λ = Φ̂ / ((2π)² X)`. The plane transform and its inversion are in
`Major/Mellin/Plane.lean`, and the derivative bounds in `Major/Mellin/Kernel.lean` and
`Major/Mellin/Smooth.lean`.

Also needed is the 1-D Mellin form of `f_λ(y) = η(y) e(−λy)` (`exists_bumpTwist_mellin`):
`f_λ(y) = ∫ g_λ(ξ) y^{iξ} dξ` for `y > 0`, with `∫ |g_λ| ≤ C₀ (1 + |λ|)²`. This is
`ft_inversion` (`Analysis/Fourier.lean`) applied to `z ↦ f_λ(e^z)`.

**One arc term (`norm_arcTerm_le` in `Major/Assembly.lean`).** Fix the arc `(k, h)`,
`θ = λ/Y` with `|λ| ≤ 2L^{A₀}`, and the characters of the expansion. The term is
`(XY)² ∫∫ K_λ(τ, s − τ) Q(τ) Q'(s − τ) dτ ds`, with `Q = B_λ^{χ₁} M^{χ₂} N^{χ₃}`. Its
pointwise bound is `|Q| ≤ 16 L^{2C}`, and `∫_I |Q|² ≪ L^{C₄} (1 + |I|/X)` on every
interval. With `T = XL^B` and `E = ∫_{|τ| ≤ T} |Q|²`, the integral splits into two regions
(`Major/Regions.lean`):

- **Main**, `|τ| ≤ T`. Substitute `s = τ + σ` and integrate in `s` last, against
  `∫ (1 + |s|)^{−2} ≤ π`. For fixed `s`, use `2|Q Q'| ≤ ε|Q|² + ε^{−1}|Q'|²` with
  `ε = L^{A' − P}`, `P = D + 13A₀`; the bound is `ε E + ε^{−1} L^{C₄}(1 + 2T/X)`, up to
  constants.
- **`τ`-tail**, `|τ| > T`: dyadic `Z ≥ T`, with `(1 + |τ|/X)^{−2} ≤ (X/Z)²` on `[Z, 2Z]`.
  The bound is `8 L^{C₄} X/T = 8 L^{C₄ − B}`, up to constants.

The bound on `|τ| ≤ T` is uniform in `s`, so no separate `s`-tail is needed. Each arc term
is `O(XY² L^{10A₀ − P}) = O(XY² L^{−D − 3A₀})` (`arcBound_le`).

**Parameters.** Summing over the arcs (`≤ L^{2A₀}` of them, each of length `4L^{A₀}/Y`)
and the `≤ L^{6A₀}` character tuples requires `[⋯] ≤ L^{−D − 13A₀}`. This gives:

| Name | Value |
|---|---|
| `B` | `D + 13A₀ + C₄` |
| `A'` | `4(D + 13A₀) + 3C₄ + B` |
| `A''` | `A' + 4A₀ + 4` |
| `A_s` | `(A'' + C₄ + B + 2)/2` |
| `A` | `(A'' + 2C + 4)/2` |

These are the values of §1. They depend only on `(D_*, C)`.

**Energy (`eventually_energy_le` in `Major/Energy.lean`).** `E ≤ L^{−A'}`, as in §6.3
steps 6–7:
- Mellin-separate `η(b/Y) e(−λb/Y)` with `g_λ`.
- Split band 1 into `O(L)` dyads `[P, 2P)`. For each, write `b = p b'`, with
  `|Q_{b'}| ≤ 8`.
- On `{|P_s| ≤ L^{−A_s}}` use the mean value. On the sparse family use P4,
  `|M| ≤ c₄ L^{−A}` for `|t| ≤ 2XL^B`, together with Lemma 6.2 for `∑ sup |N|²`.

---

## 7. Assembly

`oneSidedTypeII` (`Erdos408/OneSided.lean`) takes the §1 values. Given `K ≥ K₀`, `g`, `c₄`
and `c_G`, Theorem 2 (`eventually_replacement`) and Theorem 3 (`eventually_majorSquare`)
give, eventually,
`Q_Y ≤ |Q_Y − Q_Y^{maj}| + |Q_Y^{maj}| ≤ (|C₂| + |C₃|) X Y L^{−D₁}` for every `Y`.
Theorem 1 (`cauchy_reduction`) then gives `|S| ≤ C₁ X L^{−D_*}`.

---

## 8. Where the band exponents enter (O3 checklist)

| Site | Needs | Supplied by |
|---|---|---|
| `𝒲` expansion into label products | disjoint bands | B1 |
| squareful error, shared labels, pad and unshared collisions | `∑ p^{−2}`, `sup μ` | B4 |
| `Y`-range `det:Y-range`, pad dyads | label-product sizes | B5 |
| roughness: `G(Dbm) = Db`, damping 1, primitivity, units mod `k` | band primes `< W` and `> L^{A₀}` | B2 |
| `V_i` bounded above and below (`∏V^{−2}`, ghost bounds, `ν/μ`) | Mertens uniform in `a ≥ α₋` | B3 |
| Lemma 3.2 test (ii) | `∑_{i<i_*} L^{a_i} = o(L^{a_{i_*}})` | B6 (gap) |
| `ε_K` exceptional mass | `e^{−L^{a_{i_*}}/4} ≤ e^{−L^{α₋}/4}` | window |
| dirty-edge separation `mem:anchor-congruence` | `p_* ≥ exp(L^{a_{i_*}})` | definition of `band` (exact) |
| `|𝒫_i|` in budgets | `≤ exp(2L^{α₊})` | B4 |

**O3 is closed.** Every threshold depends on the bands only through `K, g, α₋, α₊`.

---

## 9. Deviations from PD and their justification

1. **Explicit exponents** (§1). PD fixes only their order. This makes the Lean
   `∃ K₀ A₀ B A` concrete.
2. **Explicit budgets in Lemma 3.4** (§5.4), closing O1. The grid side is `m_*^{−1/40}`
   instead of `x^{−c_δ/8}`.
3. **Riemann-sum model** (§5.4). PD integrates over the archimedean root; since the §4
   bound is pointwise, a sum over grid cubes suffices and avoids measure theory.
   `c₂ = ∑ μ(l)/l²` replaces `1/ζ(2)`.
4. **Discrepancy by completion** in Lemma 3.3 (§5.2). PD sandwiches interval indicators by
   smooth bumps and bounds Fourier tails. Finite Fourier analysis on `(ℤ/m₁)²` gives the
   discrepancy using only finite sums, and the constant `c₂/|SL₂(ℤ/S)|` is identified by
   summing over residue classes.
5. **Uniformity in the band exponents** (§2, §5.3, §8), closing O3.
6. **Smooth partition** `η = s(y) − s(y/2)` from `Real.smoothTransition`. PD only asks for
   a smooth dyadic partition.
7. **Order-2 Mellin decay and a larger `B`** (§6.4). Tails are controlled by mean values on
   dyadic intervals, so only second derivatives of the kernel are bounded. The energy of
   an average uses Cauchy–Schwarz instead of Minkowski (§6.3 step 6).
8. **Goodness removal by counting** (§14). PD uses the one-edge root replacement; the Lean
   proof counts bad positions with the root residues.
9. **Finite phases and rank cut** (§13). The circle integral of `mem:local-phases` is a
   finite Fourier average, and the rank cut is `r₀ = ⌈L^{9/20}⌉`.

None of these changes a statement that the rest of the argument consumes.

---

## 10. The §4 representation

PD §4 works on a symmetric memory space with operators given by their actions on
histories. The Lean proof represents them as follows.

- **Memory states are multiplicity functions.** One particle type `X` covers all groups,
  since the bands are disjoint. A memory state is `S : X → ℕ`, weighted by
  `memWeight ν S = ∏_x ν(x)^{S x} / (S x)!`. This is PD's symmetric space with measure
  `λ^{⊗k}/k!`, with each symmetric function read as a function of its multiset
  (`Memory/Space.lean`). The cap `Π_B` restricts to total size at most `B`, so the space is
  finite and no completion or topology is needed.
- **Every operator is a choice operator**, `(Tf)(i) = ∑_{c ∈ cs} a(i, c) f(out(i, c))`
  (`choiceOp`). Fresh labels, target positions, store subsets, promotions and slot
  symmetrizations are all finite choices with coefficients. Index choices among repeated
  values become binomial coefficients in the coefficient.
- **Norms** use the predicate `NormLe μ ν T c` on weighted `ℓ²` (`Analysis/Schur.lean`),
  not Mathlib's operator norm. Its tools are `normLe_choiceOp`, the weighted Schur test PD
  uses throughout §4 (`mem:schur-weight`), and `NormLe.comp`. Matrix elements
  `⟨𝐛, T 𝐛⟩` are bounded through `wnormSq` and Cauchy–Schwarz
  (`norm_sum_mul_le_of_normLe`).
- **Histories are definitional.** `choiceOp_comp` shows that a composite of choice
  operators is the choice operator over pairs of choices. So `⟨𝐛, 𝒢₀ ℰ₀ ⋯ 𝒢_N 𝐛⟩` expands
  as a sum over choice histories, and the two history arguments become manipulations of
  one finite sum:
  - M2 says that, restricted to histories with distinct births, this sum equals the
    lifespan expansion;
  - M10 inserts the partition identity into the same sum.

  PD's operator identity is therefore kept. Direct induction along the path is not
  needed.
- **The clean edge** is the one bound that is not a Schur test. It is proved for kernels
  on finite index sets (`KerLe`, `Moment/Edge/Operator.lean`) by Fourier analysis in the
  unrestricted product variable: Parseval's identity over one period (`kerLe_parseval`,
  `Moment/Edge/Parseval.lean`), the Fourier expansion of the cutoff
  (`exists_kerLe_cutoff`, `mem:cutoff-fourier`), and the bilinear Gram bound in between
  (`Moment/Edge/Gram.lean`). All supports are finite.

**Facts about PD §4 checked in this representation.**

- With multiplicities, the ghost coefficient factors over particles. A particle with `h`
  hits, `d` deleted and `n` created carries `C(h, d) del^d surv^{h−d} (cre ν)^n / n!`. The
  row sum is then the binomial theorem times an exponential series, giving `mem:ghost-row`
  exactly. The column sum, by the factorial identity
  `ν^s/s! · C(s, d) · ν^n/n! = ν^t/t! · ν^d/d! · C(t, n)` with `s − d = t − n`, is the
  adjoint ghost of `mem:ghost-factorial`, giving `mem:ghost-column` exactly (`ghost_col`,
  `ghostOp_normLe` in `Memory/Ghost.lean`).
- The adjoint identities with repeated pending values (PD §4.3) are `ghost_col` for the
  ghost. The edge case is the same computation with one promoted index, a factor
  `C(m, 1) = m` (`crudeWeight_le_col` in `Moment/Phased/Edge.lean`, and `Moment/Edge/RawCol.lean`).
- The `ρ`-cancellation (`mem:rho-cancellation`, PD §4.2) is the arithmetic
  `ρ (q/ρ²) ρ = q`, together with the birth and termination factors
  (`Moment/Chain/GhostStage.lean`).
- A rank-`r` system modifies at most `2r` operations (PD §4.8): a block system of rank `r`
  has at most `2r` addresses (`card_biUnion_le_two_mul_blockRank`), and the phased ghost
  needs no symmetrization (§13).
- Removing the cross-edge ban on the clean edge (PD §4.5) costs a coincidence `a_i = b_i`,
  with weighted Schur sides `16 (1 + 52 L^{3A₀}) K 4^K sup ν` (`Moment/Edge/Clean.lean`).

---

## 11. Lean architecture for the moment (leaf C)

The moment bound `eventually_detMoment` is root replacement (Lemma 3.4) followed by the
memory bound (§4). Both are stated about one object: the lift over a **position model**
(`Model.lean`).

**Position models.** A position model (`PosModel`) consists of:
- a finite type `Pos` of positions;
- `det : Pos → Pos → ℤ`;
- a predicate `FirstDvd p P`, meaning "`p` divides the first coordinate";
- a ratio `ratio : Pos → ℝ`, meaning `r_P`.

`rowOp`, `symOp`, `goodOp`, `edgeOp` and the moment are defined once, over any model. The
state measure is constant, so adjoints are conjugate transposes. The two instances:

- **Physical** (`physModel`): `Pos` = the primitive positions in `Ω`, `det` as in §4,
  `FirstDvd p P ⟺ p ∣ P₁`, `ratio = rootRatio`. Its operators are those of `Lift.lean`
  (`detMoment_eq_sum_moment`).
- **At a root `ϱ = (u, v, r)` with lines `ℓ`** (`rootModel`): `Pos` = the primitive
  `z ∈ ℤ²` with `g(ϱ) z ∈ Ω` (`rootPositions`; `(gz)₁ = u τ(z)`,
  `(gz)₂ = v τ(z) + z₂/u`), `det(z, z')`, `FirstDvd p z ⟺ [z]_p = ℓ_p`, and
  `ratio z = τ(w_z)/τ(z)` with a canonical complement `w_z`. The lines are
  `ℓ ∈ ∏_{p band prime} ℙ¹(𝔽_p)`, encoded as `ℓ p ∈ {0, …, p}` (`lineOf`,
  `Moment/Lines.lean`). The root moment `rootMoment` is `⟨u_{e₁}, (𝒜𝒜ᴴ)^R u_{e₁}⟩`.

Models are compared with ratios modulo `ℤ`, since the good-state tests are invariant under
adding an integer to the ratio.

**Three statements.**

1. *Reindexing (exact; `detMoment_eq_sum_rootMoment` in `Moment/Reindex.lean`).* For an
   integer root `g` with lines `ℓ(g)`, the map `z ↦ g z` is an isomorphism of models
   (`PosModel.Iso`) onto the physical positions: it preserves `det`, divisibility and
   ratio. Hence `detMoment = ∑_{P₀} rootMoment(g(P₀), ℓ(g(P₀)))`. The general lemma is
   that isomorphic models have equal moments, by relabeling a matrix power
   (`PosModel.Iso.moment_eq`).
2. *Root replacement (Lemma 3.4; `eventually_root_replacement`).*
   `(UV)^{−1} ∑_{P₀} rootMoment(g(P₀), ℓ(g(P₀)))` is within `exp(−L^{0.76})` of
   `c₂ ∑_{cubes Q} vol(Q) 𝔼_ℓ rootMoment(ϱ_Q, ℓ)` (`rootRiemannSum`). The proof is §5.4
   and §15:
   - expand the matrix power into paths, each a product of box, good, line and edge
     factors;
   - apply Bonferroni to the damping;
   - apply Lemma 3.3 per monomial and per cube;
   - bound the boundary cubes.
3. *Memory bound (§4; `eventually_norm_lineAverage_le`).* For every real root `ϱ` in the
   box, `|𝔼_ℓ rootMoment(ϱ, ℓ)| ≤ L^{−(E₀+1)N}`. This is proved on the memory space of
   §10 (multiplicity functions, choice operators, `NormLe`), via M0–M10 (§§12–13).

Leaf C follows, since `∑ vol(Q) = 15` and `c₂ ≤ 2`.

**Leaf B (goodness removal)** is proved by counting on the physical model (§14), and
**leaf A** (lift identity and collisions) is combinatorics on the physical model alone
(`Decomposition.lean`).

---

## 12. The memory chain in Lean

All objects are at a fixed real root `ϱ` (positions `𝒵 = rootPositions`) and a fixed
`d, Y, d₀`. Put `N = 2R` and `η'_j = 1 − q_j`, with `q_0 = q_N = √q` and `q_j = q`
otherwise.

**S1 (path expansion; `lineAverage_rootMoment_eq` in `Moment/PathExpansion.lean`).** The
line average of the root moment is
`σ ∑_{π : s₀ → ⋯ → s_N, z₀ = z_N = e₁} ∏_{j<N} A⁰(s_j, s_{j+1}) · ∏_p E_p(π)`.
- `A⁰` is the line-free edge operator, `freeRootModel.edgeOp` at `q = 1`. It is Hermitian
  (`Moment/PathExpansion/Hermitian.lean`), so both orientations of the alternating product
  give the same kernel.
- `E_p = primeFactor p N (lines along π) η' (active visits of p)`.
- The hypotheses are disjoint bands and `e₁ ∈ 𝒵`.

The fixed-line form, before averaging over `ℓ`, is `rootMoment_eq_sum_lineFactor`. Generic
facts on paths in matrix powers are in `Moment/PathExpansion/Paths.lean`, and averages of
products over independent lines in `Moment/PathExpansion/Average.lean`.

**S2 (primewise identities; `Moment/PrimeFactor.lean`).** The orphan identity
(`primeFactor_eq_orphan`), the active case (`primeFactor_eq_active`), and the prefix and
suffix telescoping (`prod_one_sub_eq_prefix`).

**Particles and memory.** A particle (`Particle`) is a pair `(p, ℓ)` with `p` a band prime
and `ℓ ≤ p`. The particle hits `z` when `lineOf p z = ℓ`. A memory state is a multiplicity
function `S` on particles. For the exact identity the cap is the number of band primes
(`memCap`): with distinct births, no prime is pending twice. The measures are:
- `ν_i(p) = 1/(V_i (p+1) b'_p)`, with `b'_p = 1 − (p+1)^{−1} ∑_{j ≤ N} η'_j`;
- `memWeight` uses `ν` for each particle;
- active lists `act ∈ lists x d J` carry `∏_{i,h} ν_i(act_{i,h})`;
- positions carry counting measure.

The product of these is `chainMeasure`.

**The ghost `𝒢_j` (`chainGhost`).** This is `Memory/Ghost.lean` applied fiberwise in
`(z, act)`, with `hit = hits z`, `del = −η'_j/ρ`, `surv = q_j/ρ²`,
`cre(p, ℓ) = −η'_j V_{grp p}/ρ`, and `ν(p, ℓ) = ν_{grp p}(p)`. Fix `0 < ρ < 1` with
`ρ² > √q`.

**The edge `ℰ` (`chainEdge`)** is the same at every `j`. From the source `(z, act, S)`, a
choice consists of:
1. a source symmetrization `σ`, with weight `M!^{−K}`; the unshared source slot of group
   `i` is `(act ∘ σ)_{i, last}`;
2. a set `St ⊆ Fin K` of groups whose unshared source prime `p_i` is stored as the particle
   `(p_i, [z]_{p_i})`; the other unshared source slots are dropped;
3. a target `z' ∈ 𝒵`;
4. for each group `i`, a new label, which is one of:
   - a **promotion** of a particle `x = (p, ℓ)` in `S` (not one just stored) with
     `p ∈ band_i` and `x` hitting `z'`, with weight `S(x) / V_i` (the factor `S(x)` counts
     the index choices);
   - a **fresh** prime `p ∈ band_i`, with weight `ν_i(p)`;
5. a target symmetrization `σ'`, with weight `M!^{−K}`.

The output is `(z', act', S')`, where `act'` is the copied pad slots plus the new labels,
reordered by `σ'`, and `S' = S − promoted + stored`. The coefficient is
`ρ^{hits(S, z)} · ρ^{hits(S', z')} · κ(det(z, z')/D; b, a)` times the weights above, times
the restrictions. Here `κ` is the line-free row kernel without `∏V^{−1}`, which the
weights supply. The restrictions are:
- the cross-edge ban: new labels avoid every source label;
- the target lists are distinct;
- `D ∈ [d₀, 2d₀)` and `D ∣ det`;
- both ends are good.

Forgetting the stored groups and the promotion flags leaves a free choice, and `A⁰` is the
choice operator over free choices (`Moment/Chain/Free.lean`).

**Boundary vector.** `𝐛(z, act, S) = [z = e₁ ∧ S = 0]` (`chainInit`).

**Histories and births.** A history (`History`) is a ghost choice at each of the `N + 1`
visits and an edge choice at each of the `N` edges (`chainVisit`, `chainWeight`,
`chainEnd`). `chainProduct_eq_sum_history` is the history expansion. The births sit at
fixed addresses (`BirthAddr`):
- the `KM` initial slots, always performed;
- the label of each group at each edge, performed when it is fresh;
- the first `B` batch indices of each ghost, performed up to the batch length, with the
  batch primes listed in increasing order (`batchPrimes`).

**S3 (memory identity; `lineAverage_rootMoment_eq_chain` in
`Moment/Chain/Identity.lean`).** `lineAverage(rootMoment) = (∏_p b'_p) · distinctSum(memCap)`,
where `distinctSum(B)` is `∑_s μ(s) 𝐛(s) ∑_h w(s, h) 𝐛(end)` over the histories with
pairwise distinct performed births, with memory cap `B`. The cap `memCap` is the number of
band primes, which distinct births never exceed.

*Why not a born set in the state.* Recording the born primes in the chain state would make
distinctness a local restriction, but it breaks both later steps. The final vector then
sums over all born sets, so its norm carries a factor `2^{#band primes}`. And the future
then depends on the fresh labels, which destroys the Fourier cancellation of the clean edge
(M6). So, as in PD, distinctness is imposed on histories and restored by the rank expansion
of §13.

The proof composes S1 and S2 per prime and matches each `(π, lifespan choices)` with a
unique history:
- store on leaving a nonfinal active run, promote on entering the next;
- create and delete at the ghost endpoints;
- pending hits pay `ρ · (q_j/ρ²) · ρ = q_j`.

Each prime is born once, paying its line probability and baseline `1/((p+1) b'_p)` through
`ν`. In Lean the global distinctness becomes a running condition along the history
(`distinctFold`, `Moment/Chain/Births.lean`). Each prime then has a status: active,
pending with an anchor, dead or unborn (`Moment/Chain/Status.lean`). Its lifespan value
is the total weight of its future (`Moment/Chain/Lifespan.lean`). The ghost step
(`ghost_stage`, `Moment/Chain/GhostStage.lean`) and the edge step (`edge_stage`,
`Moment/Chain/EdgeStage.lean`) reproduce these values. A backward induction on the
remaining edges (`distinctFold_eq_path`, `Moment/Chain/Induction.lean`) gives S3.

**Then, M3–M10.** These are as in the §5.5 table, on this chain:
- truncation to `B_m = ⌈L²⌉`;
- the ghost and crude edge bounds by `normLe_choiceOp`;
- the clean edge by Fourier (§10);
- dirty raw and comparison edges by Schur;
- restoring distinctness by the partition identity on birth addresses. With
  multiplicities, an address is (operation, slot), or (ghost operation, particle, copy
  index).

---

## 13. The memory bound in Lean

`Moment/Memory.lean`. With `B = ⌈L²⌉` (`truncCap`):

- **M3** `eventually_distinctSum_truncation`:
  `|distinctSum(memCap) − distinctSum(B)| ≤ exp(−L²/2)`. A history that reaches memory size
  above `B` has more than `B − KN` ghost births; insert `2` per ghost birth in an absolute
  majorant (PD `mem:truncation-error`). The cap change is in `Moment/Truncation/Cap.lean`
  and the majorant in `Moment/Truncation/Majorant.lean`.
- **M4–M10** `eventually_norm_distinctSum_le`: `|distinctSum(B)| ≤ 2 L^{−(E₀+2)N}`.
- `eventually_norm_lineAverage_le` follows, using `|∏ b'_p| ≤ 1` and S3 under the
  hypotheses `hdisj` (B1), `hbig` (band primes exceed `N`, from B2) and `hV` (B3), which all
  follow from `Admissible`.

**M10 in Lean.** The rank expansion (`Moment/Rank.lean`) works on the births
`β : BirthAddr → Option ℕ` of a history.

1. *Partition identity* (`Memory/Partition.lean`, generic, on any finite address type):
   `[β injective on performed addresses] = ∑_𝒞 ∏_{C ∈ 𝒞} (−1)^{|C|−1} (|C| − 1)! · ∏_C [E_C]`,
   over collections `𝒞` of disjoint non-singleton blocks, where `E_C` says that every
   address in `C` is performed and all share one prime. Rank `r(𝒞) = ∑ (|C| − 1)`. The
   total coefficient mass at rank `r` is at most `Q^{2r}`, with `Q = |BirthAddr| ≤ L⁴`
   (`distinctSum_eq_sum_blockSum`, `norm_sum_blockCoef_mul_le`).
2. *High rank, absolute* (`exists_realized_history_le`, `Moment/Phased/HighRank.lean`).
   For a fixed `𝒞` of rank `r`, `∑_s μ 𝐛 ∑_h |w| ∏_C [E_C] ≤ L^{C(N+1)} (C_K Δ)^r`. Instead
   of conditioning chronologically on the pivot values, sum over them: for fixed values
   every address carries a prescription, and a row iteration
   (`Moment/Phased/Rows.lean`) charges each prescribed birth an atom of mass `≤ C ν(p)`
   (PD `mem:edge-atoms`, `mem:ghost-atoms`; `Moment/Phased/EdgeAtoms.lean`,
   `Moment/Phased/GhostAtoms.lean`).
3. *Low rank, signed* (`exists_blockPhase`, `Moment/Rank/Phase.lean`). Replace the circle
   integral of PD `mem:local-phases` by a finite Fourier average: with `P` larger than
   every band prime, `[p = p'] = P^{−1} ∑_{k mod P} e(k p/P) e(−k p'/P)`. For fixed
   frequencies every birth carries a local unimodular multiplier at the operation that
   creates it. The *phased* operators `𝒢^φ`, `ℰ^φ` (`Moment/Phased.lean`) are the chain
   operators with the birth multipliers `φ` in their coefficients. They are still choice
   operators on the same space, so the norm bounds apply unchanged:
   - `‖𝒢^φ_j‖ ≤ C_K` for all `|φ| ≤ 1` (M4, absolute; `exists_phasedGhost_normLe`);
   - `‖ℰ^φ‖ ≤ L^{C_e}` for all `|φ| ≤ 1` (crude, M4; `exists_phasedEdge_normLe`);
   - `‖ℰ‖ ≤ L^{−G}` when `φ ≡ 1` on that edge (M9 = M6 + M7 + M8, on the cap-`B` space;
     `eventually_chainEdge_normLe`).

   A rank-`r` system modifies at most `2r` operations. Since the memory is a multiplicity
   function, the phased ghost needs no symmetrization: its multiplier is a function of the
   choice alone. This gives
   `|term| ≤ C_K^{N+1} ‖𝐛‖² L^{−G(N−2r) + 2C_e r}` (`normLe_phasedProduct`), with
   `‖𝐛‖² ≤ 2^{KM}` (`wnormSq_chainInit_le`).
4. *Sum* (`Moment/Rank/Budget.lean`). Cut at `r₀ = ⌈L^{9/20}⌉` (PD uses
   `⌈C' N log L / L^{0.1}⌉`): `r₀ L^{1/10} ≥ L^{11/20}` beats `N log L`, and
   `r₀ = o(N / log L)`. The high ranks give `≤ L^{−(E₀+2)N}` (`eventually_highRank_sum_le`),
   and the low ranks `≤ L^{−GN + 2N} = L^{−(E₀+2)N}` (`eventually_lowRank_sum_le`).

The norms are taken in `NormLe` with the chain measure `chainMeasure` at both ends, for a
cap `B ≤ L³`. The chain measure is eventually nonnegative (`eventually_chainMeasure_nonneg`,
`Moment/Edge/Measure.lean`). `⟨𝐛, T 𝐛⟩` is bounded by `‖𝐛‖ · ‖T 𝐛‖` through `wnormSq` and
Cauchy–Schwarz.

---

## 14. Goodness removal in Lean

`Goodness/Removal.lean`. Leaf B splits into two statements:

- `norm_rowPairing_sub_pairing_le` (exact, no asymptotics, `x ≥ 1`). `𝒢 f` is invariant
  under list permutations, and lists have distinct entries, so `𝒮 𝒢 f = 𝒢 f` and
  `⟨f, 𝒜 f⟩ = ⟨𝒢 f, 𝒯 𝒢 f⟩` (`Goodness/Symmetry.lean`). Hence
  `⟨f, 𝒯 f⟩ − ⟨f, 𝒜 f⟩ = m ∑ f̄(s) 𝒯(s, s') f(s') (1 − g(s) g(s'))`, which is bounded by
  `stateMass · L^{4C} · badMass` (`|f| ≤ L^{2C}` at each end).
- `eventually_badMass_le`: `stateMass · badMass ≤ C₀ UV L^{3A₀} exp(−L^{α₋}/8)`
  (`Goodness/BadMass.lean`). An entry of `𝒯` is at most
  `∏ V_i^{−1} ([t = b − a] + 4 L^{3A₀}/Y)` on its support (`norm_rowOp_le`,
  `Goodness/Targets.lean`).
  - **Comparison part.** A source has at most `17 (10Y + 1)` target positions and
    `(log₂ 16U)^K` target lists at each (PD `mem:neighbor`, `mem:major-absolute`), so the
    factor `4 L^{3A₀}/Y` leaves `O(L^{3A₀} (log U)^K)` per source.
  - **Bad sources.** At fixed lists with product `G`, count the bad positions with the root
    residues (`Goodness/RootBox.lean`, `exists_card_cong_le`) at `S = G`. The counting form
    of Lemma 3.2 (`eventually_card_not_isGood_le`, `Goodness/BadCount.lean`) measures the
    ratios where test (i) fails, and applies Markov's inequality over the fresh draws for
    test (ii). The result is at most `90 UV/G · e^{−L^{α₋}/4}`, up to errors.
  - **Raw part.** At fixed lists the pairs `(P, Q)` with `det(P, Q) = D (b − a)` are
    counted jointly (`card_pairs_le`) with `S = G a`.
  - **The lists.** Their total mass is at most one (PD `mem:one-edge-label-mass`).
  - **Bad targets.** Same argument, with source and target exchanged.
  - The errors are `exp(O(L^{1/2})) UV min(U, V)^{−1/5}`, negligible since
    `min(U, V) ≥ exp(L^{0.99})`.

`eventually_goodness_removal` in `Replacement.lean` follows from these two statements and
`L^{4C + 3A₀ + D'} ≤ exp(L^{α₋}/8)`.

---

## 15. Root replacement in Lean

`eventually_root_replacement` (Lemma 5.4, `Moment/Statements.lean`) splits into exact
identities and one equidistribution estimate. The pieces are in
`Moment/RootReplacement/`.

**RR1. Integer-root reindexing (exact; `Moment/Reindex.lean`).** For a physical position
`P₀ = (u, v)`, take the integer root `g = (u c; v d)` with `c = rootC u v`, ratio
`r = c/u`, and lines `ℓ(P₀)_p = lineOf p (c, −u)`, the kernel line of the first row mod
`p`. Then `p ∣ (g z)₁ ⟺ lineOf p z = ℓ(P₀)_p`, and `z ↦ g z` is a `PosModel.Iso` from the
root model onto the physical model restricted to the paths through `P₀`. So
`detMoment = ∑_{P₀ ∈ positions} rootMoment(u, v, c/u, ℓ(P₀))`
(`detMoment_eq_sum_rootMoment`), using `PosModel.Iso.moment_eq`.

**RR2. Fixed-line path expansion (exact; `Config.lean`).**
`rootMoment(ϱ, ℓ) = ∑_ω c(ω) · A(ω, ϱ) · ∏_p λ_p(ω, ℓ_p)` (`rootMoment_eq_sum_conf`). A
*configuration* `ω` is a path of `N + 1` states over the `ϱ`-independent square
`|z_i| ≤ rootBound` (`squareModel`). `c(ω)` (`confCoeff`) holds the state mass, the
endpoint condition and the edge kernels. `A(ω, ϱ)` (`confInd`) is the box and good
indicator, which depends on `ϱ` only through the box `[z_j ∈ rootPositions ϱ]` and the
goodness of the ratio `τ(w_z)/τ(z)` at `r`. A live configuration stays in the tube (3.30)
(`Tube.lean`).

**RR3. Bonferroni (`Analysis/Bonferroni.lean`).** This is the pointwise sandwich at degree
`T = T_b = ⌈L^{0.76}⌉` for the inactive primes, `X_p = 1 − ∏_j (1 − η'_j H_j)`. The gap
`e_T(X)` is a polynomial with nonnegative coefficients. Its model mean is at most
`(∑_p 𝔼 X_p)^T / T!`.

**RR4. Root equidistribution for functions of the lines (`Residues.lean`).** Let `S` be
the product of a set of band primes, and let `G` be a function of the lines at those
primes, bounded by `‖G‖_∞`. For a box of intervals `I₁ × I₂ × I₃`:
`|∑_{P₀, ϱ(P₀) ∈ box} G(ℓ(P₀)) − c₂ UV |box| 𝔼_ℓ G| ≤ ‖G‖_∞ S⁶ · C UV m_*^{−1/5}`. This is
`abs_rootCount_sub_le` summed over the residue classes `g₀`, with `|SL₂(ℤ/S)| ≤ S⁴`.

**RR5. Lines (Lemma 5.2′; `Lines.lean`).** For `G` that depends only on the lines
`ℓ(g)_p`, `p ∣ S`: `avg_{SL₂(ℤ/S)} G(ℓ(g)) = 𝔼_{ℓ indep. uniform} G(ℓ)`.

**RR6. Cubes (`Boundary.lean`, `BoundaryCount.lean`).** On each grid cube, the archimedean
factors of a fixed configuration, namely the box and good indicators, are constant except
on boundary cubes. Boundary cubes are those meeting a box face or a good-test breakpoint of
some visit. Each face meets `O(κ^{−2} (1 + |z_{j,2}|))` cubes, with
`|z_{j,2}| ≤ 2560 N H`. The tests depend only on comparisons `‖mρ‖ ≶ θ` with
`|m| ≤ exp(C_K L^{0.21})`, each changing at most `256|m| + 1` times. So the `N + 1` visits
make at most `κ^{−2} exp(L^{1/2})` cubes bad (`badCubes`).

**Assembly.**
1. By RR1 and RR2, `(UV)^{−1} detMoment` is a sum over configurations of
   `c(ω) · (UV)^{−1} ∑_{P₀} A(ω, ϱ(P₀)) · ∏_p λ_p(ℓ(P₀))` (`Assembly.lean`).
2. Per configuration, split the primes into active and inactive and apply RR3 to the
   inactive ones (`Bonferroni.lean`).
3. Expand into monomials in the lines at `≤ K(M + N + 1) + T` primes. Per monomial and per
   cube, RR4 and RR5 replace the `P₀`-sum by `c₂ vol(Q)` times the model mean
   (`Grid.lean`, `norm_sum_positions_sub_le`).
4. The gap term, physical and model, is again handled by RR4 and RR5 per monomial, then by
   RR3's bound.
5. The budgets are the table of §5.4: the coefficient mass is in `Mass.lean`, and the
   final comparison in `Budget.lean`.

PD's one-edge version of this assembly would give the bad-mass estimate of §14; the Lean
proof uses the direct count there instead.

---

## 16. The signed edge in Lean

`Moment/Edge.lean`. Write the edge coefficient as `edgeAmp · ([t − b + a = 0] − ∫_𝔐)`
(`chainEdgeCoef_eq`). Then split the choices by the stored set `S` and the promoted set
`I` (`chainEdge_eq_parts`):

- **M6** `eventually_edgeClean_normLe` (`Moment/Edge/Clean.lean`). The clean piece
  `S = I = ∅` keeps the full kernel, i.e. the minor-arc integral. Its norm is
  `≤ L^{−G − 1/2}`, by PD `mem:lattice-shape` (M5), `mem:product-mass`,
  `mem:cutoff-fourier`, `mem:dirichlet-minor`, `mem:bilinear-gram` and `mem:minor-decay`.
  The core kernel bound is `exists_coreKer_bound` (`Moment/Edge/Core.lean`), with the
  lattice blocks in `Moment/Edge/Block.lean` and the minor arcs in `Moment/Edge/Minor.lean`.
- **M7** `eventually_edgeRaw_normLe` (`Moment/Edge/DirtyRaw.lean`). Each dirty raw part is
  `≤ L^{−G − 1}` for `K ≥ K₀`. The weighted Schur sides are `ε_K` and `C_K`
  (`Moment/Edge/RawRow.lean`, `Moment/Edge/RawCol.lean`), using `mem:anchor-congruence`
  (`Moment/Edge/Anchor.lean`) and `mem:index-damping`.
- **M8** `eventually_edgeComp_normLe` (`Moment/Edge/DirtyComp.lean`). Each dirty comparison
  part is `≤ L^{−G − 1}`. The sides are `ζ_K` and `L^{C_e}`, using `mem:line-count`
  (`card_filter_line_le`, `Moment/Edge/LineCount.lean`).
- **M9** follows by `NormLe.sum` over the `≤ 4^K` pieces
  (`eventually_chainEdge_normLe_of_parts`, which gives `eventually_chainEdge_normLe` in
  `Moment/Phased.lean`).
