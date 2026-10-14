# Blueprint: the rectangle statistic from the graph theorems

This document states the graph-paper results from which the formalization
derives the rectangle statistic `RectangleInput`, and outlines the
derivation. All three results are proved in Lean, so the compared theorems
have no hypotheses. (H1) follows PD §§3–5. (H2) follows PD §6, with its
graph input proved from the vendored formalization of WD. The block sieve
(H3) is proved directly. The analytic estimates come from the zero-free
half-plane, whose Lean proof is vendored from openai/math. The rest is
proved here too: the analytic contracts, the damped-proxy extraction of
`RectangleInput`, and the deduction of the normal order from it.

Sources. "PD" is *The Poisson–Dirichlet law for prime predecessors* and
"WD" is *Weighted dilation graphs, smooth shifted primes and totient fibers*
(OpenAI, 24 September 2026). The half-plane is Theorem 1.1 of *The
Quasi-Riemann Hypothesis* (OpenAI, 30 September 2026). Section, equation
and lemma numbers are those of the papers. "The paper" is *The normal order
of the number of iterations of Euler's function* (Plasma AI, 2026). Its
Theorem 2.1 is `RectangleInput`, and its §6 outlines the extraction that
§§2–4 below make precise.

Notation. `L = log x`, `T = log L`, `s = log T`, `W = exp(L^{0.24})`,
`V(W) = ∏_{p ≤ W}(1 − 1/p)`. An integer is *rough* if it has no prime factor
`≤ W`.

---

## 1. The three graph-paper results

- **(H1) One-sided marked Type II estimate**, `OneSidedTypeII`. It extends
  PD Theorem 3.1 to an abstract coefficient class, the shrinking scale
  `x^γ` and uniform band exponents, with the integer kernel as a premise.
  It is proved as `Erdos408.oneSidedTypeII` in `Erdos408/OneSided.lean`,
  following PD §§3–5 as restated in `one_sided_type_ii.md`.
- **(H2) Two-sided marked correlation**, `TwoSidedCorrelation`. It extends
  PD Theorem 6.1 to a joint coefficient on all slots but a spare one,
  margins `x^{cT^{−20}}`, varying inert bands, a clipped core and cutoffs
  with `T^{O(1)}` derivatives, with two analytic estimates as premises. It
  is proved as `Erdos408.twoSidedCorrelation_of_graphTransference` in
  `Erdos408/TwoSided.lean`, following PD §6 as restated in
  `two_sided_correlation.md`. Its graph input `GraphTransference` (PD
  Propositions 6.2–6.3, that is WD Lemma 3.4, Theorem 3.5, Corollary 3.11,
  Theorem 4.1 and Lemma 4.3) is proved as `Erdos408.graphTransference` in
  `Erdos408/Graph.lean`, from the vendored WD formalization
  `vendor/TotientFibers/`.
- **(H3) Block sieve**, `BlockSieve`. It is WD Lemma 2.9 (PD Lemma 2.6) as
  printed, with `z ≥ 1` made explicit. It is proved as
  `Erdos408.blockSieve` in `Erdos408/BlockSieve.lean`.

All three are stated in `Erdos408/Hypotheses.lean`.

**No zero-free region in the statements.** None of (H1)–(H3) mentions the
half-plane. Each analytic estimate that PD's proofs need at the extended
parameters is a premise of (H1) or (H2) instead (§2), and
`Erdos408/Analytic/` proves the premises from the half-plane (§3). The proof
of (H2) also uses one proved consequence of the half-plane directly:
`IntegerKernel.norm_sum_filter_modEq_le`, at the scales above `x` in PD's
constant part at high times (`two_sided_correlation.md` §6.6).

**Why the printed theorems do not suffice.** PD Theorems 3.1 and 6.1 fix the
scale, the margin, the bands and the proxy, and give no rate. At these fixed
parameters they yield only the qualitative PD Theorem 7.1, and the renewal
step needs an integrable error.

**What the extensions require.** That PD's proofs give (H1) and (H2) rests
on four points the printed text leaves implicit. Each is checked in a
companion blueprint, and the Lean proofs confirm it.

- **O1.** PD Theorem 3.1 at shrinking `δ = γ`. PD writes several counting
  budgets in Lemma 3.4 as `exp(o(L))` without exponents. (H1) needs them to
  be `exp(O_K(L^{0.98}))`, which the saving `exp(−cγL)` absorbs. Closed in
  `one_sided_type_ii.md` §5.4, which bounds every budget.
- **O2.** The `ε`-dependence of the non-analytic steps of PD Theorem 6.1 at
  `ε = cT^{−20}`: (6.28)–(6.29), Lemma 6.5, the square exceptions at
  (6.30), and the slot multiplicities. Each loss must be `poly(1/ε)` or
  better. Closed in `two_sided_correlation.md` §7.1: every loss is a power
  of `T`, and every saving is `exp(−cL/(2T^{20}))` or better.
- **O3.** Uniformity in the band exponents. PD's constants may depend on the
  `a_i`, while (H1) and (H2) let them vary in a fixed window (with a fixed
  gap, for (H1)). Closed for (H1) in `one_sided_type_ii.md` §§2, 5.3 and 8:
  every threshold depends on the bands only through `K, g, α₋, α₊`. Closed
  for (H2) in `two_sided_correlation.md` §7.3 (X5), where no gap is needed.
- **O4.** The spare-slot placement at PD (6.31). PD takes `p_l = l_1`, while
  (H2) spares the last slot. This is a relabeling, but repeated slots must
  be removed before the factorization. Closed in `two_sided_correlation.md`
  §7.2.

---

## 2. The statements

### (H1) One-sided Type II, extended

**Fixed data.** `q ∈ (0,1)`; `C, D_* > 0`; `C_X ≥ 1`; a window
`[α₋, α₊] ⊂ (0.1, 0.2)`.

**Statement.** There are `K₀` and `A₀, B, A` (depending on `D_*, C` only)
such that, for every fixed `K ≥ K₀`, every gap `g > 0` and all constants
`c₄, c_G`, there are `C₁, x₁` such that the following holds for every
`x ≥ x₁`. The gap comes after `K₀`. With `g` fixed first, `K₀` could be so
large that `K` bands spaced `g` apart do not fit in the window, and the
statement would hold vacuously.

Let all of the following depend on `x` arbitrarily, subject to:

- **Bands.** `α₋ ≤ a₁ < ⋯ < a_K ≤ α₊` with `a_{i+1} − a_i ≥ g`;
  `𝒫_i = {p : exp(L^{a_i}) ≤ p ≤ exp(2L^{a_i})}`;
  `𝒲(h) = q^{ω(h)−K} ∏_i ω_i(h)/V_i` as in PD (3.4).
- **Scale.** `γ ≥ L^{−1/100}`; `H_m, H_n ≥ x^γ`;
  `x/C_X ≤ X := H_m H_n ≤ C_X x`.
- **F.** `|F(h)| ≤ 1`, and `F(ph) = F(h)` for every `p ∈ ⋃ 𝒫_i`.
- **α.** (P1) `α_m = 0` off `[H_m, 2H_m]`; (P2) `α_m ≠ 0` only for rough `m`;
  (P3) `|α_m| ≤ L^C`; (P4) for every Dirichlet character `χ` of modulus
  `≤ L^{A₀}` and every real `|t| ≤ 2XL^B`,
  `|H_m^{−1} ∑_m α_m χ(m) m^{it}| ≤ c₄ L^{−A}`.
- **β.** `β_n = 0` off rough `n ∈ [H_n, 2H_n]`; `|β_n| ≤ L^C`.
- **Kernel premise (G).** For `1 ≤ |Δ| ≤ 4XL^B + 2`,
  `H_n^{−1} |∑_{H_n ≤ n ≤ 2H_n} n^{iΔ}| ≤ c_G (|Δ|^{−1} + exp(−L^{0.95}))`.

Then `|∑_{m,n} α_m β_n F(mn−1) 𝒲(mn−1)| ≤ C₁ X L^{−D_*}`.

**Beyond the printed theorem.**

- α ranges over the class P1–P4 instead of the single proxy, and P4 is the
  conclusion of PD Lemma 5.2. PD's proof uses the proxy's special form only
  through Lemma 5.2, in the major-arc bound of §5.
- The scale `x^γ` shrinks, with `γ ≥ L^{−1/100}`. The extraction's
  `γ ≍ T^{−20}/s` qualifies. The proof needs only `γL/L^{0.98} → ∞` (O1).
- (G) replaces the uses of (5.13) and Lemma 2.4 in PD Lemma 5.3, which need
  `log H_n ≥ L/(log L)²`. It is proved from the half-plane (AC3, §3).
- The band exponents vary in a fixed window with a fixed gap (O3). PD's `K`
  depends only on `(D_*, C)`, through the choice `.005K > G + 2` at PD
  (4.42), so `K` stays fixed.
- The coefficient `m^{iv}` is absorbed into α.

### (H2) Two-sided correlation, extended

**Fixed data.** `q, q₀ ∈ (0,1)`; active-group constants `c₀, C₀, v₋, v₊`;
inert window `[α₋, α₊] ⊂ (0.1, 0.2)`, and `K₀, C_N`; margin constant
`c > 0`; `d ≤ 2`; core exponent `B₀`; cutoff class `κ > 1, C_Ψ, (M_r)`;
target `A > 0`.

**Analytic premises.** For a precision `A′`, a frequency threshold `E`, a
modulus exponent `C_m` and a constant `κ′`:

- (AP1) `PrimeTwistBound x A′ E C_m κ′`, replacing PD (6.38): for every
  `H ∈ [exp(L/T^{22}), x]`, interval `I ⊂ [H, 2H]`, character `χ` of modulus
  `≤ L^{C_m}`, and `L^E ≤ |u| ≤ x³`,
  `|∑_{p ∈ I} χ(p) p^{−1+iu}| ≤ κ′ L^{−A′}`;
- (AP2) `IntegerKernelBound x C_m κ′`, replacing PD (6.37): for every
  `H ∈ [exp(L/T^{22}), x]`, interval `I ⊂ [H, 2H]`, modulus `k ≤ L^{C_m}`,
  residue class `a mod k`, and `1 ≤ |u| ≤ x³`,
  `H^{−1} |∑_{n ∈ I, n ≡ a (k)} n^{iu}| ≤ κ′ ((1+|u|)^{−1} + exp(−L^{0.95}))`.

**Statement.** There are `A′` and `C_m`, depending on the fixed data only,
such that for every `E` and `κ′` there are `C*, x₀` with the following
property. For every `x ≥ x₀` satisfying (AP1)–(AP2), and every admissible
choice at that `x` of:

- active groups as in PD (6.1);
- `r ≤ K₀ + C_N s` disjoint inert bands with exponents in `[α₋, α₊]`;
- slots `I₁, …, I_{d+1}` with every `inf I_i ≥ x^{cT^{−20}}` and
  `∏ sup I_i ≤ x^{1−cT^{−20}}` (slot `d+1` is the spare);
- `B : primes^d → ℝ` with `|B| ≤ 1`;
- `G` with `G(n) = G(n_*)` and `0 ≤ G ≤ L^{B₀}`;
- `Ψ` supported in `[κ^{−1}, κ]` with `‖Ψ^{(r)}‖_∞ ≤ M_r T^{C_Ψ r}`,

the correlation `|∑_w Ψ(w/x) w^{−1} F_x(w) G(w+1) W₁(w) W₁(w+1)|` is at most
`C* L^{−A}`. Here
`F_x = 𝒲 (f_B − C_B)`,
`f_B(n) = ∑_{l distinct} B(l₁..l_d) 1_{l₁⋯l_{d+1} ∣ n}`, and
`C_B = ∑ B(l₁..l_d)/(l₁⋯l_{d+1})`.

**Beyond the printed theorem.** The extensions X1–X8, which
`two_sided_correlation.md` §7.3 tracks through the proof:

- X1: the joint coefficient `B` on all slots but the spare;
- X2: the shrinking margins `x^{cT^{−20}}`;
- X3: the analytic premises AP1 and AP2 in place of PD (6.38) and (6.37);
- X4: a clipped invariant core, with explicit uniformity in `G`;
- X5: up to `K₀ + C_N s` inert bands, with exponents varying in the window;
- X6: `x`-dependent cutoffs with `T^{O(1)}` derivative norms;
- X7: `d + 1 ≤ 3` slots;
- X8: the bound `C* L^{−A}` uniform in all of the above.

PD Propositions 6.2–6.3 enter as `GraphTransference`, at fixed graph
parameters.

### (H3) Block sieve

WD Lemma 2.9 (PD Lemma 2.6) as printed. Nonnegatively weighted objects have
bad conditions at designated primes `p ≤ z`, where `z ≥ 1`. Suppose the
weight on which the conditions at every prime of a set `D` hold is
`X g(D) + r(D)`, with `g` multiplicative, `0 ≤ g(p) ≤ 1 − η₀`, and
`∑_{w<p≤w²} g(p) ≤ C₀`. Then, for even `h` large, the avoiding weight is
`X ∏_{p ≤ z}(1 − g(p))(1 + O(e^{−h})) + O(∑_{∏ D ≤ z^{4h+2}} |r(D)|)`,
with constants depending only on `η₀, C₀` and uniform in `h`. For `h = 2`
the upper bound holds with a fixed constant.

For `z < 1` the remainder sum would omit `D = ∅`, and the printed statement
fails. Hence the explicit `z ≥ 1`.

---

## 3. Analytic contracts, proved from the half-plane

`(Q)`: `L(s, χ) ≠ 0` for `re s > 7/8` and every Dirichlet character `χ`,
apart from the principal pole. This is the vendored theorem, restated as
`Erdos408.LFunction_ne_zero_of_seven_eighths_lt_re` in
`Erdos408/Analytic/QuasiRH.lean`. The paper's argument uses only that some
fixed `β < 1` works. The Lean proofs shift to the lines `re s = 15/16` and
`63/64`.

`Erdos408/Analytic/Core.lean` proves the bounds for `L(s, χ)` that the
contour shifts use, with `ℓ = log(k(|im s| + 3))` for modulus `k`:

- polynomial growth on `re s ≥ 1/2`, by partial summation
  (`norm_LFunction_le_poly`);
- `|L′/L(s, χ)| ≪ ℓ` on `15/16 ≤ re s ≤ 2`, by Borel–Carathéodory
  (`norm_logDeriv_LFunction_le`);
- `|L(s, χ)| ≤ exp(C√ℓ)` on `63/64 ≤ re s ≤ 2`, by Hadamard's three circles
  for `log L` (`norm_LFunction_le_exp_sqrt`).

The smoothed Perron formula and the rectangle residue calculus come from the
vendored `PrimeNumberTheoremAnd`. The contracts, all uniform in the stated
ranges:

- **AC0 (prime number theorem with a power saving).**
  `ψ(y, χ) = [χ = 1] y + O(k^C y^{1−c})`, with `c = 1/64`
  (`Erdos408.sum_vonMangoldt_mul_char_sub_le`, `Analytic/PNT.lean`). It
  bounds the primes in the unsmoothing strips, normalizes by `Π_x`, and
  supplies the prime main term in AC1.
- **AC1 (damped-proxy twists, gives P4).** For intervals `I ⊂ [H, 2H]` with
  `x^γ/2 ≤ H ≤ x^{K_an}`, characters of modulus `≤ L^{C_m}`, and
  `|t| ≤ x^{K_an}`, uniformly in `1 ≤ j ≤ C_j s + 1`,
  `H^{−1} ∑_{n ∈ I} χ(n) n^{it} ([n prime, n > x^γ] − a_j^0(n)) = O(L^{−A})`
  (`Erdos408.eventually_proxyTwist`, `Analytic/ProxyTwist.lean`). Write
  `g_j = λ * 1` with `λ` supported on `Y`-smooth numbers and `|λ| ≤ 1`.
  Rankin's trick bounds the divisors `d > H^{1/2}`, saving
  `exp(−γT^{25}/2)`. At low frequencies the principal main terms are exactly
  `D_j ∫_I u^{it}/log u`, by the Euler product, and cancel the prime main
  term from AC0. At high frequencies AC3 bounds each inner sum, and AC2
  bounds the prime sum. The paper (§6.3) obtains the same saving by
  shifting the contour of the prime-minus-proxy Dirichlet series by
  `1/log Y`.
- **AC2 (prime twists, gives AP1).** `Erdos408.eventually_primeTwistBound`
  (`Analytic/PrimeTwist.lean`). Shift `−L′/L` to a fixed line inside the
  half-plane, saving a fixed power of `H`.
- **AC3 (integer kernel, gives AP2 and (G)).**
  `Erdos408.eventually_integerKernelBound` and
  `Erdos408.eventually_kernel_premise` (`Analytic/IntegerKernel.lean`). For
  `u⁴ ≤ H³`, elementary summation keeps the principal term
  `O(H/(1 + |u|))`. For larger `|u|`, shift `L(s − iu, χ)` to
  `re s = 63/64`, where `|L| ≤ exp(C√L)`, saving `H^{−1/128}`. A residue
  class reduces to character twists.

With `γ ≥ L^{−1/100}` in (H1), and scales `≥ exp(L/T^{22})` in (H2), AC3's
saving `H^{−1/128}` is below `exp(−L^{0.95})` eventually. This fixes the
premise thresholds.

---

## 4. The extraction: (H1) + (H2) + block sieve + contracts ⇒ smooth R

Target (**R_smooth**). For `k ≤ 3` slots satisfying R's margins, every
`|𝔟| ≤ 1` ignoring the last slot, and every cutoff `Φ` with `T^{O(1)}`
derivative norms:
`(L/x) |∑_p Φ((p−1)/x) (f_𝔟(p−1) − C_𝔟)| ≤ C T^{−300}`.
This is `Erdos408.eventually_smooth_rectangle` in
`Erdos408/Extraction/Sieve.lean`.

Parameters (`Erdos408/Extraction/Defs.lean`), with `ε = cT^{−20}`:

- `h = 2⌈C_h s⌉` and `γ = (ε/4)/(4h+3)`, so `z = x^γ` has
  `z^{4h+2} < x^{ε/4}` and `γ ≥ L^{−1/100}`;
- `J_c = ⌈C_j s⌉`, `Y = exp(L/T^{25})`, and `t = 1/j` for `2 ≤ j ≤ J_c`;
- the candidate groups of PD §7, in the exponent windows `(0.28, 0.35)` and
  `(0.40, 0.45)`;
- `K` fixed clusters of `⌈C_N s/K⌉` inert bands, with exponents
  `0.11 + c · 0.08/K + i · 2/T`. One band per cluster is a distinguished
  band of (H1), so the gap `g` is fixed by the cluster layout;
- the clipping exponents `B_comp`, `B_core` and the graph parameters fixed.

The order of choice is part of the argument (paper §§6.3–6.4). The precision,
the clipping exponents, the graph precisions and `K` come first, then
`C_N`. The coefficient mass `2^N` of the inert polynomial is `L^{o(1)}` for
every `C_N`, so this order is consistent.

The steps, with the paper's account in §§6.3–6.4:

- **E0.** Reduce to `0 ≤ 𝔟 ≤ 1` by splitting `𝔟 = 𝔟⁺ − 𝔟⁻`, and to smooth
  `Φ`. Size bounds: `C_𝔟 ≤ T⁴`, and `|f_𝔟| ≤ T^{61}` on `n ≤ x²`, by
  Mertens (`Sieve.eventually_slot_size`).
- **E1.** The progression lemma for the inert polynomial `P`: at level
  `x^{ε/4}`, error `O(x/L²)`. In each progression the band set has the law
  of the independent divisor model, by (H3) on each fiber and Rankin's
  bound for large band parts (`Sieve.eventually_progression`).
- **E2.** Presieve with (H3) at depth `h` on the weights `ΦPf_𝔟` and `ΦP`,
  with E1 supplying the remainder. The main terms cancel, and the relative
  error is `O(e^{−h}/γ) · C_𝔟` (`Sieve.eventually_presieve`).
- **E3.** In the surviving `z`-rough `u + 1`, discard nonsquarefree `u + 1`
  and those with more than `J_c` prime factors (Rankin, the upper sieve and
  Mertens). The rest is `∑_{2 ≤ j ≤ J_c} Comp_j / j!`
  (`Sieve.eventually_composite`).
- **E4.** In `Comp_j`, replace the primes by the unstripped proxy `a_j^0`,
  one factor at a time. The other factors form one companion coefficient,
  whose mean square is `≤ H L^{−1+o(1)}` on a dyad, so it is clipped at
  `L^{B_comp}`. Only the two remaining variables are split into dyads,
  `O(L²)` boxes independent of `j`. Separate `m, n` in the cutoff by Fourier
  inversion, and expand `P` into monomials (mass `2^N = L^{o(1)}`). Each box
  is then an instance of (H1), with the other band weights and
  `f_𝔟 − C_𝔟` in the invariant `F`, P4 from AC1, and (G) from AC3.
- **E5.** Strip `a_j^0 → a_j`, at cost `(x/L) L^{−c+o(1)}`, using AC1's
  weighted rough counts at `γ/2`. E4 and E5 together are
  `Erdos408.eventually_compositeSum_sub_proxySum`
  (`Extraction/TypeII.lean`): `|Comp_j − Prox_j| ≪ x L^{−1−c}`.
- **E6.** Toss independent coins in the candidate groups. Outcomes with few
  successes have mass `(x/L) L^{−c+o(1)}`, by the exact one-factor residue
  law, a multigroup Chinese remainder estimate at Bonferroni depth `O(T)`,
  and Chernoff's bound. They are discarded before the signed expansion
  (`Erdos408.exists_failure_mass_le`, `Extraction/Allocation/Analytic.lean`).
- **E7.** Expand the failure factors, discard candidate-square multiples,
  and allocate: each candidate prime of `v` has `j` slots of equal stripped
  coefficient, so `j^ω t^ω = 1`. The coefficient becomes the core `G_j`,
  invariant under every candidate prime (`Allocation/Coefficients.lean`,
  `Allocation/Expansion.lean`, `Allocation/MainTerm.lean`).
- **E8.** Clip `G_j` at `L^{B_core}`, paying for the tail with the core
  moments, and apply (H2) with AP1 from AC2 and AP2 from AC3
  (`Erdos408.abs_proxySum_le_at`, `Allocation/Assembly.lean`). E6–E8
  together are `Erdos408.eventually_abs_proxySum_le`
  (`Extraction/Allocation.lean`): `|Prox_j| ≪ x L^{−1−c}`.
- **E9.** Subtract the composite contributions (E3–E8) from the presieved
  sum (E2). This gives the statistic weighted by `P`
  (`Erdos408.eventually_smooth_rectangle_nonneg`).
- **E10.** Remove `P` by one upper sieve, (H3) at `h = 2`, on `1 − P`, with
  E1 at `f = 1`. Its divisor-model mean is `≤ K exp(−N/(12e))`
  (`Sieve.eventually_mark_removal`).
- **E11.** The budget. With `h = 2⌈200 s⌉`, `J_c = ⌈1001 s⌉` and
  `N = ⌈30000 s⌉` bands per cluster, every error is `≤ T^{−300}`
  (`Sieve.final_budget`). The paper gives E9 and E11 only in aggregate.

Then **unsmoothing** gives the hard `RectangleInput`
(`Erdos408.rectangleInput_of_hypotheses`, `Extraction/Unsmooth.lean`).
Bound the dyad above by a smooth cutoff of steepness `T^{400}`, and bound
its two edge strips with AC0, using `|f_𝔟| ≤ 27T^{60}` and `|C_𝔟| ≤ 8T³`.
AC0 also normalizes `x/L` to `Π_x`. `RectangleInput` then feeds the
deduction of the normal order (paper §§3–5).

---

## 5. Lean architecture

- `Erdos408/Hypotheses.lean` (Mathlib only): bands, `𝒲`, active groups,
  `W₁`, `n_*`, the premises `PrimeTwistBound` and `IntegerKernelBound`, and
  the Props `OneSidedTypeII`, `TwoSidedCorrelation`, `GraphTransference`
  and `BlockSieve`. The slot tuples are in `Erdos408/Statement.lean`, and the
  slot statistic `slotCount`, `slotMean` in `Erdos408/Extraction/Defs.lean`.
- The proofs of the Props: `Erdos408/OneSided.lean`,
  `Erdos408/TwoSided.lean`, `Erdos408/Graph.lean` and
  `Erdos408/BlockSieve.lean`.
- `Erdos408/Analytic/`: `QuasiRH`, the growth bounds in `Core`, and AC0–AC3
  in `PNT`, `ProxyTwist`, `PrimeTwist` and `IntegerKernel`, indexed by
  `Contracts`.
- `Erdos408/Extraction/`: E0–E11 and unsmoothing, ending in
  `theorem rectangleInput_of_hypotheses (h₁ : OneSidedTypeII)
  (h₂ : TwoSidedCorrelation) : RectangleInput`. The block sieve enters
  through `blockSieve`, inside `eventually_smooth_rectangle`.
- `Solution.lean`: `rectangleInput` applies `rectangleInput_of_hypotheses`
  to `oneSidedTypeII` and
  `twoSidedCorrelation_of_graphTransference graphTransference`, and the
  compared theorems follow from it.

---

## 6. Design choices

- The frequency threshold `E` of AP1 comes after `A′` and `C_m` in (H2)
  (`∃ A′ C_m, ∀ E κ′`). AC2 supplies AP1 only above a threshold that
  depends on the precision and the modulus exponent
  (`eventually_primeTwistBound` returns `E` after `A` and `C_m`). PD's proof
  supports this order, since it picks its low/high frequency split after
  the analytic threshold (`two_sided_correlation.md` §1.3).
- The cutoff in (H2) is smooth: `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`. In
  this Mathlib, `ContDiff ℝ ⊤` at the top of `WithTop ℕ∞` means analytic,
  which no nonzero compactly supported function is.
- The extraction is split at two intermediate sums from
  `Erdos408/Extraction/Defs.lean`: `compositeSum` (`Comp_j`) and `proxySum`
  (`Prox_j`).
  - Layer A (`Sieve.lean`, `Sieve/`, `Unsmooth.lean`): E0–E3, E9–E11 and
    unsmoothing.
  - Layer B (`TypeII.lean`, `TypeII/`): `|Comp_j − Prox_j| ≪ x L^{−1−c}`,
    from (H1).
  - Layer C (`Allocation.lean`, `Allocation/`): `|Prox_j| ≪ x L^{−1−c}`,
    from (H2).

---

## 7. Scale conventions

The premise thresholds `L^{−1/100}`, `exp(L/T^{22})` and `exp(−L^{0.95})`
are chosen weak enough for the extraction and strong enough for the
contracts. They are the only numbers in (H1) and (H2) that are not in PD.
The paper uses the same thresholds (§§6.1–6.2).
