# Erdős Problem 408: distribution of iterated totient heights

This Lean 4 project concerns [Erdős Problem 408](https://www.erdosproblems.com/408), as cataloged by Thomas F. Bloom. Let `φ_k` be the `k`-th iterate of Euler's totient function, and let `f(n)` be the least `k ≥ 1` with `φ_k(n) = 1`. Erdős asked whether `f(n) / log n` has a distribution function, and whether it is almost always constant. We prove that there is a constant `1 / log 3 ≤ α ≤ 1 / log 2` such that

```
∑_{n ≤ x} (f(n) − α log n)² ≪ x (log x)² / (log log x)⁵.
```

Hence `|f(n) − α log n| ≤ log n / log log n` outside a set with counting function `O(x / (log log x)³ + √x)`. In particular `f(n) / log n → α` on a set of natural density one, and the distribution function of `f(n) / log n` is the point mass at `α`. This answers the first two questions of the problem in the affirmative. The paper also discusses the third, open-ended question about the largest prime factor of `φ_k(n)` when, for example, `k = ⌊log log n⌋`.

**The inputs.** The argument, written up in the paper [*The normal order of the number of iterations of Euler's function*](https://github.com/plasma-ai/erdos-408/blob/main/paper/totient_iterates.pdf) (Plasma AI, 2026), derives the normal order from two announced inputs:

- a zero-free half-plane `re s > β` for every Dirichlet L-function, with `β < 1` fixed. This is Theorem 1.1 of OpenAI's [*The Quasi-Riemann Hypothesis*](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) (30 September 2026), with `β = 7/8`;
- the graph comparison and transference machinery of OpenAI's [*The Poisson–Dirichlet law for prime predecessors*](https://github.com/openai/math/blob/main/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf) (PD) and [*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/main/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf) (WD) (24 September 2026).

Neither is assumed. The half-plane's Lean proof from [openai/math](https://github.com/openai/math) is vendored, and so is Yao Xu's Lean formalization of WD, [totient-fibers-lean4](https://github.com/cadamcat/totient-fibers-lean4); both build as part of this project. The graph input enters through three results of PD, extended as the paper's quantitative extraction needs them, and all three are proved here. Put `L = log x` and `T = log L`, and call an integer rough if it has no prime factor at most `exp(L^{0.24})`.

- `OneSidedTypeII` extends PD Theorem 3.1 (`Erdos408/OneSided/`, following PD §§3–5). For rough coefficients `α_m` on `[H_m, 2H_m]` that cancel against Dirichlet characters and `β_n` on `[H_n, 2H_n]`, with `H_m H_n ≍ x` and `H_m, H_n ≥ x^γ` for `γ ≥ L^{−1/100}`, the correlation of `α_m β_n` with a coefficient of `mn − 1` invariant under `K` bands of primes, weighted by the marked band weight of `mn − 1`, is `O(x L^{−D})`.
- `TwoSidedCorrelation` extends PD Theorem 6.1 (`Erdos408/TwoSided/`, following PD §6). For prime slots `(x^{u_i}, x^{v_i}]` with margin `c / T²⁰` and a bounded coefficient on all slots but the last, the slot count of `w` minus its harmonic model, correlated against marked weights of `w` and `w + 1`, a clipped invariant core of `w + 1` and a smooth cutoff, is `O(L^{−A})`. Its graph input, `GraphTransference` (PD Propositions 6.2 and 6.3, that is WD Lemma 3.4, Theorem 3.5, Corollary 3.11, Theorem 4.1 and Lemma 4.3), is proved in `Erdos408/Graph/` from the vendored WD formalization.
- The block sieve of WD Lemma 2.9 (PD Lemma 2.6) is proved here (`Erdos408/BlockSieve.lean`).

The two extensions are not the printed theorems. The printed statements fix the scale, the slot margin, the bands and the proxy, and give no rate, so they do not imply what is needed. The paper argues that PD's proofs give the extensions, and the Lean proofs settle this. The analytic estimates the extensions need (twisted prime sums and the integer kernel at the required precision) are proved from the vendored half-plane.

So the three compared theorems have no hypotheses, and Comparator checks them against `Challenge.lean`.

**The intermediate statistic.** The proof passes through the quantitative rectangle estimate, Theorem 2.1 of the paper, formalized as `RectangleInput`. It concerns one, two or three prime slots `(x^{u_i}, x^{v_i}]` with every `u_i ≥ c / T²⁰` and `∑ v_i ≤ 1 − c / T²⁰`. It asserts that, averaged over the primes `x < p ≤ 2x`, the number of tuples of distinct slot primes whose product divides `p − 1` agrees with its harmonic model `∑ 1 / (q_1 ⋯ q_k)` up to `C / T³⁰⁰`. The count may carry an arbitrary coefficient of modulus at most one depending on every slot prime except the last.

## Literature and scope

Pillai (*On a function connected with φ(n)*, Bull. Amer. Math. Soc. 35 (1929)) proved `⌊(log n − log 2) / log 3⌋ + 1 ≤ f(n) ≤ ⌊log n / log 2⌋ + 1` for `n ≥ 2`. Erdős, Granville, Pomerance and Spiro (*On the normal behavior of the iterates of some arithmetic functions*, Analytic number theory, Progr. Math. 85 (1990), 165–204) work with the completely additive `F` with `F(2) = 1` and `F(p) = F(p − 1)`, which differs from `f` by at most one. They proved that `f(n)` has normal order `α log n` under a form of the Elliott–Halberstam conjecture. We prove this normal order unconditionally, using their moment and renewal method. To our knowledge, this unconditional normal-order result has not previously been recorded. The additional work is to derive the two required prime-moment estimates from quantitative, weighted extensions of OpenAI's shifted-prime estimates, using the zero-free half-plane theorem. The intermediate estimate `RectangleInput` supplies these moments with explicit error bounds.

In connection with the third question, the paper records a consequence of Ford, Konyagin and Luca, *Prime chains and Pratt trees* (Geom. Funct. Anal. 20 (2010)), Theorem 5: for every integer-valued `k(n) → ∞`, the largest prime factor of `φ_{k(n)}(n)` is `n^{o(1)}` on a set of natural density one. This consequence is not formalized here.

**Extraction of `RectangleInput`.** This follows §6 of the paper, a quantitative modification of PD §7, with `s = log T`.

- *Presieve.* Smooth the dyad `x < p ≤ 2x` by a cutoff of `(p − 1)/x`. Mark `p − 1` by `O(s)` clusters of inert prime bands, presieve `p − 1` with the block sieve at depth `O(s)`, and discard non-squarefree and highly composite survivors. The statistic becomes a sum over `2 ≤ j ≤ O(s)` of composite sums over `p − 1` with `j` large prime factors.
- *Type II.* `OneSidedTypeII` replaces each prime in a composite sum by a damped proxy: a weighted sum over rough integers whose twists by Dirichlet characters are small. The proxy's twist bound and the integer kernel bound come from the half-plane, through growth bounds for `L` and `L'/L` proved by Borel–Carathéodory and three circles.
- *Allocation.* Toss independent coins in candidate prime groups, discard the outcomes with few successes by a multigroup Chinese remainder theorem and Chernoff's bound, and expand the rest into an invariant core. `TwoSidedCorrelation` then makes each proxy sum `O(x L^{−1−c})`.
- *The two-sided correlation.* Following PD §6, `GraphTransference` turns the correlation into the raw correlation plus signed stripped comparison terms. Each comparison term is separated into bilinear pieces, cut into major and minor arcs, and reduced to a mean square of a twisted Dirichlet polynomial. At low frequencies the divisor model (PD Lemma 6.5) makes the slot count and its harmonic model cancel exactly. At high frequencies the spare slot factors off a prime polynomial, and the twisted prime sums and the integer kernel bound the result off a sparse set of exceptional times.
- *Unsmoothing.* Remove the inert marking by an upper block sieve, and the cutoff by the prime number theorem in progressions, with a power saving from the half-plane, on its two edges.

**From `RectangleInput` to the normal order.** This follows §§3–5 of the paper. Put `L = log x`, `T = log L`, `a = T⁻⁶` and `m ≈ T⁻²⁰`, and let `F` be the additive function above.

- *Spare-slot removal.* Cut the logarithmic coordinates of the prime factors into cells of width `m`. Let `region₁` be the primes in `(x^a, x^{1−a}]`, cut to a union of cells, and `region₂` a staircase of cell pairs of distinct primes with product at most `x^{1−a}`. For an arbitrary coefficient `B` on `region₁` or `region₂`, append a spare prime `r` in the unweighted last slot with weight `w = (δ + j m) L / log(2x / Q)`, where `δ = c T⁻²⁰`. Then the spare mass `Z_Q(p − 1) = ∑ w` lies exactly in `[0, 1]`, so the deficit `1 − Z` is a positive measure controlled by the unweighted statistic. Every sum is a finite union of exact rectangle statistics, and Mertens' second theorem gives the harmonic deficit `O(T⁻¹³)`.
- *Positivity.* Since `∑_{q ∣ n} log q ≤ log n`, the regions already carry all but `O(T⁻⁶)` of the logarithmic mass of `p − 1`, and of its square. This controls small primes, large primes, prime powers and large products without a sieve. The dyadic prime moments then match `B(x) = ∑ F(q)/q` and `C(x) + D(x)`, where `C(x) = ∑ F(q)²/q` and `D(x) = ∑_{q ≠ r} F(q)F(r)/(qr)`, up to `O(L T⁻⁶)` and `O(L² T⁻⁶)`.
- *Renewal.* On the dyads `(2^k, 2^{k+1}]`, Abel summation gives `B_{k+1} = B_k (1 + h_k) + O(T_k⁻⁶ + 1/k)` with `h_k = ∑ 1/p` over the dyad. Telescoping against `∏ (1 + h_j) = c K (1 + O(1/K))` gives `B(x) = α L + O(L T⁻⁵)`. The cross term `D` and then `C` follow the same way, and the integer moments of `F` give the variance.

## Publication layout

`Challenge.lean` states the results using only Mathlib imports. Its three `sorry` proofs are deliberate: this file contains the statements to audit. `f` is copied verbatim from [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/408.lean) (commit `7db2ea3b91`), and `erdos_408.parts.i` and `erdos_408.parts.ii` are its statements of the same names verbatim, with `Set.HasDensity` written as `HasDensity`, which inlines formal-conjectures' definition. `Solution.lean` imports the proof development and supplies the three theorems. `comparator.json` selects their names and the allowed axioms for [Comparator](https://github.com/leanprover/comparator).

The proof development lives under `Erdos408/`:

- `Statement.lean` repeats the definitions of `Challenge.lean` and states `RectangleInput`. `Hypotheses.lean` states the graph-paper results `OneSidedTypeII`, `TwoSidedCorrelation`, `GraphTransference` and the block sieve, with the analytic premises.
- `Additive.lean` defines `F` and proves its additivity, its relation to `f`, and `log n / log 3 ≤ F(n) ≤ log n / log 2`.
- `Basic.lean` names the prime sums `B`, `C`, `D` and the prime moments `A₁`, `A₂`.
- `Mertens.lean` states Mertens' theorems on intervals and Chebyshev's bounds.
- `Grid.lean`, `SpareSlot.lean` and `PrimeMoments.lean` turn `RectangleInput` into the dyadic prime moments.
- `Cumulative.lean`, `Renewal.lean` and `CrossTerm.lean` turn those into the asymptotics of `B`, `C` and `D`.
- `IntegerMoments.lean` holds the integer moments of `F`, and `FinalAssembly.lean` derives the normal order from `RectangleInput`.
- `Analytic/` restates the vendored half-plane (`QuasiRH.lean`) and proves the analytic estimates from it: polynomial and `exp(C√ℓ)` growth bounds and `L'/L` bounds (`Core.lean`), the prime number theorem in progressions with a power saving (`PNT.lean`), and the premises of `OneSidedTypeII` and `TwoSidedCorrelation` (`PrimeTwist.lean`, `IntegerKernel.lean`, `ProxyTwist.lean`).
- `BlockSieve.lean` proves the block sieve.
- `OneSided.lean` and `OneSided/` prove `OneSidedTypeII`, following PD §§3–5 as restated in `blueprint/one_sided_type_ii.md`.
- `TwoSided.lean` and `TwoSided/` prove `TwoSidedCorrelation` from `GraphTransference`, following PD §6 as restated in `blueprint/two_sided_correlation.md`: `Graph/` reduces to the stripped comparisons, `Comparison/` reduces those to an endpoint mean square, and `Endpoint/` bounds it.
- `Graph.lean` and `Graph/` prove `GraphTransference` from the vendored WD results.
- `Extraction/` derives `RectangleInput` from `OneSidedTypeII` and `TwoSidedCorrelation`: `Defs.lean` defines the composite and proxy sums, `TypeII/` and `Allocation/` bound them, `Sieve/` presieves, and `Unsmooth.lean` removes the cutoff.

Four vendored libraries live under `vendor/`, each under its own directory with its upstream license and a provenance README:

- `vendor/OAI/` holds the import closure of the Dirichlet seven-eighths theorem from [openai/math](https://github.com/openai/math), and the prime-gap, Egyptian-fraction and two-point modules the WD formalization imports, under their upstream module names, ported to this toolchain.
- `vendor/TotientFibers/` holds the import closure of the WD results (transference, ideal construction and lifted shifted correlations) from Yao Xu's [totient-fibers-lean4](https://github.com/cadamcat/totient-fibers-lean4), under its upstream module names `Erdos821.*`, ported to this toolchain.
- `vendor/PrimeNumberTheoremAnd/` holds Mertens' theorems, the Wiener closure the OAI library imports, and the Perron formula and rectangle residue calculus used by `Erdos408/Analytic/`, from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).
- `vendor/RellichKondrachov/` holds the Rellich–Kondrachov closure the OAI library imports, from [rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov).

`blueprint/rectangle_input.md` states the graph-paper results, the analytic estimates and the extraction in prose, and records where each is proved; `blueprint/one_sided_type_ii.md` and `blueprint/two_sided_correlation.md` restate PD §§3–5 and §6 for the proofs of `OneSidedTypeII` and `TwoSidedCorrelation`.

`Challenge.lean` and the files of `Erdos408/` that import only Mathlib use the module system. The vendored libraries do not, and a module cannot import an ordinary file, so the files that depend on them and `Solution.lean` are ordinary files.

`paper/` holds the paper, `totient_iterates.tex` and its compiled `totient_iterates.pdf`.

`formalization.yaml` records the mathematical sources, authorship, AI use, source fidelity, and review status for a registry submission.

The Lean and Mathlib versions are fixed by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The full build includes `Challenge` and therefore reports its intentional `sorry` warnings. The proofs in `Solution` can also be built directly with `lake build Solution`.
