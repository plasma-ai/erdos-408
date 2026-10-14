# OAI source provenance

The 2,987 Lean modules in this directory are taken from the `lean/` directory
of [openai/math](https://github.com/openai/math) at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (2026-10-07), except that 63 of
them, described below, are taken at its ancestor
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` (2026-10-06), where they are
identical. As recorded upstream,
they were produced by an internal OpenAI model. They are distributed under the
Apache License 2.0, whose full text is in [LICENSE](LICENSE).

They are the import closures of `OAI.NumberTheory.DirichletL.Nonvanishing` and
of the OAI modules that `vendor/TotientFibers/` imports, not the whole upstream
library, and keep their upstream module names. The first module
proves `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`: every
Dirichlet L-function is zero-free in `re s > 7/8`, apart from the principal
character's pole at `s = 1`. This is Theorem 1.1 of
[*The Quasi-Riemann Hypothesis*](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf),
and upstream checks it with Comparator against
`lean/ComparatorChallenges/DirichletSevenEighths.lean`.
`Erdos408/Analytic/QuasiRH.lean` restates it for this project.

The other 63 modules, under `EgyptianFractions/` (12), `PrimeGaps/` (48), and
`TwoPoint/ShortIntervals/` (3), complete the closure for `vendor/TotientFibers/`,
which pins them at `adc7f124`, and import only Mathlib. They supply derivative
tests, sieve bounds, prime estimates in arithmetic progressions, and mean
squares over short intervals.

The closure also imports `PrimeNumberTheoremAnd.Wiener` and
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`, which
are vendored alongside it in `vendor/PrimeNumberTheoremAnd/` and
`vendor/RellichKondrachov/`.

Upstream pins Lean `v4.34.1` and Mathlib commit `d13f23b`. This project pins
Lean and Mathlib `v4.35.0`, and 44 of the modules were changed to build here,
as were two of the 63 modules for `vendor/TotientFibers/`. The changes follow
Lean and Mathlib changes and keep every statement:

- A singleton set literal whose element spans several lines is now parsed as
  the start of set-builder notation. In 21 modules under `CubicSieve/`,
  `Descent/`, `Eisenstein/`, `Energy/`, `Fourier/`, `GaussSum/`, `Moments/`,
  and `RowCompletion/`, the element of such an `Ideal.span {…}` is
  parenthesized.
- `MemLp.indicator` takes a `NullMeasurableSet`, so
  `Eisenstein/CompactEnergyFamilies.lean` passes `hK.nullMeasurableSet`.
- `Measure.QuasiMeasurePreserving` is now `QuasiMeasurePreserving`, and field
  notation no longer resolves through the deprecated alias. Eight modules under
  `Eisenstein/` and `Reciprocity/` use the new name.
- Core's `ULift.ext` takes `x` and `y` implicitly, so
  `Reflection/SectorData.lean` passes them by name.
- `congr 1` now closes two goals outright, so the tactics that followed it in
  `Moments/FirstSectors.lean` and `Moments/CommonAllocationSum.lean` are
  removed.
- `contDiff_apply` takes the coordinate family `F' : ι → Type` rather than a
  single codomain. `CubicSieve/RowCaps.lean`, `Eisenstein/CuspHeight.lean`,
  `Eisenstein/SeedHeight.lean`, `Eisenstein/ConjugateCuspProfiles.lean`,
  `PrimeGaps/MarkedMoments.lean` and `PrimeGaps/TensorProfiles.lean` pass
  `fun _ => ℝ` (or `ℂ`, with the index type `Fin 3` where it is not otherwise
  determined) instead of the codomain.
- `positivity` no longer sees through `id` or an ordinary definition to a
  hypothesis about the atom. `Eisenstein/ConjugateCuspProfiles.lean` proves
  `id x / 2 ≠ 0` with `div_ne_zero`, and `Descent/SecondCellParameters.lean`
  states `0 ≤ scales d 1` before `gcongr`.
- `dsimp [x]` also unfolds the other local definitions in the goal, and turns a
  sum over `Bool` into one over `{true, false}`, so the hypotheses that
  `positivity` and `gcongr` relied on no longer match. In `PrimeRows/`
  (`FirstWGrowth`, `FirstJoint`, `ZGrowth`, `XGrowth`, `BufferedGrowth`,
  `BufferedHeightGrowth`) the bounds `selectedFirstBound_nonneg` get explicit
  arguments and the constants' nonnegativity is proved without `dsimp`;
  `Dictionary/InverseMarkedReferenceFiberEnergy.lean` restates the goal with
  `show` instead.

All 2,987 modules also use the module system: each begins with `module`,
imports with `public import`, and exposes its definitions with
`@[expose] public section`. The eight that imported all of Mathlib import the
Mathlib modules they use instead, and 37 others import Mathlib modules they
use but no longer see, because a module sees only what its imports export.
A module does not export its private declarations, so 31 modules drop
`private` from the declarations that a public statement or definition
mentions, or that a later module uses: `PrimeRows/Measurable.lean` relies on
the `Countable (Ideal O)` instance of `Hecke/Dyadic.lean`.

No `sorry`, `axiom`, or heartbeat option was added.
