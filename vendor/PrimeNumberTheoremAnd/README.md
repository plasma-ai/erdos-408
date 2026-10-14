# PrimeNumberTheoremAnd source provenance

The 13 Lean modules in this directory are taken from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
at commit `c39a751132c88b6e8080b74c74023fd95b3d8be0` (2026-09-30), by Alex
Kontorovich, Terence Tao, and the other contributors recorded upstream. They
are distributed under the Apache License 2.0, whose full text is in
[LICENSE](LICENSE).

They keep their upstream module names (`PrimeNumberTheoremAnd.*`) and fall into
four groups:

- `IEANTN/Mertens` and `EulerMaclaurin` are the import closure of
  `PrimeNumberTheoremAnd.IEANTN.Mertens`. That module proves Mertens' first
  theorem, `∑_{p ≤ x} log p / p = log x + O(1)` (`Mertens.E₁p.bounded`), and
  his second theorem, `∑_{p ≤ x} 1 / p = log log x + M + O(1 / log x)`
  (`Mertens.E₂p.abs_le`).
- `Wiener`, `Fourier`, `SmoothExistence`, and `Sobolev` are the import closure
  of `PrimeNumberTheoremAnd.Wiener`, which the vendored OAI library imports.
  They are taken with the compatibility patch
  `lean/patches/PrimeNumberTheoremAnd-lean4341.patch` from
  [openai/math](https://github.com/openai/math) at commit
  `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` applied, as the OAI library builds
  them, and are otherwise unchanged.
- `PerronFormula`, `ResidueCalcOnRectangles`, `Rectangle`, and
  `Mathlib/Analysis/Asymptotics/{Asymptotics,Uniformly}` supply the smoothed
  Perron formula and rectangle residue calculus used by `Erdos408/Analytic/`.
  The compatibility patch above applies to `PerronFormula`.
- `Erdos970/MertensClassical` and `Erdos970/EulerMaclaurin` are the import
  closure of `PrimeNumberTheoremAnd.Erdos970.MertensClassical`, which supplies
  Mertens' theorems to `vendor/TotientFibers/`. They are not in the upstream
  commit: the compatibility patch above creates them.

The upstream source pins Lean `v4.34.0`, and this project pins Lean and
Mathlib `v4.35.0`. Six modules were changed to build here. The changes
follow Lean and Mathlib changes, or remove LeanArchitect, and keep every
statement:

- `IEANTN/Mertens`, `PerronFormula`, `ResidueCalcOnRectangles`, and
  `Rectangle` no longer import `Architect`. Their `blueprint_comment` blocks
  and `@[blueprint …]` attributes, which carry only blueprint metadata, are
  removed.
- `PerronFormula` uses LeanArchitect's docstrings inside tactic blocks. These
  are now ordinary comments.
- Mathlib deleted `Mathlib.Tactic.LinearCombinationPrime`, which upstream's
  `PrimeNumberTheoremAnd.Tactic.AdditiveCombination` needs. That module is
  dropped, and its single use in `ResidueCalcOnRectangles` became
  `linear_combination (norm := module)` with the same hypotheses.
- Mathlib renamed `Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic`
  to `Mathlib.Analysis.SpecialFunctions.Integrability.Log`, and
  `IEANTN/Mertens` and `Erdos970/MertensClassical` import the new name.
- `MeasureTheory.integrableOn_indicator_iff` takes a `NullMeasurableSet`, so
  `IEANTN/Mertens` and `Erdos970/MertensClassical` pass
  `measurableSet_Ici.nullMeasurableSet`.
- `Mathlib.NumberTheory.AbelSummation` now imports
  `Mathlib.MeasureTheory.Function.Floor` privately, so `EulerMaclaurin`, whose
  `fun_prop` call needs that module's `Nat.floor` lemma, imports it directly.

No `sorry`, `axiom`, or heartbeat option was added.
