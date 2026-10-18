# TotientFibers source provenance

The 647 Lean modules in this directory are taken from
[cadamcat/totient-fibers-lean4](https://github.com/cadamcat/totient-fibers-lean4)
at commit `dfce35707a67fce7362cb2bd95af8b80a0b0373e` (2026-10-14), by Yao Xu
([@cadamcat](https://github.com/cadamcat)), written by AI coding agents under
their direction as recorded upstream. They formalize OpenAI's
[*Weighted dilation graphs, smooth shifted primes and totient fibers*](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/paper.pdf)
(WD). They are distributed under the Apache License 2.0, whose full text is in
[LICENSE](LICENSE); upstream's [NOTICE](NOTICE) is copied unchanged. The
Formal Conjectures material that the NOTICE mentions (`Challenge.lean`,
`Erdos821/Challenge.lean`, `Erdos821/Fidelity/`) is not part of this
directory.

They keep their upstream module names (`Erdos821.*`) and are the import
closure of `Erdos821.P3Final.Transference`, `Erdos821.P3Rare.Proof`,
`Erdos821.S34.IdealInputs`, `Erdos821.P5.ShiftTwoTasks`,
`Erdos821.P5MinorAdapter.Proof`, `Erdos821.P5MarkedEnergy.Main`,
`Erdos821.Prelim.SieveInputsProof`, and `Erdos821.P1.ClassicalInputs`, not the
whole upstream library. Upstream's `Erdos821.Final.packageInterfaces` assembles
these modules' theorems into the packages P1 to P5, which prove:

| WD result | Proposition | Proved by |
| --- | --- | --- |
| Lemma 3.4 | `Erdos821.Blueprint.Graph.AbsolutePhysicalBounds` | field `absolute` of the P3 term below |
| Theorem 3.5 | `Erdos821.Blueprint.Graph.TransferenceEstimate` | field `moment` of the P3 term below |
| Corollary 3.11 | `Erdos821.Blueprint.Graph.TransferencePairing` | field `pairing` of the P3 term below |
| Theorem 4.1 | `Erdos821.Blueprint.Graph.IdealConstruction` | field `construction` of the P4 term below |
| Lemma 4.3 | `Erdos821.Blueprint.ComparisonEstimate` | `Erdos821.S34Core.comparisonEstimate_proof` |
| lifted shifted correlations (upstream's `thm:shift`) | `Erdos821.Blueprint.ShiftEstimate` | the P5 term below |

The P3 term `Erdos821.Blueprint.TransferenceInputs` is
`Erdos821.S2Core.transference_inputs_of_remaining
Erdos821.S2Packet.AbsolutePhysicalPacketTask_proof
Erdos821.S2Ltrans.LocalTransferenceAssemblyTask_proof
(Erdos821.P3Final.remaining_of_rare Erdos821.S2Core.MemoryRareTask_proof)`,
and the P4 term `Erdos821.Blueprint.IdealInputs` is
`Erdos821.S34Core.ideal_inputs_of_cancellation_task
Erdos821.P4Probe.FiniteProbeCancellationTask_proof`. Upstream's assembly
reaches the same terms through `Erdos821.P3Final.transference_inputs_of_rare`
and `Erdos821.Blueprint.ideal_inputs_proof`, whose `ClassicalInputs` argument
is unused. The P5 term is `Erdos821.P5Core.shifted_cancellation_of_two_tasks
Erdos821.P5Core.ComparisonMinorArcAdapterTask_proof
Erdos821.P5Core.MarkedEndpointEnergyTask_proof`, applied to
`Erdos821.Blueprint.classical_inputs`,
`Erdos821.Blueprint.sieve_inputs_proof Erdos821.Blueprint.classical_inputs`,
and the P3 and P4 terms. Each depends only on `propext`, `Classical.choice`,
and `Quot.sound`.

The closure imports 13 modules of OpenAI's library, whose closure is vendored
in `vendor/OAI/`, and `PrimeNumberTheoremAnd.Erdos970.MertensClassical`,
vendored in `vendor/PrimeNumberTheoremAnd/`.

Upstream pins Lean `v4.34.1`, Mathlib commit `d13f23b`, and
[openai/math](https://github.com/openai/math) commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. This project pins Lean and Mathlib
`v4.35.0`, and three modules were changed to build here. The change
follows a Lean change and keeps every statement:

- `simp only [hp]` with a hypothesis `hp : p ∧ q` now rewrites `p` and `q`
  separately and leaves `True ∧ True` in an `if` condition. In
  `P5/PatternPairing.lean`, `P5/EdgePropagation.lean`, and
  `P5/PhysicalKernelDomination.lean`, such a call also simplifies with
  `and_self`, as upstream's `P5MarkedEnergy/BoxInputs.lean` already does.

All 647 modules also use the module system: each begins with `module`,
imports with `public import`, and exposes its definitions with
`@[expose] public section`. None imports all of Mathlib: of the 54 that did,
35 import the Mathlib modules they use instead, and the other 19 see them
through their other imports. Another 76 import Mathlib modules they use but no
longer see, because a module sees only what its imports export.
`P5Log/LogPhaseSum.lean` and `S2Phys/PhysicalPathExpansion.lean` drop
`private` from declarations that a public statement mentions, since a module
does not export its private declarations. In `P3Rare/Base.lean`, two `dsimp`
calls now close their goals, and the `rfl` after each is removed.

255 modules were also changed to clear Lean's and Mathlib's warnings:

- Deprecated names are replaced by their successors, for example `if_pos`,
  `if_neg`, `dif_pos` and `dif_neg` by `ite_eq_left`, `ite_eq_right`,
  `dite_eq_left` and `dite_eq_right`, and `push_neg` by `push Not`.
- The `simp` arguments, tactics and `<;>` combinators that the linters report
  as unused are removed, a `simpa` that `simp` closes becomes `simp`, `letI`
  and `haveI` in proofs become `let` and `have`, consecutive `intro`s are
  merged, and names that a proof never uses become `_`.
- In `Classical/HarmonicCharacters.lean`, the linter reports `abs_of_pos hy`
  and `abs_of_pos hlogpos` as unused in one `simp` call that needs them, so
  that call keeps them and drops the arguments it does not use.
- Hypotheses and arguments that a declaration never uses are removed from its
  signature, together with the matching argument at every call site, and
  unused section variables are omitted with `omit … in`. Callers whose own
  hypotheses then went unused were shortened in turn. Where an unused argument
  is the only thing that determines an implicit one (the `Model` argument of
  `rawEdgeWeight`, `bannedPatternCoefficient` and
  `allPrimes_sup_le_two_exp`), it is kept and named `_A`.
- Unused names of bound variables inside statements, such as hypotheses
  quantified in the propositions of `Blueprint/`, become `_` or an arrow,
  which leaves the propositions unchanged.

The modules build without warnings.

No `sorry`, `axiom`, or heartbeat option was added. Eighteen modules carry
upstream's own `maxHeartbeats` or `synthInstance.maxHeartbeats` options, which
are kept as they are.
