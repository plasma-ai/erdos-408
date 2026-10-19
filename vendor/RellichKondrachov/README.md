# Rellich–Kondrachov source provenance

The 15 Lean modules in this directory are taken from
[abenenson/rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov)
at commit `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` (2026-05-14), by Adam
Benenson. They are distributed under the Apache License 2.0, whose full text is
in [LICENSE](LICENSE).

They are the import closure of
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`, which
the vendored OAI library imports, and keep their upstream module names. They
are taken with the compatibility patch
`lean/patches/rellich-kondrachov-lean4341.patch` from
[openai/math](https://github.com/openai/math) at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` applied, as the OAI library builds
them.

This project pins Lean and Mathlib `v4.35.0-rc3`.

All 15 modules use the module system: each begins with `module`,
imports with `public import`, and exposes its definitions with
`@[expose] public section`. `L2Compactness/Approximation.lean` imports
`Mathlib.Algebra.Order.Star.Real`, which it uses but no longer sees, because a
module sees only what its imports export.
