import Erdos408.Analytic.IntegerKernel
import Erdos408.Analytic.PNT
import Erdos408.Analytic.PrimeTwist

/-!
# Analytic contracts from the zero-free half-plane

The estimates the derivation of the rectangle statistic takes from the
zero-free half-plane `re s > 7/8`: the analytic contracts AC0–AC3 of
`blueprint/rectangle_input.md` §3. Each comes from a smoothed Mellin
inversion shifted to a line `re s = 1 - d` inside the half-plane, using the
bounds of `Erdos408.Analytic.Core`.

* `Erdos408.Analytic.PNT` (AC0): the prime number theorem in progressions
  with a power saving, `ψ(y, χ) = [χ = 1] y + O(k^C y^{1-c})`.
* `Erdos408.Analytic.PrimeTwist` (AC2): the premise `PrimeTwistBound` of
  `TwoSidedCorrelation`. Shift `-L'/L` to `re s = 1 - d`, saving `H^{-d}`.
* `Erdos408.Analytic.IntegerKernel` (AC3): the premise `IntegerKernelBound`
  of `TwoSidedCorrelation`, and the integer-kernel premise of
  `OneSidedTypeII`. For `|u| ≤ H^a` use elementary summation, keeping the
  principal integral. For larger `|u|`, shift `L(s, χ)` to `re s = 1 - d`,
  using `|L| ≤ exp(C √L)` there.
-/
