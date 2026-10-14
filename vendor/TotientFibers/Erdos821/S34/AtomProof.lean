import Erdos821.S34.OwnedLeafProofs
import Erdos821.S34.AtomBound

set_option autoImplicit false

open scoped BigOperators Classical
open Filter

namespace Erdos821.Blueprint.Analytic

theorem product_atom_bound_proof : Erdos821.Blueprint.Analytic.product_atom_bound_statement := by
  intro P m
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  intro G hG k hk n hn
  have hL : 1 ≤ L x := by
    rw [L, ← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hv : 0 < P.vmin := P.positive.2.2.1
  have hmass : ∀ g ∈ G.big, P.vmin ≤ Erdos821.S34.Core.mass (Erdos821.S34Core.coreGroups G) g := by
    intro g _
    exact (hG.2.2.1 g).1
  have hcap : ∀ g, k g ≤ m := fun g => (hk.2 g).1
  have hinactive : ∀ g, g ∉ G.big → k g = 0 := by
    intro g hg
    have hsmall : g ∈ G.small := by simpa only [PrimeGroups.big, Finset.mem_sdiff,
      Finset.mem_univ, true_and, not_not] using hg
    exact (hk.2 g).2 hsmall
  have hc := Erdos821.S34Core.product_atom_group_count
    (Erdos821.S34Core.coreGroups G) k m G.big P.vmin hv hmass hcap hinactive n
  have hpow := Erdos821.S34Core.group_cost_log_power m G.big.card P.vmin P.C₀ (L x)
    hv hL (hG.2.1.2)
  exact hc.trans (div_le_div_of_nonneg_right hpow (Nat.cast_nonneg n))

example : Erdos821.Blueprint.Analytic.product_atom_bound_statement := @product_atom_bound_proof

end Erdos821.Blueprint.Analytic
