import Erdos821.P5.GoodLiftedRow
import Erdos821.P5.UnsharedBan
import Erdos821.P5.SharedRemoval

noncomputable section
open scoped BigOperators Classical

namespace Erdos821.P5Core
open Blueprint.Analytic Blueprint.Graph

/-- A fixed reference shared draw realizes the residual coefficient as a
function of only the designated free draw and two unshared endpoint lists. -/
def residualUnsharedCoefficient {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m : ℕ} (B : Family F G J m) (v : Fin B.count)
    (z₀ : SharedDraw (B.pattern v)) (u : FreeDraw (B.pattern v))
    (r s : UnsharedDraw (B.pattern v)) : ℂ :=
  (B.pattern v).coefficient (G.restrictBig (assembleLabels (B.pattern v) z₀ r))
    (G.restrictBig (assembleLabels (B.pattern v) z₀ s))
    (fun g => assembleAux (B.pattern v) u z₀ g.val)

theorem residualUnsharedCoefficient_eq {F : FixedData} {G : Blueprint.Graph.PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family F G J m) (hB : B.Residual Q h ξ)
    (v : Fin B.count) (z z₀ unused : SharedDraw (B.pattern v))
    (u : FreeDraw (B.pattern v)) (r s : UnsharedDraw (B.pattern v)) :
    (B.pattern v).coefficient (G.restrictBig (assembleLabels (B.pattern v) z r))
      (G.restrictBig (assembleLabels (B.pattern v) z s))
      (fun g => assembleAux (B.pattern v) u unused g.val) =
      residualUnsharedCoefficient B v z₀ u r s := by
  rw [residual_coefficient_assemble_shared_ext B hB v z z₀ r s]
  exact coefficient_assembleAux_unused_ext (B.pattern v) _ _ u unused z₀

theorem banned_residual_coefficient_good {P : Geometry} {G : Blueprint.Analytic.PrimeGroups}
    {J m Q : ℕ} {h ξ : ℝ} (B : Family P.graph G.graph J m) (hB : B.Residual Q h ξ)
    (v : Fin B.count) (k : ℤ) (ζ : ℝ)
    (z z₀ unused : SharedDraw (B.pattern v)) (u : FreeDraw (B.pattern v))
    (n n' : ℕ) (hn : n ≠ 0) (hn' : n' ≠ 0) (hD : freeDrawProduct (B.pattern v) u ≠ 0)
    (hz : GoodSharedDraw (B.pattern v) n n' (freeDrawProduct (B.pattern v) u) z)
    (r s : UnsharedDraw (B.pattern v)) :
    bannedPatternCoefficient (B.model k ζ) (B.pattern v)
      (assembleAux (B.pattern v) u unused) z r s =
      if UnsharedBan (B.pattern v) r s u then residualUnsharedCoefficient B v z₀ u r s else 0 := by
  have hgood := (goodSharedDraw_iff (B.pattern v) n n' _ hn hn' hD z).mp hz
  unfold bannedPatternCoefficient
  rw [pattern_ban_assemble_iff (B.pattern v) z r s u unused (fun i => (hgood.1 i).2.2),
    residualUnsharedCoefficient_eq B hB v z z₀ unused u r s]

end Erdos821.P5Core
