import Erdos821.P3Clean.TiltedAdjoint

/-! The same quantitative comparison holds in both signed directions. -/

noncomputable section

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem normBound_tiltedBannedKernel (A : Model F P J m) (n : ℕ) (C D atom : ℝ)
    (hD : 1 ≤ D) (hat : 0 ≤ atom)
    (hV : ∀ g : P.BigGroup, P.V g.val ≠ 0)
    (hb : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val)
    (hatom : ∀ g : P.BigGroup, ∀ p : P.Prime g.val, P.mu g.val p ≤ atom)
    (hsqrt : ∀ v : Fin A.patternCount, ∀ a b,
      1 ≤ Real.sqrt (freshDensity F n (A.pattern v) a) * Real.sqrt (freshDensity F n (A.pattern v) b) ∧
        Real.sqrt (freshDensity F n (A.pattern v) a) * Real.sqrt (freshDensity F n (A.pattern v) b) ≤ D)
    (hideal : ∀ theta : ℝ, NormBound P.idealMass (A.idealKernel theta) C)
    (theta : ℝ) (forward : Bool) :
    NormBound (tiltedIdealMass F n) (tiltedBannedKernel A n theta forward)
      (C + ((D - 1) + D * ((Fintype.card P.BigGroup : ℝ) * J * (J + F.ell) * (2 * atom))) *
        A.patternMass) := by
  cases forward with
  | false =>
    rw [tiltedBannedKernel_backward A n theta hb]
    exact normBound_weightedAdjoint _ _ _ (fun a => (tiltedIdealMass_pos F n hb a).ne')
      (normBound_tiltedBannedKernel_forward A n (-theta) C D atom hD hat hV hb hatom hsqrt (hideal (-theta)))
  | true =>
    exact normBound_tiltedBannedKernel_forward A n theta C D atom hD hat hV hb hatom hsqrt (hideal theta)


end Erdos821.P3Clean
