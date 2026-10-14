import Erdos821.P3Clean.SmallAverage
import Erdos821.P3Clean.ConditionedNorm
import Erdos821.P3Clean.Damping

/-! The finite conditioned estimate controls the original projected clean memory kernel. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P3Clean

open Erdos821.Blueprint.Graph Erdos821.S2Core

theorem clean_projected_norm (F : FixedData) (r : MemoryParameters F) :
    ∃ Cs : ℝ, ∀ (x : ℝ) (P : PrimeGroups), P.Admissible F x → 0 < L x →
      ∀ (J m n B : ℕ) (A : Model F P J m) (theta : ℝ) (i : Fin n) (C : ℝ), 0 ≤ C →
        (∀ g : P.BigGroup, ∀ p : P.Prime g.val, 0 < baselinePrime F n p.val) →
        (∀ theta' : ℝ, ∀ forward : Bool,
          NormBound (tiltedIdealMass F n) (tiltedBannedKernel A n theta' forward) C) →
        NormBound (P.memoryMass F J n)
          (projectKernel (fun s => P.memorySize s ≤ B)
            (memoryEdgeKernel A n r.rho theta i .clean (fun _ _ _ => 1)))
          (C * (L x) ^ Cs) := by
  obtain ⟨Cs, hraw⟩ := big_averaged_clean_norm F
  refine ⟨Cs, ?_⟩
  intro x P hP hL J m n B A theta i C hC hb hbig
  letI : Fintype (CutPendingState P B) := Fintype.ofFinite _
  have hV (g : P.Group) : 0 < P.V g := F.vMin_pos.trans_le (hP.2.2.2.2.1 g).1
  have hm := memoryMass_nonneg (P := P) (F := F) J n hV hb
  have hCC : 0 ≤ C * (L x) ^ Cs := mul_nonneg hC (Real.rpow_nonneg hL.le _)
  have hcoordinate := hraw x P hP hL J m n B A theta (edgeForward i) C hC
    (betweenMass_nonneg F P n hb)
    (fun d => normBound_bigAveragedConditionedKernel A n B theta (edgeForward i) d C hC hb
      (fun theta' => hbig theta' (edgeForward i)))
  have hsmall := normBound_averageSmallCoordinateKernel F J n B _ _ hcoordinate
  let e := cutoffStateCoordinates P (J + F.ell) B
  have hcut := normBound_equiv (coordinateMass F J n B)
    (averageSmallCoordinateKernel (bigAveragedRawKernel A n theta (edgeForward i) (B := B)))
    (C * (L x) ^ Cs) e hsmall
  have hmass : (fun s : {s : P.MemoryState (J + F.ell) // P.memorySize s ≤ B} =>
      coordinateMass F J n B (e s)) = fun s => P.memoryMass F J n s.val := by
    funext s
    simpa only [e, Equiv.symm_apply_apply] using coordinateMass_eq_memoryMass F J n B (e s)
  have hkernel : (fun s t : {s : P.MemoryState (J + F.ell) // P.memorySize s ≤ B} =>
      averageSmallCoordinateKernel (bigAveragedRawKernel A n theta (edgeForward i) (B := B)) (e s) (e t)) =
      fun s t => cleanEdgeKernel A n 1 theta i s.val t.val := by
    funext s t
    simpa only [e, Equiv.symm_apply_apply] using averageSmallCoordinateKernel_clean A n theta i (e s) (e t)
  rw [hmass, hkernel] at hcut
  have hproject := normBound_subtype_project (P.memoryMass F J n) (cleanEdgeKernel A n 1 theta i)
    (fun s => P.memorySize s ≤ B) (C * (L x) ^ Cs) hm hCC hcut
  have h := normBound_mul_endpoints hm hCC hproject
    (fun s => (pendingDamping r.rho s : ℂ)) (fun s => (pendingDamping r.rho s : ℂ))
    (fun s => by simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pendingDamping_nonneg r s)] using pendingDamping_le_one r s)
    (fun s => by simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pendingDamping_nonneg r s)] using pendingDamping_le_one r s)
  have he : (fun s t => (pendingDamping r.rho s : ℂ) *
      projectKernel (fun s => P.memorySize s ≤ B) (cleanEdgeKernel A n 1 theta i) s t *
        (pendingDamping r.rho t : ℂ)) =
      projectKernel (fun s => P.memorySize s ≤ B)
        (memoryEdgeKernel A n r.rho theta i .clean (fun _ _ _ => 1)) := by
    funext s t
    unfold projectKernel
    rw [memoryEdgeKernel_rho]
    rw [memoryEdgeKernel_clean]
    by_cases hs : P.memorySize s ≤ B <;> by_cases ht : P.memorySize t ≤ B <;>
      simp [projectKernel, hs, ht]
  rw [he] at h
  exact h


end Erdos821.P3Clean
