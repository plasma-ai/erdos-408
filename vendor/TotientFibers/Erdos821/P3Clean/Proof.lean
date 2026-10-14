import Erdos821.P3Clean.CutoffNorm
import Erdos821.P3Clean.EventualComparison

/-! The frozen signed clean-memory norm task. -/

noncomputable section

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph Erdos821.P3Clean

theorem MemoryCleanTask_proof (F : FixedData) (r : MemoryParameters F) : MemoryCleanTask F r := by
  obtain ⟨Cs, hclean⟩ := clean_projected_norm F r
  refine ⟨Cs, ?_⟩
  intro m C₁ J C₂ Eid hEid
  obtain ⟨x₀, hx₀⟩ := eventually_tiltedBanned_norm F J m C₁ Eid
  refine ⟨x₀, ?_⟩
  intro x hx P hP A hpat _ _ hideal theta i
  obtain ⟨⟨hL, hb⟩, hbig⟩ := hx₀ x hx P hP
  have h := hclean x P hP hL J m (N x) (memoryCutoff x) A theta i
    (2 * (L x) ^ (-Eid)) (by positivity) hb (hbig A hpat hideal)
  rw [mul_assoc, ← Real.rpow_add hL] at h
  exact h

#check MemoryCleanTask_proof

end Erdos821.S2Core
