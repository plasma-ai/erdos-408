import Erdos821.S2.TransferenceAssemblyTask
import Erdos821.P3Pair.PairingFromMoment

/-! The exact local moment theorem supplies the transference package interfaces. -/

noncomputable section
namespace Erdos821.S2Core

open Filter Erdos821.Blueprint.Graph

theorem transferenceEstimate_of_local
    (hLocal : Erdos821.Blueprint.Graph.local_transference_statement) : TransferenceEstimate := by
  intro F E hE
  obtain ⟨Eid, hEid, h⟩ := hLocal F E hE
  refine ⟨Eid, hEid, ?_⟩
  intro m C₁
  obtain ⟨J₀, hJ⟩ := h m C₁
  refine ⟨J₀, ?_⟩
  intro J hJJ gamma C₂ hgamma _
  obtain ⟨x₀, hx⟩ := hJ J hJJ C₂ gamma hgamma
  filter_upwards [eventually_ge_atTop x₀] with x hxx
  intro P A hP hmass hk hkBound hIdeal X hXlo hXhi
  have hkpos : 0 < |A.k| := abs_pos.mpr hk
  have hkReal : (|A.k| : ℝ) ≤ (L x) ^ C₂ := by
    simpa only [Int.cast_abs] using hkBound
  have hb := hx x hxx P hP A hmass hkpos hkReal hIdeal X hXlo hXhi
  have hdec : (52 : ℝ) / 100 = (0.52 : ℝ) := by norm_num
  simpa [Model.averageMoment, Model.averagedMoment, R, N, dyad, hdec,
    div_eq_mul_inv, mul_comm] using hb

theorem transferenceInputs_of_local
    (hAbs : AbsolutePhysicalPacketTask)
    (hLocal : Erdos821.Blueprint.Graph.local_transference_statement) :
    Erdos821.Blueprint.TransferenceInputs := by
  have hMoment := transferenceEstimate_of_local hLocal
  exact ⟨hAbs, hMoment, PairingFromMomentTask_proof hAbs hMoment⟩

end Erdos821.S2Core
