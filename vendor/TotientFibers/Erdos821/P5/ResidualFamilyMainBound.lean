import Erdos821.P5.MellinFrequencyBounds

noncomputable section
open scoped BigOperators Classical
open Filter

namespace Erdos821.P5Core
open Blueprint.Analytic
open Blueprint.Graph hiding L T PrimeGroups

/-- An actual residual family, chosen independently of endpoints and
frequencies, satisfies P3 on the whole main Mellin frequency ball. -/
theorem residual_family_main_dyadic_bound (ht : TransferencePairing) (hid : IdealConstruction)
    (P : Geometry) (C τ η Cf D : ℝ) (hC : 0 < C) (hτ : 0 < τ) (hτhi : τ ≤ 1)
    (hD : 0 < D) :
    ∃ m J₀ : ℕ, ∃ C₁ qexp hexp ξexp : ℝ,
      0 < qexp ∧ 0 < hexp ∧ 0 < ξexp ∧
      ∀ J : ℕ, J₀ ≤ J → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
        ∀ (G : PrimeGroups), Admissible P x G → ∃ B : Family P.graph G.graph J m,
          B.Residual ⌊L x ^ qexp⌋₊ (L x ^ (-hexp)) (L x ^ (-ξexp)) ∧
          (B.model 1 0).patternMass ≤ L x ^ C₁ ∧
          ∀ (E H : Endpoint) (k : ℤ) (Z a₁ a₂ ζ : ℝ) (ξ : Fin 1 → ℝ) (i : ℕ),
            EndpointBound x C τ η E → EndpointBound x C τ η H →
            k ≠ 0 → |(k : ℝ)| ≤ L x ^ C → |a₁| ≤ L x ^ C → |a₂| ≤ L x ^ C →
            ζ = -a₁ - a₂ → ‖ξ‖ ≤ L x ^ Cf → i ∈ retainedSourceDyads x τ →
            ‖dyadicMellinPairing B x Z a₁ a₂ E H k ζ i (mellinFrequency ξ)‖ ≤ K * L x ^ (-D) := by
  obtain ⟨Eid, hEid, htransfer⟩ := dyadic_mellin_transference ht P C τ η hC hτ hτhi D hD
  have hfreq := eventual_mellin_shift_frequency_bound C Cf hC
  obtain ⟨m, Jid, C₁, qexp, hexp, ξexp, hq, hh, hξ, hideal⟩ :=
    hid P.graph Eid (max C Cf + 1) hEid hfreq.1
  obtain ⟨Jtransfer, hJtransfer⟩ := htransfer m C₁
  refine ⟨m, max Jid Jtransfer, C₁, qexp, hexp, ξexp, hq, hh, hξ, ?_⟩
  intro J hJ
  have hJid : Jid ≤ J := (le_max_left _ _).trans hJ
  have hJtrans : Jtransfer ≤ J := (le_max_right _ _).trans hJ
  obtain ⟨K, hK, hpair⟩ := hJtransfer J hJtrans
  refine ⟨K, hK, ?_⟩
  filter_upwards [hideal J hJid, hpair, hfreq.2] with x hid hpair hfreq
  intro G hG
  obtain ⟨B, hres, hmass, hkernel⟩ := hid G.graph (graph_admissible P x G hG)
    (graph_intervalBigGroups P x G hG)
  refine ⟨B, hres, hmass, ?_⟩
  intro E H k Z a₁ a₂ ζ ξ i hE hH hk hkbound ha₁ ha₂ hζ hξ hi
  exact hpair G B E H k Z a₁ a₂ ζ (mellinFrequency ξ) i hG hE hH hmass hk hkbound
    (fun θ => hkernel θ (ζ - mellinFrequency ξ) (hfreq a₁ a₂ ζ ξ ha₁ ha₂ hζ hξ)) hi

end Erdos821.P5Core
