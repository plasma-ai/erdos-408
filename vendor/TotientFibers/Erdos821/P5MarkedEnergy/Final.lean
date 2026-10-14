import Erdos821.P5MarkedEnergy.FinalNumeric
import Erdos821.P5MarkedEnergy.Decomposition
import Erdos821.P5Energy.Final
import Erdos821.P5.MellinCutoffBridge
import Erdos821.P5.ExceptionalTheorem
import Erdos821.P5.LongRoughProof
import Erdos821.P1.ClassicalInputs

/-! Proof of the frozen `MarkedEndpointEnergyTask`. -/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic P5Core

/-- The coefficient term of one piece, divided by `Y`. -/
theorem sqterm_le {KLM H α αmin Y x sq M0 BB b0 ℓ C v1 v2 Cmk KS hi cS : ℝ}
    (hKLM : 0 ≤ KLM) (hx : 1 ≤ x) (hℓ : ℓ = L x) (hY : x ^ (0.99 : ℝ) ≤ Y) (hH0 : 0 ≤ H)
    (hH : H ≤ x ^ (0.01 : ℝ)) (hα : αmin ≤ α) (hαmin : 0 < αmin)
    (hM0 : 0 ≤ M0) (hM0b : M0 ≤ b0 * ℓ ^ C) (hBB0 : 0 ≤ BB)
    (hBB : BB ≤ ℓ ^ C * v1 * 1 * (ℓ ^ C * (v2 * ℓ ^ Cmk))) (hKS : 0 ≤ KS) (hhi : 0 < hi)
    (hcS : 0 ≤ cS) (hlog : Real.log (2 * (hi * Y)) ≤ 2 * ℓ) (hlog0 : 0 ≤ Real.log (2 * (hi * Y)))
    (hsq : sq ≤ M0 ^ 2 * BB ^ 2 * (KS * (hi * Y) * Real.log (2 * (hi * Y)) ^ cS)) :
    KLM * (H / (α * Y)) ^ 2 * sq ≤
      Y * (KLM * (b0 * ℓ ^ C) ^ 2 * (ℓ ^ C * v1 * 1 * (ℓ ^ C * (v2 * ℓ ^ Cmk))) ^ 2 *
        (KS * hi * (2 * ℓ) ^ cS) / αmin ^ 2 * Real.exp (-(1.96 * ℓ))) := by
  have hxpos : 0 < x := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hY
  have hαpos : 0 < α := lt_of_lt_of_le hαmin hα
  have hq : (H / (α * Y)) ^ 2 ≤ Real.exp (-(1.96 * ℓ)) / αmin ^ 2 := by
    have h1 : (H / (α * Y)) ^ 2 ≤ (x ^ (0.01 : ℝ) / (αmin * x ^ (0.99 : ℝ))) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      apply div_le_div₀ (Real.rpow_nonneg hxpos.le _) hH (by positivity)
      exact mul_le_mul hα hY (Real.rpow_nonneg hxpos.le _) hαpos.le
    have h2 : (x ^ (0.01 : ℝ) / (αmin * x ^ (0.99 : ℝ))) ^ 2 =
        Real.exp (-(1.96 * ℓ)) / αmin ^ 2 := by
      rw [rpow_x_eq hxpos, rpow_x_eq hxpos, ← hℓ, div_pow, mul_pow]
      have e1 : Real.exp (0.01 * ℓ) ^ 2 = Real.exp (0.02 * ℓ) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have e2 : Real.exp (0.99 * ℓ) ^ 2 = Real.exp (1.98 * ℓ) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have e3 : Real.exp (-(1.96 * ℓ)) = Real.exp (0.02 * ℓ) / Real.exp (1.98 * ℓ) := by
        rw [← Real.exp_sub]; congr 1; ring
      rw [e1, e2, e3]
      field_simp
    exact h1.trans (le_of_eq h2)
  have hpw : Real.log (2 * (hi * Y)) ^ cS ≤ (2 * ℓ) ^ cS := Real.rpow_le_rpow hlog0 hlog hcS
  have hpw0 : 0 ≤ Real.log (2 * (hi * Y)) ^ cS := Real.rpow_nonneg hlog0 _
  have hb0 : 0 ≤ b0 * ℓ ^ C := hM0.trans hM0b
  have hℓ0 : 0 ≤ ℓ := by rw [hℓ]; exact Real.log_nonneg hx
  calc KLM * (H / (α * Y)) ^ 2 * sq
      ≤ KLM * (H / (α * Y)) ^ 2 * (M0 ^ 2 * BB ^ 2 * (KS * (hi * Y) *
          Real.log (2 * (hi * Y)) ^ cS)) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = Y * (KLM * M0 ^ 2 * BB ^ 2 * (KS * hi * Real.log (2 * (hi * Y)) ^ cS) *
          (H / (α * Y)) ^ 2) := by ring
    _ ≤ Y * (KLM * (b0 * ℓ ^ C) ^ 2 * (ℓ ^ C * v1 * 1 * (ℓ ^ C * (v2 * ℓ ^ Cmk))) ^ 2 *
          (KS * hi * (2 * ℓ) ^ cS) * (Real.exp (-(1.96 * ℓ)) / αmin ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- The second uniform term (coefficient square sum) divided by `Y`. -/
def Psi2 (ℓ KLM b0 C vmin vmax Cmk KS hi cS αmin : ℝ) : ℝ :=
  KLM * (b0 * ℓ ^ C) ^ 2 * (ℓ ^ C * vmin⁻¹ * 1 * (ℓ ^ C * (vmax * ℓ ^ Cmk))) ^ 2 *
    (KS * hi * (2 * ℓ) ^ cS) / αmin ^ 2 * Real.exp (-(1.96 * ℓ))

set_option maxHeartbeats 4000000 in
/-- One piece and one character, uniformly. -/
theorem piece_final (P : Geometry) (C τ η lo hi : ℝ) (bounds : ℕ → ℝ)
    (K3r c3r Y0sp KW cW : ℝ) (hpiece : PieceBoundSpec K3r c3r Y0sp KW cW)
    (hK3r : 0 < K3r) (hKW : 0 < KW) (hcW : 0 ≤ cW) (hc3r : 0 ≤ c3r)
    (cS KS : ℝ) (hsqS : SqSpec cS KS) (hcS : 0 ≤ cS) (hKS : 0 < KS)
    (Cmk : ℝ) (kk : ℕ) (Kc Cf KA : ℕ → ℝ) (Kmm KAm Cfm As Al At B B0 Kex Kl KLM : ℝ) (j : ℕ)
    (hKcm : ∀ i < kk, Kc i ≤ Kmm) (hKAm : ∀ i < kk, KA i ≤ KAm) (hKA0 : ∀ i, 0 < KA i)
    (hCfm : ∀ i < kk, Cf i ≤ Cfm)
    (hC : 0 < C) (hlo : 0 < lo) (hlohi : lo < hi) (hbounds : ∀ j, 0 ≤ bounds j)
    (x : ℝ) (hexcx : ExcAt P.a P.b As Kex x) (hlongx : LongAt τ η C B0 Kl Al x) (hKl : 0 < Kl)
    (hLMj : LocalMellinAt j KLM) (hKLM : 0 < KLM) (hj : 4 ≤ j)
    (hMCx : ∀ i : Fin kk, ∀ Ψ' : ℝ → ℂ,
      CutoffBound x C (ptA lo i) (ptA lo (i + 2)) Ψ' (pieceBounds lo bounds i) →
      ∃ a : (Fin 1 → ℝ) → ℂ, Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ (Kc i) ∧
        (∀ y : ℝ, 0 < y → Ψ' y = ∫ ξ, a ξ * mellin y (2 * Real.pi * ξ 0)) ∧
        (∫ ξ in {ξ : Fin 1 → ℝ | L x ^ (Cf i) < ‖ξ‖}, ‖a ξ‖) ≤ KA i * L x ^ (-At))
    (hx1 : 1 ≤ x) (hL2 : 2 ≤ L x)
    (hszY : ∀ Y : ℝ, x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) →
      1 ≤ hi * Y ∧ Y0sp ≤ Y ∧ 2 ≤ Y ∧ x ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ x ^ (2 : ℕ) ∧
        2 * Y ≤ x ^ (2 : ℕ))
    (hszα : ∀ Y α : ℝ, x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) → ptA lo 0 ≤ α →
      α ≤ ptA lo kk → 10 ≤ α * Y ∧ x ^ (0.01 : ℝ) ≤ α * Y / 10 ∧ 64 * α * Y ≤ x ^ (2 : ℕ))
    (hszT : ∀ Y H α : ℝ, x ^ (0.99 : ℝ) ≤ Y → Y ≤ x ^ (1.01 : ℝ) →
      Real.exp (L x ^ P.c / 2) ≤ H → 0 < α → α ≤ ptA lo kk → 2 ≤ Y →
      2 * L x / (H / (α * Y)) + 1 ≤ Y ∧ 2 * L x / (H / (α * Y)) + L x ^ C ≤ x ^ (2 : ℕ) ∧
        2 * (2 * L x / (H / (α * Y))) * (16 * Real.exp (L x ^ P.b)) ≤ α * Y)
    (hszz : ∀ Y α P1 P2 : ℝ, x ^ (0.99 : ℝ) ≤ Y → ptA lo 0 ≤ α → α ≤ ptA lo kk →
      Real.exp (L x ^ P.a) / 2 ≤ P1 → P1 ≤ Real.exp (L x ^ P.b) → x ^ τ / 2 ≤ P2 → P2 ≤ x ^ η →
      Y ^ (0.6 : ℝ) * (16 * P1 * P2) ≤ α * Y ∧ 4 * α * Y ≤ Y * (P1 * P2))
    (hszc : ∀ Y : ℝ, x ^ (0.99 : ℝ) ≤ Y →
      Real.exp (Kex * (L x ^ P.b + L x ^ (1 - P.a) * Real.log (L x))) ≤ Y ^ (0.05 : ℝ))
    (hszf : ∀ Y H α : ℝ, x ^ (0.99 : ℝ) ≤ Y → 0 < H → H ≤ x ^ (0.01 : ℝ) →
      ptA lo 0 ≤ α → L x ^ C + 2 * Real.pi * L x ^ Cfm ≤ L x / (H / (α * Y)))
    (hszW : L x ^ (2 * C) < W x) (hszB1 : L x ^ (2 * C) ≤ L x ^ B)
    (hszB2 : L x ^ B0 + L x ^ C ≤ L x ^ B)
    (hszl : ∀ Y : ℝ, Y ≤ x ^ (1.01 : ℝ) → 2 * (hi * Y) ≤ x ^ (2 : ℕ))
    (G : PrimeGroups) (E : Endpoint) (Y H v : ℝ) (t : Fin G.size → ℕ) (b : Tuple G t → ℂ)
    (Ψ : ℝ → ℂ) (r : ℕ) (u : ℤ) (gs : Fin G.size) (ls : Fin (t gs)) (i : Fin kk)
    (χ : DirichletCharacter ℂ r)
    (hG : Admissible P x G) (hE : EndpointBound x C τ η E) (hdisc : discrepancy x B E.alpha)
    (hgs : gs ∈ G.small) (hr1 : 1 ≤ r) (hrC : (r : ℝ) ≤ L x ^ C)
    (hWres : ∀ k, ‖Wres G t gs ls P.q b k‖ ≤ mass G gs * L x ^ Cmk)
    (hΨ : CutoffBound x C lo hi Ψ bounds)
    (hY1 : x ^ (0.99 : ℝ) ≤ Y) (hY2 : Y ≤ x ^ (1.01 : ℝ))
    (hH1 : Real.exp (L x ^ P.c / 2) ≤ H) (hH2 : H ≤ x ^ (0.01 : ℝ)) (hv : |v| ≤ L x ^ C) :
    ∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial (spiece lo hi Y i)
        (bpiece G x Y v lo E Ψ gs (Wres G t gs ls P.q b) r u ⌊hi * Y⌋₊ i χ) θ‖ ^ 2 ≤
      Y * Psi1 (L x) KLM (ptA lo 0) Kmm K3r c3r As Al Kl B0 B C Cmk P.vmax KW cW KAm At j +
        Y * Psi2 (L x) KLM (bounds 0) C P.vmin P.vmax Cmk KS hi cS (ptA lo 0) := by
  set ℓ := L x with hℓdef
  have hL1 : 1 ≤ ℓ := by linarith
  have hLpos : 0 < ℓ := by linarith
  have hi' : (i : ℕ) < kk := i.2
  set α := ptA lo i with hαdef
  have hαlo : ptA lo 0 ≤ α := ptA_mono hlo (Nat.zero_le _)
  have hαhi : α ≤ ptA lo kk := ptA_mono hlo hi'.le
  have hα0 : 0 < ptA lo 0 := ptA_pos hlo 0
  have hαpos : 0 < α := ptA_pos hlo i
  have hmass0 : 0 < mass G gs := P.positive.2.2.1.trans_le (hG.2.2.1 gs).1
  have hmassv : mass G gs ≤ P.vmax := (hG.2.2.1 gs).2
  have hmassm : P.vmin ≤ mass G gs := (hG.2.2.1 gs).1
  have hvmin : 0 < P.vmin := P.positive.2.2.1
  obtain ⟨hhiY, hY0, hY2', hYh, hYx, h2Y⟩ := hszY Y hY1 hY2
  obtain ⟨h10, hHα, h64⟩ := hszα Y α hY1 hY2 hαlo hαhi
  have hHpos : 0 < H := lt_of_lt_of_le (Real.exp_pos _) hH1
  have hH1' : 1 ≤ H := le_trans (Real.one_le_exp (by
    have : 0 ≤ ℓ ^ P.c := Real.rpow_nonneg hLpos.le _
    linarith)) hH1
  obtain ⟨hT1, hT2, hT3⟩ := hszT Y H α hY1 hY2 hH1 hαpos hαhi hY2'
  have hΨsupp : ∀ y, Ψ y ≠ 0 → lo ≤ y ∧ y ≤ hi := fun y hy => hΨ.2.1 hy
  have hΨi := cutoff_piece hlo hC.le hL1 hbounds hΨ i
  obtain ⟨a, ha, haL1, hrep, htail⟩ := hMCx i _ hΨi
  have hR0 : 0 ≤ ℓ ^ Cf i := Real.rpow_nonneg hLpos.le _
  have hfreq : |v| + 2 * Real.pi * ℓ ^ Cf i ≤ ℓ / (H / (α * Y)) := by
    have h1 := hszf Y H α hY1 hHpos hH2 hαlo
    have h2 : ℓ ^ Cf i ≤ ℓ ^ Cfm := Real.rpow_le_rpow_of_exponent_le hL1 (hCfm i hi')
    have h3 : 2 * Real.pi * ℓ ^ Cf i ≤ 2 * Real.pi * ℓ ^ Cfm :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hP := hpiece P x C τ η B As Al B0 Kex Kl lo hi KLM (Kc i) Cmk (ℓ ^ Cf i) (KA i * ℓ ^ (-At)) j
    G E Y H v t b Ψ r u gs ls i χ a hexcx hlongx hKl hLMj hKLM hj hG hE hdisc hgs hr1 hrC hWres hlo
    hΨsupp ha haL1 hrep htail hR0 hx1 hL1 hC (by linarith) hhiY h10 hH1' (hH2.trans hHα) hY0 hYh hYx hT1 hT2
    (fun P1 P2 h1 h2 h3 h4 => hszz Y α P1 P2 hY1 hαlo hαhi h1 h2 h3 h4) hT3 h64 h2Y (hszc Y hY1)
    hszB1 hszB2 hszW hfreq
  -- the coefficient term
  have hΨb : ∀ y, ‖Ψ y‖ ≤ bounds 0 * ℓ ^ C := by
    intro y
    have := hΨ.2.2 0 y
    simpa using this
  have hYpos : 0 < Y := by linarith
  have hsqb := hsqS G x Y v lo hi (bounds 0 * ℓ ^ C) (ℓ ^ C) (mass G gs)⁻¹ 1
    (ℓ ^ C * (mass G gs * ℓ ^ Cmk)) E Ψ gs (Wres G t gs ls P.q b) r u i χ hlo hYpos hhiY hΨb
    (fun m => norm_cf1_le hE r χ m) (fun m => norm_cf2_le G gs hmass0 r χ m)
    (fun m => norm_cf3_le E x r χ m) (fun m => norm_cf4_le G hE _ _ hWres r u χ m)
  have hlogx2 : Real.log (x ^ (2 : ℕ)) = 2 * ℓ := by rw [Real.log_pow]; push_cast; rfl
  have hlogY : Real.log (2 * (hi * Y)) ≤ 2 * ℓ := by
    rw [← hlogx2]; exact Real.log_le_log (by linarith) (hszl Y hY2)
  have hlogY0 : 0 ≤ Real.log (2 * (hi * Y)) := Real.log_nonneg (by linarith)
  have hLC : 0 ≤ ℓ ^ C := Real.rpow_nonneg hLpos.le _
  have hLCm : 0 ≤ ℓ ^ Cmk := Real.rpow_nonneg hLpos.le _
  have hBB : ℓ ^ C * (mass G gs)⁻¹ * 1 * (ℓ ^ C * (mass G gs * ℓ ^ Cmk)) ≤
      ℓ ^ C * P.vmin⁻¹ * 1 * (ℓ ^ C * (P.vmax * ℓ ^ Cmk)) := by
    have h1 : (mass G gs)⁻¹ ≤ P.vmin⁻¹ := inv_anti₀ hvmin hmassm
    gcongr
  have hSqT := sqterm_le (KLM := KLM) (H := H) (α := α) (αmin := ptA lo 0) (Y := Y) (x := x)
    (ℓ := ℓ) hKLM.le hx1 rfl hY1 hHpos.le hH2 hαlo hα0 (mul_nonneg (hbounds 0) hLC) le_rfl
    (by positivity) hBB
    hKS.le (by linarith) hcS hlogY hlogY0 hsqb
  -- uniform atoms
  set K := Nat.log 2 ⌊hi * Y⌋₊ with hK
  have hKle : ((K : ℕ) : ℝ) ≤ 3 * ℓ := log2_floor_le hx1 hhiY (by
    have := hszl Y hY2; linarith)
  have hcR : (((relBoxes K (α * Y)).card : ℕ) : ℝ) ≤ (3 * ℓ + 1) ^ 4 :=
    (card_relBoxes_le K (α * Y)).trans (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hA1 : ℓ ^ (Kc i) ≤ ℓ ^ Kmm := Real.rpow_le_rpow_of_exponent_le hL1 (hKcm i hi')
  have hJ := J3_le_PhiJ (ℓ := ℓ) (K3r := K3r) (c3r := c3r) (As := As) (Al := Al) (Kl := Kl)
    (B0 := B0) (B := B) (C := C) (Cmk := Cmk) (vmax := P.vmax) hLpos hK3r.le hmass0 hmassv
  have hW := WM_eq_PhiW (ℓ := ℓ) (KW := KW) (cW := cW) (C := C) (Cmk := Cmk) hmass0
  have hεt : KA i * ℓ ^ (-At) ≤ KAm * ℓ ^ (-At) :=
    mul_le_mul_of_nonneg_right (hKAm i hi') (Real.rpow_nonneg hLpos.le _)
  have hB0nn : 0 ≤ ℓ ^ B0 := Real.rpow_nonneg hLpos.le _
  have hc3nn : 0 ≤ (2 * ℓ) ^ c3r := Real.rpow_nonneg (by positivity) _
  have hcWnn : 0 ≤ (2 * ℓ) ^ cW := Real.rpow_nonneg (by positivity) _
  have hrhs := piece_rhs_le (KLM := KLM) (α := α) (αmin := ptA lo 0) (Y := Y)
    (cR := (((relBoxes K (α * Y)).card : ℕ) : ℝ)) (cRb := (3 * ℓ + 1) ^ 4) (A1 := ℓ ^ (Kc i))
    (A1b := ℓ ^ Kmm) (J3b := PhiJ ℓ K3r c3r As Al Kl B0 B C Cmk P.vmax)
    (w := ((1 + ℓ) ^ (j - 4))⁻¹) (WMb := PhiW ℓ KW cW C Cmk) (εt := KA i * ℓ ^ (-At))
    (εb := KAm * ℓ ^ (-At)) (SqT := KLM * (H / (α * Y)) ^ 2 * sqNorm (spiece lo hi Y i)
      (bpiece G x Y v lo E Ψ gs (Wres G t gs ls P.q b) r u ⌊hi * Y⌋₊ i χ))
    hKLM.le hαlo hα0 hYpos (Nat.cast_nonneg _) hcR (Real.rpow_nonneg hLpos.le _) hA1
    (by positivity) hJ (by positivity) (by positivity) hW.le
    (mul_nonneg (hKA0 i).le (Real.rpow_nonneg hLpos.le _)) hεt
  refine hP.trans (hrhs.trans ?_)
  apply add_le_add le_rfl
  exact hSqT

/-- The error term divided by `Y`. -/
def Psi3 (ℓ b0 C Cms Cmk J0 KE lo cE vmax a : ℝ) : ℝ :=
  (b0 * ℓ ^ C * (ℓ ^ Cms + 3 * ℓ * ℓ ^ Cmk)) ^ 2 *
    (J0 * KE * lo * ℓ ^ (4 * C) * (2 * ℓ) ^ cE * (vmax * Real.exp (-(ℓ ^ a))))

set_option maxHeartbeats 2000000 in
/-- The square-multiple error, uniformly. -/
theorem error_final (P : Geometry) (C τ η lo hi : ℝ) (bounds : ℕ → ℝ) (cE KE : ℝ)
    (herrS : ErrorSpec cE KE) (hcE : 0 ≤ cE) (hKE : 0 < KE) (Cms Cmk : ℝ) (J0 : ℕ)
    (hJ0 : hi ≤ lo * 2 ^ J0) (hlo : 0 < lo) (hlohi : lo < hi) (hbounds : ∀ j, 0 ≤ bounds j)
    (x : ℝ) (hx1 : 1 ≤ x) (hL2 : 2 ≤ L x)
    (hszerr : ∀ Y : ℝ, x ^ (0.99 : ℝ) ≤ Y → ∀ p : ℕ, (p : ℝ) ≤ Real.exp (L x ^ P.b) →
      ((p ^ 2 : ℕ) : ℝ) ≤ lo * Y)
    (hszl2 : ∀ Y : ℝ, Y ≤ x ^ (1.01 : ℝ) → 4 * (lo * Y * 2 ^ J0) ≤ x ^ (2 : ℕ))
    (hszl : ∀ Y : ℝ, Y ≤ x ^ (1.01 : ℝ) → 2 * (hi * Y) ≤ x ^ (2 : ℕ))
    (G : PrimeGroups) (E : Endpoint) (Y v : ℝ) (t : Fin G.size → ℕ) (b : Tuple G t → ℂ)
    (Ψ : ℝ → ℂ) (r : ℕ) (u : ℤ) (gs : Fin G.size) (ls : Fin (t gs))
    (hG : Admissible P x G) (hE : EndpointBound x C τ η E) (hgs : gs ∈ G.small)
    (hbinv : ∀ z z' : Tuple G t, (∀ g, g ∈ G.big → z g = z' g) → b z = b z')
    (hWm : ∀ n, ‖weightedMarks G P.q t b n‖ ≤ L x ^ Cms)
    (hWres : ∀ k, ‖Wres G t gs ls P.q b k‖ ≤ mass G gs * L x ^ Cmk)
    (hΨ : CutoffBound x C lo hi Ψ bounds)
    (hY1 : x ^ (0.99 : ℝ) ≤ Y) (hY2 : Y ≤ x ^ (1.01 : ℝ)) :
    (∑ n ∈ Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊,
        ‖epsf P G x Y v E t b Ψ gs (Wres G t gs ls P.q b) r u n‖ ^ 2) ≤
      Y * Psi3 (L x) (bounds 0) C Cms Cmk ((J0 : ℝ) + 1) KE (lo * 2 ^ J0) cE P.vmax P.a := by
  set ℓ := L x with hℓ
  have hL1 : 1 ≤ ℓ := by linarith
  have hLpos : 0 < ℓ := by linarith
  have hxpos : 0 < x := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hY1
  have hmass0 : 0 < mass G gs := P.positive.2.2.1.trans_le (hG.2.2.1 gs).1
  have hmassv : mass G gs ≤ P.vmax := (hG.2.2.1 gs).2
  have hΨb : ∀ y, ‖Ψ y‖ ≤ bounds 0 * ℓ ^ C := by
    intro y; have := hΨ.2.2 0 y; simpa using this
  have hlogx2 : Real.log (x ^ (2 : ℕ)) = 2 * ℓ := by rw [Real.log_pow]; push_cast; rfl
  -- the mark difference
  have hMw : ∀ n ∈ Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊,
      ‖weightedMarks G P.q t b n - Wtil G gs (Wres G t gs ls P.q b) n‖ ≤
        ℓ ^ Cms + 3 * ℓ * ℓ ^ Cmk := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hnpos : 1 ≤ n := by
      have : 0 < ⌈lo * Y⌉₊ := Nat.ceil_pos.mpr (by positivity)
      omega
    have hnR : (n : ℝ) ≤ hi * Y := (Nat.le_floor_iff' (by omega)).mp hn2
    have hcard := card_primes_dvd_le ((G.primes gs).filter (fun p => p ∣ n))
      (fun p hp => G.prime gs p (Finset.mem_filter.mp hp).1) n hnpos
      (fun p hp => (Finset.mem_filter.mp hp).2)
    have hlogn : Real.log n ≤ 2 * ℓ := by
      rw [← hlogx2]
      exact Real.log_le_log (by exact_mod_cast hnpos) (by have := hszl Y hY2; linarith)
    have hcard3 : (((G.primes gs).filter (fun p => p ∣ n)).card : ℝ) ≤ 3 * ℓ := by
      have hl2 : (2 : ℝ) / 3 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hl2pos : 0 < Real.log 2 := by linarith
      refine hcard.trans ?_
      rw [div_le_iff₀ hl2pos]
      nlinarith
    have hWt := norm_Wtil_le G gs (Wres G t gs ls P.q b) _ hWres hmass0 n
    have e : (mass G gs)⁻¹ * (mass G gs * ℓ ^ Cmk) = ℓ ^ Cmk := by field_simp
    rw [e] at hWt
    have hLCm : 0 ≤ ℓ ^ Cmk := Real.rpow_nonneg hLpos.le _
    calc ‖weightedMarks G P.q t b n - Wtil G gs (Wres G t gs ls P.q b) n‖
        ≤ ‖weightedMarks G P.q t b n‖ + ‖Wtil G gs (Wres G t gs ls P.q b) n‖ := norm_sub_le _ _
      _ ≤ ℓ ^ Cms + 3 * ℓ * ℓ ^ Cmk := by
          have := mul_le_mul_of_nonneg_right hcard3 hLCm
          linarith [hWm n]
  have hp2 : ∀ p ∈ G.primes gs, ((p ^ 2 : ℕ) : ℝ) ≤ lo * Y := by
    intro p hp
    have hadm := hG.2.2.2.1 gs p hp
    rw [if_pos hgs] at hadm
    exact hszerr Y hY1 p hadm.2
  have h := herrS P G x C τ η Y v lo hi (bounds 0 * ℓ ^ C) (ℓ ^ Cms + 3 * ℓ * ℓ ^ Cmk) E t b Ψ gs ls
    r u J0 hL1 hE hlo hYpos hJ0 hgs hmass0 hbinv hp2 hΨb hMw
  refine h.trans ?_
  -- the removed-prime sum
  have hsum : ∑ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2) ≤ P.vmax * Real.exp (-(ℓ ^ P.a)) := by
    have hterm : ∀ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2) ≤ Real.exp (-(ℓ ^ P.a)) * (1 / (p : ℝ)) := by
      intro p hp
      have hadm := hG.2.2.2.1 gs p hp
      rw [if_pos hgs] at hadm
      have hppos : (0 : ℝ) < p := lt_of_lt_of_le (Real.exp_pos _) hadm.1
      have h1 : 1 / (p : ℝ) ≤ Real.exp (-(ℓ ^ P.a)) := by
        rw [Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le (Real.exp_pos _) hadm.1
      calc 1 / ((p : ℝ) ^ 2) = (1 / (p : ℝ)) * (1 / (p : ℝ)) := by ring
        _ ≤ Real.exp (-(ℓ ^ P.a)) * (1 / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
    calc ∑ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2) ≤ ∑ p ∈ G.primes gs, Real.exp (-(ℓ ^ P.a)) * (1 / (p : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = Real.exp (-(ℓ ^ P.a)) * mass G gs := by rw [← Finset.mul_sum]; rfl
      _ ≤ Real.exp (-(ℓ ^ P.a)) * P.vmax := mul_le_mul_of_nonneg_left hmassv (Real.exp_pos _).le
      _ = P.vmax * Real.exp (-(ℓ ^ P.a)) := by ring
  have hlog4 : Real.log (4 * (lo * Y * 2 ^ J0)) ≤ 2 * ℓ := by
    rw [← hlogx2]; exact Real.log_le_log (by positivity) (hszl2 Y hY2)
  have hlog40 : 0 ≤ Real.log (4 * (lo * Y * 2 ^ J0)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 ^ J0 := one_le_pow₀ (by norm_num)
    have : 1 ≤ lo * Y := by
      have hne : (G.primes gs).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have : mass G gs = 0 := by unfold mass; rw [hemp, Finset.sum_empty]
        linarith
      obtain ⟨p, hp⟩ := hne
      have hpp := hp2 p hp
      have h2 : 2 ≤ p := (G.prime gs p hp).two_le
      have : (4 : ℝ) ≤ ((p ^ 2 : ℕ) : ℝ) := by exact_mod_cast (by nlinarith : 4 ≤ p ^ 2)
      linarith
    nlinarith
  have hpw : Real.log (4 * (lo * Y * 2 ^ J0)) ^ cE ≤ (2 * ℓ) ^ cE := Real.rpow_le_rpow hlog40 hlog4 hcE
  have hsum0 : 0 ≤ ∑ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2) := Finset.sum_nonneg fun p _ => by positivity
  have hb0 : 0 ≤ bounds 0 := hbounds 0
  have hpw0 : 0 ≤ Real.log (4 * (lo * Y * 2 ^ J0)) ^ cE := Real.rpow_nonneg hlog40 _
  unfold Psi3
  calc (bounds 0 * ℓ ^ C * (ℓ ^ Cms + 3 * ℓ * ℓ ^ Cmk)) ^ 2 * (((J0 : ℝ) + 1) * KE *
        (lo * Y * 2 ^ J0) * ℓ ^ (4 * C) * Real.log (4 * (lo * Y * 2 ^ J0)) ^ cE *
        ∑ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2))
      = Y * ((bounds 0 * ℓ ^ C * (ℓ ^ Cms + 3 * ℓ * ℓ ^ Cmk)) ^ 2 * (((J0 : ℝ) + 1) * KE *
        (lo * 2 ^ J0) * ℓ ^ (4 * C) * Real.log (4 * (lo * Y * 2 ^ J0)) ^ cE *
        ∑ p ∈ G.primes gs, 1 / ((p : ℝ) ^ 2))) := by ring
    _ ≤ Y * ((bounds 0 * ℓ ^ C * (ℓ ^ Cms + 3 * ℓ * ℓ ^ Cmk)) ^ 2 * (((J0 : ℝ) + 1) * KE *
        (lo * 2 ^ J0) * ℓ ^ (4 * C) * (2 * ℓ) ^ cE * (P.vmax * Real.exp (-(ℓ ^ P.a))))) := by
        gcongr

end Erdos821.P5Marked
