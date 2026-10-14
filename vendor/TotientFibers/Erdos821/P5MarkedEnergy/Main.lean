import Erdos821.P5MarkedEnergy.Final

/-! The exported proof of `Erdos821.P5Core.MarkedEndpointEnergyTask`. -/

noncomputable section
open scoped BigOperators
open Filter MeasureTheory Classical

namespace Erdos821.P5Core
open Blueprint.Analytic P5Marked

set_option maxHeartbeats 8000000 in
theorem MarkedEndpointEnergyTask_proof : MarkedEndpointEnergyTask := by
  intro P R C A τ η lo hi bounds hC hA hlo hlohi hbounds
  by_cases hτη : 0 < τ ∧ η < 1 / 4
  swap
  · refine ⟨1, 1, one_pos, one_pos, Filter.Eventually.of_forall ?_⟩
    intro x G E Y H v t b Ψ r u hG hE
    exact absurd ⟨hE.1, hE.2.2.1⟩ hτη
  obtain ⟨hτ, hη⟩ := hτη
  have hPa : 0 < P.a := P.ordered.1
  have hPab : P.a < P.b := P.ordered.2.1
  have hPbc : P.b < P.c := P.ordered.2.2.1
  have hPcd : P.c < P.d := P.ordered.2.2.2.1
  have hPd : P.d < 0.47 := P.ordered.2.2.2.2
  have hPb1 : P.b < 1 := by linarith
  have hPb0 : 0 ≤ P.b := by linarith
  have hPc0 : 0 < P.c := by linarith
  have hvmin : 0 < P.vmin := P.positive.2.2.1
  have hvmax : 0 < P.vmax := lt_of_lt_of_le hvmin P.positive.2.2.2
  obtain ⟨K3r, c3r, Y0sp, KW, cW, hK3r, hc3r, hY0sp, hKW, hcW, hpiece⟩ := piece_bound'
  obtain ⟨Cmk, hCmk⟩ := norm_Wres_le P R
  obtain ⟨Cms, hCms⟩ := mark_sup P R
  obtain ⟨cE, KE, hcE, hKE, herrS⟩ := error_total'
  obtain ⟨cS, KS, hcS, hKS, hsqS⟩ := sq_total'
  obtain ⟨kk, hkk⟩ := exists_ptA_ge hlo hi
  obtain ⟨J0, hJ0⟩ : ∃ J0 : ℕ, hi ≤ lo * 2 ^ J0 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (hi / lo) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hlo] at hn
    linarith
  have hMC := mellinCutoffTask_proof Blueprint.classical_inputs.separation
  have hMCi : ∀ i : ℕ, ∃ Cf K : ℝ, 0 < Cf ∧ 0 < K ∧ ∀ At : ℝ, 0 < At → ∃ KA : ℝ, 0 < KA ∧
      ∀ᶠ x : ℝ in atTop, ∀ Ψ' : ℝ → ℂ,
        CutoffBound x C (ptA lo i) (ptA lo (i + 2)) Ψ' (pieceBounds lo bounds i) →
        ∃ a : (Fin 1 → ℝ) → ℂ, Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ K ∧
          (∀ y : ℝ, 0 < y → Ψ' y = ∫ ξ, a ξ * mellin y (2 * Real.pi * ξ 0)) ∧
          (∫ ξ in {ξ : Fin 1 → ℝ | L x ^ Cf < ‖ξ‖}, ‖a ξ‖) ≤ KA * L x ^ (-At) :=
    fun i => hMC C (ptA lo i) (ptA lo (i + 2)) (pieceBounds lo bounds i) hC (ptA_pos hlo i)
      (lt_of_lt_of_le (ptA_lt_succ hlo i) (ptA_mono hlo (by omega)))
      (pieceBounds_nonneg hlo hbounds i)
  choose Cf Kc hCf hKc hMCt using hMCi
  set Kmm : ℝ := ∑ i ∈ Finset.range kk, Kc i with hKmm
  set Cfm : ℝ := ∑ i ∈ Finset.range kk, Cf i with hCfm
  have hKcm : ∀ i < kk, Kc i ≤ Kmm := fun i hi =>
    Finset.single_le_sum (f := Kc) (fun j _ => (hKc j).le) (Finset.mem_range.mpr hi)
  have hCfm' : ∀ i < kk, Cf i ≤ Cfm := fun i hi =>
    Finset.single_le_sum (f := Cf) (fun j _ => (hCf j).le) (Finset.mem_range.mpr hi)
  -- the parameters
  set Sz : ℝ := 2 * |C| + 8 + 2 * |Kmm| + 4 * |C| + 2 * |Cmk| + |c3r| + |cW| + 1 with hSz
  set E1 : ℝ := Sz + |A| + 1 with hE1def
  have hSzpos : 0 ≤ Sz := by positivity
  have hE1 : 0 < E1 := by positivity
  set j : ℕ := 4 + ⌈E1⌉₊ with hj
  obtain ⟨Kex, hKex, hexc⟩ := exceptional_times P.a P.b E1 hPa hPab hPb1 hE1
  obtain ⟨B0, Kl, hB0, hKl, hlong⟩ :=
    Blueprint.Analytic.long_rough_polynomial_proof τ η C E1 hτ hη hC hE1
  obtain ⟨KLM, hKLM, hLM⟩ := LocalMellinEnergyTask_proof j (by omega)
  choose KA hKA hMCx using fun i : ℕ => hMCt i E1 hE1
  set KAm : ℝ := ∑ i ∈ Finset.range kk, KA i with hKAmdef
  have hKAm : ∀ i < kk, KA i ≤ KAm := fun i hi =>
    Finset.single_le_sum (f := KA) (fun j _ => (hKA j).le) (Finset.mem_range.mpr hi)
  have hKAm0 : 0 ≤ KAm := Finset.sum_nonneg fun i _ => (hKA i).le
  set B : ℝ := Sz + |B0| + |A| + 2 + 2 * |C| + 1 with hBdef
  have hBpos : 0 < B := by positivity
  refine ⟨B, 1, hBpos, one_pos, ?_⟩
  -- exponent bookkeeping
  have hj4 : ((j - 4 : ℕ) : ℝ) = (⌈E1⌉₊ : ℝ) := by rw [hj, Nat.add_sub_cancel_left]
  have hceil : E1 ≤ (⌈E1⌉₊ : ℝ) := Nat.le_ceil E1
  have aC := le_abs_self C; have aK := le_abs_self Kmm; have aCm := le_abs_self Cmk
  have ac3 := le_abs_self c3r; have acW := le_abs_self cW; have aA := le_abs_self A
  have aB0 := le_abs_self B0
  have nC := abs_nonneg C; have nK := abs_nonneg Kmm; have nCm := abs_nonneg Cmk
  have nc3 := abs_nonneg c3r; have ncW := abs_nonneg cW; have nA := abs_nonneg A
  have nB0 := abs_nonneg B0
  have he1 : (2 * C + 4 + 4) + Kmm + Kmm + 0 + 2 * (-E1) + 1 + 2 * (C + C + Cmk) + c3r < -A := by
    rw [hE1def, hSz]; linarith only [aC, aK, aCm, ac3, acW, aA, aB0, nC, nK, nCm, nc3, ncW, nA, nB0]
  have he2 : (2 * C + 4 + 4) + Kmm + Kmm + 0 + 2 * (-E1) + 2 * (C + C + Cmk) + c3r + 1 < -A := by
    rw [hE1def, hSz]; linarith only [aC, aK, aCm, ac3, acW, aA, aB0, nC, nK, nCm, nc3, ncW, nA, nB0]
  have he3 : (2 * C + 4 + 4) + Kmm + Kmm + B0 + 2 * (-B) + 2 * (C + Cmk) < -A := by
    rw [hBdef, hSz]; linarith only [aC, aK, aCm, ac3, acW, aA, aB0, nC, nK, nCm, nc3, ncW, nA, nB0]
  have he4 : (2 * C + 4 + 4) + Kmm + Kmm + (-((j - 4 : ℕ) : ℝ)) + 1 + 2 * (C + C + Cmk) + cW < -A := by
    rw [hj4]; rw [hE1def, hSz] at hceil; linarith only [hceil, aC, aK, aCm, ac3, acW, aA, nC, nK, nCm, nc3, ncW, nA]
  have he5 : (2 * C + 4 + 4) + Kmm + (-E1) + 1 + 2 * (C + C + Cmk) + cW < -A := by
    rw [hE1def, hSz]; linarith only [aC, aK, aCm, ac3, acW, aA, aB0, nC, nK, nCm, nc3, ncW, nA, nB0]
  have hB1 : 2 * C ≤ B := by rw [hBdef]; linarith
  have hB2 : B0 + 1 ≤ B := by rw [hBdef]; linarith
  have hB3 : C + 1 ≤ B := by rw [hBdef]; linarith
  -- eventual facts
  have hMCall : ∀ᶠ x : ℝ in atTop, ∀ i : Fin kk, ∀ Ψ' : ℝ → ℂ,
      CutoffBound x C (ptA lo i) (ptA lo (i + 2)) Ψ' (pieceBounds lo bounds i) →
      ∃ a : (Fin 1 → ℝ) → ℂ, Integrable a ∧ (∫ ξ, ‖a ξ‖) ≤ L x ^ (Kc i) ∧
        (∀ y : ℝ, 0 < y → Ψ' y = ∫ ξ, a ξ * mellin y (2 * Real.pi * ξ 0)) ∧
        (∫ ξ in {ξ : Fin 1 → ℝ | L x ^ (Cf i) < ‖ξ‖}, ‖a ξ‖) ≤ KA i * L x ^ (-E1) :=
    Filter.eventually_all.mpr (fun i => hMCx i)
  have hn1 := ev_psi1 (kk : ℝ) KLM (ptA lo 0) Kmm K3r c3r E1 E1 Kl B0 B C Cmk P.vmax KW cW KAm E1 A j
    (Nat.cast_nonneg _) hKLM.le (ptA_pos hlo 0) hK3r.le hKl.le hvmax.le hKW.le hKAm0 he1 he2 he3 he4 he5
  have hn2 := ev_psi2 (kk : ℝ) KLM (bounds 0) C P.vmin⁻¹ P.vmax Cmk KS hi cS (ptA lo 0) A
    (Nat.cast_nonneg _) hKLM.le (hbounds 0) (inv_nonneg.mpr hvmin.le) hvmax.le hKS.le (by linarith)
    (ptA_pos hlo 0)
  have hn3 := ev_psi3 (bounds 0) C Cms Cmk ((J0 : ℝ) + 1) KE (lo * 2 ^ J0) cE P.vmax P.a A hPa
    (hbounds 0) (by positivity) hKE.le (by positivity) hvmax.le
  have hH2ev : ∀ᶠ x : ℝ in atTop, 2 * Real.log 2 ≤ L x ^ P.c := ev_const_le_rpow _ _ hPc0
  filter_upwards [hCmk, hCms, hexc, hlong, hMCall, hn1, hn2, hn3,
    sz_Y Y0sp hi (by linarith), sz_alpha (ptA lo 0) (ptA lo kk) (ptA_pos hlo 0),
    sz_T1 C P.b P.c (ptA lo kk) hPb0 hPbc,
    sz_hz1 P.a P.b τ η (ptA lo 0) (ptA lo kk) hPb1 hτ hη (ptA_pos hlo 0),
    sz_count P.a P.b Kex hPa hPb1 hKex, sz_freq C Cfm (ptA lo 0) (ptA_pos hlo 0),
    sz_err P.b lo hPb1 hlo, sz_W C P.d (by linarith), sz_expa C P.a hPa,
    ev_const_xpow_le (2 * hi) 1.01 2 (by norm_num),
    ev_const_xpow_le (4 * (lo * 2 ^ J0)) 1.01 2 (by norm_num), hH2ev, ev_x_ge 1, ev_L_ge 2]
    with x hCmkx hCmsx hexcx hlongx hMCx' hn1x hn2x hn3x hszY hszα hszT hszz hszc hszf hszerr
      hszW hszexpa hszl hszl2 hH2x hx1 hL2
  intro G E Y H v t b Ψ r u hG hE hY1 hY2 hH1 hH2 hv htR hsmall hb1 hbinv hΨ hr1 hrC hdisc
  obtain ⟨gs, hgs, hgs1⟩ := hsmall
  set ls : Fin (t gs) := ⟨0, by omega⟩ with hls
  set Wr := Wres G t gs ls P.q b with hWr
  set ℓ := L x with hℓ
  have hL1 : 1 ≤ ℓ := by linarith
  have hLpos : 0 < ℓ := by linarith
  have hxpos : 0 < x := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hY1
  have hWres : ∀ k, ‖Wr k‖ ≤ mass G gs * ℓ ^ Cmk := hCmkx G hG t gs ls b htR hb1
  have hWm : ∀ n, ‖weightedMarks G P.q t b n‖ ≤ ℓ ^ Cms := by
    intro n; have := hCmsx G hG t b 1 htR zero_le_one hb1 n; rwa [one_mul] at this
  obtain ⟨hszB1, hszB2⟩ := sz_B hL2 hB1 hB2 hB3
  have hHge2 : 2 ≤ H := by
    have h1 : Real.log 2 ≤ ℓ ^ P.c / 2 := by linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (ℓ ^ P.c / 2) := Real.exp_le_exp.mpr h1
      _ ≤ H := hH1
  have hx2 : ∀ z : ℝ, x ^ (2 : ℕ) = x ^ (2 : ℝ) := fun _ => by norm_cast
  have hszl' : ∀ Y' : ℝ, Y' ≤ x ^ (1.01 : ℝ) → 2 * (hi * Y') ≤ x ^ (2 : ℕ) := by
    intro Y' hY'
    rw [hx2 0]
    have : 2 * hi * Y' ≤ 2 * hi * x ^ (1.01 : ℝ) :=
      mul_le_mul_of_nonneg_left hY' (by linarith)
    linarith
  have hszl2' : ∀ Y' : ℝ, Y' ≤ x ^ (1.01 : ℝ) → 4 * (lo * Y' * 2 ^ J0) ≤ x ^ (2 : ℕ) := by
    intro Y' hY'
    rw [hx2 0]
    have : 4 * (lo * 2 ^ J0) * Y' ≤ 4 * (lo * 2 ^ J0) * x ^ (1.01 : ℝ) :=
      mul_le_mul_of_nonneg_left hY' (by positivity)
    linarith
  -- structural facts
  have hfree : ∀ m, rough (W x) m → S56Core.GroupFree G m := by
    intro m hm p hp hpm
    obtain ⟨g, _, hpg⟩ := Finset.mem_biUnion.mp hp
    have hadm := hG.2.2.2.1 g p hpg
    have hple : (p : ℝ) ≤ Real.exp (ℓ ^ P.d) := by
      split_ifs at hadm with hgsm
      · exact hadm.2.trans (Real.exp_le_exp.mpr
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)))
      · exact hadm.2
    have := hm.2 p (G.prime g p hpg) hpm
    linarith [hszW.2]
  have hαrough : ∀ m, E.alpha m ≠ 0 → rough (W x) m := hE.2.2.2.2.1
  have hinv : ∀ e k, S56Core.GroupFree G e → Wr (e * k) = Wr k :=
    fun e k he => Wres_mul_groupFree ls hgs P.q b hbinv he
  have hrW : (r : ℝ) < W x := lt_of_le_of_lt hrC
    (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hszW.1)
  have hcop : ∀ m s p, A0 E m * S0 G gs s * P0 E x p ≠ 0 → Nat.Coprime (m * s * p) r := by
    intro m s p h
    have hA : A0 E m ≠ 0 := fun h' => h (by rw [h']; ring)
    have hS : S0 G gs s ≠ 0 := fun h' => h (by rw [h']; ring)
    have hP' : P0 E x p ≠ 0 := fun h' => h (by rw [h']; ring)
    have hαm : E.alpha m ≠ 0 := fun h' => hA (by simp [A0, h'])
    have hm : Nat.Coprime m r := coprime_of_rough (hαrough m hαm) hr1 hrW
    have hsP : s ∈ G.primes gs := by
      by_contra hs'; exact hS (by simp [S0, hs'])
    have hs : Nat.Coprime s r := by
      have hadm := hG.2.2.2.1 gs s hsP
      rw [if_pos hgs] at hadm
      apply Nat.coprime_of_lt_prime (by omega) _ (G.prime gs s hsP)
      have : (r : ℝ) < s := lt_of_le_of_lt hrC (lt_of_lt_of_le hszexpa hadm.1)
      exact_mod_cast this
    have hp : Nat.Coprime p r := by
      unfold P0 at hP'
      split_ifs at hP' with hc
      · exact coprime_of_rough hc.2.2 hr1 hrW
      · exact absurd rfl hP'
    exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr ⟨hm, hs⟩, hp⟩
  -- the decomposition
  set S := Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊ with hS
  have hsupp' : ∀ p : Fin kk × DirichletCharacter ℂ r, ∀ n ∈ S, n ∉ spiece lo hi Y p.1 →
      bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ p.1 p.2 n = 0 := by
    intro p n hn hns
    unfold bpiece
    have : psi lo p.1 (n / Y) = 0 := by
      by_contra hpsi
      apply hns
      obtain ⟨h1, h2⟩ := psi_support hlo p.1 hpsi
      refine Finset.mem_filter.mpr ⟨hn, ?_, ?_⟩
      · rw [le_div_iff₀ hYpos] at h1; linarith
      · rw [div_le_iff₀ hYpos] at h2; linarith
    simp [this]
  have hdec := energy_decomposition (ι := Fin kk × DirichletCharacter ℂ r) S
    (markedEnergyCoefficient P G x Y v E t b Ψ) ((u : ℝ) / r) H hHge2
    (fun p => spiece lo hi Y p.1) (fun p => bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ p.1 p.2)
    (epsf P G x Y v E t b Ψ gs Wr r u)
    (fun n hn => pointwise_decomposition P G x Y v lo hi E t b Ψ gs Wr r u kk hr1 hlo hYpos hkk
      hΨ.2.1 hfree hαrough hinv hcop n hn)
    hsupp' (fun p => Finset.filter_subset _ _)
  -- pieces
  have hpc : ∀ p : Fin kk × DirichletCharacter ℂ r,
      ∫ β in (-1 / H)..(1 / H), ‖localAdditivePolynomial (spiece lo hi Y p.1)
        (bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ p.1 p.2) β‖ ^ 2 ≤
      Y * Psi1 ℓ KLM (ptA lo 0) Kmm K3r c3r E1 E1 Kl B0 B C Cmk P.vmax KW cW KAm E1 j +
        Y * Psi2 ℓ KLM (bounds 0) C P.vmin P.vmax Cmk KS hi cS (ptA lo 0) := fun p =>
    piece_final P C τ η lo hi bounds K3r c3r Y0sp KW cW hpiece hK3r hKW hcW hc3r cS KS hsqS hcS hKS
      Cmk kk Kc Cf KA Kmm KAm Cfm E1 E1 E1 B B0 Kex Kl KLM j hKcm hKAm hKA hCfm' hC hlo hlohi
      hbounds x hexcx hlongx hKl hLM hKLM (by omega) hMCx' hx1 hL2 hszY hszα hszT hszz hszc hszf
      hszW.1 hszB1 hszB2 hszl' G E Y H v t b Ψ r u gs ls p.1 p.2 hG hE hdisc hgs hr1 hrC hWres hΨ
      hY1 hY2 hH1 hH2 hv
  -- error
  have herr := error_final P C τ η lo hi bounds cE KE herrS hcE hKE Cms Cmk J0 hJ0 hlo hlohi
    hbounds x hx1 hL2 hszerr hszl2' hszl' G E Y v t b Ψ r u gs ls hG hE hgs hbinv hWm hWres hΨ
    hY1 hY2
  -- the number of pieces
  have hcardχ : (Fintype.card (DirichletCharacter ℂ r) : ℝ) ≤ r := by
    haveI : NeZero r := ⟨by omega⟩
    have h1 := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
    rw [Nat.card_eq_fintype_card] at h1
    rw [h1]; exact_mod_cast Nat.totient_le r
  have hcard : (Fintype.card (Fin kk × DirichletCharacter ℂ r) : ℝ) ≤ kk * ℓ ^ C := by
    rw [Fintype.card_prod, Fintype.card_fin]; push_cast
    exact mul_le_mul_of_nonneg_left (hcardχ.trans hrC) (Nat.cast_nonneg _)
  set c := (Fintype.card (Fin kk × DirichletCharacter ℂ r) : ℝ) with hc
  set Ψ1 := Psi1 ℓ KLM (ptA lo 0) Kmm K3r c3r E1 E1 Kl B0 B C Cmk P.vmax KW cW KAm E1 j with hΨ1
  set Ψ2 := Psi2 ℓ KLM (bounds 0) C P.vmin P.vmax Cmk KS hi cS (ptA lo 0) with hΨ2
  set Ψ3 := Psi3 ℓ (bounds 0) C Cms Cmk ((J0 : ℝ) + 1) KE (lo * 2 ^ J0) cE P.vmax P.a with hΨ3
  have hLC : 0 ≤ ℓ ^ C := Real.rpow_nonneg hLpos.le _
  have hΨ10 : 0 ≤ Ψ1 := by
    rw [hΨ1]; unfold Psi1 PhiJ PhiW
    have := ptA_pos hlo 0
    have : 0 ≤ (2 * ℓ) ^ c3r := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ (2 * ℓ) ^ cW := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ ℓ ^ B0 := Real.rpow_nonneg hLpos.le _
    positivity
  have hΨ20 : 0 ≤ Ψ2 := by
    rw [hΨ2]; unfold Psi2
    have := ptA_pos hlo 0
    have := hbounds 0
    have : 0 < hi := by linarith
    have : 0 ≤ (2 * ℓ) ^ cS := Real.rpow_nonneg (by positivity) _
    positivity
  have hsum : ∑ p : Fin kk × DirichletCharacter ℂ r, ∫ β in (-1 / H)..(1 / H),
      ‖localAdditivePolynomial (spiece lo hi Y p.1)
        (bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ p.1 p.2) β‖ ^ 2 ≤ c * (Y * Ψ1 + Y * Ψ2) := by
    calc _ ≤ ∑ _p : Fin kk × DirichletCharacter ℂ r, (Y * Ψ1 + Y * Ψ2) :=
          Finset.sum_le_sum fun p _ => hpc p
      _ = c * (Y * Ψ1 + Y * Ψ2) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hX0 : 0 ≤ Y * Ψ1 + Y * Ψ2 := by positivity
  have hcc : c * c ≤ (kk : ℝ) ^ 2 * ℓ ^ (2 * C) := by
    rw [← sq_rpow hLpos C]
    calc c * c ≤ (kk * ℓ ^ C) * (kk * ℓ ^ C) := mul_le_mul hcard hcard hc0 (by positivity)
      _ = (kk : ℝ) ^ 2 * (ℓ ^ C) ^ 2 := by ring
  refine hdec.trans ?_
  calc 2 * c * (∑ p : Fin kk × DirichletCharacter ℂ r, ∫ β in (-1 / H)..(1 / H),
        ‖localAdditivePolynomial (spiece lo hi Y p.1)
          (bpiece G x Y v lo E Ψ gs Wr r u ⌊hi * Y⌋₊ p.1 p.2) β‖ ^ 2) +
      2 * ∑ n ∈ S, ‖epsf P G x Y v E t b Ψ gs Wr r u n‖ ^ 2
      ≤ 2 * c * (c * (Y * Ψ1 + Y * Ψ2)) + 2 * (Y * Ψ3) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hsum (by positivity)
        · exact mul_le_mul_of_nonneg_left herr (by norm_num)
    _ = 2 * (c * c) * (Y * Ψ1 + Y * Ψ2) + 2 * (Y * Ψ3) := by ring
    _ ≤ 2 * ((kk : ℝ) ^ 2 * ℓ ^ (2 * C)) * (Y * Ψ1 + Y * Ψ2) + 2 * (Y * Ψ3) := by
        apply add_le_add _ le_rfl
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcc (by norm_num)) hX0
    _ = Y * (2 * (kk : ℝ) ^ 2 * ℓ ^ (2 * C) * Ψ1 + 2 * (kk : ℝ) ^ 2 * ℓ ^ (2 * C) * Ψ2 +
          2 * Ψ3) := by ring
    _ ≤ Y * (ℓ ^ (-A) / 3 + ℓ ^ (-A) / 3 + ℓ ^ (-A) / 3) := by
        apply mul_le_mul_of_nonneg_left _ hYpos.le
        have h1 : 2 * (kk : ℝ) ^ 2 * ℓ ^ (2 * C) * Ψ1 ≤ ℓ ^ (-A) / 3 := hn1x
        have h2 : 2 * (kk : ℝ) ^ 2 * ℓ ^ (2 * C) * Ψ2 ≤ ℓ ^ (-A) / 3 := hn2x
        have h3 : 2 * Ψ3 ≤ ℓ ^ (-A) / 3 := hn3x
        linarith
    _ = 1 * Y * L x ^ (-A) := by ring

end Erdos821.P5Core

example : Erdos821.P5Core.MarkedEndpointEnergyTask := Erdos821.P5Core.MarkedEndpointEnergyTask_proof

