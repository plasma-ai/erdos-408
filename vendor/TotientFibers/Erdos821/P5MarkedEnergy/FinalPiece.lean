import Erdos821.P5MarkedEnergy.PieceCore
import Erdos821.P5MarkedEnergy.PiecewiseIdentity
import Erdos821.P5.LocalEnergyTask

/-! The energy of one smooth piece and one character, at a fixed large `x`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic P5Core

/-- The support of a smooth piece inside the summation range. -/
def spiece (lo hi Y : ℝ) (i : ℕ) : Finset ℕ :=
  (Finset.Icc ⌈lo * Y⌉₊ ⌊hi * Y⌋₊).filter
    (fun n => ptA lo i * Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * (ptA lo i * Y))

/-- The local Mellin energy statement at a fixed decay index. -/
def LocalMellinAt (j : ℕ) (K : ℝ) : Prop :=
  ∀ (Y H : ℝ) (s : Finset ℕ) (a : ℕ → ℂ),
    10 ≤ Y → 1 ≤ H → H ≤ Y / 10 →
    (∀ n ∈ s, Y ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Y) →
    (∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial s a θ‖ ^ 2) ≤
      K / Y * (∫ t : ℝ, (1 + |H / Y * t|) ^ (-(j : ℤ)) * ‖dp s a t‖ ^ 2) +
      K * (H / Y) ^ 2 * sqNorm s a

theorem psi_support {lo : ℝ} (hlo : 0 < lo) (i : ℕ) {y : ℝ} (hy : psi lo i y ≠ 0) :
    ptA lo i ≤ y ∧ y ≤ 2 * ptA lo i := by
  by_contra h
  apply hy
  apply psi_eq_zero hlo i
  intro hmem
  apply h
  exact ⟨hmem.1, hmem.2.trans (ptA_two_step_le hlo i)⟩

theorem wmv_frac_le {Z ih ℓ Lx : ℝ} (hZ : 0 < Z) (hinv : ih ≤ 16 * Z) (hℓ : ℓ ≤ 2 * Lx) :
    (ih + 16 * Z * ℓ) / Z ≤ 16 * (1 + 2 * Lx) := by
  rw [div_le_iff₀ hZ]
  have := mul_le_mul_of_nonneg_left hℓ (show (0 : ℝ) ≤ 16 * Z by positivity)
  linarith

set_option maxHeartbeats 2000000 in
theorem piece_bound : ∃ K3r c3r Y0sp KW cW : ℝ, 0 < K3r ∧ 0 ≤ c3r ∧ 1 < Y0sp ∧ 0 < KW ∧ 0 ≤ cW ∧
    ∀ (P : Geometry) (x C τ η B A_s A_l B0 K_ex K_l lo hi KLM Kmc Cmk R εt : ℝ) (j : ℕ)
      (G : PrimeGroups) (E : Endpoint) (Y H v : ℝ) (t : Fin G.size → ℕ) (b : Tuple G t → ℂ)
      (Ψ : ℝ → ℂ) (r : ℕ) (u : ℤ) (gs : Fin G.size) (ls : Fin (t gs)) (i : ℕ)
      (χ : DirichletCharacter ℂ r) (a : (Fin 1 → ℝ) → ℂ),
      ExcAt P.a P.b A_s K_ex x → LongAt τ η C B0 K_l A_l x → 0 < K_l →
      LocalMellinAt j KLM → 0 < KLM → 4 ≤ j →
      Admissible P x G → EndpointBound x C τ η E → discrepancy x B E.alpha → gs ∈ G.small →
      1 ≤ r → (r : ℝ) ≤ L x ^ C →
      (∀ k, ‖Wres G t gs ls P.q b k‖ ≤ mass G gs * L x ^ Cmk) →
      0 < lo → (∀ y, Ψ y ≠ 0 → lo ≤ y ∧ y ≤ hi) →
      Integrable a → (∫ ξ, ‖a ξ‖) ≤ L x ^ Kmc →
      (∀ y : ℝ, 0 < y → Ψ y * chiW lo i y = ∫ ξ, a ξ * Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0)) →
      (∫ ξ in {ξ : Fin 1 → ℝ | R < ‖ξ‖}, ‖a ξ‖) ≤ εt → 0 ≤ R →
      -- sizes
      1 ≤ x → 1 ≤ L x → 0 < C → 0 < Y → 1 ≤ hi * Y →
      10 ≤ ptA lo i * Y → 1 ≤ H → H ≤ ptA lo i * Y / 10 →
      Y0sp ≤ Y → x ^ (1 / 2 : ℝ) ≤ Y → Y ≤ x ^ (2 : ℕ) →
      2 * L x / (H / (ptA lo i * Y)) + 1 ≤ Y →
      2 * L x / (H / (ptA lo i * Y)) + L x ^ C ≤ x ^ (2 : ℕ) →
      (∀ P1 P2 : ℝ, Real.exp (L x ^ P.a) / 2 ≤ P1 → P1 ≤ Real.exp (L x ^ P.b) →
        x ^ τ / 2 ≤ P2 → P2 ≤ x ^ η →
        Y ^ (0.6 : ℝ) * (16 * P1 * P2) ≤ ptA lo i * Y ∧ 4 * (ptA lo i) * Y ≤ Y * (P1 * P2)) →
      2 * (2 * L x / (H / (ptA lo i * Y))) * (16 * Real.exp (L x ^ P.b)) ≤ ptA lo i * Y →
      64 * (ptA lo i) * Y ≤ x ^ (2 : ℕ) → 2 * Y ≤ x ^ (2 : ℕ) →
      Real.exp (K_ex * (L x ^ P.b + L x ^ (1 - P.a) * Real.log (L x))) ≤ Y ^ (0.05 : ℝ) →
      L x ^ (2 * C) ≤ L x ^ B → L x ^ B0 + L x ^ C ≤ L x ^ B → L x ^ (2 * C) < W x →
      |v| + 2 * Real.pi * R ≤ L x / (H / (ptA lo i * Y)) →
      ∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial (spiece lo hi Y i)
          (bpiece G x Y v lo E Ψ gs (Wres G t gs ls P.q b) r u ⌊hi * Y⌋₊ i χ) θ‖ ^ 2 ≤
        KLM / (ptA lo i * Y) * (Y ^ 2 *
          (((relBoxes (Nat.log 2 ⌊hi * Y⌋₊) (ptA lo i * Y)).card : ℝ) * L x ^ Kmc *
            (((relBoxes (Nat.log 2 ⌊hi * Y⌋₊) (ptA lo i * Y)).card : ℝ) *
              (L x ^ Kmc * ((K3r * ((((mass G gs)⁻¹ * L x ^ (-A_s)) ^ 2 * (1 + 16 * L x) *
                (L x ^ C * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 * (2 * L x) ^ c3r) +
              (K_l * L x ^ (-A_l)) ^ 2 * (L x ^ C * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 *
                (2 * L x) ^ c3r * (2 * L x)) +
              2 * L x ^ B0 * ((L x ^ (-B)) ^ 2 * (L x ^ C * (mass G gs * L x ^ Cmk)) ^ 2)) +
              ((1 + L x) ^ (j - 4))⁻¹ * (KW * (16 * (1 + 2 * L x)) *
                ((L x ^ C * (mass G gs)⁻¹ * 1 * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 *
                  (2 * L x) ^ cW))) +
              εt * (KW * (16 * (1 + 2 * L x)) *
                ((L x ^ C * (mass G gs)⁻¹ * 1 * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 *
                  (2 * L x) ^ cW)))))) +
        KLM * (H / (ptA lo i * Y)) ^ 2 * sqNorm (spiece lo hi Y i)
          (bpiece G x Y v lo E Ψ gs (Wres G t gs ls P.q b) r u ⌊hi * Y⌋₊ i χ) := by
  obtain ⟨K3r, c3r, Y0sp, hK3r, hc3r, hY0sp, hJ3⟩ := box_J3
  obtain ⟨KW, cW, hKW, hcW, hWMV⟩ := box_wmv
  refine ⟨K3r, c3r, Y0sp, KW, cW, hK3r, hc3r, hY0sp, hKW, hcW, ?_⟩
  intro P x C τ η B A_s A_l B0 K_ex K_l lo hi KLM Kmc Cmk R εt j G E Y H v t b Ψ r u gs ls i χ a
    hexc hlong hKl hLM hKLM hj hG hE hdisc hgs hr1 hrC hWres hlo hΨsupp ha haL1 hrep htail hR
    hx1 hL1 hC hY hhiY hYi10 hH1 hHYi hY0 hYx1 hYx2 hT1Y hT1x hz1 hz2 hz3 hz3' hcount hBC hBB0
    hWC hfreq
  set Wr := Wres G t gs ls P.q b with hWr
  set Wb := mass G gs * L x ^ Cmk with hWb
  set N := ⌊hi * Y⌋₊ with hN
  set α := ptA lo i with hα
  set Yi := α * Y with hYi
  set h' := H / Yi with hh'
  set s := spiece lo hi Y i with hs
  set bco := bpiece G x Y v lo E Ψ gs Wr r u N i χ with hbco
  set Rel := relBoxes (Nat.log 2 N) (α * Y) with hRel
  set f1 := cf1 E r χ with hf1
  set f2 := cf2 G gs r χ with hf2
  set f3 := cf3 E x r χ with hf3
  set f4 := cf4 G E Wr r u χ with hf4
  have hαpos : 0 < α := ptA_pos hlo i
  have hYipos : 0 < Yi := by positivity
  have hHpos : 0 < H := by linarith
  have hh'pos : 0 < h' := by positivity
  have hmass : 0 < mass G gs := P.positive.2.2.1.trans_le (hG.2.2.1 gs).1
  have hLpos : 0 < L x := by linarith
  have hLC : 0 ≤ L x ^ C := Real.rpow_nonneg hLpos.le _
  have hWb0 : 0 ≤ Wb := mul_nonneg hmass.le (Real.rpow_nonneg hLpos.le _)
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hhiY)
  have hT10 : 0 ≤ 2 * L x / h' := by positivity
  -- local Mellin energy
  have hsub : ∀ n ∈ s, Yi ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Yi := fun n hn => (Finset.mem_filter.mp hn).2
  have hLM' := hLM Yi H s bco hYi10 hH1 hHYi hsub
  -- the Mellin box identity
  set Ψi : ℝ → ℂ := fun y => Ψ y * (psi lo i y : ℂ) with hΨi
  have hsuppi : ∀ y, Ψi y ≠ 0 → α ≤ y ∧ y ≤ 2 * α := by
    intro y hy
    have hpsi : psi lo i y ≠ 0 := by
      intro h; apply hy; simp [hΨi, h]
    exact psi_support hlo i hpsi
  have hrepi : ∀ y : ℝ, 0 < y → (y : ℂ) * Ψi y = ∫ ξ, a ξ * Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0) := by
    intro y hy
    rw [← hrep y hy]
    simp only [hΨi, chiW]
    push_cast; ring
  have hSi : ∀ n : ℕ, Ψi (n / Y) ≠ 0 → n ∈ s := by
    intro n hn
    have hΨ : Ψ (n / Y) ≠ 0 := by intro h; apply hn; simp [hΨi, h]
    have hpsi : psi lo i (n / Y) ≠ 0 := by intro h; apply hn; simp [hΨi, h]
    obtain ⟨h1, h2⟩ := hΨsupp _ hΨ
    obtain ⟨h3, h4⟩ := psi_support hlo i hpsi
    rw [le_div_iff₀ hY] at h1 h3
    rw [div_le_iff₀ hY] at h2 h4
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (by linarith),
      Nat.le_floor (by linarith)⟩, by linarith, by linarith⟩
  have hSN : s ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨hn1, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn1
    have hlY : (0 : ℝ) < lo * Y := by positivity
    have : 0 < ⌈lo * Y⌉₊ := Nat.ceil_pos.mpr hlY
    exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
  have hid := mellin_box_identity f1 f2 f3 f4 Ψi a ha Y α v hY hαpos hsuppi hrepi N hN1 s hSi hSN
  -- the separation measure
  set b' : (Fin 1 → ℝ) → ℂ := fun ξ => a ξ * Blueprint.Analytic.mellin (1 / Y) (2 * Real.pi * ξ 0) with hb'
  have hb'norm : ∀ ξ, ‖b' ξ‖ = ‖a ξ‖ := by
    intro ξ; simp only [hb', norm_mul, P5Core.norm_mellin, mul_one]
  have hb'int : Integrable b' :=
    ha.mul_bdd (continuous_mellin_freq _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => (P5Core.norm_mellin _ _).le)
  have hA1 : ∫ ξ, ‖b' ξ‖ ≤ L x ^ Kmc := by simp_rw [hb'norm]; exact haL1
  have htail' : ∫ ξ in {ξ : Fin 1 → ℝ | R < ‖ξ‖}, ‖b' ξ‖ ≤ εt := by
    simp_rw [hb'norm]; exact htail
  -- three-range bounds for every relevant box
  have hJ3' : ∀ β ∈ Rel, ∫ t in (-(2 * L x / h'))..(2 * L x / h'),
      ‖boxPoly f1 f2 f3 f4 β t‖ ^ 2 ≤
        K3r * ((((mass G gs)⁻¹ * L x ^ (-A_s)) ^ 2 * (1 + 16 * L x) *
            (L x ^ C * (L x ^ C * Wb)) ^ 2 * (2 * L x) ^ c3r) +
          (K_l * L x ^ (-A_l)) ^ 2 * (L x ^ C * (L x ^ C * Wb)) ^ 2 * (2 * L x) ^ c3r * (2 * L x)) +
          2 * L x ^ B0 * ((L x ^ (-B)) ^ 2 * (L x ^ C * Wb) ^ 2) := by
    intro β hβ
    exact hJ3 P x C τ η B A_s A_l B0 K_ex K_l hexc hlong hKl G E gs r χ u Wr Wb Y α
      (2 * L x / h') β (Nat.log 2 N) hG hE hdisc hgs hr1 hrC hWres hβ hx1 hL1 hC hαpos hY hY0
      hYx1 hYx2 hT10 hT1Y hT1x hz1 hz2 (by linarith) hz3' hcount hBC hBB0 hWC
  -- weighted mean values for every relevant box
  set BB4 := L x ^ C * (mass G gs)⁻¹ * 1 * (L x ^ C * Wb) with hBB4
  have hWM' : ∀ β ∈ Rel, ∀ c : ℝ,
      Integrable (fun t => wt h' t * ‖boxPoly f1 f2 f3 f4 β (t + c)‖ ^ 2) ∧
      ∫ t, wt h' t * ‖boxPoly f1 f2 f3 f4 β (t + c)‖ ^ 2 ≤
        KW * (16 * (1 + 2 * L x)) * (BB4 ^ 2 * (2 * L x) ^ cW) := by
    intro β hβ c
    obtain ⟨hint, hle⟩ := hWMV f1 f2 f3 f4 β (L x ^ C) (mass G gs)⁻¹ 1 (L x ^ C * Wb) h' c hLC
      (inv_nonneg.mpr hmass.le) zero_le_one (mul_nonneg hLC hWb0)
      (fun m _ => norm_cf1_le hE r χ m) (fun m _ => norm_cf2_le G gs hmass r χ m)
      (fun m _ => norm_cf3_le E x r χ m) (fun m _ => norm_cf4_le G hE Wr Wb hWres r u χ m) hh'pos
    refine ⟨hint, hle.trans ?_⟩
    obtain ⟨_, hrel1, hrel2⟩ := Finset.mem_filter.mp hβ
    set Z : ℝ := (2 : ℝ) ^ bsize β with hZ
    have hZpos : 0 < Z := by positivity
    have hinv : 1 / h' ≤ 16 * Z := by
      rw [hh', one_div_div]
      calc Yi / H ≤ Yi := div_le_self hYipos.le hH1
        _ ≤ 16 * Z := hrel1.le
    have hpow4 : (2 : ℝ) ^ (bsize β + 4) = 16 * Z := by rw [hZ, pow_add]; ring
    have hℓ4 : Real.log (2 * 2 ^ (bsize β + 4)) ≤ 2 * L x := by
      have hlogx2 : Real.log (x ^ (2 : ℕ)) = 2 * L x := by rw [Real.log_pow]; push_cast; rfl
      rw [← hlogx2]
      apply Real.log_le_log (by positivity)
      rw [hpow4]; linarith
    have hℓ4' : 0 ≤ Real.log (2 * 2 ^ (bsize β + 4)) :=
      Real.log_nonneg (by have : (1 : ℝ) ≤ 2 ^ (bsize β + 4) := one_le_pow₀ (by norm_num); linarith)
    have hX : (1 / h' + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) / Z ≤
        16 * (1 + 2 * L x) := by
      have := wmv_frac_le hZpos hinv hℓ4
      rwa [← hpow4] at this
    have hpw : Real.log (2 * 2 ^ (bsize β + 4)) ^ cW ≤ (2 * L x) ^ cW :=
      Real.rpow_le_rpow hℓ4' hℓ4 hcW
    have hpw0 : 0 ≤ Real.log (2 * 2 ^ (bsize β + 4)) ^ cW := Real.rpow_nonneg hℓ4' _
    have hX0 : 0 ≤ (1 / h' + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) / Z := by
      positivity
    calc KW * (1 / h' + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) *
          ((L x ^ C * (mass G gs)⁻¹ * 1 * (L x ^ C * Wb)) ^ 2 *
            Real.log (2 * 2 ^ (bsize β + 4)) ^ cW / 2 ^ bsize β)
        = KW * BB4 ^ 2 * (((1 / h' + 2 ^ (bsize β + 4) * Real.log (2 * 2 ^ (bsize β + 4))) / Z) *
            Real.log (2 * 2 ^ (bsize β + 4)) ^ cW) := by
          rw [hBB4, hZ]; ring
      _ ≤ KW * BB4 ^ 2 * ((16 * (1 + 2 * L x)) * (2 * L x) ^ cW) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hX hpw hpw0 (by positivity)
      _ = KW * (16 * (1 + 2 * L x)) * (BB4 ^ 2 * (2 * L x) ^ cW) := by ring
  -- the core estimate
  have hcont : ∀ β, Continuous (boxPoly f1 f2 f3 f4 β) := fun β => continuous_boxPoly _ _ _ _ _
  have hMb : ∀ β t, ‖boxPoly f1 f2 f3 f4 β t‖ ≤
      L x ^ C * (mass G gs)⁻¹ * 1 * (L x ^ C * Wb) := fun β t =>
    norm_boxPoly_le f1 f2 f3 f4 β _ _ _ _ (fun m _ => norm_cf1_le hE r χ m)
      (fun m _ => norm_cf2_le G gs hmass r χ m) (fun m _ => norm_cf3_le E x r χ m)
      (fun m _ => norm_cf4_le G hE Wr Wb hWres r u χ m) t
  have hJ30 : 0 ≤ K3r * ((((mass G gs)⁻¹ * L x ^ (-A_s)) ^ 2 * (1 + 16 * L x) *
            (L x ^ C * (L x ^ C * Wb)) ^ 2 * (2 * L x) ^ c3r) +
          (K_l * L x ^ (-A_l)) ^ 2 * (L x ^ C * (L x ^ C * Wb)) ^ 2 * (2 * L x) ^ c3r * (2 * L x)) +
          2 * L x ^ B0 * ((L x ^ (-B)) ^ 2 * (L x ^ C * Wb) ^ 2) := by
    have : 0 ≤ (2 * L x) ^ c3r := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ L x ^ B0 := Real.rpow_nonneg hLpos.le _
    positivity
  have hWM0 : 0 ≤ KW * (16 * (1 + 2 * L x)) * (BB4 ^ 2 * (2 * L x) ^ cW) := by
    have : 0 ≤ (2 * L x) ^ cW := Real.rpow_nonneg (by positivity) _
    positivity
  have hcore := piece_energy_core Rel (boxPoly f1 f2 f3 f4) hcont (fun _ => BB4) hMb s bco Y Yi H
    (L x) v R (L x ^ Kmc) εt _ _ KLM j b' hb'int hj hL1 hYipos hHpos hKLM.le hJ30 hWM0 hR hLM'
    hid hA1 htail' hJ3' hWM' hfreq
  rw [Finset.sum_const, nsmul_eq_mul] at hcore
  exact hcore

/-- The fixed-`x` piece bound, as a predicate on its constants. -/
def PieceBoundSpec (K3r c3r Y0sp KW cW : ℝ) : Prop :=
    ∀ (P : Geometry) (x C τ η B A_s A_l B0 K_ex K_l lo hi KLM Kmc Cmk R εt : ℝ) (j : ℕ)
      (G : PrimeGroups) (E : Endpoint) (Y H v : ℝ) (t : Fin G.size → ℕ) (b : Tuple G t → ℂ)
      (Ψ : ℝ → ℂ) (r : ℕ) (u : ℤ) (gs : Fin G.size) (ls : Fin (t gs)) (i : ℕ)
      (χ : DirichletCharacter ℂ r) (a : (Fin 1 → ℝ) → ℂ),
      ExcAt P.a P.b A_s K_ex x → LongAt τ η C B0 K_l A_l x → 0 < K_l →
      LocalMellinAt j KLM → 0 < KLM → 4 ≤ j →
      Admissible P x G → EndpointBound x C τ η E → discrepancy x B E.alpha → gs ∈ G.small →
      1 ≤ r → (r : ℝ) ≤ L x ^ C →
      (∀ k, ‖Wres G t gs ls P.q b k‖ ≤ mass G gs * L x ^ Cmk) →
      0 < lo → (∀ y, Ψ y ≠ 0 → lo ≤ y ∧ y ≤ hi) →
      Integrable a → (∫ ξ, ‖a ξ‖) ≤ L x ^ Kmc →
      (∀ y : ℝ, 0 < y → Ψ y * chiW lo i y = ∫ ξ, a ξ * Blueprint.Analytic.mellin y (2 * Real.pi * ξ 0)) →
      (∫ ξ in {ξ : Fin 1 → ℝ | R < ‖ξ‖}, ‖a ξ‖) ≤ εt → 0 ≤ R →
      -- sizes
      1 ≤ x → 1 ≤ L x → 0 < C → 0 < Y → 1 ≤ hi * Y →
      10 ≤ ptA lo i * Y → 1 ≤ H → H ≤ ptA lo i * Y / 10 →
      Y0sp ≤ Y → x ^ (1 / 2 : ℝ) ≤ Y → Y ≤ x ^ (2 : ℕ) →
      2 * L x / (H / (ptA lo i * Y)) + 1 ≤ Y →
      2 * L x / (H / (ptA lo i * Y)) + L x ^ C ≤ x ^ (2 : ℕ) →
      (∀ P1 P2 : ℝ, Real.exp (L x ^ P.a) / 2 ≤ P1 → P1 ≤ Real.exp (L x ^ P.b) →
        x ^ τ / 2 ≤ P2 → P2 ≤ x ^ η →
        Y ^ (0.6 : ℝ) * (16 * P1 * P2) ≤ ptA lo i * Y ∧ 4 * (ptA lo i) * Y ≤ Y * (P1 * P2)) →
      2 * (2 * L x / (H / (ptA lo i * Y))) * (16 * Real.exp (L x ^ P.b)) ≤ ptA lo i * Y →
      64 * (ptA lo i) * Y ≤ x ^ (2 : ℕ) → 2 * Y ≤ x ^ (2 : ℕ) →
      Real.exp (K_ex * (L x ^ P.b + L x ^ (1 - P.a) * Real.log (L x))) ≤ Y ^ (0.05 : ℝ) →
      L x ^ (2 * C) ≤ L x ^ B → L x ^ B0 + L x ^ C ≤ L x ^ B → L x ^ (2 * C) < W x →
      |v| + 2 * Real.pi * R ≤ L x / (H / (ptA lo i * Y)) →
      ∫ θ in (-1 / H)..(1 / H), ‖localAdditivePolynomial (spiece lo hi Y i)
          (bpiece G x Y v lo E Ψ gs (Wres G t gs ls P.q b) r u ⌊hi * Y⌋₊ i χ) θ‖ ^ 2 ≤
        KLM / (ptA lo i * Y) * (Y ^ 2 *
          (((relBoxes (Nat.log 2 ⌊hi * Y⌋₊) (ptA lo i * Y)).card : ℝ) * L x ^ Kmc *
            (((relBoxes (Nat.log 2 ⌊hi * Y⌋₊) (ptA lo i * Y)).card : ℝ) *
              (L x ^ Kmc * ((K3r * ((((mass G gs)⁻¹ * L x ^ (-A_s)) ^ 2 * (1 + 16 * L x) *
                (L x ^ C * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 * (2 * L x) ^ c3r) +
              (K_l * L x ^ (-A_l)) ^ 2 * (L x ^ C * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 *
                (2 * L x) ^ c3r * (2 * L x)) +
              2 * L x ^ B0 * ((L x ^ (-B)) ^ 2 * (L x ^ C * (mass G gs * L x ^ Cmk)) ^ 2)) +
              ((1 + L x) ^ (j - 4))⁻¹ * (KW * (16 * (1 + 2 * L x)) *
                ((L x ^ C * (mass G gs)⁻¹ * 1 * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 *
                  (2 * L x) ^ cW))) +
              εt * (KW * (16 * (1 + 2 * L x)) *
                ((L x ^ C * (mass G gs)⁻¹ * 1 * (L x ^ C * (mass G gs * L x ^ Cmk))) ^ 2 *
                  (2 * L x) ^ cW)))))) +
        KLM * (H / (ptA lo i * Y)) ^ 2 * sqNorm (spiece lo hi Y i)
          (bpiece G x Y v lo E Ψ gs (Wres G t gs ls P.q b) r u ⌊hi * Y⌋₊ i χ)

theorem piece_bound' : ∃ K3r c3r Y0sp KW cW : ℝ, 0 < K3r ∧ 0 ≤ c3r ∧ 1 < Y0sp ∧ 0 < KW ∧ 0 ≤ cW ∧
    PieceBoundSpec K3r c3r Y0sp KW cW := piece_bound

end Erdos821.P5Marked
