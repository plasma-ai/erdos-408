import Erdos821.P5MarkedEnergy.BoxThree
import Erdos821.P5MarkedEnergy.BoxInputs
import Erdos821.P5MarkedEnergy.BoxBounds

/-! The three-range estimate for an actual box of the marked endpoint. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Classical

namespace Erdos821.P5Marked
open Blueprint.Analytic

/-- The four coefficient functions of the marked endpoint after the character expansion. -/
def cf1 (E : Endpoint) (r : ℕ) (χ : DirichletCharacter ℂ r) (m : ℕ) : ℂ := A0 E m * χ (m : ZMod r)
def cf2 (G : PrimeGroups) (gs : Fin G.size) (r : ℕ) (χ : DirichletCharacter ℂ r) (s : ℕ) : ℂ :=
  S0 G gs s * χ (s : ZMod r)
def cf3 (E : Endpoint) (x : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r) (p : ℕ) : ℂ :=
  P0 E x p * χ (p : ZMod r)
def cf4 (G : PrimeGroups) (E : Endpoint) (Wr : ℕ → ℂ) (r : ℕ) (u : ℤ) (χ : DirichletCharacter ℂ r)
    (k : ℕ) : ℂ := E.residual (groupFreePart G k) * Wr k * cchi r u χ k

theorem norm_cf1_le {x C τ η : ℝ} {E : Endpoint} (hE : EndpointBound x C τ η E) (r : ℕ)
    (χ : DirichletCharacter ℂ r) (m : ℕ) : ‖cf1 E r χ m‖ ≤ L x ^ C := by
  unfold cf1 A0
  rw [norm_mul, norm_mul, norm_mul, P5Core.norm_mellin, mul_one]
  have h1 := (hE.2.2.2.1 m).1
  have h2 := E.chi.norm_le_one (m : ZMod E.modulus)
  have h3 := χ.norm_le_one (m : ZMod r)
  have hLC : 0 ≤ L x ^ C := (norm_nonneg _).trans h1
  calc ‖E.alpha m‖ * ‖E.chi (m : ZMod E.modulus)‖ * ‖χ (m : ZMod r)‖ ≤ L x ^ C * 1 * 1 :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hLC) h3 (norm_nonneg _) (by positivity)
    _ = L x ^ C := by ring

theorem norm_cf2_le (G : PrimeGroups) (gs : Fin G.size) (hmass : 0 < mass G gs) (r : ℕ)
    (χ : DirichletCharacter ℂ r) (s : ℕ) : ‖cf2 G gs r χ s‖ ≤ (mass G gs)⁻¹ := by
  unfold cf2 S0
  rw [norm_mul]
  have h3 := χ.norm_le_one (s : ZMod r)
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
    calc (mass G gs)⁻¹ * ‖χ (s : ZMod r)‖ ≤ (mass G gs)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hmass.le)
      _ = _ := mul_one _
  · simp only [norm_zero, zero_mul]; positivity

theorem norm_cf3_le (E : Endpoint) (x : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r) (p : ℕ) :
    ‖cf3 E x r χ p‖ ≤ 1 := by
  unfold cf3 P0
  rw [norm_mul]
  have h3 := χ.norm_le_one (p : ZMod r)
  split_ifs
  · rw [P5Core.norm_mellin, one_mul]; exact h3
  · simp

theorem norm_cf4_le {x C τ η : ℝ} (G : PrimeGroups) {E : Endpoint} (hE : EndpointBound x C τ η E)
    (Wr : ℕ → ℂ) (Wb : ℝ) (hWb : ∀ k, ‖Wr k‖ ≤ Wb) (r : ℕ) (u : ℤ) (χ : DirichletCharacter ℂ r)
    (k : ℕ) : ‖cf4 G E Wr r u χ k‖ ≤ L x ^ C * Wb := by
  unfold cf4
  rw [norm_mul, norm_mul]
  have h1 := (hE.2.2.2.1 (groupFreePart G k)).2
  have h2 := hWb k
  have h3 := norm_cchi_le r u χ k
  have hW0 : 0 ≤ Wb := (norm_nonneg _).trans h2
  have hLC : 0 ≤ L x ^ C := (norm_nonneg _).trans h1
  calc ‖E.residual (groupFreePart G k)‖ * ‖Wr k‖ * ‖cchi r u χ k‖ ≤ L x ^ C * Wb * 1 :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hLC) h3 (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- A box whose small-prime dyad misses the removed group vanishes. -/
theorem hpoly_cf2_eq_zero (G : PrimeGroups) (gs : Fin G.size) (r : ℕ) (χ : DirichletCharacter ℂ r)
    (i : ℕ) (h : ¬ ((G.primes gs).filter (fun p : ℕ => p ∈ dyad i)).Nonempty) (t : ℝ) :
    hpoly (cf2 G gs r χ) i t = 0 := by
  have := hpoly_S0_eq G gs r χ i t
  unfold cf2
  rw [this, Finset.not_nonempty_iff_eq_empty.mp h]
  simp [primePolynomial, dp]

theorem hpoly_cf3_eq_zero (E : Endpoint) (x : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r) (i : ℕ)
    (hlo : 0 ≤ E.lo) (hlohi : E.lo ≤ E.hi)
    (h : ¬ (max ((2 : ℝ) ^ i) E.lo ≤ min ((2 : ℝ) ^ (i + 1) - 1) E.hi)) (t : ℝ) :
    hpoly (cf3 E x r χ) i t = 0 := by
  unfold cf3
  rw [hpoly_P0_eq E x r χ i hlo hlohi t]
  apply Finset.sum_eq_zero
  intro n hn
  exfalso
  obtain ⟨hn1, _⟩ := Finset.mem_filter.mp hn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn1
  apply h
  have hmin : 0 ≤ min ((2 : ℝ) ^ (i + 1) - 1) E.hi := by
    apply le_min _ (hlo.trans hlohi)
    have : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ (by norm_num)
    linarith
  have a1 := Nat.ceil_le.mp h1
  have a2 := (Nat.le_floor_iff hmin).mp h2
  linarith

/-- The exceptional-times conclusion at a fixed `x`. -/
def ExcAt (a b A K x : ℝ) : Prop :=
  ∀ (Y P Tmax : ℝ) (s : Finset ℕ) (coeff : ℕ → ℂ),
    x ^ (1 / 2 : ℝ) ≤ Y → Y ≤ x ^ (2 : ℕ) → 0 ≤ Tmax → Tmax ≤ Y →
    Real.exp (L x ^ a) / 2 ≤ P → P ≤ Real.exp (L x ^ b) →
    (∀ p ∈ s, p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P) →
    (∀ p ∈ s, ‖coeff p‖ ≤ 1) →
    (occupied s coeff (L x ^ (-A)) Tmax).Finite ∧
    ((occupied s coeff (L x ^ (-A)) Tmax).ncard : ℝ) ≤
      Real.exp (K * (L x ^ b + L x ^ (1 - a) * Real.log (L x)))

/-- The long rough-polynomial conclusion at a fixed `x`. -/
def LongAt (τ η C B0 K A x : ℝ) : Prop :=
  ∀ (P lo hi σ t : ℝ) (r : ℕ) (χ : DirichletCharacter ℂ r),
    x ^ τ / 2 ≤ P → P ≤ x ^ η → P ≤ lo → lo ≤ hi → hi ≤ 2 * P →
    1 ≤ r → (r : ℝ) ≤ L x ^ C → |σ| ≤ L x ^ C →
    L x ^ B0 ≤ |t| → |t + σ| ≤ x ^ (2 : ℕ) →
    ‖∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter (rough (W x)),
      χ (n : ZMod r) * mellin n (t + σ) / (n : ℂ)‖ ≤ K * L x ^ (-A)

theorem pow_bsize (β : Q4) : (2 : ℝ) ^ bsize β =
    2 ^ (β.1 + β.2.2.2) * 2 ^ β.2.1 * 2 ^ β.2.2.1 := by
  unfold bsize; rw [← pow_add, ← pow_add]; congr 1; ring

theorem j3_simplify (K3r c3r T1 Lx θ ε3 BB T3 Y : ℝ) (i1 i3 i4 : ℕ) (hK : 0 ≤ K3r) (hc : 0 ≤ c3r)
    (hT10 : 0 ≤ T1) (h2L : 0 ≤ 2 * Lx) (hT1S3 : 2 * T1 ≤ 2 ^ (i1 + i3 + i4))
    (hℓ3 : Real.log (2 * 2 ^ (i1 + i3 + i4 + 3)) ≤ 2 * Lx)
    (hℓ3' : 0 ≤ Real.log (2 * 2 ^ (i1 + i3 + i4 + 3)))
    (hℓ2 : Real.log (2 * 2 ^ (i1 + i4 + 2)) ≤ 2 * Lx) (hℓ2' : 0 ≤ Real.log (2 * 2 ^ (i1 + i4 + 2)))
    (hlY : Real.log (2 * Y) ≤ 2 * Lx) (hlY' : 0 ≤ Real.log (2 * Y)) :
    θ ^ 2 * (K3r * (2 * T1 + 2 ^ (i1 + i3 + i4 + 3) * Real.log (2 * 2 ^ (i1 + i3 + i4 + 3))) *
        BB ^ 2 * Real.log (2 * 2 ^ (i1 + i3 + i4 + 3)) ^ c3r / 2 ^ (i1 + i3 + i4)) +
      ε3 ^ 2 * (K3r * BB ^ 2 * Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ c3r * Real.log (2 * Y)) + T3 ≤
      K3r * (θ ^ 2 * (1 + 16 * Lx) * BB ^ 2 * (2 * Lx) ^ c3r +
        ε3 ^ 2 * BB ^ 2 * (2 * Lx) ^ c3r * (2 * Lx)) + T3 := by
  set S3 := i1 + i3 + i4 with hS3
  have hS3pos : (0 : ℝ) < 2 ^ S3 := by positivity
  have hA : (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
      Real.log (2 * 2 ^ (S3 + 3)) ^ c3r / 2 ^ S3 ≤ (1 + 16 * Lx) * (2 * Lx) ^ c3r := by
    have e : (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
        Real.log (2 * 2 ^ (S3 + 3)) ^ c3r / 2 ^ S3 =
        (2 * T1 / 2 ^ S3 + 8 * Real.log (2 * 2 ^ (S3 + 3))) * Real.log (2 * 2 ^ (S3 + 3)) ^ c3r := by
      field_simp; ring
    rw [e]
    have h1 : 2 * T1 / 2 ^ S3 ≤ 1 := (div_le_one hS3pos).mpr hT1S3
    have h2 : Real.log (2 * 2 ^ (S3 + 3)) ^ c3r ≤ (2 * Lx) ^ c3r :=
      Real.rpow_le_rpow hℓ3' hℓ3 hc
    have h3 : 0 ≤ Real.log (2 * 2 ^ (S3 + 3)) ^ c3r := Real.rpow_nonneg hℓ3' _
    have h4 : 0 ≤ 2 * T1 / 2 ^ S3 := by positivity
    apply mul_le_mul _ h2 h3 (by linarith)
    linarith
  have hB2 : Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ c3r * Real.log (2 * Y) ≤ (2 * Lx) ^ c3r * (2 * Lx) :=
    mul_le_mul (Real.rpow_le_rpow hℓ2' hℓ2 hc) hlY hlY' (Real.rpow_nonneg h2L _)
  have t1 : θ ^ 2 * (K3r * (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
      BB ^ 2 * Real.log (2 * 2 ^ (S3 + 3)) ^ c3r / 2 ^ S3) ≤
      K3r * (θ ^ 2 * (1 + 16 * Lx) * BB ^ 2 * (2 * Lx) ^ c3r) := by
    have e1 : θ ^ 2 * (K3r * (2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
        BB ^ 2 * Real.log (2 * 2 ^ (S3 + 3)) ^ c3r / 2 ^ S3) =
        (K3r * θ ^ 2 * BB ^ 2) * ((2 * T1 + 2 ^ (S3 + 3) * Real.log (2 * 2 ^ (S3 + 3))) *
          Real.log (2 * 2 ^ (S3 + 3)) ^ c3r / 2 ^ S3) := by ring
    have e2 : K3r * (θ ^ 2 * (1 + 16 * Lx) * BB ^ 2 * (2 * Lx) ^ c3r) =
        (K3r * θ ^ 2 * BB ^ 2) * ((1 + 16 * Lx) * (2 * Lx) ^ c3r) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have t2 : ε3 ^ 2 * (K3r * BB ^ 2 * Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ c3r * Real.log (2 * Y)) ≤
      K3r * (ε3 ^ 2 * BB ^ 2 * (2 * Lx) ^ c3r * (2 * Lx)) := by
    have e1 : ε3 ^ 2 * (K3r * BB ^ 2 * Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ c3r * Real.log (2 * Y)) =
        (K3r * ε3 ^ 2 * BB ^ 2) * (Real.log (2 * 2 ^ (i1 + i4 + 2)) ^ c3r * Real.log (2 * Y)) := by
      ring
    have e2 : K3r * (ε3 ^ 2 * BB ^ 2 * (2 * Lx) ^ c3r * (2 * Lx)) =
        (K3r * ε3 ^ 2 * BB ^ 2) * ((2 * Lx) ^ c3r * (2 * Lx)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hB2 (by positivity)
  have : K3r * (θ ^ 2 * (1 + 16 * Lx) * BB ^ 2 * (2 * Lx) ^ c3r +
        ε3 ^ 2 * BB ^ 2 * (2 * Lx) ^ c3r * (2 * Lx)) =
      K3r * (θ ^ 2 * (1 + 16 * Lx) * BB ^ 2 * (2 * Lx) ^ c3r) +
        K3r * (ε3 ^ 2 * BB ^ 2 * (2 * Lx) ^ c3r * (2 * Lx)) := by ring
  rw [this]
  linarith

set_option maxHeartbeats 1000000 in
/-- The three-range bound for an actual relevant box. -/
theorem box_J3 : ∃ K3r c3r Y0sp : ℝ, 0 < K3r ∧ 0 ≤ c3r ∧ 1 < Y0sp ∧
    ∀ (P : Geometry) (x C τ η B A_s A_l B0 K_ex K_l : ℝ),
      ExcAt P.a P.b A_s K_ex x → LongAt τ η C B0 K_l A_l x → 0 < K_l →
    ∀ (G : PrimeGroups) (E : Endpoint) (gs : Fin G.size) (r : ℕ) (χ : DirichletCharacter ℂ r)
      (u : ℤ) (Wr : ℕ → ℂ) (Wb Y α T1 : ℝ) (β : Q4) (K : ℕ),
      Admissible P x G → EndpointBound x C τ η E → discrepancy x B E.alpha →
      gs ∈ G.small → 1 ≤ r → (r : ℝ) ≤ L x ^ C → (∀ k, ‖Wr k‖ ≤ Wb) →
      β ∈ relBoxes K (α * Y) → 1 ≤ x → 1 ≤ L x → 0 < C → 0 < α → 0 < Y →
      Y0sp ≤ Y → x ^ (1 / 2 : ℝ) ≤ Y → Y ≤ x ^ (2 : ℕ) →
      0 ≤ T1 → T1 + 1 ≤ Y → T1 + L x ^ C ≤ x ^ (2 : ℕ) →
      (∀ P1 P2 : ℝ, Real.exp (L x ^ P.a) / 2 ≤ P1 → P1 ≤ Real.exp (L x ^ P.b) →
        x ^ τ / 2 ≤ P2 → P2 ≤ x ^ η →
        Y ^ (0.6 : ℝ) * (16 * P1 * P2) ≤ α * Y ∧ 4 * α * Y ≤ Y * (P1 * P2)) →
      2 * T1 * (16 * Real.exp (L x ^ P.b)) ≤ α * Y →
      32 * α * Y ≤ x ^ (2 : ℕ) → 2 * Y ≤ x ^ (2 : ℕ) →
      Real.exp (K_ex * (L x ^ P.b + L x ^ (1 - P.a) * Real.log (L x))) ≤ Y ^ (0.05 : ℝ) →
      L x ^ (2 * C) ≤ L x ^ B → L x ^ B0 + L x ^ C ≤ L x ^ B → L x ^ (2 * C) < W x →
      ∫ s in (-T1)..T1, ‖boxPoly (cf1 E r χ) (cf2 G gs r χ) (cf3 E x r χ) (cf4 G E Wr r u χ) β s‖ ^ 2 ≤
        K3r * ((((mass G gs)⁻¹ * L x ^ (-A_s)) ^ 2 * (1 + 16 * L x) *
            (L x ^ C * (L x ^ C * Wb)) ^ 2 * (2 * L x) ^ c3r) +
          (K_l * L x ^ (-A_l)) ^ 2 * (L x ^ C * (L x ^ C * Wb)) ^ 2 * (2 * L x) ^ c3r * (2 * L x)) +
          2 * L x ^ B0 * ((L x ^ (-B)) ^ 2 * (L x ^ C * Wb) ^ 2) := by
  obtain ⟨K3r, c3r, Y0sp, hK3r, hc3r, hY0sp, hthree⟩ := box_three_range
  refine ⟨K3r, c3r, Y0sp, hK3r, hc3r, hY0sp, ?_⟩
  intro P x C τ η B A_s A_l B0 K_ex K_l hexc hlong hKl G E gs r χ u Wr Wb Y α T1 β K
    hG hE hdisc hgs hr1 hrC hWb hβ hx1 hL1 hC hα hY hY0 hYx1 hYx2 hT10 hT1Y hT1x hz1 hz2 hz3 hz3'
    hcount hBC hBB0 hWC
  set f1 := cf1 E r χ with hf1
  set f2 := cf2 G gs r χ with hf2
  set f3 := cf3 E x r χ with hf3
  set f4 := cf4 G E Wr r u χ with hf4
  set Lx := L x with hLx
  have hLpos : 0 < Lx := by linarith
  have hmass : 0 < mass G gs := P.positive.2.2.1.trans_le (hG.2.2.1 gs).1
  have hWb0 : 0 ≤ Wb := (norm_nonneg _).trans (hWb 0)
  have hLC : 0 ≤ Lx ^ C := Real.rpow_nonneg hLpos.le _
  have hboxzero : (∀ s, boxPoly f1 f2 f3 f4 β s = 0) →
      ∫ s in (-T1)..T1, ‖boxPoly f1 f2 f3 f4 β s‖ ^ 2 = 0 := by
    intro h; simp [h]
  have hJ0 : 0 ≤ K3r * ((((mass G gs)⁻¹ * Lx ^ (-A_s)) ^ 2 * (1 + 16 * Lx) *
            (Lx ^ C * (Lx ^ C * Wb)) ^ 2 * (2 * Lx) ^ c3r) +
          (K_l * Lx ^ (-A_l)) ^ 2 * (Lx ^ C * (Lx ^ C * Wb)) ^ 2 * (2 * Lx) ^ c3r * (2 * Lx)) +
          2 * Lx ^ B0 * ((Lx ^ (-B)) ^ 2 * (Lx ^ C * Wb) ^ 2) := by
    have : 0 ≤ (2 * Lx) ^ c3r := Real.rpow_nonneg (by positivity) _
    have : 0 ≤ Lx ^ B0 := Real.rpow_nonneg hLpos.le _
    positivity
  obtain ⟨hβall, hrel1, hrel2⟩ := Finset.mem_filter.mp hβ
  set i1 := β.1 with hi1
  set i2 := β.2.1 with hi2
  set i3 := β.2.2.1 with hi3
  set i4 := β.2.2.2 with hi4
  set s2 := (G.primes gs).filter (fun p : ℕ => p ∈ dyad i2) with hs2
  by_cases h2e : s2.Nonempty
  swap
  · rw [hboxzero (fun s => by
      simp only [boxPoly]
      rw [show hpoly f2 β.2.1 s = 0 from hpoly_cf2_eq_zero G gs r χ i2 h2e s]
      ring)]
    exact hJ0
  have hxτ : 0 < x ^ τ := Real.rpow_pos_of_pos (by linarith) τ
  have hElo' : x ^ τ ≤ E.lo := hE.2.2.2.2.2.2.2.2.1
  have hElo : 0 ≤ E.lo := hxτ.le.trans hElo'
  have hlohi : E.lo ≤ E.hi := hE.2.2.2.2.2.2.2.2.2.1
  have hEhi : E.hi ≤ x ^ η := hE.2.2.2.2.2.2.2.2.2.2
  by_cases h3e : max ((2 : ℝ) ^ i3) E.lo ≤ min ((2 : ℝ) ^ (i3 + 1) - 1) E.hi
  swap
  · rw [hboxzero (fun s => by
      simp only [boxPoly]
      rw [show hpoly f3 β.2.2.1 s = 0 from hpoly_cf3_eq_zero E x r χ i3 hElo hlohi h3e s]
      ring)]
    exact hJ0
  -- the dyadic scales
  obtain ⟨p2, hp2⟩ := h2e
  obtain ⟨hp2G, hp2d⟩ := Finset.mem_filter.mp hp2
  have hp2adm := hG.2.2.2.1 gs p2 hp2G
  rw [if_pos hgs] at hp2adm
  have hp2dy := mem_dyad.mp hp2d
  set P1 : ℝ := (2 : ℝ) ^ i2 with hP1
  have hP1ge1 : 1 ≤ P1 := one_le_pow₀ (by norm_num)
  have hp2R1 : P1 ≤ (p2 : ℝ) := by rw [hP1]; exact_mod_cast hp2dy.1
  have hp2R2 : (p2 : ℝ) < 2 * P1 := by
    have : ((p2 : ℕ) : ℝ) < ((2 ^ (i2 + 1) : ℕ) : ℝ) := by exact_mod_cast hp2dy.2
    rw [hP1]; push_cast at this; rw [pow_succ] at this; linarith
  have hP1lo : Real.exp (Lx ^ P.a) / 2 ≤ P1 := by linarith [hp2adm.1]
  have hP1hi : P1 ≤ Real.exp (Lx ^ P.b) := hp2R1.trans hp2adm.2
  set P2 : ℝ := (2 : ℝ) ^ i3 with hP2
  have hP2ge1 : 1 ≤ P2 := one_le_pow₀ (by norm_num)
  have hP2hi : P2 ≤ x ^ η :=
    (le_max_left _ _).trans (h3e.trans ((min_le_right _ _).trans hEhi))
  have hP2lo : x ^ τ / 2 ≤ P2 := by
    have h1 : E.lo ≤ (2 : ℝ) ^ (i3 + 1) - 1 := (le_max_right _ _).trans (h3e.trans (min_le_left _ _))
    have h2 : (2 : ℝ) ^ (i3 + 1) = 2 * P2 := by rw [hP2, pow_succ]; ring
    linarith
  obtain ⟨hz1a, hz1b⟩ := hz1 P1 P2 hP1lo hP1hi hP2lo hP2hi
  have hbs : (2 : ℝ) ^ bsize β = 2 ^ (i1 + i4) * P1 * P2 := pow_bsize β
  have hPP : 0 < P1 * P2 := by positivity
  have hU1 : Y ^ (0.6 : ℝ) ≤ (2 : ℝ) ^ (i1 + i4) := by
    have h : Y ^ (0.6 : ℝ) * (16 * P1 * P2) < (2 : ℝ) ^ (i1 + i4) * (16 * P1 * P2) := by
      calc Y ^ (0.6 : ℝ) * (16 * P1 * P2) ≤ α * Y := hz1a
        _ < 16 * (2 : ℝ) ^ bsize β := hrel1
        _ = (2 : ℝ) ^ (i1 + i4) * (16 * P1 * P2) := by rw [hbs]; ring
    exact (lt_of_mul_lt_mul_right h (by positivity)).le
  have hU2 : 2 * (2 : ℝ) ^ (i1 + i4) ≤ Y := by
    have h : 2 * (2 : ℝ) ^ (i1 + i4) * (P1 * P2) ≤ Y * (P1 * P2) := by
      calc 2 * (2 : ℝ) ^ (i1 + i4) * (P1 * P2) = 2 * (2 : ℝ) ^ bsize β := by rw [hbs]; ring
        _ ≤ 2 * (2 * (α * Y)) := by linarith
        _ = 4 * α * Y := by ring
        _ ≤ Y * (P1 * P2) := hz1b
    exact le_of_mul_le_mul_right h hPP
  -- exceptional unit intervals
  have hs2prime : ∀ p ∈ s2, p.Prime ∧ P1 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * P1 := by
    intro p hp
    obtain ⟨hpG, hpd⟩ := Finset.mem_filter.mp hp
    have hpdy := mem_dyad.mp hpd
    refine ⟨G.prime gs p hpG, by rw [hP1]; exact_mod_cast hpdy.1, ?_⟩
    have : ((p : ℕ) : ℝ) < ((2 ^ (i2 + 1) : ℕ) : ℝ) := by exact_mod_cast hpdy.2
    rw [hP1]; push_cast at this; rw [pow_succ] at this; linarith
  have hexc' := hexc Y P1 T1 s2 (fun p => χ (p : ZMod r)) hYx1 hYx2 hT10 (by linarith) hP1lo
    hP1hi hs2prime (fun p _ => χ.norm_le_one _)
  set occ := hexc'.1.toFinset with hocc
  have hocc_card : (occ.card : ℝ) ≤ Y ^ (0.05 : ℝ) := by
    rw [hocc, ← Set.ncard_eq_toFinset_card _ hexc'.1]
    exact hexc'.2.trans hcount
  have hoccY : ∀ j ∈ occ, |(j : ℝ)| ≤ Y := by
    intro j hj
    rw [hocc, Set.Finite.mem_toFinset] at hj
    exact (occupied_abs_le _ _ _ _ j hj).trans hT1Y
  have hoff : ∀ s, |s| ≤ T1 → (∀ j ∈ occ, s ∉ Set.Icc (j : ℝ) (j + 1)) →
      ‖hpoly f2 i2 s‖ ≤ (mass G gs)⁻¹ * Lx ^ (-A_s) := by
    intro s hs hsoff
    exact hpoly_S0_off_occ G gs r χ i2 hmass (Lx ^ (-A_s)) T1 occ
      (fun j hj => by rw [hocc, Set.Finite.mem_toFinset]; exact hj) s hs hsoff
  have hF2 : ∀ s, ‖hpoly f2 i2 s‖ ≤ 1 := fun s => norm_hpoly_S0_le G gs r χ i2 hmass s
  -- the long rough-integer polynomial
  have hσ1 : |E.sigma₁| ≤ Lx ^ C := hE.2.2.2.2.2.2.2.1
  have hσ0 : |E.sigma₀| ≤ Lx ^ C := hE.2.2.2.2.2.2.1
  have hlong' : ∀ s, Lx ^ B0 ≤ |s| → |s| ≤ T1 → ‖hpoly f3 i3 s‖ ≤ K_l * Lx ^ (-A_l) := by
    intro s hs1 hs2
    rw [show hpoly f3 i3 s = hpoly (fun p => P0 E x p * χ (p : ZMod r)) i3 s from rfl,
      hpoly_P0_eq E x r χ i3 hElo hlohi s]
    apply hlong P2 _ _ E.sigma₁ s r χ hP2lo hP2hi (le_max_left _ _) h3e
    · have : (2 : ℝ) ^ (i3 + 1) = 2 * P2 := by rw [hP2, pow_succ]; ring
      linarith [min_le_left ((2 : ℝ) ^ (i3 + 1) - 1) E.hi]
    · exact hr1
    · exact hrC
    · exact hσ1
    · exact hs1
    · calc |s + E.sigma₁| ≤ |s| + |E.sigma₁| := abs_add_le _ _
        _ ≤ T1 + Lx ^ C := add_le_add hs2 hσ1
        _ ≤ _ := hT1x
  -- the discrepancy-bearing polynomial
  have hMr1 : 1 ≤ E.modulus * r := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero E.positive.ne' (by omega))
  have hMrL : ((E.modulus * r : ℕ) : ℝ) ≤ Lx ^ (2 * C) := by
    push_cast
    rw [show 2 * C = C + C by ring, Real.rpow_add hLpos]
    exact mul_le_mul hE.2.2.2.2.2.1 hrC (Nat.cast_nonneg _) hLC
  obtain ⟨ψ, hψ⟩ := exists_prod_char E.modulus r E.chi χ
  have hcop : ∀ m, E.alpha m ≠ 0 → Nat.Coprime m (E.modulus * r) := by
    intro m hm
    exact coprime_of_rough (hE.2.2.2.2.1 m hm) hMr1 (lt_of_le_of_lt hMrL hWC)
  have hdisc' : ∀ s, |s| ≤ Lx ^ B0 → ‖hpoly f1 i1 s‖ ≤ Lx ^ (-B) := by
    intro s hs
    rw [show hpoly f1 i1 s = hpoly (fun m => A0 E m * χ (m : ZMod r)) i1 s from rfl,
      hpoly_A0_eq E r χ i1 ψ hψ hcop s]
    have hi1le : (2 : ℝ) ^ i1 ≤ 2 ^ bsize β := pow_le_pow_right₀ (by norm_num) (by
      simp only [bsize, hi1]; omega)
    apply hdisc
    · exact one_le_pow₀ (by norm_num)
    · have : (2 : ℝ) ^ (i1 + 1) = 2 * 2 ^ i1 := by ring
      have : (1 : ℝ) ≤ 2 ^ i1 := one_le_pow₀ (by norm_num)
      linarith
    · have : (2 : ℝ) ^ (i1 + 1) = 2 * 2 ^ i1 := by ring
      linarith
    · exact hMr1
    · exact hMrL.trans hBC
    · calc |s + E.sigma₀| ≤ |s| + |E.sigma₀| := abs_add_le _ _
        _ ≤ Lx ^ B0 + Lx ^ C := add_le_add hs hσ0
        _ ≤ Lx ^ B := hBB0
  have hthr := hthree f1 f2 f3 f4 i1 i2 i3 i4 (Lx ^ C) (Lx ^ C * Wb) Y (Lx ^ B0) T1
    ((mass G gs)⁻¹ * Lx ^ (-A_s)) (Lx ^ (-B)) (K_l * Lx ^ (-A_l)) occ hLC (mul_nonneg hLC hWb0)
    (fun m _ => norm_cf1_le hE r χ m) (fun m _ => norm_cf3_le E x r χ m)
    (fun m _ => norm_cf4_le G hE Wr Wb hWb r u χ m) (Real.rpow_nonneg hLpos.le _) hT10
    (by have := Real.rpow_nonneg hLpos.le (-A_s); positivity)
    (by have := Real.rpow_nonneg hLpos.le (-A_l); positivity) hY0 hU1 hU2 hocc_card hoccY
    hoff hF2 hlong' hdisc'
  -- simplification of the bound
  have hx0 : 0 < x := by linarith
  have hlogx2 : Real.log (x ^ (2 : ℕ)) = 2 * Lx := by rw [Real.log_pow]; push_cast; rfl
  set S3 := i1 + i3 + i4 with hS3
  have h2S3 : (2 : ℝ) ^ S3 * P1 = 2 ^ bsize β := by
    rw [hP1, ← pow_add]; congr 1; simp only [bsize, hS3, hi1, hi2, hi3, hi4]; ring
  have hS3pos : (0 : ℝ) < 2 ^ S3 := by positivity
  have hT1S3 : 2 * T1 ≤ 2 ^ S3 := by
    have hexp : 0 < Real.exp (Lx ^ P.b) := Real.exp_pos _
    have h : 2 * T1 * (16 * Real.exp (Lx ^ P.b)) ≤ 2 ^ S3 * (16 * Real.exp (Lx ^ P.b)) := by
      calc 2 * T1 * (16 * Real.exp (Lx ^ P.b)) ≤ α * Y := hz2
        _ ≤ 16 * 2 ^ bsize β := hrel1.le
        _ = 16 * (2 ^ S3 * P1) := by rw [h2S3]
        _ ≤ 2 ^ S3 * (16 * Real.exp (Lx ^ P.b)) := by
          have := mul_le_mul_of_nonneg_left hP1hi (show (0 : ℝ) ≤ 16 * 2 ^ S3 by positivity)
          linarith
    exact le_of_mul_le_mul_right h (by positivity)
  have hbig : 16 * (2 : ℝ) ^ bsize β ≤ x ^ (2 : ℕ) := by linarith
  have hS3le : (2 : ℝ) ^ S3 ≤ 2 ^ bsize β := by
    rw [← h2S3]; exact le_mul_of_one_le_right hS3pos.le hP1ge1
  have hℓ3 : Real.log (2 * 2 ^ (S3 + 3)) ≤ 2 * Lx := by
    rw [← hlogx2]
    apply Real.log_le_log (by positivity)
    have : (2 : ℝ) * 2 ^ (S3 + 3) = 16 * 2 ^ S3 := by ring
    rw [this]; linarith
  have hℓ3' : 0 ≤ Real.log (2 * 2 ^ (S3 + 3)) :=
    Real.log_nonneg (by have : (1 : ℝ) ≤ 2 ^ (S3 + 3) := one_le_pow₀ (by norm_num); linarith)
  have h14le : (2 : ℝ) ^ (i1 + i4) ≤ 2 ^ bsize β := by
    rw [hbs, mul_assoc]
    exact le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hP1ge1 hP2ge1)
  have hℓ2 : Real.log (2 * 2 ^ (i1 + i4 + 2)) ≤ 2 * Lx := by
    rw [← hlogx2]
    apply Real.log_le_log (by positivity)
    have : (2 : ℝ) * 2 ^ (i1 + i4 + 2) = 8 * 2 ^ (i1 + i4) := by ring
    rw [this]; linarith
  have hℓ2' : 0 ≤ Real.log (2 * 2 ^ (i1 + i4 + 2)) :=
    Real.log_nonneg (by have : (1 : ℝ) ≤ 2 ^ (i1 + i4 + 2) := one_le_pow₀ (by norm_num); linarith)
  have hlY : Real.log (2 * Y) ≤ 2 * Lx := by
    rw [← hlogx2]; exact Real.log_le_log (by positivity) hz3'
  have hlY' : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  have h2L : 0 ≤ 2 * Lx := by positivity
  refine hthr.trans ?_
  exact j3_simplify K3r c3r T1 Lx _ _ _ _ Y i1 i3 i4 hK3r.le hc3r hT10 h2L hT1S3 hℓ3 hℓ3' hℓ2 hℓ2'
    hlY hlY'

end Erdos821.P5Marked
