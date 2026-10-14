module

public import Erdos408.OneSided.Major.Assembly

/-!
# The major term

Interface 3 of `blueprint/one_sided_type_ii.md` (§6, PD §5). On each major arc
`h/k + λ/Y`, expand `e(h(bmn - ars - b + a)/k)` into products of characters modulo `k`,
and separate `w = bmn / (YX)` from `w' = ars / (YX)` by Mellin inversion of
`ψ(X(w - w')) e(λ X (w - w'))`. The major sum is then controlled by the energy
`∫ |B_λ M_α N_β|²` over `|t| ≤ 2 X L^B`. Peel one prime from the label product. Where its
polynomial is small, the mean value of `M_α N_β` suffices. Where it is large, the
frequencies are sparse, P4 makes `M_α` small, and the kernel premise (G) bounds the
energy of `N_β` on the sparse set (PD Lemma 5.3).

The Lean route is §6.4. `majorSquare_eq_sum_arcs` (`Major/Arcs.lean`) writes the major sum
arc by arc. `norm_arcTerm_le` (`Major/Assembly.lean`) bounds one arc term by the energy
(`eventually_energy_le`) and the mean values, through the three regions of
`Major/Regions.lean`. `arcBound_le` below does the parameter bookkeeping.
-/

@[expose] public section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### Thresholds and bookkeeping -/

/-- `L^A < W = exp(L^{0.24})` eventually, for any fixed `A`. -/
private theorem eventually_rpow_lt_roughLevel (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ A < roughLevel x := by
  have hexp := (tendsto_exp_div_rpow_atTop (A / 0.24)).comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.24)).comp Real.tendsto_log_atTop)
  filter_upwards [hexp.eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hL
  have hx' : 1 < Real.exp (Real.log x ^ (0.24 : ℝ)) / (Real.log x ^ (0.24 : ℝ)) ^ (A / 0.24) :=
    hx
  -- `(L^{0.24})^{A/0.24} = L^A`
  rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ (by norm_num),
    one_lt_div (by positivity)] at hx'
  exact hx'

/-- There are at most `L^{2A₀}` arcs: at most `k` for each `k ≤ L^{A₀}`. -/
private theorem card_arcSet_le (A₀ x : ℝ) (hL : 0 < Real.log x) :
    (#(arcSet A₀ x) : ℝ) ≤ Real.log x ^ (2 * A₀) := by
  set N := ⌊Real.log x ^ A₀⌋₊
  have hcard : #(arcSet A₀ x) ≤ N * N := by
    rw [arcSet, card_sigma]
    calc ∑ k ∈ Icc 1 N, #((range k).filter fun h => Nat.Coprime h k)
        ≤ ∑ _k ∈ Icc 1 N, N := sum_le_sum fun k hk =>
          (card_filter_le _ _).trans ((card_range k).le.trans (mem_Icc.1 hk).2)
      _ = N * N := by rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
  have hN : (N : ℝ) ≤ Real.log x ^ A₀ := Nat.floor_le (by positivity)
  calc (#(arcSet A₀ x) : ℝ) ≤ (N : ℝ) * N := by exact_mod_cast hcard
    _ ≤ Real.log x ^ A₀ * Real.log x ^ A₀ := mul_le_mul hN hN (by positivity) (by positivity)
    _ = Real.log x ^ (2 * A₀) := by rw [← Real.rpow_add hL, two_mul]

/-- The bookkeeping of one arc term (blueprint §6.4, "Parameters"). With `ε = L^{A' - P}`,
`E = |C_E| L^{-A'}`, `M = 165888 L^{C₄}`, `T = X L^B`, `Λ = 2 L^{A₀}` and at most `L^{3A₀}`
character triples, where `P = D + 13A₀`, `B = P + C₄` and `A' = 5P + 4C₄`, the bound of
`norm_arcTerm_le` is `O(X Y² L^{10A₀ - P})`: the three terms are `O(L^{-P})`. -/
private theorem arcBound_le {L X Y C₀ CE n A₀ P C₄ B A' : ℝ} (hL : 1 ≤ L) (hX : 0 < X)
    (hY : 0 < Y) (hn0 : 0 ≤ n) (hn : n ≤ L ^ (3 * A₀)) (hP : 0 ≤ P) (hC₄ : 0 ≤ C₄)
    (hB : B = P + C₄) (hA' : A' = 5 * P + 4 * C₄) :
    |C₀| * (2 * L ^ A₀) ^ 4 / X * (X * Y) ^ 2 *
      (π * ((L ^ (A' - P) * (n ^ 2 * (|CE| * L ^ (-A'))) +
          (L ^ (A' - P))⁻¹ * (n ^ 2 * (165888 * L ^ C₄) * (1 + 2 * (X * L ^ B) / X))) / 2 +
        8 * (n ^ 2 * (165888 * L ^ C₄)) * X / (X * L ^ B))) ≤
      16 * π * |C₀| * (|CE| / 2 + 3 * 165888 / 2 + 8 * 165888) * X * Y ^ 2 *
        L ^ (10 * A₀ - P) := by
  have hL0 : 0 < L := by linarith
  set u := L ^ (-P) with hu
  have hu0 : 0 ≤ u := by positivity
  -- the energy term: `ε E = |C_E| L^{-P}`
  have e₁ : L ^ (A' - P) * L ^ (-A') = u := by
    rw [hu, ← Real.rpow_add hL0]
    congr 1
    ring
  -- the mean-value term on `[-T, T]`: `ε⁻¹ L^{C₄} L^B = L^{-3P - 2C₄} ≤ L^{-P}`
  have e₂ : (L ^ (A' - P))⁻¹ * L ^ C₄ * L ^ B ≤ u := by
    rw [hu, ← Real.rpow_neg hL0.le, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by rw [hB, hA']; linarith)
  have hLB : 1 ≤ L ^ B := Real.one_le_rpow hL (by rw [hB]; linarith)
  have e₃ : 1 + 2 * (X * L ^ B) / X ≤ 3 * L ^ B := by
    have h : 2 * (X * L ^ B) / X = 2 * L ^ B := by field_simp
    rw [h]
    linarith
  -- the `τ`-tail: `L^{C₄} X / T = L^{C₄ - B} = L^{-P}`
  have e₄ : L ^ C₄ * X / (X * L ^ B) = u := by
    rw [hu, show -P = C₄ - B by rw [hB]; ring, Real.rpow_sub hL0]
    field_simp
  have hΦ : (L ^ (A' - P) * (n ^ 2 * (|CE| * L ^ (-A'))) +
        (L ^ (A' - P))⁻¹ * (n ^ 2 * (165888 * L ^ C₄) * (1 + 2 * (X * L ^ B) / X))) / 2 +
      8 * (n ^ 2 * (165888 * L ^ C₄)) * X / (X * L ^ B) ≤
      n ^ 2 * (|CE| / 2 + 3 * 165888 / 2 + 8 * 165888) * u := by
    have t₁ : L ^ (A' - P) * (n ^ 2 * (|CE| * L ^ (-A'))) = n ^ 2 * |CE| * u := by
      rw [← e₁]
      ring
    have t₂ : (L ^ (A' - P))⁻¹ * (n ^ 2 * (165888 * L ^ C₄) * (1 + 2 * (X * L ^ B) / X)) ≤
        n ^ 2 * 165888 * 3 * u :=
      calc (L ^ (A' - P))⁻¹ * (n ^ 2 * (165888 * L ^ C₄) * (1 + 2 * (X * L ^ B) / X))
          ≤ (L ^ (A' - P))⁻¹ * (n ^ 2 * (165888 * L ^ C₄) * (3 * L ^ B)) := by gcongr
        _ = n ^ 2 * 165888 * 3 * ((L ^ (A' - P))⁻¹ * L ^ C₄ * L ^ B) := by ring
        _ ≤ n ^ 2 * 165888 * 3 * u := by gcongr
    have t₃ : 8 * (n ^ 2 * (165888 * L ^ C₄)) * X / (X * L ^ B) = n ^ 2 * (8 * 165888) * u := by
      rw [← e₄]
      ring
    rw [t₁, t₃]
    linarith
  have hcoef : |C₀| * (2 * L ^ A₀) ^ 4 / X * (X * Y) ^ 2 =
      16 * |C₀| * L ^ (4 * A₀) * X * Y ^ 2 := by
    rw [mul_pow, show (L ^ A₀) ^ 4 = L ^ (4 * A₀) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring]
    field_simp
    ring
  have hn2 : n ^ 2 ≤ L ^ (6 * A₀) :=
    calc n ^ 2 ≤ (L ^ (3 * A₀)) ^ 2 := pow_le_pow_left₀ hn0 hn 2
      _ = L ^ (6 * A₀) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        congr 1
        push_cast
        ring
  have hexp : L ^ (4 * A₀) * L ^ (6 * A₀) * u = L ^ (10 * A₀ - P) := by
    rw [hu, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  rw [hcoef]
  calc 16 * |C₀| * L ^ (4 * A₀) * X * Y ^ 2 *
        (π * ((L ^ (A' - P) * (n ^ 2 * (|CE| * L ^ (-A'))) +
          (L ^ (A' - P))⁻¹ * (n ^ 2 * (165888 * L ^ C₄) * (1 + 2 * (X * L ^ B) / X))) / 2 +
        8 * (n ^ 2 * (165888 * L ^ C₄)) * X / (X * L ^ B)))
      ≤ 16 * |C₀| * L ^ (4 * A₀) * X * Y ^ 2 *
          (π * (n ^ 2 * (|CE| / 2 + 3 * 165888 / 2 + 8 * 165888) * u)) := by gcongr
    _ ≤ 16 * |C₀| * L ^ (4 * A₀) * X * Y ^ 2 *
          (π * (L ^ (6 * A₀) * (|CE| / 2 + 3 * 165888 / 2 + 8 * 165888) * u)) := by gcongr
    _ = 16 * π * |C₀| * (|CE| / 2 + 3 * 165888 / 2 + 8 * 165888) * X * Y ^ 2 *
          (L ^ (4 * A₀) * L ^ (6 * A₀) * u) := by ring
    _ = _ := by rw [hexp]

/-! ### The major term -/

/-- Interface 3: under P4 and (G), the major sum is `O(X Y L^{-D₁ - 1})` for every dyadic
`Y`. Write it as `∑_{k, h} ∫_{|θ| ≤ 2L^{A₀}/Y}` of the arc terms (`majorSquare_eq_sum_arcs`).
Each arc term is `O(X Y² L^{-D - 3A₀})` (`norm_arcTerm_le`, `arcBound_le`), there are at most
`L^{2A₀}` arcs, and each has length `4L^{A₀}/Y`. -/
theorem eventually_majorSquare {C CX alo ahi Dstar g c₄ cG : ℝ} (hC : 0 < C) (hD : 0 < Dstar)
    (hCX : 1 ≤ CX) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5) :
    ∃ C₃ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      TwistBound (arcExp Dstar C) (freqExp Dstar C) (twistExp Dstar C) c₄ x d →
      KernelBound (freqExp Dstar C) cG x d → ∀ j : ℕ,
      ‖majorSquare (arcExp Dstar C) x d (2 ^ j)‖ ≤
        C₃ * d.X * 2 ^ j * Real.log x ^ (-(squarePrec Dstar + 1)) := by
  obtain ⟨C₀, hsep⟩ := exists_plateauTwist_separation
  obtain ⟨CE, hEn⟩ := eventually_energy_le (K := K) (g := g) (c₄ := c₄) (cG := cG) hC hD hCX
    halo hahi
  set A₀ := arcExp Dstar C with hA₀
  set B := freqExp Dstar C with hB
  set A' := energyExp Dstar C with hA'
  set C₄ := meanExp C with hC₄
  set P := majorPrec Dstar + 13 * A₀ with hP
  set c₁ : ℝ := |CE| / 2 + 3 * 165888 / 2 + 8 * 165888 with hc₁
  have hA₀0 : 0 < A₀ := by
    simp only [hA₀, arcExp, edgePrec, momentPrec, squarePrec]
    linarith
  have hC₄0 : 0 < C₄ := by
    simp only [hC₄, meanExp]
    linarith
  have hP0 : 0 < P := by
    simp only [hP, majorPrec, squarePrec]
    linarith
  have hBP : B = P + C₄ := by simp only [hB, hP, hC₄, hA₀, freqExp]
  have hA'P : A' = 5 * P + 4 * C₄ := by
    simp only [hA', hP, hC₄, hA₀, energyExp, freqExp]
    ring
  have hCX0 : 0 < CX := by linarith
  refine ⟨64 * π * |C₀| * c₁, ?_⟩
  filter_upwards [hEn, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (4 * CX)), eventually_ge_atTop 1,
    (tendsto_id.atTop_div_const hCX0).eventually_ge_atTop 2,
    eventually_rpow_lt_of_mem_band (by linarith : (0 : ℝ) < alo) A₀,
    eventually_rpow_lt_roughLevel A₀] with x hEx hL hL4 hx1 hx2 hband hrough
  intro d hd hP4 hKB j
  set L := Real.log x with hLdef
  set Y : ℝ := 2 ^ j with hYdef
  have hL0 : 0 < L := by linarith
  have hY : 0 < Y := by positivity
  have hx0 : 0 < x := by linarith
  have hHm : 0 < d.Hm := (Real.rpow_pos_of_pos hx0 _).trans_le hd.Hm_ge
  have hHn : 0 < d.Hn := (Real.rpow_pos_of_pos hx0 _).trans_le hd.Hn_ge
  have hX : 0 < d.X := mul_pos hHm hHn
  have hX2 : 2 ≤ d.X := hx2.trans hd.X_ge
  have hlog : Real.log (4 * d.X) ≤ 2 * L := by
    have h₁ : 4 * d.X ≤ 4 * CX * x := by
      have := hd.X_le
      unfold Data.X
      linarith
    calc Real.log (4 * d.X) ≤ Real.log (4 * CX * x) := Real.log_le_log (by positivity) h₁
      _ = Real.log (4 * CX) + L := Real.log_mul (by positivity) hx0.ne'
      _ ≤ 2 * L := by linarith
  -- the sides: products are positive, and `w_u ∈ [1, 16]` where `c_u ≠ 0`
  have hmem : ∀ u ∈ sideSet x d, u.1 ∈ d.labels x ∧ u.2.1 ∈ d.mRange ∧ u.2.2 ∈ d.nRange :=
    fun u hu => by simpa only [sideSet, mem_product] using hu
  have hpos : ∀ u ∈ sideSet x d, 0 < sideProd u := by
    intro u hu
    obtain ⟨hp, hm, hn⟩ := hmem u hu
    have hl : sideLabel u ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ =>
      (TypeII.band_prime (Fintype.mem_piFinset.1 hp i)).ne_zero
    have hm0 : u.2.1 ≠ 0 :=
      (lt_of_lt_of_le (Nat.ceil_pos.2 hHm) (Finset.mem_Icc.1 hm).1).ne'
    have hn0 : u.2.2 ≠ 0 :=
      (lt_of_lt_of_le (Nat.ceil_pos.2 hHn) (Finset.mem_Icc.1 hn).1).ne'
    exact Nat.pos_of_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero hl hm0) hn0)
  have hcoeff : ∀ u, sideCoeff x d Y u ≠ 0 → dyadicBump (sideLabel u / Y) ≠ 0 ∧
      d.α u.2.1 ≠ 0 ∧ d.β u.2.2 ≠ 0 := by
    intro u hcu
    refine ⟨fun h0 => hcu ?_, fun h0 => hcu ?_, fun h0 => hcu ?_⟩ <;> simp [sideCoeff, h0]
  have hsupp : ∀ u ∈ sideSet x d, sideCoeff x d Y u ≠ 0 →
      1 ≤ (sideProd u : ℝ) / (d.X * Y) ∧ (sideProd u : ℝ) / (d.X * Y) ≤ 16 := by
    intro u _ hcu
    obtain ⟨hη, hα, hβ⟩ := hcoeff u hcu
    obtain ⟨ha₁, ha₂⟩ := lt_of_dyadicBump_ne_zero hη
    rw [lt_div_iff₀ hY, one_mul] at ha₁
    rw [div_lt_iff₀ hY] at ha₂
    obtain ⟨hm₁, hm₂, -, -⟩ := hd.α_supp _ hα
    obtain ⟨hn₁, hn₂, -, -⟩ := hd.β_supp _ hβ
    have hN : (sideProd u : ℝ) = sideLabel u * u.2.1 * u.2.2 := by
      simp only [sideProd, Nat.cast_mul]
    have hXY : d.X * Y = Y * d.Hm * d.Hn := by unfold Data.X; ring
    rw [hN, hXY]
    constructor
    · rw [le_div_iff₀ (by positivity), one_mul]
      exact mul_le_mul (mul_le_mul ha₁.le hm₁ hHm.le (by positivity)) hn₁ hHn.le (by positivity)
    · rw [div_le_iff₀ (by positivity)]
      calc (sideLabel u : ℝ) * u.2.1 * u.2.2 ≤ (4 * Y) * (2 * d.Hm) * (2 * d.Hn) :=
            mul_le_mul (mul_le_mul ha₂.le hm₂ (by positivity) (by positivity)) hn₂
              (by positivity) (by positivity)
        _ = 16 * (Y * d.Hm * d.Hn) := by ring
  -- one arc term is `O(X Y² L^{10A₀ - P})`
  set U : ℝ := 16 * π * |C₀| * c₁ * d.X * Y ^ 2 * L ^ (10 * A₀ - P) with hU
  have harc : ∀ kh ∈ arcSet A₀ x,
      ∀ θ ∈ Set.uIoc (-(2 * L ^ A₀ / Y)) (2 * L ^ A₀ / Y), ‖arcTerm x d Y kh.1 kh.2 θ‖ ≤ U := by
    rintro ⟨k, h⟩ hkh θ hθ
    simp only [arcSet, mem_sigma, mem_Icc, mem_filter, mem_range] at hkh
    have hk1 : 1 ≤ k := hkh.1.1
    have hkL : (k : ℝ) ≤ L ^ A₀ :=
      (Nat.cast_le.2 hkh.1.2).trans (Nat.floor_le (by positivity))
    have : NeZero k := ⟨by omega⟩
    obtain ⟨lam, rfl⟩ : ∃ lam, θ = lam / Y := ⟨Y * θ, by field_simp⟩
    have hδ : 0 ≤ 2 * L ^ A₀ / Y := by positivity
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hθ
    have hlam : |lam| ≤ 2 * L ^ A₀ := by
      have h₁ : |lam / Y| ≤ 2 * L ^ A₀ / Y := abs_le.2 ⟨hθ.1.le, hθ.2⟩
      rw [abs_div, abs_of_pos hY, div_le_div_iff_of_pos_right hY] at h₁
      exact h₁
    have hΛ : 1 ≤ 2 * L ^ A₀ := by
      have := Real.one_le_rpow hL hA₀0.le
      linarith
    obtain ⟨Kf, hKi, hKb, hK⟩ := hsep (2 * L ^ A₀) d.X lam hΛ hX2 hlam
    -- the variables of a side with `c_u ≠ 0` are units modulo `k`
    have hndvd : ∀ q : ℕ, L ^ A₀ < q → ¬q ∣ k := fun q hq hqk => by
      have : (q : ℝ) ≤ k := by exact_mod_cast Nat.le_of_dvd (by omega) hqk
      linarith
    have hrough' : ∀ m : ℕ, m ≠ 0 → IsRough x m → Nat.Coprime m k := fun m hm hm' =>
      Nat.coprime_of_dvd fun q hq hqm => hndvd q
        (hrough.trans (hm' q (Nat.mem_primeFactors.2 ⟨hq, hqm, hm⟩)))
    have hunit : ∀ u ∈ sideSet x d, sideCoeff x d Y u ≠ 0 →
        IsUnit (sideLabel u : ZMod k) ∧ IsUnit (u.2.1 : ZMod k) ∧ IsUnit (u.2.2 : ZMod k) := by
      intro u hu hcu
      obtain ⟨hp, -, -⟩ := hmem u hu
      obtain ⟨-, hα, hβ⟩ := hcoeff u hcu
      obtain ⟨hm₁, -, hmr, -⟩ := hd.α_supp _ hα
      obtain ⟨hn₁, -, hnr, -⟩ := hd.β_supp _ hβ
      have hm0 : u.2.1 ≠ 0 := by
        rintro h0
        rw [h0, Nat.cast_zero] at hm₁
        linarith
      have hn0 : u.2.2 ≠ 0 := by
        rintro h0
        rw [h0, Nat.cast_zero] at hn₁
        linarith
      refine ⟨(ZMod.isUnit_iff_coprime _ _).2 ?_, (ZMod.isUnit_iff_coprime _ _).2
        (hrough' _ hm0 hmr), (ZMod.isUnit_iff_coprime _ _).2 (hrough' _ hn0 hnr)⟩
      exact Nat.Coprime.prod_left fun i _ =>
        (Nat.Prime.coprime_iff_not_dvd (TypeII.band_prime (Fintype.mem_piFinset.1 hp i))).2
          (hndvd _ (hband _ (hd.window i).1 _ (Fintype.mem_piFinset.1 hp i)))
    -- the energy, the mean values and the number of character triples
    have hE : ∀ χ₁ χ₂ χ₃ : DirichletCharacter ℂ k, ∫ τ in (-(d.X * L ^ B))..(d.X * L ^ B),
        ‖labelPoly x d Y lam χ₁ τ * markedPoly d χ₂ τ * unmarkedPoly d χ₃ τ‖ ^ 2 ≤
          |CE| * L ^ (-A') := fun χ₁ χ₂ χ₃ =>
      (hEx d hd hP4 hKB j lam hlam k hk1 hkL χ₁ χ₂ χ₃).trans
        (mul_le_mul_of_nonneg_right (le_abs_self CE) (by positivity))
    have hM := fun (χ₁ χ₂ χ₃ : DirichletCharacter ℂ k) (a b : ℝ) (hab : a ≤ b) =>
      integral_norm_labelPoly_mul_sq_le hd hx1 hL hlog hY lam χ₁ χ₂ χ₃ hab
    have hn : ((Fintype.card (DirichletCharacter ℂ k) : ℝ) ^ 3) ≤ L ^ (3 * A₀) := by
      have h₁ : (Fintype.card (DirichletCharacter ℂ k) : ℝ) ≤ L ^ A₀ :=
        (Nat.cast_le.2 (card_dirichletCharacter_le k)).trans hkL
      calc ((Fintype.card (DirichletCharacter ℂ k) : ℝ) ^ 3) ≤ (L ^ A₀) ^ 3 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) h₁ 3
        _ = L ^ (3 * A₀) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
          congr 1
          push_cast
          ring
    have hXT : d.X ≤ d.X * L ^ B :=
      le_mul_of_one_le_right hX.le (Real.one_le_rpow hL (by rw [hBP]; linarith))
    refine (norm_arcTerm_le hY hHm hHn k h lam (c := |C₀| * (2 * L ^ A₀) ^ 4 / d.X) hKi
      (fun τ σ => (hKb τ σ).trans (by gcongr; exact le_abs_self _)) hK hsupp hpos hunit hXT
      (Real.rpow_pos_of_pos hL0 (A' - P)) hE hM).trans ?_
    exact arcBound_le hL hX hY (by positivity) hn hP0.le hC₄0.le hBP hA'P
  -- sum over the arcs, each of length `4L^{A₀}/Y`
  rw [majorSquare_eq_sum_arcs]
  have hexp : L ^ (2 * A₀) * L ^ (10 * A₀ - P) * L ^ A₀ = L ^ (-(squarePrec Dstar + 1)) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    rw [hP, majorPrec]
    ring
  have hδ : 0 ≤ 2 * L ^ A₀ / Y := by positivity
  calc ‖∑ kh ∈ arcSet A₀ x, ∫ θ in (-(2 * L ^ A₀ / Y))..(2 * L ^ A₀ / Y),
        arcTerm x d Y kh.1 kh.2 θ‖
      ≤ ∑ kh ∈ arcSet A₀ x, ‖∫ θ in (-(2 * L ^ A₀ / Y))..(2 * L ^ A₀ / Y),
          arcTerm x d Y kh.1 kh.2 θ‖ := norm_sum_le _ _
    _ ≤ ∑ _kh ∈ arcSet A₀ x, U * |2 * L ^ A₀ / Y - -(2 * L ^ A₀ / Y)| :=
        Finset.sum_le_sum fun kh hkh =>
          intervalIntegral.norm_integral_le_of_norm_le_const (harc kh hkh)
    _ = #(arcSet A₀ x) * (U * (4 * L ^ A₀ / Y)) := by
        rw [Finset.sum_const, nsmul_eq_mul, abs_of_nonneg (by linarith)]
        ring
    _ ≤ L ^ (2 * A₀) * (U * (4 * L ^ A₀ / Y)) := by
        gcongr
        exact card_arcSet_le A₀ x hL0
    _ = 64 * π * |C₀| * c₁ * d.X * Y * (L ^ (2 * A₀) * L ^ (10 * A₀ - P) * L ^ A₀) := by
        rw [hU]
        field_simp
        ring
    _ = 64 * π * |C₀| * c₁ * d.X * Y * L ^ (-(squarePrec Dstar + 1)) := by rw [hexp]

end Erdos408.OneSided
