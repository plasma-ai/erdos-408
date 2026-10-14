import Erdos408.OneSided.Moment.Chain.Identity
import Erdos408.OneSided.Moment.Rank
import Erdos408.OneSided.Moment.Truncation
import Erdos408.OneSided.Bands

/-!
# The memory bound

PD §4 at a real root (`blueprint/one_sided_type_ii.md` §5.5 and §13). By S3
(`lineAverage_rootMoment_eq_chain`) the line average of the root moment is `∏_p b'_p` times
the distinct-birth history sum `distinctSum` with the exact cap. Two statements bound it:

* `eventually_distinctSum_truncation` (M3): lowering the cap to `B = ⌈L²⌉` costs at most
  `exp(-L²/2)`.
* `eventually_norm_distinctSum_le` (M4–M10): with the cap `B`, the distinct-birth history
  sum is at most `2 L^{-(E₀ + 2) N}`. The rank expansion of `Moment/Rank.lean` splits it at
  `r₀ = ⌈L^{9/20}⌉`: the ranks `r ≥ r₀` are bounded absolutely, the ranks `r < r₀` by the
  phased products.

Together they give `eventually_norm_lineAverage_le`, the memory bound of blueprint §11.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-- The truncation cap `B = ⌈L²⌉`. -/
def truncCap (x : ℝ) : ℕ := ⌈Real.log x ^ 2⌉₊

/-- M3, the truncation: lowering the memory cap from the number of band primes to
`B = ⌈L²⌉` changes the distinct-birth history sum by at most `exp(-L²/2)`. -/
theorem eventually_distinctSum_truncation {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q)
    (hq₁ : q < 1) (hC : 0 < C) (hD : 0 < Dstar) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5)
    (hK : bandThreshold Dstar C ≤ K) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
        ‖distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (memCap x d)
              (2 * momentPower x) -
            distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (truncCap x)
              (2 * momentPower x)‖ ≤
          Real.exp (-(Real.log x ^ 2 / 2)) := by
  filter_upwards [eventually_norm_distinctSum_sub_le hq hq₁ hC hD halo hahi hK]
    with x hx d hd j k u v r _ _ _ _ _ _
  exact hx d hd j k u v r

/-- M4–M10, the truncated memory bound: with the cap `B = ⌈L²⌉`, the distinct-birth history
sum is at most `2 L^{-(E₀ + 2) N}`. -/
theorem eventually_norm_distinctSum_le {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q)
    (hq₁ : q < 1) (hC : 0 < C) (hD : 0 < Dstar) (hCX : 1 ≤ CX) (halo : 1 / 10 < alo)
    (hahi : ahi < 1 / 5) (hK : bandThreshold Dstar C ≤ K) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
        ‖distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (truncCap x)
            (2 * momentPower x)‖ ≤
          2 * Real.log x ^ (-((momentPrec Dstar C + 2) * (2 * momentPower x : ℕ))) := by
  have hE₀ : 0 < momentPrec Dstar C := by
    unfold momentPrec squarePrec
    linarith
  have hG₀ : 0 ≤ edgePrec Dstar C := by
    unfold edgePrec
    linarith
  -- the operator bounds, with their constants made nonnegative
  obtain ⟨C₀, hG⟩ := exists_phasedGhost_normLe (K := K) (C := C) (CX := CX) (ahi := ahi)
    (g := g) hq hq₁ halo
  obtain ⟨Ce, hE⟩ := exists_phasedEdge_normLe (K := K) (C := C) (CX := CX) (ahi := ahi)
    (A₀ := arcExp Dstar C) hq hq₁ halo hg
  obtain ⟨C₁, hR⟩ := exists_realized_history_le (K := K) (C := C) (CX := CX) (ahi := ahi)
    (g := g) (A₀ := arcExp Dstar C) hq hq₁ halo
  obtain ⟨C₀', hC₀'1, hC₀'⟩ : ∃ C₀' : ℝ, 1 ≤ C₀' ∧ |C₀| ≤ C₀' :=
    ⟨|C₀| + 1, by linarith [abs_nonneg C₀], by linarith⟩
  obtain ⟨Ce', hCe'0, hCe'⟩ : ∃ Ce' : ℝ, 0 ≤ Ce' ∧ Ce ≤ Ce' :=
    ⟨max Ce 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C₁', hC₁'1, hC₁'⟩ : ∃ C₁' : ℝ, 1 ≤ C₁' ∧ |C₁| ≤ C₁' :=
    ⟨|C₁| + 1, by linarith [abs_nonneg C₁], by linarith⟩
  have hlog := Real.tendsto_log_atTop
  filter_upwards [hG, hE, hR, eventually_chainEdge_normLe hq hq₁ hC hD hCX halo hahi hK hg,
    eventually_rpow_lt_of_mem_band (by linarith : (0 : ℝ) < alo) 1,
    eventually_harmonicMass_band halo.le,
    hlog.eventually (eventually_highRank_sum_le (C₁ := C₁') (E := momentPrec Dstar C)
      (by linarith) hE₀.le halo.le),
    hlog.eventually (eventually_lowRank_sum_le K (E := momentPrec Dstar C) hC₀'1 hCe'0 hG₀ rfl),
    hlog.eventually (eventually_addrCount_le K), hlog.eventually_ge_atTop 16]
    with x hGx hEx hRx hE₀x hbig hV hhigh hlow haddr hL16 d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  set N := 2 * momentPower x with hNdef
  set B := truncCap x with hBdef
  obtain ⟨hN₁, hN₂⟩ := two_mul_momentPower_mem hL0
  -- `B ≤ L² + 1 ≤ L³`
  have hB : (B : ℝ) ≤ L ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hB3 : (B : ℝ) ≤ L ^ 3 :=
    calc (B : ℝ) ≤ L ^ 2 + 1 := hB
      _ ≤ L ^ 2 + 15 * L ^ 2 := by linarith [one_le_pow₀ (n := 2) hL1]
      _ = 16 * L ^ 2 := by ring
      _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hL16 (by positivity)
      _ = L ^ 3 := by ring
  have hJ : (padCount x : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
  -- the number `Q` of birth addresses is at most `L⁴`
  set Q := Fintype.card (BirthAddr (K := K) x B N) with hQdef
  have hQ : (Q : ℝ) ≤ L ^ 4 := by
    have hQeq : Q = K * (padCount x + 1) + (N * K + (N + 1) * B) := by
      simp [hQdef, BirthAddr, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [hQeq]
    exact haddr N (padCount x) B hN₂ hJ hB
  -- band primes exceed `L ≥ 2N + 1`
  have hpN : ∀ p ∈ bandPrimes x d, 2 * (N + 1) ≤ p + 1 := by
    intro p hp
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    have hLp := hbig (d.a i) (hd.window i).1 p hpi
    rw [Real.rpow_one] at hLp
    have hs := four_le_rpow_half hL16
    have hss : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by
      rw [← Real.rpow_add hL0]
      norm_num
    have h4s : 4 * L ^ (1 / 2 : ℝ) ≤ L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    have : 2 * ((N : ℝ) + 1) ≤ p + 1 := by linarith
    exact_mod_cast this
  -- the birth weights, the chain measure and the boundary norm
  have hν₀ : ∀ p ∈ bandPrimes x d, 0 ≤ primeWeight q x d N p := by
    intro p hp
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    exact (primeWeight_le_two_div q x d hq.le hpi (hV (d.a i) (hd.window i).1).1
      (hpN p hp)).1
  have hν : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 2 := fun i =>
    sum_band_primeWeight_le q x d hq.le (hV (d.a i) (hd.window i).1).1 fun p hp =>
      hpN p (mem_biUnion.2 ⟨i, mem_univ _, hp⟩)
  have hμ : ∀ s, 0 ≤ chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s := chainMeasure_nonneg hν₀
  have hW := wnormSq_chainInit_le (Y := 2 ^ j) (d₀ := 2 ^ k) (u := u) (v := v) (r := r) (B := B)
    hν₀ hν
  -- the modulus `P` exceeds every band prime, hence every birth
  set P := (bandPrimes x d).sup id + 1 with hP
  have hβ : ∀ s : ChainState x d (2 ^ j) (2 ^ k) u v r B,
      ∀ h ∈ histories x d (2 ^ j) (2 ^ k) u v r B N, ∀ a p, births s h a = some p → p < P :=
    fun s h hh a p hp => Nat.lt_succ_of_le (le_sup (f := id) (births_mem_bandPrimes s hh a p hp))
  -- the operator bounds at `x`
  have hGψ : ∀ (j' : ℕ) (ψ : Fin B → Option ℕ → ℂ), (∀ k o, ‖ψ k o‖ ≤ 1) →
      NormLe (chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N)
        (chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N)
        (phasedGhost q x d (2 ^ j) (2 ^ k) u v r B N j' ψ) C₀' := fun j' ψ hψ =>
    NormLe.mono hμ (abs_nonneg _) hC₀'
      (hGx d hd (2 ^ j) (2 ^ k) u v r B N j' hB3 rfl ψ hψ).abs
  have hEψ : ∀ ψ : Fin K → Option ℕ → ℂ, (∀ i o, ‖ψ i o‖ ≤ 1) →
      NormLe (chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N)
        (chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N)
        (phasedEdge q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N ψ) (L ^ Ce') :=
    fun ψ hψ => NormLe.mono hμ (Real.rpow_nonneg hL0.le _)
      (Real.rpow_le_rpow_of_exponent_le hL1 hCe')
      (hEx d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁ B N hB3 rfl ψ hψ)
  have hE₀ := hE₀x d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁ B N hB3 rfl
  -- low ranks: the phased products
  set r₀ := ⌈L ^ (9 / 20 : ℝ)⌉₊ with hr₀def
  have hlo : ∀ 𝒞 ∈ (blockSystems (BirthAddr (K := K) x B N)).filter (blockRank · < r₀),
      ‖blockSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N 𝒞‖ ≤
        C₀' ^ (N + 1) * L ^ (-edgePrec Dstar C * N +
          (Ce' + edgePrec Dstar C) * ((2 * blockRank 𝒞 : ℕ) : ℝ)) *
            2 ^ (K * (padCount x + 1)) := by
    intro 𝒞 h𝒞
    have h𝒞' := (mem_filter.1 h𝒞).1
    have hU : ((𝒞.biUnion id).card : ℝ) ≤ ((2 * blockRank 𝒞 : ℕ) : ℝ) := by
      exact_mod_cast card_biUnion_le_two_mul_blockRank h𝒞'
    have hc0 : 0 ≤ C₀' ^ (N + 1) * L ^ (-edgePrec Dstar C * N +
        (Ce' + edgePrec Dstar C) * (𝒞.biUnion id).card) :=
      mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg hL0.le _)
    calc ‖blockSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N 𝒞‖
        ≤ C₀' ^ (N + 1) * L ^ (-edgePrec Dstar C * N +
            (Ce' + edgePrec Dstar C) * (𝒞.biUnion id).card) *
          wnormSq (chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N)
            (chainInit x d (2 ^ j) (2 ^ k) u v r B) :=
          norm_blockSum_le hμ h𝒞' (Nat.succ_pos _) hβ hc0 fun ψ hψ hψU =>
            normLe_phasedProduct hL1 (by linarith) (by linarith) hμ hGψ hEψ hE₀ hψ hψU
      _ ≤ C₀' ^ (N + 1) * L ^ (-edgePrec Dstar C * N +
            (Ce' + edgePrec Dstar C) * ((2 * blockRank 𝒞 : ℕ) : ℝ)) *
          2 ^ (K * (padCount x + 1)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)) hW
            (wnormSq_nonneg hμ _) (mul_nonneg (pow_nonneg (by linarith) _)
              (Real.rpow_nonneg hL0.le _))
          exact Real.rpow_le_rpow_of_exponent_le hL1
            (add_le_add_right (mul_le_mul_of_nonneg_left hU (by linarith)) _)
  -- high ranks: the absolute bound
  have hhi : ∀ 𝒞 ∈ (blockSystems (BirthAddr (K := K) x B N)).filter (¬blockRank · < r₀),
      ‖blockSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N 𝒞‖ ≤
        L ^ (C₁' * (N + 1)) * (C₁' * Real.exp (-L ^ alo)) ^ blockRank 𝒞 := by
    intro 𝒞 h𝒞
    have h := hRx d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁ B N hB3 rfl 𝒞 (mem_filter.1 h𝒞).1
    refine (norm_blockSum_le_realized hμ 𝒞).trans (h.trans ?_)
    -- enlarge `C₁` to `C₁'`
    have ha : L ^ (C₁ * (N + 1)) ≤ L ^ (C₁' * (N + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hL1
        (mul_le_mul_of_nonneg_right ((le_abs_self C₁).trans hC₁') (by positivity))
    have hb : (C₁ * Real.exp (-L ^ alo)) ^ blockRank 𝒞 ≤
        (C₁' * Real.exp (-L ^ alo)) ^ blockRank 𝒞 := by
      refine (le_abs_self _).trans ?_
      rw [abs_pow, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_right hC₁' (Real.exp_pos _).le) _
    calc L ^ (C₁ * (N + 1)) * (C₁ * Real.exp (-L ^ alo)) ^ blockRank 𝒞
        ≤ L ^ (C₁ * (N + 1)) * (C₁' * Real.exp (-L ^ alo)) ^ blockRank 𝒞 :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL0.le _)
      _ ≤ L ^ (C₁' * (N + 1)) * (C₁' * Real.exp (-L ^ alo)) ^ blockRank 𝒞 :=
          mul_le_mul_of_nonneg_right ha
            (pow_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) _)
  -- split the rank expansion at `r₀`
  have hlowsum := norm_sum_blockCoef_mul_le (filter_subset _ _) (R := range r₀)
    (fun 𝒞 h => mem_range.2 (mem_filter.1 h).2)
    (blockSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N)
    (f := fun t => C₀' ^ (N + 1) * L ^ (-edgePrec Dstar C * N +
      (Ce' + edgePrec Dstar C) * ((2 * t : ℕ) : ℝ)) * 2 ^ (K * (padCount x + 1)))
    (fun _ _ => mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (Real.rpow_nonneg hL0.le _)) (by positivity)) hlo
  have hhighsum := norm_sum_blockCoef_mul_le (filter_subset _ _) (R := Ico r₀ (Q + 1))
    (fun 𝒞 h => mem_Ico.2 ⟨not_lt.1 (mem_filter.1 h).2,
      Nat.lt_succ_of_le (blockRank_le_card (mem_filter.1 h).1)⟩)
    (blockSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N)
    (f := fun t => L ^ (C₁' * (N + 1)) * (C₁' * Real.exp (-L ^ alo)) ^ t)
    (fun _ _ => mul_nonneg (Real.rpow_nonneg hL0.le _)
      (pow_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) _)) hhi
  rw [distinctSum_eq_sum_blockSum, ← sum_filter_add_sum_filter_not _ (blockRank · < r₀)]
  calc ‖∑ 𝒞 ∈ (blockSystems (BirthAddr (K := K) x B N)).filter (blockRank · < r₀),
          (blockCoef 𝒞 : ℂ) * blockSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N 𝒞 +
        ∑ 𝒞 ∈ (blockSystems (BirthAddr (K := K) x B N)).filter (¬blockRank · < r₀),
          (blockCoef 𝒞 : ℂ) * blockSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r B N 𝒞‖
      ≤ L ^ (-((momentPrec Dstar C + 2) * N)) + L ^ (-((momentPrec Dstar C + 2) * N)) :=
        (norm_add_le _ _).trans (add_le_add
          (hlowsum.trans (hlow N (padCount x) Q hN₁ hJ hQ))
          (hhighsum.trans (hhigh N Q hN₂ hQ)))
    _ = 2 * L ^ (-((momentPrec Dstar C + 2) * N)) := by ring

/-- The damping defects are in `[0, 1]`. -/
private theorem dampDefect_mem_Icc {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (N j : ℕ) :
    0 ≤ dampDefect q N j ∧ dampDefect q N j ≤ 1 := by
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
  unfold dampDefect
  split_ifs <;> constructor <;> linarith [Real.sqrt_nonneg q]

/-- For band primes beyond `N`, the baseline `b'_p` is in `[0, 1]`: each of the `N + 1`
defects is at most `1`, and `p + 1 > N + 1`. -/
private theorem baseline_mem_Icc {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {N p : ℕ} (hp : N < p) :
    0 ≤ baseline q N p ∧ baseline q N p ≤ 1 := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  -- `0 ≤ ∑_{j ≤ N} η'_j ≤ N + 1 ≤ p + 1`
  have hsum₀ : 0 ≤ ∑ j ∈ range (N + 1), dampDefect q N j :=
    sum_nonneg fun j _ => (dampDefect_mem_Icc hq hq₁ N j).1
  have hsum₁ : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (p : ℝ) + 1 :=
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (dampDefect_mem_Icc hq hq₁ N j).2
      _ = (N : ℝ) + 1 := by simp
      _ ≤ (p : ℝ) + 1 := by gcongr
  have h₀ : 0 ≤ ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j := by positivity
  have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 := by
    rw [inv_mul_le_iff₀ hp1, mul_one]
    exact hsum₁
  unfold baseline
  constructor <;> linarith

/-- For `L ≥ 4`, `2 ≤ L^{1/2}` and `2 L^{1/2} ≤ L`. -/
theorem two_le_rpow_half_of_four_le {L : ℝ} (hL : 4 ≤ L) :
    2 ≤ L ^ (1 / 2 : ℝ) ∧ 2 * L ^ (1 / 2 : ℝ) ≤ L := by
  set s := L ^ (1 / 2 : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  -- `s² = L`
  have hss : s * s = L := by
    rw [hs, ← Real.rpow_add (by linarith)]
    norm_num
  have hs2 : 2 ≤ s := by
    by_contra h
    push Not at h
    have : s * s < 2 * 2 := mul_lt_mul'' h h hs0 hs0
    linarith
  refine ⟨hs2, ?_⟩
  calc 2 * s ≤ s * s := mul_le_mul_of_nonneg_right hs2 hs0
    _ = L := hss

/-- `N = 2R` is between `2` and `L^{1/2} + 2`. -/
theorem two_mul_momentPower_bounds {x : ℝ} (hL : 0 < Real.log x) :
    2 ≤ ((2 * momentPower x : ℕ) : ℝ) ∧
      ((2 * momentPower x : ℕ) : ℝ) ≤ Real.log x ^ (1 / 2 : ℝ) + 2 := by
  have hpos : 0 < Real.log x ^ (1 / 2 : ℝ) / 2 := by positivity
  have hR : 1 ≤ momentPower x := Nat.ceil_pos.2 hpos
  have hR' : (momentPower x : ℝ) < Real.log x ^ (1 / 2 : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one hpos.le
  push_cast
  constructor
  · have : (1 : ℝ) ≤ momentPower x := by exact_mod_cast hR
    linarith
  · linarith

/-- The final comparison: for `L ≥ 8E + 16` and `2 ≤ n ≤ L^{1/2} + 2`,
`2 L^{-(E + 2) n} + exp(-L²/2) ≤ L^{-(E + 1) n}`. -/
private theorem two_mul_rpow_add_exp_le {E L n : ℝ} (hE : 0 < E) (hL : 8 * E + 16 ≤ L)
    (hn₂ : 2 ≤ n) (hn : n ≤ L ^ (1 / 2 : ℝ) + 2) :
    2 * L ^ (-((E + 2) * n)) + Real.exp (-(L ^ 2 / 2)) ≤ L ^ (-((E + 1) * n)) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  obtain ⟨hs2, hsL⟩ := two_le_rpow_half_of_four_le (show 4 ≤ L by linarith)
  set a := L ^ (-((E + 1) * n)) with ha
  -- the first term: `L^{-(E + 2) n} = a L^{-n} ≤ a / 4`
  have hLn : L ^ (-n) ≤ 1 / 4 :=
    calc L ^ (-n) ≤ L ^ (-2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = 1 / (L * L) := by
          rw [Real.rpow_neg hL0.le, show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
          ring
      _ ≤ 1 / 4 := by
          gcongr
          calc (4 : ℝ) = 2 * 2 := by norm_num
            _ ≤ L * L := mul_le_mul (by linarith) (by linarith) (by norm_num) hL0.le
  have h₁ : 2 * L ^ (-((E + 2) * n)) ≤ a / 2 := by
    have hsplit : L ^ (-((E + 2) * n)) = a * L ^ (-n) := by
      rw [ha, ← Real.rpow_add hL0]
      ring_nf
    rw [hsplit]
    have ha0 : 0 ≤ a := by positivity
    calc 2 * (a * L ^ (-n)) ≤ 2 * (a * (1 / 4)) := by gcongr
      _ = a / 2 := by ring
  -- the second term: `(E + 1) n log L + log 2 ≤ 4 (E + 1) L + L ≤ L² / 2`
  have hlog : Real.log L ≤ 2 * L ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hL0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  have hn' : n ≤ 2 * L ^ (1 / 2 : ℝ) := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hprod : (E + 1) * n * Real.log L ≤ 4 * (E + 1) * L :=
    calc (E + 1) * n * Real.log L ≤ (E + 1) * (2 * L ^ (1 / 2 : ℝ)) * (2 * L ^ (1 / 2 : ℝ)) := by
          gcongr
      _ = 4 * (E + 1) * (L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * (E + 1) * L := by
          rw [← Real.rpow_add hL0]
          norm_num
  have hquad : 4 * (E + 1) * L + L ≤ L ^ 2 / 2 := by
    have : 4 * (E + 1) + 1 ≤ L / 2 := by linarith
    calc 4 * (E + 1) * L + L = (4 * (E + 1) + 1) * L := by ring
      _ ≤ L / 2 * L := mul_le_mul_of_nonneg_right this hL0.le
      _ = L ^ 2 / 2 := by ring
  have h₂ : Real.exp (-(L ^ 2 / 2)) ≤ a / 2 := by
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    have : a / 2 = Real.exp (Real.log L * (-((E + 1) * n)) - Real.log 2) := by
      rw [ha, Real.rpow_def_of_pos hL0, Real.exp_sub, Real.exp_log two_pos]
    rw [this]
    exact Real.exp_le_exp.2 (by linarith)
  linarith

/-- PD §4 (the memory bound): for `K ≥ K₀`, at every real root in the box, the line average
of the root moment is at most `L^{-(E₀ + 1) N}`. -/
theorem eventually_norm_lineAverage_le {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q)
    (hq₁ : q < 1) (hC : 0 < C) (hD : 0 < Dstar) (hCX : 1 ≤ CX) (halo : 1 / 10 < alo)
    (hahi : ahi < 1 / 5) (hK : bandThreshold Dstar C ≤ K) (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
        ‖lineAverage x d fun ℓ =>
            rootMoment q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r ℓ‖ ≤
          Real.log x ^ (-((momentPrec Dstar C + 1) * (2 * momentPower x : ℕ))) := by
  have hE : 0 < momentPrec Dstar C := by
    unfold momentPrec squarePrec
    linarith
  filter_upwards [eventually_distinctSum_truncation (CX := CX) (g := g) hq hq₁ hC hD halo
      hahi hK,
    eventually_norm_distinctSum_le hq hq₁ hC hD hCX halo hahi hK hg,
    eventually_band_disjoint hg, eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) 1,
    eventually_harmonicMass_band halo.le,
    Real.tendsto_log_atTop.eventually_ge_atTop (8 * momentPrec Dstar C + 16)]
    with x htrunc hsum hdisj hbig hV hL d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁
  set L := Real.log x
  obtain ⟨hn₂, hn⟩ := two_mul_momentPower_bounds (show 0 < L by linarith)
  -- the root moment vanishes unless `e₁` is a position
  by_cases h₀ : ((1 : ℤ), (0 : ℤ)) ∈ rootPositions ((2 : ℝ) ^ k * 2 ^ j * d.Hm) d.Hn u v r
  swap
  · simp only [rootMoment, h₀, dite_false, lineAverage, sum_const_zero, mul_zero, norm_zero]
    exact Real.rpow_nonneg (by linarith) _
  -- the hypotheses of S3
  have hdisj' : ∀ i i', i ≠ i' → Disjoint (band x (d.a i)) (band x (d.a i')) := by
    intro i i' hi
    rcases lt_or_gt_of_ne hi with h | h
    · exact hdisj _ _ (hd.gap i i' h)
    · exact (hdisj _ _ (hd.gap i' i h)).symm
  have hbig' : ∀ p ∈ bandPrimes x d, 2 * momentPower x < p := by
    intro p hp
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    have hLp := hbig (d.a i) (hd.window i).1 p hpi
    rw [Real.rpow_one] at hLp
    -- `N ≤ L^{1/2} + 2 ≤ L < p`
    have hsL := (two_le_rpow_half_of_four_le (show 4 ≤ L by linarith)).2
    exact_mod_cast (show ((2 * momentPower x : ℕ) : ℝ) < p by linarith)
  have hV' : ∀ i, 0 < harmonicMass (band x (d.a i)) := fun i =>
    lt_of_lt_of_le (by norm_num) (hV (d.a i) (hd.window i).1).1
  have hR : 0 < momentPower x := by
    have : 2 ≤ 2 * momentPower x := by exact_mod_cast hn₂
    omega
  rw [lineAverage_rootMoment_eq_chain q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r hq hR hdisj'
    hbig' hV']
  -- the baseline product has norm at most `1`
  have hb : ‖∏ p ∈ bandPrimes x d, (baseline q (2 * momentPower x) p : ℂ)‖ ≤ 1 := by
    rw [norm_prod]
    refine prod_le_one₀ (fun p _ => norm_nonneg _) fun p hp => ?_
    obtain ⟨hb₀, hb₁⟩ := baseline_mem_Icc hq hq₁ (hbig' p hp)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb₀]
    exact hb₁
  -- M3 and M4–M10 bound the history sum, and the final comparison absorbs both terms
  have hS := hsum d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁
  have hT := htrunc d hd j k u v r hu₁ hu₂ hv₁ hv₂ hr₀ hr₁
  have hfin := two_mul_rpow_add_exp_le hE hL hn₂ hn
  calc ‖(∏ p ∈ bandPrimes x d, (baseline q (2 * momentPower x) p : ℂ)) *
        distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (memCap x d)
          (2 * momentPower x)‖
      ≤ 1 * ‖distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (memCap x d)
          (2 * momentPower x)‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ Real.exp (-(L ^ 2 / 2)) + 2 * L ^ (-((momentPrec Dstar C + 2) *
          (2 * momentPower x : ℕ))) := by
        rw [one_mul]
        have := norm_sub_norm_le
          (distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (memCap x d)
            (2 * momentPower x))
          (distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (truncCap x)
            (2 * momentPower x))
        linarith
    _ ≤ L ^ (-((momentPrec Dstar C + 1) * (2 * momentPower x : ℕ))) := by linarith

end Erdos408.OneSided
