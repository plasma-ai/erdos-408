import Erdos408.OneSided.Bands
import Erdos408.OneSided.Moment.Truncation.Majorant

/-!
# The memory truncation

M3 (`eventually_distinctSum_truncation` in `Moment/Memory.lean`, PD `mem:truncation-error`,
`blueprint/one_sided_type_ii.md` §13): lowering the memory cap from the number of band primes
to `B = ⌈L²⌉` changes the distinct-birth history sum by at most `exp(-L²/2)`.

* The number of band primes is eventually at least `B` (`le_memCap`), since a band of harmonic
  mass `≥ 1/2` made of primes `> L³` has at least `L³/2` primes; and it is at most
  `K exp(2 L^{1/5})` (`memCap_le`).
* `norm_distinctSum_sub_mul_le` bounds the difference by
  `2^{KN} R_G^{N+1} R_E^N ‖𝐛‖² / 2^{B+1}`. Here `R_G = exp(4K v₀/ρ)` is the doubled ghost row
  bound, `R_E = v₀^K 2^K (2|𝒫| + 4)^K · 16 (1 + 52 L^{3A₀})` is the edge row bound with the cap
  `|𝒫|` (the number of band primes), and `‖𝐛‖² ≤ 2^{KM}`.
* `log R_E = O(1 + L^{1/5})`, so the numerator is `exp(O(L))` (`log_bound_le`), far below
  `2^{L²} exp(-L²/2)`.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

/-! ### The final comparison -/

/-- The exponent comparison: for `L ≥ 16`, `0 ≤ N ≤ L^{1/2} + 2`, `M ≤ L^{1/100} + 1`,
, `B ≥ L²`, nonnegative constants and `L ≥ 6 (4K log 2 + 3c + 2a + 2b)`,
`K N log 2 + (N + 1) c + N (a + b L^{1/5}) + K M log 2 + L²/2 ≤ (B + 1) log 2`. -/
theorem log_bound_le {L N M B Kr a b c : ℝ} (hL : 16 ≤ L) (hN0 : 0 ≤ N)
    (hN : N ≤ L ^ (1 / 2 : ℝ) + 2) (hM : M ≤ L ^ (1 / 100 : ℝ) + 1)
    (hB : L ^ 2 ≤ B) (hK : 0 ≤ Kr) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hL' : 6 * (4 * Kr * Real.log 2 + 3 * c + 2 * a + 2 * b) ≤ L) :
    Kr * N * Real.log 2 + (N + 1) * c + N * (a + b * L ^ (1 / 5 : ℝ)) +
        Kr * M * Real.log 2 + L ^ 2 / 2 ≤ (B + 1) * Real.log 2 := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  set s := L ^ (1 / 2 : ℝ) with hs
  have hss : s * s = L := by
    rw [hs, ← Real.rpow_add hL0]
    norm_num
  have hs0 : 0 ≤ s := by positivity
  have hs4 : 4 ≤ s := by
    by_contra h
    push Not at h
    have : s * s < 4 * 4 := mul_lt_mul'' h h hs0 hs0
    linarith
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  -- `N ≤ 2s ≤ L`, `N L^{1/5} ≤ 2L`, `M ≤ 2L`
  have hN2 : N ≤ 2 * s := by linarith
  have hsL : 2 * s ≤ L := by nlinarith
  have hfifth : L ^ (1 / 5 : ℝ) ≤ s :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hfifth0 : 0 ≤ L ^ (1 / 5 : ℝ) := by positivity
  have hNf : N * L ^ (1 / 5 : ℝ) ≤ 2 * L :=
    calc N * L ^ (1 / 5 : ℝ) ≤ (2 * s) * s := mul_le_mul hN2 hfifth hfifth0 (by linarith)
      _ = 2 * L := by rw [mul_assoc, hss]
  have hcent : L ^ (1 / 100 : ℝ) ≤ L := by
    calc L ^ (1 / 100 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hM2 : M ≤ 2 * L := by linarith
  have hNL : N ≤ L := by linarith
  -- the linear terms are at most `(4K log 2 + 3c + 2a + 2b) L ≤ L²/6`
  have h₁ : Kr * N * Real.log 2 ≤ Kr * L * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hNL hK
    nlinarith
  have h₂ : (N + 1) * c ≤ 2 * L * c := mul_le_mul_of_nonneg_right (by linarith) hc
  have h₃ : N * (a + b * L ^ (1 / 5 : ℝ)) ≤ L * a + 2 * L * b := by
    have e₁ : N * a ≤ L * a := mul_le_mul_of_nonneg_right hNL ha
    have e₂ : N * (b * L ^ (1 / 5 : ℝ)) ≤ 2 * L * b := by
      calc N * (b * L ^ (1 / 5 : ℝ)) = b * (N * L ^ (1 / 5 : ℝ)) := by ring
        _ ≤ b * (2 * L) := mul_le_mul_of_nonneg_left hNf hb
        _ = 2 * L * b := by ring
    nlinarith
  have h₄ : Kr * M * Real.log 2 ≤ 2 * Kr * L * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hM2 hK
    nlinarith
  have h₅ : (4 * Kr * Real.log 2 + 3 * c + 2 * a + 2 * b) * L ≤ L ^ 2 / 6 := by
    have := mul_le_mul_of_nonneg_right hL' hL0.le
    nlinarith
  have h₆ : L ^ 2 * Real.log 2 ≤ B * Real.log 2 := mul_le_mul_of_nonneg_right hB (by linarith)
  have h₇ : 0.6931471803 * L ^ 2 ≤ L ^ 2 * Real.log 2 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hlog2.le (by positivity)
  have h₈ : 0 ≤ Kr * L * Real.log 2 := by positivity
  have h₉ : 0 ≤ L * c := by positivity
  have h₁₀ : 0 ≤ L * a := by positivity
  have h₁₁ : 0 ≤ L * b := by positivity
  linarith

/-! ### Band facts -/

section Facts

variable {q x : ℝ} {d : Data K} {N : ℕ}

/-- For primes `p ≥ 2N + 1`, the baseline is `b'_p ≥ 1/2`. -/
private theorem half_le_baseline' (hq : 0 < q) {p : ℕ} (hp : 2 * N + 1 ≤ p) :
    1 / 2 ≤ baseline q N p := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  have hNp : 2 * ((N : ℝ) + 1) ≤ p + 1 := by exact_mod_cast (show 2 * (N + 1) ≤ p + 1 by omega)
  have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 :=
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => by
            have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
            unfold dampDefect
            split_ifs <;> linarith
      _ = (N : ℝ) + 1 := by simp
  have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hp1]
    linarith
  unfold baseline
  linarith

/-- The harmonic mass `V(p)` of the bands containing `p` is nonnegative. -/
private theorem primeMass_nonneg₃ (p : ℕ) : 0 ≤ primeMass x d p :=
  sum_nonneg fun i _ => by
    split_ifs
    · exact sum_nonneg fun p _ => by positivity
    · exact le_rfl

/-- With band masses at least `1/2`, a prime of a band has `V(p) ≥ 1/2`. -/
private theorem half_le_primeMass₃ (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    {i : Fin K} {p : ℕ} (hp : p ∈ band x (d.a i)) : 1 / 2 ≤ primeMass x d p :=
  calc 1 / 2 ≤ harmonicMass (band x (d.a i)) := hV i
    _ = if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0 := (ite_eq_left hp).symm
    _ ≤ primeMass x d p :=
        single_le_sum (f := fun i => if p ∈ band x (d.a i) then harmonicMass (band x (d.a i))
          else 0) (fun j _ => by
            split_ifs
            · exact sum_nonneg fun p _ => by positivity
            · exact le_rfl) (mem_univ i)

/-- With baselines at least `1/2` at the band primes, every birth weight is nonnegative. -/
private theorem primeWeight_nonneg₃ (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)
    (p : ℕ) : 0 ≤ primeWeight q x d N p := by
  unfold primeWeight
  by_cases hp : p ∈ bandPrimes x d
  · have := hb p hp
    exact one_div_nonneg.2 (mul_nonneg (mul_nonneg (primeMass_nonneg₃ p) (by positivity))
      (by linarith))
  · have h0 : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_biUnion.2 ⟨i, mem_univ i, hpi⟩)
    rw [h0]
    simp

/-- At a band prime with `V(p) > 0` and `b'_p ≥ 1/2`, `V(p) ν(p) ≤ 2/p`. -/
private theorem primeMass_mul_primeWeight_le {p : ℕ} (hp0 : 0 < p) (hV : 0 < primeMass x d p)
    (hb : 1 / 2 ≤ baseline q N p) : primeMass x d p * primeWeight q x d N p ≤ 2 * (1 / p) := by
  have hp0' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hb0 : baseline q N p ≠ 0 := by linarith
  unfold primeWeight
  calc primeMass x d p * (1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p))
      = 1 / (((p : ℝ) + 1) * baseline q N p) := by field_simp
    _ ≤ 1 / (p * (1 / 2)) :=
        one_div_le_one_div_of_le (by positivity)
          (mul_le_mul (by linarith) hb (by norm_num) (by linarith))
    _ = 2 * (1 / p) := by field_simp

end Facts

/-- Eventually every band prime is at least `2N + 1` for `N = 2R`. -/
private theorem eventually_two_mul_add_one_le' {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ∀ p ∈ bandPrimes x d, 2 * (2 * momentPower x) + 1 ≤ p := by
  have hL := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop
  filter_upwards [eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) 1,
    hL.eventually_ge_atTop 8, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hbig hs8 hL0 d hd p hp
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  have hLp := hbig (d.a i) (hd.window i).1 p hpi
  rw [Real.rpow_one] at hLp
  set s := Real.log x ^ (1 / 2 : ℝ) with hs
  have hs8' : 8 ≤ s := hs8
  have hss : s * s = Real.log x := by
    rw [hs, ← Real.rpow_add hL0]
    norm_num
  have hR : (momentPower x : ℝ) < s / 2 + 1 := by
    unfold momentPower
    exact Nat.ceil_lt_add_one (by linarith)
  have h8 : 8 * s ≤ s * s := mul_le_mul_of_nonneg_right hs8' (by linarith)
  have : ((2 * (2 * momentPower x) + 1 : ℕ) : ℝ) < p := by
    push_cast
    linarith
  exact_mod_cast this.le

/-- **The number of band primes is at most `K exp(2 L^{1/5})`** for exponents at most `1/5`
and `L ≥ 1`. -/
theorem memCap_le {x : ℝ} {d : Data K} {ahi : ℝ} (hahi : ahi ≤ 1 / 5)
    (ha : ∀ i, d.a i ≤ ahi) (hL : 1 ≤ Real.log x) :
    (memCap x d : ℝ) ≤ K * Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) :=
  calc (memCap x d : ℝ) ≤ ∑ i, ((band x (d.a i)).card : ℝ) := by
        unfold memCap bandPrimes
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _i : Fin K, Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) :=
        sum_le_sum fun i _ => (card_band_le x (d.a i)).trans (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL
            ((ha i).trans hahi)) (by norm_num)))
    _ = K * Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) := by simp

/-- **The number of band primes is eventually at least `⌈L²⌉`**: a band of harmonic mass
`≥ 1/2` whose primes exceed `L³` has at least `L³/2 ≥ L² + 1` primes. -/
theorem eventually_le_memCap {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo) (hK : 1 ≤ K) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d →
      ⌈Real.log x ^ 2⌉₊ ≤ memCap x d := by
  filter_upwards [eventually_rpow_lt_of_mem_band (by linarith : 0 < alo) 3,
    eventually_harmonicMass_band halo.le, Real.tendsto_log_atTop.eventually_ge_atTop 4]
    with x hbig hV hL d hd
  set L := Real.log x with hLdef
  set i₀ : Fin K := ⟨0, hK⟩
  have hL3 : (0 : ℝ) < L ^ (3 : ℝ) := by positivity
  have hL3' : L ^ (3 : ℝ) = L ^ 3 := by exact_mod_cast Real.rpow_natCast L 3
  -- `1/2 ≤ ∑_{p ∈ 𝒫_{i₀}} 1/p ≤ |𝒫_{i₀}| / L³`
  have hcard : L ^ (3 : ℝ) / 2 ≤ (band x (d.a i₀)).card := by
    have h₁ := (hV (d.a i₀) (hd.window i₀).1).1
    have h₂ : harmonicMass (band x (d.a i₀)) ≤ (band x (d.a i₀)).card * (1 / L ^ (3 : ℝ)) := by
      unfold harmonicMass
      calc ∑ p ∈ band x (d.a i₀), (1 : ℝ) / p ≤ ∑ _p ∈ band x (d.a i₀), 1 / L ^ (3 : ℝ) :=
            sum_le_sum fun p hp =>
              one_div_le_one_div_of_le hL3 (hbig (d.a i₀) (hd.window i₀).1 p hp).le
        _ = (band x (d.a i₀)).card * (1 / L ^ (3 : ℝ)) := by
            rw [sum_const, nsmul_eq_mul]
    have h₃ : (1 : ℝ) / 2 ≤ (band x (d.a i₀)).card * (1 / L ^ (3 : ℝ)) := h₁.trans h₂
    rw [mul_one_div, le_div_iff₀ hL3] at h₃
    linarith
  have hsub : (band x (d.a i₀)).card ≤ memCap x d :=
    card_le_card fun p hp => mem_biUnion.2 ⟨i₀, mem_univ _, hp⟩
  have hceil : (⌈L ^ 2⌉₊ : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hcube : L ^ 2 + 1 ≤ L ^ (3 : ℝ) / 2 := by
    rw [hL3']
    nlinarith
  have : (⌈L ^ 2⌉₊ : ℝ) ≤ memCap x d := by
    have : ((band x (d.a i₀)).card : ℝ) ≤ memCap x d := by exact_mod_cast hsub
    linarith
  exact_mod_cast this

/-! ### The row constants -/

/-- `2^n = exp(n log 2)`. -/
private theorem two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log two_pos]

/-- **The edge row constant**: for `L ≥ 1`, `v₀ ≥ 1`, `A₀ ≥ 0` and a cap
`0 ≤ B ≤ K exp(2 L^{1/5})`,
`v₀^K 2^K (2B + 4)^K · 16 (1 + 52 L^{3A₀}) ≤ exp(a + b L^{1/5})` with
`a = K log v₀ + K log 2 + K log(2K + 4) + log 848` and `b = 2K + 15 A₀`. -/
theorem edgeRow_le_exp {L v₀ A₀ Bc : ℝ} (hL : 1 ≤ L) (hv₀ : 1 ≤ v₀) (hA₀ : 0 ≤ A₀)
    (hB0 : 0 ≤ Bc) (hB : Bc ≤ K * Real.exp (2 * L ^ (1 / 5 : ℝ))) :
    v₀ ^ K * (2 ^ K * (2 * Bc + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀)))) ≤
      Real.exp ((K * Real.log v₀ + K * Real.log 2 + K * Real.log (2 * K + 4) +
        Real.log 848) + (2 * K + 15 * A₀) * L ^ (1 / 5 : ℝ)) := by
  set e := Real.exp (2 * L ^ (1 / 5 : ℝ)) with he
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h₁ : 2 * Bc + 4 ≤ (2 * K + 4) * e := by nlinarith
  have hLp : 1 ≤ L ^ (3 * A₀) := Real.one_le_rpow hL (by positivity)
  have h₂ : 16 * (1 + 52 * L ^ (3 * A₀)) ≤ 848 * L ^ (3 * A₀) := by linarith
  have h₃ : L ^ (3 * A₀) ≤ Real.exp (15 * A₀ * L ^ (1 / 5 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    refine Real.exp_le_exp.2 ?_
    have hlog := Real.log_le_rpow_div (by linarith : 0 ≤ L) (by norm_num : (0 : ℝ) < 1 / 5)
    have : Real.log L * (3 * A₀) ≤ L ^ (1 / 5 : ℝ) / (1 / 5) * (3 * A₀) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    linarith
  have hexp : Real.exp ((K * Real.log v₀ + K * Real.log 2 + K * Real.log (2 * K + 4) +
      Real.log 848) + (2 * K + 15 * A₀) * L ^ (1 / 5 : ℝ)) =
        v₀ ^ K * (2 ^ K * ((2 * K + 4) ^ K * e ^ K) *
          (848 * Real.exp (15 * A₀ * L ^ (1 / 5 : ℝ)))) := by
    rw [show (K * Real.log v₀ + K * Real.log 2 + K * Real.log (2 * K + 4) + Real.log 848) +
        (2 * K + 15 * A₀) * L ^ (1 / 5 : ℝ) = K * Real.log v₀ + K * Real.log 2 +
          K * Real.log (2 * K + 4) + K * (2 * L ^ (1 / 5 : ℝ)) + Real.log 848 +
            15 * A₀ * L ^ (1 / 5 : ℝ) by ring]
    simp only [Real.exp_add, Real.exp_nat_mul]
    rw [Real.exp_log (by linarith), Real.exp_log two_pos, Real.exp_log (by positivity),
      Real.exp_log (by norm_num)]
    ring
  rw [hexp]
  have h₄ : (2 * Bc + 4) ^ K ≤ (2 * K + 4) ^ K * e ^ K := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h₁ K
  exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left h₄ (by positivity))
    (h₂.trans (mul_le_mul_of_nonneg_left h₃ (by norm_num))) (by positivity) (by positivity))
    (by positivity)

/-! ### The boundary vector -/

section Boundary

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The active labels of group `i` are primes of `𝒫_i`. -/
private theorem chainState_mem_band' (s : ChainState x d Y d₀ u v r B) (i : Fin K)
    (k : Fin (padCount x + 1)) : s.2.1.1 i k ∈ band x (d.a i) := by
  have h := s.2.1.2
  unfold lists at h
  exact Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 h).1 i) k

/-- The prime of a particle is a band prime. -/
private theorem particle_mem_bandPrimes' (xp : Particle x d) : xp.1.1 ∈ bandPrimes x d := by
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 xp.2
  obtain ⟨ℓ, -, hℓ⟩ := mem_image.1 hxp
  rw [← hℓ]
  exact hp

/-- The chain measure is nonnegative when the birth weights of band primes are. -/
theorem chainMeasure_nonneg' (hν : ∀ p ∈ bandPrimes x d, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) : 0 ≤ chainMeasure q x d Y d₀ u v r B N s :=
  mul_nonneg
    (prod_nonneg fun i _ => prod_nonneg fun k _ =>
      hν _ (mem_biUnion.2 ⟨i, mem_univ _, chainState_mem_band' s i k⟩))
    (memWeight_nonneg (fun xp => hν _ (particle_mem_bandPrimes' xp)) _)

/-- **The boundary mass**: if the birth weights of each band sum to at most `c`, then
`∑_s μ(s) |𝐛(s)| ≤ c^{KM}`. On the support of `𝐛` the memory is empty, and the active lists
carry at most `∏_{i,k} ∑_{p ∈ 𝒫_i} ν(p)`. -/
theorem sum_chainMeasure_norm_chainInit_le {c : ℝ}
    (hν₀ : ∀ p ∈ bandPrimes x d, 0 ≤ primeWeight q x d N p)
    (hν : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ c) :
    ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ ≤
      c ^ (K * (padCount x + 1)) := by
  -- on the support of `𝐛` the memory weight is one
  have hpt : ∀ s : ChainState x d Y d₀ u v r B,
      chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ =
        (if s.1.1 = (1, 0) then 1 else 0) *
          ((∏ i, ∏ k, primeWeight q x d N (s.2.1.1 i k)) *
            if memSize s.2.2.1 = 0 then 1 else 0) := by
    intro s
    unfold chainInit chainMeasure
    by_cases h₁ : s.1.1 = (1, 0) <;> by_cases h₂ : memSize s.2.2.1 = 0 <;> simp [h₁, h₂]
    have h0 : ∀ xp, s.2.2.1 xp = 0 := fun xp => by
      have := le_memSize s.2.2.1 xp
      omega
    simp [memWeight, h0]
  -- at most one position is `e₁`, and at most one memory is empty
  have hz : ∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
      (if z.1 = (1, 0) then (1 : ℝ) else 0) ≤ 1 := by
    have hc : #(univ.filter fun z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) =>
        z.1 = (1, 0)) ≤ 1 :=
      card_le_one.2 fun a ha b hb =>
        Subtype.ext ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)
    rw [sum_boole]
    exact_mod_cast hc
  have hS : ∑ S : MemState (Particle x d) B, (if memSize S.1 = 0 then (1 : ℝ) else 0) ≤ 1 := by
    have hc : #(univ.filter fun S : MemState (Particle x d) B => memSize S.1 = 0) ≤ 1 := by
      refine card_le_one.2 fun a ha b hb => Subtype.ext (funext fun xp => ?_)
      have ha' := le_memSize a.1 xp
      have hb' := le_memSize b.1 xp
      rw [(mem_filter.1 ha).2] at ha'
      rw [(mem_filter.1 hb).2] at hb'
      omega
    rw [sum_boole]
    exact_mod_cast hc
  -- the lists carry at most `c^{KM}`
  have hlists : ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k) ≤
      c ^ (K * (padCount x + 1)) :=
    calc ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)
        = ∑ a ∈ lists x d (padCount x), ∏ i, ∏ k, primeWeight q x d N (a i k) :=
          sum_coe_sort _ (fun a : Lists K (padCount x) => ∏ i, ∏ k, primeWeight q x d N (a i k))
      _ ≤ ∑ a ∈ Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin (padCount x + 1) =>
            band x (d.a i), ∏ i, ∏ k, primeWeight q x d N (a i k) := by
          refine sum_le_sum_of_subset_of_nonneg (by unfold lists; exact filter_subset _ _)
            fun a ha _ => prod_nonneg fun i _ => prod_nonneg fun k _ => hν₀ _ ?_
          exact mem_biUnion.2 ⟨i, mem_univ _,
            Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 ha i) k⟩
      _ = ∏ i, ∑ a ∈ Fintype.piFinset fun _ : Fin (padCount x + 1) => band x (d.a i),
            ∏ k, primeWeight q x d N (a k) :=
          (prod_univ_sum (fun i => Fintype.piFinset fun _ : Fin (padCount x + 1) =>
            band x (d.a i)) fun i a => ∏ k, primeWeight q x d N (a k)).symm
      _ = ∏ i, ∏ _k : Fin (padCount x + 1), ∑ p ∈ band x (d.a i), primeWeight q x d N p :=
          prod_congr rfl fun i _ => sum_prod_piFinset _ _
      _ ≤ ∏ _i : Fin K, ∏ _k : Fin (padCount x + 1), c :=
          prod_le_prod₀ (fun i _ => prod_nonneg fun k _ =>
              sum_nonneg fun p hp => hν₀ p (mem_biUnion.2 ⟨i, mem_univ _, hp⟩))
            fun i _ => prod_le_prod₀ (fun k _ =>
              sum_nonneg fun p hp => hν₀ p (mem_biUnion.2 ⟨i, mem_univ _, hp⟩))
              fun k _ => hν i
      _ = c ^ (K * (padCount x + 1)) := by
          rw [prod_const, prod_const, card_univ, card_univ, Fintype.card_fin, Fintype.card_fin,
            ← pow_mul, mul_comm]
  have hL : 0 ≤ ∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k) :=
    sum_nonneg fun a _ => prod_nonneg fun i _ => prod_nonneg fun k _ =>
      hν₀ _ (mem_biUnion.2 ⟨i, mem_univ _,
        Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 (mem_filter.1 a.2).1 i) k⟩)
  calc ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖
      = ∑ s : ChainState x d Y d₀ u v r B, (if s.1.1 = (1, 0) then 1 else 0) *
          ((∏ i, ∏ k, primeWeight q x d N (s.2.1.1 i k)) *
            if memSize s.2.2.1 = 0 then 1 else 0) := sum_congr rfl fun s _ => hpt s
    _ = (∑ z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r),
          (if z.1 = (1, 0) then (1 : ℝ) else 0)) *
        ((∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)) *
          ∑ S : MemState (Particle x d) B, (if memSize S.1 = 0 then (1 : ℝ) else 0)) := by
        rw [sum_mul_sum, sum_mul_sum]
        simp only [Fintype.sum_prod_type, mul_sum]
    _ ≤ 1 * ((∑ a : ↥(lists x d (padCount x)), ∏ i, ∏ k, primeWeight q x d N (a.1 i k)) * 1) := by
        gcongr
    _ ≤ c ^ (K * (padCount x + 1)) := by rw [one_mul, mul_one]; exact hlists

end Boundary

/-! ### M3 -/

/-- **M3, the truncation**: lowering the memory cap from the number of band primes to
`B = ⌈L²⌉` changes the distinct-birth history sum by at most `exp(-L²/2)`. -/
theorem eventually_norm_distinctSum_sub_le {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q)
    (hq₁ : q < 1) (hC : 0 < C) (hD : 0 < Dstar) (halo : 1 / 10 < alo) (hahi : ahi < 1 / 5)
    (hK : bandThreshold Dstar C ≤ K) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ,
        ‖distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r (memCap x d)
              (2 * momentPower x) -
            distinctSum q (arcExp Dstar C) x d (2 ^ j) (2 ^ k) u v r ⌈Real.log x ^ 2⌉₊
              (2 * momentPower x)‖ ≤
          Real.exp (-(Real.log x ^ 2 / 2)) := by
  set A₀ := arcExp Dstar C with hA₀def
  have hK1 : 1 ≤ K := (one_le_bandThreshold hD hC).trans hK
  have hA₀ : 0 ≤ A₀ := by
    rw [hA₀def]
    unfold arcExp edgePrec momentPrec squarePrec
    linarith
  have hv₀ : 1 ≤ truncV q := one_le_truncV hq hq₁
  have hρ0 : 0 < pendingWeight q := Real.rpow_pos_of_pos hq _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  set cG := truncV q * (4 * K / pendingWeight q) with hcG
  set a := K * Real.log (truncV q) + K * Real.log 2 + K * Real.log (2 * K + 4) +
    Real.log 848 with ha
  set b := 2 * (K : ℝ) + 15 * A₀ with hb
  have hcG0 : 0 ≤ cG := by positivity
  have ha0 : 0 ≤ a := by
    have h₁ := Real.log_nonneg hv₀
    have h₃ : 0 ≤ Real.log (2 * K + 4) := Real.log_nonneg (by linarith)
    have h₄ : 0 ≤ Real.log 848 := Real.log_nonneg (by norm_num)
    positivity
  have hb0 : 0 ≤ b := by positivity
  filter_upwards [eventually_le_memCap halo hK1, eventually_harmonicMass_band halo.le,
    eventually_two_mul_add_one_le' halo,
    Real.tendsto_log_atTop.eventually_ge_atTop
      (max 16 (6 * (4 * (2 * (K : ℝ)) * Real.log 2 + 3 * cG + 2 * a + 2 * b))),
    eventually_gt_atTop 0] with x hcap hV hbig hL hx d hd j k u v r
  set L := Real.log x with hLdef
  set N := 2 * momentPower x with hN
  set B := ⌈L ^ 2⌉₊ with hB
  set M := padCount x + 1 with hM
  have hL16 : 16 ≤ L := le_of_max_le_left hL
  have hL' : 6 * (4 * (2 * (K : ℝ)) * Real.log 2 + 3 * cG + 2 * a + 2 * b) ≤ L :=
    le_of_max_le_right hL
  have hL0 : 0 < L := by linarith
  -- the band facts
  have hV₀ : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hV _ (hd.window i).1).1
  have hV₁ : ∀ i, harmonicMass (band x (d.a i)) ≤ 1 := fun i => (hV _ (hd.window i).1).2
  have hbase : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p :=
    fun p hp => half_le_baseline' hq (hbig d hd p hp)
  have hν : ∀ p, 0 ≤ primeWeight q x d N p := primeWeight_nonneg₃ hbase
  have hVp : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p :=
    fun i p hp => half_le_primeMass₃ hV₀ hp
  have hVν : ∀ p ∈ bandPrimes x d, primeMass x d p * primeWeight q x d N p ≤ 2 * (1 / p) := by
    intro p hp
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    exact primeMass_mul_primeWeight_le (TypeII.band_prime hpi).pos
      (by linarith [hVp i p hpi]) (hbase p hp)
  have hν4 : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4 := by
    intro i
    calc ∑ p ∈ band x (d.a i), primeWeight q x d N p
        ≤ ∑ p ∈ band x (d.a i), 4 * (1 / (p : ℝ)) := by
          refine sum_le_sum fun p hp => ?_
          have h₁ := hVν p (mem_biUnion.2 ⟨i, mem_univ i, hp⟩)
          have h₂ : 1 / 2 * primeWeight q x d N p ≤ primeMass x d p * primeWeight q x d N p :=
            mul_le_mul_of_nonneg_right (hVp i p hp) (hν p)
          linarith
      _ = 4 * harmonicMass (band x (d.a i)) := (mul_sum _ _ _).symm
      _ ≤ 4 := by linarith [hV₁ i]
  have hd₀ : (0 : ℝ) < 2 ^ k := by positivity
  have hY : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have hU : 0 < (2 : ℝ) ^ k * 2 ^ j * d.Hm :=
    mul_pos (by positivity) (lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) hd.Hm_ge)
  -- the majorant
  set R := (2 : ℝ) ^ K * (2 * (memCap x d : ℝ) + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀)))
    with hR
  have hR0 : 0 ≤ R := by positivity
  have hmain := norm_distinctSum_sub_mul_le (q := q) (A₀ := A₀) (x := x) (d := d) (Y := 2 ^ j)
    (d₀ := 2 ^ k) (u := u) (v := v) (r := r) (B := B) (B' := memCap x d) (N := N) (hcap d hd)
    hv₀ (Real.exp_pos cG).le (by positivity : 0 ≤ truncV q ^ K * R)
    (fun s => chainMeasure_nonneg' (fun p _ => hν p) s)
    (fun j t => sum_dblGhostCoef_le hq hq₁ hν hVν hV₁ j t)
    (fun t => sum_chainEdgeCoef_weight_le hv₀ t
      (sum_norm_chainEdgeCoef_le hq hq₁ hd₀ hY hU hL0 hν hν4 hVp t))
  have hbdry := sum_chainMeasure_norm_chainInit_le (q := q) (x := x) (d := d) (Y := 2 ^ j)
    (d₀ := 2 ^ k) (u := u) (v := v) (r := r) (B := memCap x d) (N := N) (c := 4)
    (fun p _ => hν p) hν4
  -- the constants
  have hedge : truncV q ^ K * R ≤ Real.exp (a + b * L ^ (1 / 5 : ℝ)) :=
    edgeRow_le_exp (by linarith) hv₀ hA₀ (Nat.cast_nonneg _)
      (memCap_le hahi.le (fun i => (hd.window i).2) (by linarith))
  have hNr : (N : ℝ) ≤ L ^ (1 / 2 : ℝ) + 2 := by
    have hpos : 0 ≤ L ^ (1 / 2 : ℝ) / 2 := by positivity
    have h₂ : (momentPower x : ℝ) < L ^ (1 / 2 : ℝ) / 2 + 1 := Nat.ceil_lt_add_one hpos
    rw [hN]
    push_cast
    linarith
  have hMr : (M : ℝ) ≤ L ^ (1 / 100 : ℝ) + 1 := by
    rw [hM]
    push_cast
    have : (padCount x : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
    linarith
  have hBr : L ^ 2 ≤ (B : ℝ) := Nat.le_ceil _
  set E := (2 * (K : ℝ)) * N * Real.log 2 + (N + 1) * cG + N * (a + b * L ^ (1 / 5 : ℝ)) +
    (2 * (K : ℝ)) * M * Real.log 2 with hE
  have hfin : E + L ^ 2 / 2 ≤ (B + 1) * Real.log 2 :=
    log_bound_le hL16 (Nat.cast_nonneg _) hNr hMr hBr (by positivity) ha0 hb0 hcG0 hL'
  -- the product is at most `exp(E)`
  have hT : (2 : ℝ) ^ (K * N) * Real.exp cG ^ (N + 1) * (truncV q ^ K * R) ^ N * 4 ^ (K * M) ≤
      Real.exp E := by
    have e₁ : (2 : ℝ) ^ (K * N) ≤ Real.exp ((2 * (K : ℝ)) * N * Real.log 2) := by
      rw [two_pow_eq_exp]
      refine Real.exp_le_exp.2 ?_
      push_cast
      have : 0 ≤ (K : ℝ) * N * Real.log 2 := by positivity
      linarith
    have e₂ : Real.exp cG ^ (N + 1) = Real.exp ((N + 1) * cG) := by
      rw [← Real.exp_nat_mul]
      push_cast
      rfl
    have e₃ : (truncV q ^ K * R) ^ N ≤ Real.exp (N * (a + b * L ^ (1 / 5 : ℝ))) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) hedge N
    have e₄ : (4 : ℝ) ^ (K * M) = Real.exp ((2 * (K : ℝ)) * M * Real.log 2) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, two_pow_eq_exp]
      push_cast
      ring_nf
    rw [hE, Real.exp_add, Real.exp_add, Real.exp_add, e₂, e₄]
    gcongr
  -- divide by `2^{B + 1}`
  have h2B : (0 : ℝ) < 2 ^ (B + 1) := by positivity
  have hexp : Real.exp E ≤ 2 ^ (B + 1) * Real.exp (-(L ^ 2 / 2)) := by
    rw [two_pow_eq_exp, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    push_cast
    linarith
  have hcoef : 0 ≤ (2 : ℝ) ^ (K * N) * Real.exp cG ^ (N + 1) * (truncV q ^ K * R) ^ N := by
    positivity
  refine le_of_mul_le_mul_right ?_ h2B
  calc _ ≤ (2 : ℝ) ^ (K * N) * Real.exp cG ^ (N + 1) * (truncV q ^ K * R) ^ N *
        ∑ s, chainMeasure q x d (2 ^ j) (2 ^ k) u v r (memCap x d) N s *
          ‖chainInit x d (2 ^ j) (2 ^ k) u v r (memCap x d) s‖ := hmain
    _ ≤ (2 : ℝ) ^ (K * N) * Real.exp cG ^ (N + 1) * (truncV q ^ K * R) ^ N * 4 ^ (K * M) :=
        mul_le_mul_of_nonneg_left hbdry hcoef
    _ ≤ Real.exp E := hT
    _ ≤ 2 ^ (B + 1) * Real.exp (-(L ^ 2 / 2)) := hexp
    _ = Real.exp (-(L ^ 2 / 2)) * 2 ^ (B + 1) := mul_comm _ _

end Erdos408.OneSided
