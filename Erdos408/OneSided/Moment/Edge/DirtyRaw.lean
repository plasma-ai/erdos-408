import Erdos408.OneSided.Moment.Edge.RawCol

/-!
# The dirty raw edges

M7 of `blueprint/one_sided_type_ii.md` §16 (PD §4 "Dirty raw edges: the two Schur sides",
`mem:raw-dirty-norm`): for `K ≥ K₀` and `B ≤ L³`, each dirty raw part of the edge has norm at
most `L^{-G-1}` (`eventually_edgeRaw_normLe` in `Moment/Edge.lean`).

* `rawCoef`: the coefficient `w(s, c) [t - b + a = 0]` of the raw part, with the edge amplitude
  `w` of `edgeAmp`; `norm_rawCoef_le` bounds it by `rawAmp`.
* `normLe_rawChoiceOp`: the weighted Schur test with weight one. The row of the piece `(S, I)` is
  at most `16 · 2^K` if `I = ∅` and `ε` otherwise (`RawRow.lean`); the column is at most `2^K`
  times the row of `(I, S)` (`RawCol.lean`). So a dirty piece has norm at most
  `√(2^K · 16 · 2^K · ε)`.
* `eventually_rawChoiceOp_normLe`: with `ε = C_K (B/M^K + B^K e^{-L^{0.1}/4})`, `M ≥ L^{0.01}`,
  `B ≤ L³` and `K ≥ 200(G + 3)`, `√(C_K ε) ≤ L^{-G-1}` eventually.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset Real

variable {K : ℕ}

section Coef

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

variable (q N) in
open scoped Classical in
/-- The coefficient of the raw part of an edge piece: the edge amplitude
`M!^{-2K} ρ^{hits} ρ^{hits'} ∏_i w_i (d₀/D) η(b/Y) η(a/Y) ψ(t/Y)` of an admissible choice
times the raw kernel `[t - b + a = 0]`. -/
def rawCoef (s : ChainState x d Y d₀ u v r B) (c : EdgeChoice x d Y d₀ u v r) : ℂ :=
  ((if EdgeValid x d Y d₀ u v r B s c then
      ((((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
        pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * rawWeight q N s c *
        (d₀ / edgePad s c) * dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
        dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) *
        plateau ((edgeDet s c / edgePad s c : ℤ) / Y))
    else 0 : ℝ) : ℂ) *
    if edgeDet s c / edgePad s c - (∏ i, edgeSrc s c i (Fin.last _) : ℕ) +
        (∏ i, (c.2.2.2.1 i).1 : ℕ) = 0 then 1 else 0

/-- `|η| ≤ 1`. -/
private theorem abs_dyadicBump_le' (y : ℝ) : |dyadicBump y| ≤ 1 := by
  unfold dyadicBump
  have h₁ := smoothTransition.nonneg (y - 1)
  have h₂ := smoothTransition.le_one (y - 1)
  have h₃ := smoothTransition.nonneg (y / 2 - 1)
  have h₄ := smoothTransition.le_one (y / 2 - 1)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **The raw coefficient bound**: `|w [t - b + a = 0]| ≤ rawAmp`. With `D ∣ det`, the raw kernel
is the raw determinant equation, and the factors `d₀/D`, `η`, `η`, `ψ` have modulus at most
one. -/
theorem norm_rawCoef_le (hq : 0 < q) (hd₀ : 0 < d₀)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (s : ChainState x d Y d₀ u v r B) {c : EdgeChoice x d Y d₀ u v r}
    (hc : c ∈ edgeChoices x d Y d₀ u v r) : ‖rawCoef q N s c‖ ≤ rawAmp q N s c := by
  classical
  have h0 := rawAmp_nonneg hq hdisj hV hν s hc
  unfold rawCoef
  by_cases hv : EdgeValid x d Y d₀ u v r B s c
  · by_cases hsh : edgeDet s c / edgePad s c - (∏ i, edgeSrc s c i (Fin.last _) : ℕ) +
        (∏ i, (c.2.2.2.1 i).1 : ℕ) = 0
    · -- the raw determinant equation holds
      have hdet : RawDet s c := by
        unfold RawDet
        rw [← Int.mul_ediv_cancel' hv.2.2.2.2.1]
        linear_combination (edgePad s c : ℤ) * hsh
      unfold rawAmp
      rw [ite_eq_left hv, ite_eq_left hsh, ite_eq_left ⟨hv, hdet⟩, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      set w := (((padCount x + 1).factorial ^ K : ℕ) : ℝ)⁻¹ ^ 2 *
        pendingWeight q ^ pendingHits x d s.1.1 s.2.2.1 *
        pendingWeight q ^ pendingHits x d c.2.2.1.1 (edgeMem s c) * rawWeight q N s c with hw
      have hw0 : 0 ≤ w := by
        unfold rawAmp at h0
        rwa [ite_eq_left ⟨hv, hdet⟩] at h0
      have hD : 0 < (edgePad s c : ℝ) := hd₀.trans_le hv.2.2.1
      have hk : |d₀ / edgePad s c * dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
          dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) *
          plateau ((edgeDet s c / edgePad s c : ℤ) / Y)| ≤ 1 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (div_pos hd₀ hD),
          abs_of_nonneg (show 0 ≤ plateau ((edgeDet s c / edgePad s c : ℤ) / Y) from
            smoothTransition.nonneg _)]
        have h₁ : d₀ / edgePad s c ≤ 1 := (div_le_one hD).2 hv.2.2.1
        have h₂ := abs_dyadicBump_le' ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y)
        have h₃ := abs_dyadicBump_le' ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y)
        have h₄ := smoothTransition.le_one (5 - |((edgeDet s c / edgePad s c : ℤ) : ℝ) / Y|)
        have h₅ : 0 ≤ d₀ / edgePad s c := (div_pos hd₀ hD).le
        calc d₀ / ↑(edgePad s c) * |dyadicBump _| * |dyadicBump _| * plateau _
            ≤ 1 * 1 * 1 * 1 := by
              gcongr <;> first | exact h₄ | exact smoothTransition.nonneg _
          _ = 1 := by ring
      calc |w * (d₀ / edgePad s c) * dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
            dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) *
            plateau ((edgeDet s c / edgePad s c : ℤ) / Y)|
          = w * |d₀ / edgePad s c * dyadicBump ((∏ i, edgeSrc s c i (Fin.last _) : ℕ) / Y) *
              dyadicBump ((∏ i, (c.2.2.2.1 i).1 : ℕ) / Y) *
              plateau ((edgeDet s c / edgePad s c : ℤ) / Y)| := by
            rw [← abs_of_nonneg hw0, ← abs_mul, abs_of_nonneg hw0]
            ring_nf
        _ ≤ w * 1 := mul_le_mul_of_nonneg_left hk hw0
        _ = w := mul_one w
    · rw [ite_eq_right hsh, mul_zero, norm_zero]
      exact h0
  · rw [ite_eq_right hv, Complex.ofReal_zero, zero_mul, norm_zero]
    exact h0

end Coef

section Schur

variable {q x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- The small row `ε = 16 (4 C_ρ)^K B / M^K + 16 (2B + 1)^K 2^K e^{-L^{0.1}/4}` of the dirty raw
pieces (PD `mem:epsilon`). -/
def rawEps (q x : ℝ) (B : ℕ) : ℝ :=
  16 * (4 * dampConst q) ^ K * B / ((padCount x + 1 : ℕ) : ℝ) ^ K +
    16 * (2 * B + 1) ^ K * (2 ^ K * Real.exp (-Real.log x ^ (1 / 10 : ℝ) / 4))

/-- The small row is nonnegative. -/
theorem rawEps_nonneg (hq : 0 < q) (hq₁ : q < 1) (x : ℝ) (B : ℕ) : 0 ≤ rawEps (K := K) q x B := by
  have := one_le_dampConst hq hq₁
  unfold rawEps
  positivity

/-- **The rows of the dirty raw pieces**: `16 · 2^K` without promotions, and `ε` with
promotions. -/
theorem sum_rawAmp_le_rowBound (hq : 0 < q) (hq₁ : q < 1) (hU : 0 < d₀ * Y * d.Hm) (hu : 0 < u)
    (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (ha : ∀ i, 1 / 10 ≤ d.a i)
    (hL : 1 ≤ Real.log x) (s : ChainState x d Y d₀ u v r B) (S I : Finset (Fin K)) :
    ∑ c ∈ rawChoices x d Y d₀ u v r S I, rawAmp q N s c ≤
      if I = ∅ then 16 * 2 ^ K else rawEps (K := K) q x B := by
  split_ifs with hI
  · subst hI
    exact sum_rawAmp_le_of_empty hq hq₁ hU hdisj hV hb s S
  · have hIn := nonempty_iff_ne_empty.2 hI
    refine (sum_rawAmp_le_of_nonempty hq hq₁ hU hu hdisj hV hb s S hIn).trans ?_
    unfold rawEps
    gcongr
    exact ha _

/-- **The dirty raw pieces for fixed data** (PD `mem:raw-dirty-norm`): the weighted Schur test
with weight one. The row of `(S, I)` and the column (`2^K` times the row of `(I, S)`) are
`16 · 2^K` and `ε` according as the promoted and the stored set are empty; one of them is
nonempty, so the norm is at most `√(2^K · 16 · 2^K · ε)` once `ε ≤ 16 · 2^K`. -/
theorem normLe_rawChoiceOp (hq : 0 < q) (hq₁ : q < 1) (hd₀ : 0 < d₀) (hU : 0 < d₀ * Y * d.Hm)
    (hu : 0 < u) (hdisj : ∀ i j, i ≠ j → Disjoint (band x (d.a i)) (band x (d.a j)))
    (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1)
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) (ha : ∀ i, 1 / 10 ≤ d.a i)
    (hL : 1 ≤ Real.log x) (hε : rawEps (K := K) q x B ≤ 16 * 2 ^ K) {S I : Finset (Fin K)}
    (hSI : (S, I) ≠ (∅, ∅)) :
    NormLe (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (fun s => chainMeasure q x d Y d₀ u v r B N s)
      (choiceOp (rawChoices x d Y d₀ u v r S I) (rawCoef q N) (chainEdgeOut x d Y d₀ u v r B))
      (Real.sqrt (2 ^ K * (16 * 2 ^ K) * rawEps (K := K) q x B)) := by
  classical
  have hV' : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hV i).1
  have hν := primeWeight_nonneg_of hV' hb (q := q) (N := N)
  have hμ0 : ∀ t : ChainState x d Y d₀ u v r B, 0 ≤ chainMeasure q x d Y d₀ u v r B N t :=
    fun t => mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  have hε0 := rawEps_nonneg (K := K) hq hq₁ x B
  set ρB : Finset (Fin K) → ℝ := fun J => if J = ∅ then 16 * 2 ^ K else rawEps (K := K) q x B
    with hρB
  have hρB0 : ∀ J, 0 ≤ ρB J := fun J => by
    simp only [hρB]
    split_ifs
    · positivity
    · exact hε0
  have hρBle : ∀ J, ρB J ≤ 16 * 2 ^ K := fun J => by
    simp only [hρB]
    split_ifs
    · exact le_rfl
    · exact hε
  have hrowB := fun s J T => sum_rawAmp_le_rowBound (N := N) (B := B) hq hq₁ hU hu hdisj hV' hb
    ha hL (Y := Y) (d₀ := d₀) (v := v) (r := r) s T J
  have hnorm := normLe_choiceOp (cs := rawChoices x d Y d₀ u v r S I) (a := rawCoef q N)
    (out := chainEdgeOut x d Y d₀ u v r B)
    (μ := fun s => chainMeasure q x d Y d₀ u v r B N s)
    (ν := fun s => chainMeasure q x d Y d₀ u v r B N s) (h := fun _ => 1) (h' := fun _ => 1)
    (R := ρB I) (C := 2 ^ K * ρB S) (hρB0 I) (by have := hρB0 S; positivity) hμ0
    (fun _ => zero_lt_one) (fun s => ?_) (fun s' => ?_)
  · refine fun f => (hnorm f).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt ?_) 2)
      (sum_nonneg fun t _ => mul_nonneg (hμ0 t) (sq_nonneg _)))
    -- one of the two sides is small
    by_cases hI : I = ∅
    · have hS : S ≠ ∅ := fun hS => hSI (by rw [hS, hI])
      simp only [hρB, hI, hS, ↓reduceIte]
      exact le_of_eq (by ring)
    · have h₁ : ρB I = rawEps (K := K) q x B := by simp only [hρB, hI, ↓reduceIte]
      rw [h₁]
      have h2 : (0 : ℝ) < 2 ^ K := by positivity
      have h3 := mul_le_mul_of_nonneg_left (hρBle S) (mul_nonneg hε0 h2.le)
      calc rawEps (K := K) q x B * (2 ^ K * ρB S) = rawEps (K := K) q x B * 2 ^ K * ρB S := by
            ring
        _ ≤ rawEps (K := K) q x B * 2 ^ K * (16 * 2 ^ K) := h3
        _ = _ := by ring
  · -- the row
    rw [mul_one]
    refine (sum_le_sum fun c hc => ?_).trans ((hrowB s I S).trans (le_of_eq ?_))
    · rw [mul_one]
      exact norm_rawCoef_le hq hd₀ hdisj hV' hν s (mem_filter.1 hc).1
    · simp only [hρB]
  · -- the column, by reversal
    rw [mul_one]
    calc ∑ s, ∑ c ∈ rawChoices x d Y d₀ u v r S I with chainEdgeOut x d Y d₀ u v r B s c = s',
          chainMeasure q x d Y d₀ u v r B N s * ‖rawCoef q N s c‖ * 1
        ≤ ∑ s, ∑ c ∈ (rawChoices x d Y d₀ u v r S I).filter
            (fun c => chainEdgeOut x d Y d₀ u v r B s c = s'),
            chainMeasure q x d Y d₀ u v r B N s * rawAmp q N s c := by
          refine sum_le_sum fun s _ => sum_le_sum fun c hc => ?_
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (norm_rawCoef_le hq hd₀ hdisj hV' hν s
            (mem_filter.1 (mem_filter.1 hc).1).1) (hμ0 s)
      _ ≤ 2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' *
            ∑ c' ∈ rawChoices x d Y d₀ u v r I S, rawAmp q N s' c') :=
          sum_col_rawAmp_le hq hdisj hV hb S I s'
      _ ≤ 2 ^ K * (chainMeasure q x d Y d₀ u v r B N s' * ρB S) := by
          gcongr
          · exact hμ0 s'
          · exact hrowB s' S I
      _ = 2 ^ K * ρB S * chainMeasure q x d Y d₀ u v r B N s' := by ring

end Schur

/-! ### Asymptotics -/

/-- The damping defects are in `[0, 1]`. -/
private theorem dampDefect_mem_Icc' {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) (N j : ℕ) :
    0 ≤ dampDefect q N j ∧ dampDefect q N j ≤ 1 := by
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
  unfold dampDefect
  split_ifs <;> constructor <;> linarith [Real.sqrt_nonneg q]

/-- For primes `p ≥ 2N + 1`, the baseline is `b'_p ≥ 1/2`: each of the `N + 1` defects is at
most `1`, and `p + 1 ≥ 2(N + 1)`. -/
private theorem half_le_baseline' {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {N p : ℕ}
    (hp : 2 * N + 1 ≤ p) : 1 / 2 ≤ baseline q N p := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  have hNp : 2 * ((N : ℝ) + 1) ≤ p + 1 := by exact_mod_cast (show 2 * (N + 1) ≤ p + 1 by omega)
  have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 :=
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (dampDefect_mem_Icc' hq hq₁ N j).2
      _ = (N : ℝ) + 1 := by simp
  have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hp1]
    linarith
  unfold baseline
  linarith

/-- Eventually every band prime is at least `2N + 1` for `N = 2R`: band primes exceed `L`, and
`2N + 1 ≤ 2 L^{1/2} + 5 ≤ L`. -/
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

/-- **The small row is small** (PD `mem:raw-dirty-norm`): for `K ≥ 200 (G + 3)`, eventually
every `B ≤ L³` has `2^K · 16 · 2^K · ε ≤ (L^{-G-1})²` and `ε ≤ 16 · 2^K`. Here
`B/M^K ≤ L³/L^{K/100} ≤ L^{-2G-3}`, as `M ≥ L^{0.01}`, and `B^K e^{-L^{0.1}/4}` decays faster
than every power of `L`. -/
theorem eventually_rawEps_small {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) {G : ℝ} (hG : 0 < G)
    (hK : 200 * (G + 3) ≤ (K : ℝ)) :
    ∀ᶠ x : ℝ in atTop, ∀ B : ℕ, (B : ℝ) ≤ Real.log x ^ 3 →
      2 ^ K * (16 * 2 ^ K) * rawEps (K := K) q x B ≤ (Real.log x ^ (-(G + 1))) ^ 2 ∧
        rawEps (K := K) q x B ≤ 16 * 2 ^ K := by
  have hdC := one_le_dampConst hq hq₁
  set κ : ℝ := 2 ^ K * (16 * 2 ^ K) with hκ
  have hκ1 : 1 ≤ κ := by
    rw [hκ]
    have : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    nlinarith
  set c₁ : ℝ := κ * 16 * (4 * dampConst q) ^ K with hc₁
  set c₂ : ℝ := κ * 16 * 3 ^ K * 2 ^ K with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  -- the exponential factor beats every power of `L`
  set A : ℝ := 3 * K + 2 * G + 2 with hA
  have hexp := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * A) (1 / 4)
    (by norm_num)).comp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop)).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * c₂) by
        positivity))
  filter_upwards [hexp, Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (2 * c₁))]
    with x hx hLc B hB
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := le_of_max_le_left hLc
  have hLc₁ : 2 * c₁ ≤ L := le_of_max_le_right hLc
  have hL0 : 0 < L := by linarith
  -- `L^{10 A / 10} e^{-L^{0.1}/4} < 1/(2 c₂)`
  have hx' : L ^ A * Real.exp (-(L ^ (1 / 10 : ℝ)) / 4) < 1 / (2 * c₂) := by
    have h := hx
    simp only [Function.comp] at h
    rw [← Real.rpow_mul hL0.le, show 1 / 10 * (10 * A) = A by ring,
      show -(1 / 4 : ℝ) * L ^ (1 / 10 : ℝ) = -(L ^ (1 / 10 : ℝ)) / 4 by ring] at h
    exact h
  -- `M^K ≥ L^{2G + 6}`
  have hM : L ^ (2 * G + 6) ≤ ((padCount x + 1 : ℕ) : ℝ) ^ K := by
    have hM₁ : L ^ (1 / 100 : ℝ) ≤ ((padCount x + 1 : ℕ) : ℝ) := by
      unfold padCount
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc L ^ (2 * G + 6) ≤ L ^ ((K : ℝ) / 100) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = (L ^ (1 / 100 : ℝ)) ^ K := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
          ring_nf
      _ ≤ ((padCount x + 1 : ℕ) : ℝ) ^ K :=
          pow_le_pow_left₀ (Real.rpow_nonneg hL0.le _) hM₁ K
  have hMpos : 0 < ((padCount x + 1 : ℕ) : ℝ) ^ K := by positivity
  have hpow : ∀ a b : ℝ, L ^ a * L ^ b = L ^ (a + b) := fun a b => (Real.rpow_add hL0 a b).symm
  have hL3 : L ^ 3 = L ^ (3 : ℝ) := (Real.rpow_natCast L 3).symm
  have hsq : (L ^ (-(G + 1))) ^ 2 = L ^ (-(2 * G + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    ring_nf
  -- the first term: `κ · 16 (4 C_ρ)^K B / M^K ≤ L^{-2G-2}/2`
  have ht₁ : κ * (16 * (4 * dampConst q) ^ K * B / ((padCount x + 1 : ℕ) : ℝ) ^ K) ≤
      L ^ (-(2 * G + 2)) / 2 := by
    have hBM : (B : ℝ) / ((padCount x + 1 : ℕ) : ℝ) ^ K ≤ L ^ (-(2 * G + 3)) := by
      rw [div_le_iff₀ hMpos]
      calc (B : ℝ) ≤ L ^ (3 : ℝ) := hL3 ▸ hB
        _ = L ^ (-(2 * G + 3)) * L ^ (2 * G + 6) := by rw [hpow]; ring_nf
        _ ≤ L ^ (-(2 * G + 3)) * ((padCount x + 1 : ℕ) : ℝ) ^ K :=
            mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg hL0.le _)
    calc κ * (16 * (4 * dampConst q) ^ K * B / ((padCount x + 1 : ℕ) : ℝ) ^ K)
        = c₁ * ((B : ℝ) / ((padCount x + 1 : ℕ) : ℝ) ^ K) := by rw [hc₁]; ring
      _ ≤ c₁ * L ^ (-(2 * G + 3)) := mul_le_mul_of_nonneg_left hBM (by positivity)
      _ = c₁ * L ^ (-(1 : ℝ)) * L ^ (-(2 * G + 2)) := by
          rw [mul_assoc c₁ (L ^ (-(1 : ℝ))), hpow]
          ring_nf
      _ ≤ 1 / 2 * L ^ (-(2 * G + 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
          rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_le_iff₀ hL0]
          linarith
      _ = L ^ (-(2 * G + 2)) / 2 := by ring
  -- the second term: `κ · 16 (2B + 1)^K 2^K e^{-L^{0.1}/4} ≤ L^{-2G-2}/2`
  have ht₂ : κ * (16 * (2 * B + 1) ^ K * (2 ^ K * Real.exp (-L ^ (1 / 10 : ℝ) / 4))) ≤
      L ^ (-(2 * G + 2)) / 2 := by
    have h2B : 2 * (B : ℝ) + 1 ≤ 3 * L ^ 3 := by
      have : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
      linarith
    have hLK : (3 * L ^ 3) ^ K = 3 ^ K * L ^ (3 * (K : ℝ)) := by
      rw [mul_pow, ← pow_mul, ← Real.rpow_natCast L (3 * K)]
      push_cast
      ring_nf
    have hE := Real.exp_pos (-L ^ (1 / 10 : ℝ) / 4)
    calc κ * (16 * (2 * B + 1) ^ K * (2 ^ K * Real.exp (-L ^ (1 / 10 : ℝ) / 4)))
        ≤ κ * (16 * (3 * L ^ 3) ^ K * (2 ^ K * Real.exp (-L ^ (1 / 10 : ℝ) / 4))) := by
          gcongr
      _ = c₂ * (L ^ A * Real.exp (-(L ^ (1 / 10 : ℝ)) / 4)) * L ^ (-(2 * G + 2)) := by
          have hLA : L ^ A * L ^ (-(2 * G + 2)) = L ^ (3 * (K : ℝ)) := by
            rw [hpow, hA]
            ring_nf
          rw [show c₂ * (L ^ A * Real.exp (-(L ^ (1 / 10 : ℝ)) / 4)) * L ^ (-(2 * G + 2)) =
            c₂ * Real.exp (-(L ^ (1 / 10 : ℝ)) / 4) * (L ^ A * L ^ (-(2 * G + 2))) by ring,
            hLA, hLK, hc₂, neg_div]
          ring
      _ ≤ c₂ * (1 / (2 * c₂)) * L ^ (-(2 * G + 2)) := by gcongr
      _ = L ^ (-(2 * G + 2)) / 2 := by field_simp
  have hmain : κ * rawEps (K := K) q x B ≤ (L ^ (-(G + 1))) ^ 2 := by
    rw [hsq, rawEps, mul_add]
    linarith
  refine ⟨hmain, ?_⟩
  -- `κ ε ≤ L^{-2G-2} ≤ 1` and `κ ≥ 1`
  have h1 : (L ^ (-(G + 1))) ^ 2 ≤ 1 :=
    pow_le_one₀ (Real.rpow_nonneg hL0.le _) (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith))
  have hε0 := rawEps_nonneg (K := K) hq hq₁ x B
  have : rawEps (K := K) q x B ≤ 1 := by nlinarith
  have : (1 : ℝ) ≤ 16 * 2 ^ K := by
    have : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    linarith
  linarith

/-- **M7 for the raw coefficients**: for `K ≥ K₀` and `B ≤ L³`, every dirty raw piece has norm
at most `L^{-G-1}` for the chain measure, uniformly in the root box. -/
theorem eventually_rawChoiceOp_normLe {q C CX alo ahi Dstar g : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hC : 0 < C) (hD : 0 < Dstar) (halo : 1 / 10 < alo) (hK : bandThreshold Dstar C ≤ K)
    (hg : 0 < g) :
    ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ, ∀ u v r : ℝ,
      (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
      ∀ S I : Finset (Fin K), (S, I) ≠ (∅, ∅) →
        NormLe (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (fun s => chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s)
          (choiceOp (rawChoices x d (2 ^ j) (2 ^ k) u v r S I) (rawCoef q N)
            (chainEdgeOut x d (2 ^ j) (2 ^ k) u v r B))
          (Real.log x ^ (-(edgePrec Dstar C + 1))) := by
  set G := edgePrec Dstar C with hGdef
  have hG : 0 < G := by
    rw [hGdef]
    unfold edgePrec momentPrec squarePrec
    linarith
  have hK' : 200 * (G + 3) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hK)
  filter_upwards [eventually_rawEps_small (K := K) hq hq₁ hG hK',
    eventually_band_disjoint hg, eventually_harmonicMass_band halo.le,
    eventually_two_mul_add_one_le' (C := C) (CX := CX) (ahi := ahi) (g := g) halo,
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop 0]
    with x hsmall hdisjx hVx hbig hL1 hx0 d hd j k u v r hu B N hB hN S I hSI
  subst hN
  obtain ⟨hκε, hε⟩ := hsmall B hB
  -- the band facts at `x`
  have hdisj : ∀ i i', i ≠ i' → Disjoint (band x (d.a i)) (band x (d.a i')) := by
    intro i i' hii
    rcases lt_or_gt_of_ne hii with h | h
    · exact hdisjx _ _ (hd.gap i i' h)
    · exact (hdisjx _ _ (hd.gap i' i h)).symm
  have hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) ∧ harmonicMass (band x (d.a i)) ≤ 1 :=
    fun i => hVx _ (hd.window i).1
  have hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q (2 * momentPower x) p :=
    fun p hp => half_le_baseline' hq hq₁ (hbig d hd p hp)
  have ha : ∀ i, 1 / 10 ≤ d.a i := fun i => halo.le.trans (hd.window i).1
  have hHm : 0 < d.Hm := (Real.rpow_pos_of_pos hx0 _).trans_le hd.Hm_ge
  have hU : 0 < (2 : ℝ) ^ k * 2 ^ j * d.Hm := by positivity
  have hnorm := normLe_rawChoiceOp (N := 2 * momentPower x) (v := v) (r := r) hq hq₁
    (by positivity : (0 : ℝ) < 2 ^ k) hU (hU.trans_le hu) hdisj hV hb ha hL1 hε hSI
  have hL0 : 0 < Real.log x := by linarith
  refine fun f => (hnorm f).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ 2)
    (sum_nonneg fun t _ => mul_nonneg ?_ (sq_nonneg _)))
  · rw [← Real.sqrt_sq (Real.rpow_nonneg hL0.le (-(G + 1)))]
    exact Real.sqrt_le_sqrt hκε
  · have hν := primeWeight_nonneg_of (fun i => (hV i).1) hb (q := q)
    exact mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)

end Erdos408.OneSided
