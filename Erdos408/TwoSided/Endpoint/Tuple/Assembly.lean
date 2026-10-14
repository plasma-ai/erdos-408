import Erdos408.TwoSided.Endpoint.Tuple.Split

/-!
# The tuple part at high times, for a general coefficient

S13–S18 of `blueprint/two_sided_correlation.md` §§6.3–6.6 (PD §§6.5–6.6) for the tuple sum
`𝒰_tup(w) = ψ₁(w/Y) w^{iσ} V⁻¹ ∑_{p_s p_l u = w} c(u)` with any small primes `p_s`, any
spare primes `p_l ∈ (A, B]`, `x^ε ≤ A`, `B ≤ x^{1-ε}`, and any coefficient `|c| ≤ L^{C_U}`.

* `twistedPoly_eq_sum_boxTerm`: the twisted polynomial is `∑_m c_χ(h, αβ) J_m(t)` over the
  boxes, classes and characters `m` (E6).
* `integral_boxTerm_le`: the mean square of one `J_m` is
  `≤ L^{K₁} (E₁ L^{K₁} + E₂ K_A L^{-A_t})`: separation, then the energy of the average with
  the box bounds `E₁` (S15–S18) for `|ξ| ≤ L^{C_sep}` and `E₂` (trivial) beyond.
* `tupleBound_le`: after Cauchy–Schwarz over the `≤ 64 L^{3C_m + 3}` indices, the choice of
  `A_s`, `A'` and `A_t`.

The assembly `exists_integral_tupleSum_high_le` is in `Tuple/General.lean`.
-/

namespace Erdos408.TwoSided.TupleHigh

open Filter Finset MeasureTheory

/-- Triple sums of a product condition are sums over the filtered sets. -/
theorem sum_ite_and_three (s sp U : Finset ℕ) (A B C : ℕ → Prop) [DecidablePred A]
    [DecidablePred B] [DecidablePred C] (f : ℕ → ℕ → ℕ → ℂ) :
    ∑ ps ∈ s, ∑ pl ∈ sp, ∑ u ∈ U, (if (A ps ∧ B pl ∧ C u) then f ps pl u else 0) =
      ∑ ps ∈ s.filter A, ∑ pl ∈ sp.filter B, ∑ u ∈ U.filter C, f ps pl u := by
  rw [sum_filter]
  refine sum_congr rfl fun ps _ => ?_
  by_cases hA : A ps
  · rw [ite_eq_left hA, sum_filter]
    refine sum_congr rfl fun pl _ => ?_
    by_cases hB : B pl
    · rw [ite_eq_left hB, sum_filter]
      refine sum_congr rfl fun u _ => ?_
      by_cases hC : C u
      · rw [ite_eq_left ⟨hA, hB, hC⟩, ite_eq_left hC]
      · rw [ite_eq_right fun h => hC h.2.2, ite_eq_right hC]
    · rw [ite_eq_right hB]
      exact sum_eq_zero fun u _ => ite_eq_right fun h => hB h.2.1
  · rw [ite_eq_right hA]
    exact sum_eq_zero fun pl _ => sum_eq_zero fun u _ => ite_eq_right fun h => hA h.1

/-- The term `J_m(t) = (YV)⁻¹ ∑_{(p_s, p_l, u) ∈ m} χ(p_l) ψ₁(p_s p_l u/Y) c_u
(p_s p_l u)^{i(t + σ)}` of one box, pair of classes and character `m`. -/
noncomputable def boxTerm (Y V : ℝ) (s sp : Finset ℕ) {k : ℕ} (cf : ℕ → ℂ) (ψ₁ : ℝ → ℂ)
    (σ : ℝ) (m : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × DirichletCharacter ℂ k)) (t : ℝ) : ℂ :=
  (((Y * V)⁻¹ : ℝ) : ℂ) *
    ∑ ps ∈ s.filter (fun p => boxIndex p = m.1.1.1 ∧ p % k = m.2.1.1),
      ∑ pl ∈ sp.filter (fun p => boxIndex p = m.1.1.2),
        ∑ u ∈ (Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = m.1.2 ∧ u % k = m.2.1.2),
          m.2.2 pl * (ψ₁ ((ps * pl * u : ℕ) / Y) *
            (cf u * ((ps * pl * u : ℕ) : ℂ) ^ (((t + σ : ℝ) : ℂ) * Complex.I)))

/-- `J_m` is continuous when the sets avoid `0`. -/
theorem continuous_boxTerm {Y V : ℝ} {s sp : Finset ℕ} (hs : ∀ p ∈ s, 0 < p)
    (hsp : ∀ p ∈ sp, 0 < p) {k : ℕ} (cf : ℕ → ℂ) (ψ₁ : ℝ → ℂ) (σ : ℝ)
    (m : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × DirichletCharacter ℂ k)) :
    Continuous (boxTerm Y V s sp cf ψ₁ σ m) := by
  unfold boxTerm
  refine continuous_const.mul (continuous_finsetSum _ fun ps hps => continuous_finsetSum _
    fun pl hpl => continuous_finsetSum _ fun u hu => continuous_const.mul
      (continuous_const.mul (continuous_const.mul ?_)))
  have hn : ps * pl * u ≠ 0 := by
    have h₁ := hs ps (mem_filter.1 hps).1
    have h₂ := hsp pl (mem_filter.1 hpl).1
    have h₃ : 1 < u := (mem_Ioc.1 (mem_filter.1 hu).1).1
    positivity
  simp_rw [OneSided.natCast_cpow_mul_I hn]
  fun_prop

/-- **E6 (boxes, classes and characters).** For `p_s p_l < Y`, spare primes coprime to `k`
and all variables in the boxes below `N₀`: the twisted polynomial of the tuple sum is
`∑_m c_χ(h, αβ) J_m(t)`. -/
theorem twistedPoly_eq_sum_boxTerm {Y V : ℝ} (hY : 0 < Y) (s sp : Finset ℕ)
    (hs : ∀ p ∈ s, 0 < p) (hsp : ∀ p ∈ sp, 0 < p)
    (hsmall : ∀ ps ∈ s, ∀ pl ∈ sp, ((ps * pl : ℕ) : ℝ) < Y) (ψ₁ : ℝ → ℂ)
    (hψ : ∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) (cf : ℕ → ℂ) (σ : ℝ) {k : ℕ} (hk : 1 ≤ k) (h : ℤ)
    {N₀ : ℕ} (hN₀s : ∀ p ∈ s, boxIndex p < N₀) (hN₀sp : ∀ p ∈ sp, boxIndex p < N₀)
    (hN₀U : ∀ u ∈ Ioc 1 ⌊2 * Y⌋₊, boxIndex u < N₀) (hcop : ∀ p ∈ sp, Nat.Coprime p k)
    (t : ℝ) :
    twistedPoly Y (fun w => ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * ((V⁻¹ : ℝ) : ℂ) *
        ∑ ps ∈ s.filter (· ∣ w), ∑ pl ∈ sp.filter (· ∣ w / ps), cf (w / ps / pl)) h k t =
      ∑ m ∈ boxSet N₀ k, Erdos821.P5Marked.cchi k h m.2.2 (m.2.1.1 * m.2.1.2) *
        boxTerm Y V s sp cf ψ₁ σ m t := by
  set F : ℕ → ℂ := fun w => (w : ℂ) ^ ((σ : ℂ) * Complex.I) *
    Complex.exp (2 * Real.pi * Complex.I * (h * w / k : ℝ)) * (w : ℂ) ^ ((t : ℂ) * Complex.I)
  have h₁ : twistedPoly Y (fun w => ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) *
      ((V⁻¹ : ℝ) : ℂ) * ∑ ps ∈ s.filter (· ∣ w), ∑ pl ∈ sp.filter (· ∣ w / ps),
        cf (w / ps / pl)) h k t =
      (((Y * V)⁻¹ : ℝ) : ℂ) * ∑ w ∈ Icc ⌈Y⌉₊ ⌊2 * Y⌋₊, ψ₁ (w / Y) * F w *
        ∑ ps ∈ s.filter (· ∣ w), ∑ pl ∈ sp.filter (· ∣ w / ps), cf (w / ps / pl) := by
    rw [twistedPoly, mul_sum, mul_sum]
    refine sum_congr rfl fun w _ => ?_
    simp only [F]
    push_cast
    ring
  rw [h₁, twistedSum_eq s sp hs hsp hsmall ψ₁ hψ F cf hY]
  -- the phase by boxes, classes and characters
  have h₂ : ∀ ps ∈ s, ∀ pl ∈ sp, ∀ u ∈ Ioc 1 ⌊2 * Y⌋₊,
      ψ₁ ((ps * pl * u : ℕ) / Y) * F (ps * pl * u) * cf u =
        (ψ₁ ((ps * pl * u : ℕ) / Y) *
          (cf u * ((ps * pl * u : ℕ) : ℂ) ^ (((t + σ : ℝ) : ℂ) * Complex.I))) *
        ∑ m ∈ boxSet N₀ k, (if InBox m ps pl u then
          Erdos821.P5Marked.cchi k h m.2.2 (m.2.1.1 * m.2.1.2) * m.2.2 pl else 0) := by
    intro ps hps pl hpl u hu
    rw [← phase_eq_sum_boxSet hk h (hN₀s ps hps) (hN₀sp pl hpl) (hN₀U u hu) (hcop pl hpl)]
    have hn : ((ps * pl * u : ℕ) : ℂ) ≠ 0 := by
      have h₃ : 1 < u := (mem_Ioc.1 hu).1
      have : ps * pl * u ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero (hs ps hps).ne'
        (hsp pl hpl).ne') (by omega)
      exact_mod_cast this
    simp only [F, Erdos821.Blueprint.Analytic.e]
    rw [show ((t + σ : ℝ) : ℂ) * Complex.I = (σ : ℂ) * Complex.I + (t : ℂ) * Complex.I by
      push_cast; ring, Complex.cpow_add _ _ hn]
    push_cast
    ring_nf
  rw [sum_congr rfl fun ps hps => sum_congr rfl fun pl hpl => sum_congr rfl fun u hu =>
    h₂ ps hps pl hpl u hu, tripleSum_eq_sum_boxSet, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [boxTerm, ← sum_ite_and_three]
  unfold InBox
  ring

/-- The spare primes of the box `(2^j, 2^{j+1}]` form the interval `(max(2^j, A), min(2^{j+1}, B)]`
of primes. -/
theorem spareBox_eq {A B : ℝ} (hB : 0 ≤ B) (j : ℕ) :
    ((Iic ⌊B⌋₊).filter fun p : ℕ => p.Prime ∧ A < p).filter (fun p => boxIndex p = j) =
      (Ioc ⌊max ((2 : ℝ) ^ j) A⌋₊ ⌊min (2 * (2 : ℝ) ^ j) B⌋₊).filter Nat.Prime := by
  ext p
  simp only [mem_filter, mem_Iic, mem_Ioc]
  constructor
  · rintro ⟨⟨hpB, hp, hAp⟩, hj⟩
    obtain ⟨h₁, h₂⟩ := (boxIndex_eq_iff hp.two_le).1 hj
    refine ⟨⟨(Nat.floor_lt (by positivity)).2 (max_lt (by exact_mod_cast h₁) hAp),
      Nat.le_floor (le_min (by rw [pow_succ] at h₂; exact_mod_cast (by linarith : p ≤ 2 * 2 ^ j))
        ?_)⟩, hp⟩
    · exact (Nat.le_floor_iff hB).1 hpB
  · rintro ⟨⟨h₁, h₂⟩, hp⟩
    have h₁' := (Nat.floor_lt (by positivity)).1 h₁
    have h₂' := (Nat.le_floor_iff (le_min (by positivity) hB)).1 h₂
    refine ⟨⟨Nat.le_floor (h₂'.trans (min_le_right _ _)), hp, lt_of_le_of_lt (le_max_right _ _)
      h₁'⟩, (boxIndex_eq_iff hp.two_le).2 ⟨?_, ?_⟩⟩
    · exact_mod_cast lt_of_le_of_lt (le_max_left _ _) h₁'
    · have : (p : ℝ) ≤ 2 * 2 ^ j := h₂'.trans (min_le_left _ _)
      rw [pow_succ]
      exact_mod_cast (by linarith : (p : ℝ) ≤ 2 ^ j * 2)

/-- The growth facts of the tuple part at `x`, with `x^ε = exp(c L / T²⁰)`. -/
structure TupleFacts (c Cm x : ℝ) : Prop where
  box : BoxScales Cm x
  m47 : 8 * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤
    Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20)
  m22 : 8 * Real.exp (Real.log x / Real.log (Real.log x) ^ 22) ≤
    Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20)
  m36 : 2 * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤
    Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20)
  mCm : 2 * Real.log x ^ Cm ≤ Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20)
  big : 28 ≤ Real.log x

/-- The growth facts hold eventually. -/
theorem eventually_tupleFacts {c : ℝ} (hc : 0 < c) (Cm : ℝ) :
    ∀ᶠ x : ℝ in atTop, TupleFacts c Cm x := by
  filter_upwards [eventually_boxScales Cm,
    eventually_mul_exp_rpow_le_margin (by norm_num : (0 : ℝ) ≤ 0.47) (by norm_num) hc 8,
    eventually_mul_exp_div_le_margin hc 8,
    eventually_mul_exp_rpow_le_margin (by norm_num : (0 : ℝ) ≤ 0.36) (by norm_num) hc 2,
    eventually_mul_rpow_mul_exp_le_exp (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 0.5) Cm 2,
    eventually_mul_exp_rpow_le_margin (by norm_num : (0 : ℝ) ≤ 0.5) (by norm_num) hc 1,
    Real.tendsto_log_atTop.eventually_ge_atTop 28]
    with x hbox h47 h22 h36 hk₁ hk₂ hL
  refine ⟨hbox, h47, h22, h36, ?_, hL⟩
  rw [Real.rpow_zero] at hk₁
  have : 2 * Real.log x ^ Cm ≤ 2 * Real.log x ^ Cm * Real.exp 1 :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by norm_num))
  linarith

/-- `|G| ≤ (#s_P (PV)⁻¹) (P/Y) (#s_N ∑_u |c_u|)`. -/
theorem norm_boxPoly_le {Y P V : ℝ} (hY : 0 < Y) (hP : 0 < P) (hV : 0 < V)
    {sP spN uR : Finset ℕ} (hsP : ∀ n ∈ sP, 0 < n) (hspN : ∀ n ∈ spN, 0 < n)
    (huR : ∀ n ∈ uR, 0 < n) {k : ℕ} (χ : DirichletCharacter ℂ k) (c : ℕ → ℂ) (τ : ℝ) :
    ‖boxPoly Y P V sP spN uR χ c τ‖ ≤
      (#sP * (P * V)⁻¹) * (P / Y * (#spN * ∑ u ∈ uR, ‖c u‖)) := by
  rw [boxPoly, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  have h₁ : ‖∑ p ∈ sP, (((P * V)⁻¹ : ℝ) : ℂ) * (p : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤
      #sP * (P * V)⁻¹ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [norm_mul, norm_natCast_cpow_ofReal_mul_I (hsP p hp), Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    simp
  have h₂ : ‖∑ p ∈ spN, χ p * (p : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤ #spN := by
    refine (norm_sum_le _ _).trans ?_
    rw [card_eq_sum_ones, Nat.cast_sum]
    refine sum_le_sum fun p hp => ?_
    rw [norm_mul, norm_natCast_cpow_ofReal_mul_I (hspN p hp), mul_one, Nat.cast_one]
    exact DirichletCharacter.norm_le_one χ _
  have h₃ : ‖∑ u ∈ uR, c u * (u : ℂ) ^ ((τ : ℂ) * Complex.I)‖ ≤ ∑ u ∈ uR, ‖c u‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun u hu => ?_))
    rw [norm_mul, norm_natCast_cpow_ofReal_mul_I (huR u hu), mul_one]
  gcongr

/-- `⌊2^l⌋ = 2^l` and `⌊2 · 2^l⌋ = 2^{l+1}`. -/
theorem floor_two_pow (l : ℕ) :
    ⌊(2 : ℝ) ^ l⌋₊ = 2 ^ l ∧ ⌊2 * (2 : ℝ) ^ l⌋₊ = 2 ^ (l + 1) := by
  constructor
  · exact_mod_cast Nat.floor_natCast (2 ^ l)
  · rw [pow_succ, mul_comm]
    exact_mod_cast Nat.floor_natCast (2 ^ l * 2)

/-- **The data of a relevant box.** If some `(p_s, p_l, u)` of the box
`(2^i, 2^{i+1}] × (2^j, 2^{j+1}] × (2^l, 2^{l+1}]` has `p_s p_l u ∈ [Y, 2Y]`, the scales
`P = 2^i`, `N = 2^j`, `R = 2^l` satisfy `BoxData`, with `(lo, hi] = (max(N, A), min(2N, B)]`. -/
theorem boxData_of_mem {x c Cm CU vlo : ℝ} (hc : 0 < c) (hf : TupleFacts c Cm x)
    {s : Finset ℕ} {V A B Y : ℝ} {cf : ℕ → ℂ} {k : ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hV : vlo ≤ V) (hA : Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20) ≤ A)
    (hB : B ≤ x * Real.exp (-(c * Real.log x / Real.log (Real.log x) ^ 20)))
    (hcf : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ 2 → ‖cf u‖ ≤ Real.log x ^ CU)
    (hY₁ : x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y)
    (hY₂ : Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)))
    (hk₁ : 1 ≤ k) (hk₂ : (k : ℝ) ≤ Real.log x ^ Cm) {i j l α β ps pl u : ℕ}
    (hps : ps ∈ s.filter (fun p => boxIndex p = i ∧ p % k = α))
    (hpl : pl ∈ ((Iic ⌊B⌋₊).filter fun p : ℕ => p.Prime ∧ A < p).filter
      (fun p => boxIndex p = j))
    (hu : u ∈ (Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = l ∧ u % k = β))
    (hn₁ : Y ≤ ((ps * pl * u : ℕ) : ℝ)) (hn₂ : ((ps * pl * u : ℕ) : ℝ) ≤ 2 * Y) :
    BoxData x Cm CU vlo Y (2 ^ i) (2 ^ j) (2 ^ l) V (max (2 ^ j) A) (min (2 * 2 ^ j) B)
      (s.filter (fun p => boxIndex p = i ∧ p % k = α))
      ((Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = l ∧ u % k = β)) k cf := by
  have hL : 28 ≤ Real.log x := hf.big
  have hx0 : 0 < x := by linarith [hf.box.2.1]
  set e := Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20) with he
  have he0 : 0 < e := Real.exp_pos _
  have hBx : B ≤ x / e := by
    rw [div_eq_mul_inv, he, ← Real.exp_neg]
    exact hB
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  -- the variables in their boxes
  obtain ⟨hps₁, hps₂⟩ := mem_filter.1 hps
  obtain ⟨hpsP, hpsl, hpsu⟩ := hs ps hps₁
  obtain ⟨hpsi₁, hpsi₂⟩ := (boxIndex_eq_iff hpsP.two_le).1 hps₂.1
  obtain ⟨hpl₁, hpl₂⟩ := mem_filter.1 hpl
  obtain ⟨hplB, hplP, hplA⟩ := mem_filter.1 hpl₁
  obtain ⟨hplj₁, hplj₂⟩ := (boxIndex_eq_iff hplP.two_le).1 hpl₂
  obtain ⟨hu₁, hu₂⟩ := mem_filter.1 hu
  have hu2 : 2 ≤ u := (mem_Ioc.1 hu₁).1
  obtain ⟨hul₁, hul₂⟩ := (boxIndex_eq_iff hu2).1 hu₂.1
  have hBpl : (pl : ℝ) ≤ B := (Nat.le_floor_iff (by
    by_contra h
    push Not at h
    rw [Nat.floor_of_nonpos h.le] at hplB
    have := hplP.two_le
    simp_all)).1 (mem_Iic.1 hplB)
  -- real versions
  have rps₁ : (2 : ℝ) ^ i < ps := by exact_mod_cast hpsi₁
  have rps₂ : (ps : ℝ) ≤ 2 * 2 ^ i := by rw [pow_succ] at hpsi₂; exact_mod_cast (by omega)
  have rpl₁ : (2 : ℝ) ^ j < pl := by exact_mod_cast hplj₁
  have rpl₂ : (pl : ℝ) ≤ 2 * 2 ^ j := by rw [pow_succ] at hplj₂; exact_mod_cast (by omega)
  have ru₁ : (2 : ℝ) ^ l < u := by exact_mod_cast hul₁
  have ru₂ : (u : ℝ) ≤ 2 * 2 ^ l := by rw [pow_succ] at hul₂; exact_mod_cast (by omega)
  have hn : ((ps * pl * u : ℕ) : ℝ) = ps * pl * u := by push_cast; ring
  rw [hn] at hn₁ hn₂
  have hP0 : (0 : ℝ) < 2 ^ i := by positivity
  have hN0 : (0 : ℝ) < 2 ^ j := by positivity
  have hR0 : (0 : ℝ) < 2 ^ l := by positivity
  have h27 : 1 ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) := Real.one_le_exp (by positivity)
  have hP1 : (1 : ℝ) ≤ 2 * 2 ^ i := by
    have : (2 : ℝ) ≤ ps := by exact_mod_cast hpsP.two_le
    linarith
  -- `PNR < p_s p_l u ≤ 2Y` and `Y ≤ 8PNR`
  have hPNR : (2 : ℝ) ^ i * 2 ^ j * 2 ^ l ≤ 2 * Y := by
    have : (2 : ℝ) ^ i * 2 ^ j * 2 ^ l ≤ ps * pl * u := by gcongr
    linarith
  have hY8 : Y ≤ 8 * (2 ^ i * 2 ^ j * 2 ^ l) := by
    have : (ps : ℝ) * pl * u ≤ (2 * 2 ^ i) * (2 * 2 ^ j) * (2 * 2 ^ l) := by gcongr
    linarith
  -- `N ≥ e/2`
  have hNe : e / 2 ≤ 2 ^ j := by linarith
  have hYx : Y ≤ x ^ 2 / 16 := by
    have h := hf.box.2.2.2.1
    have : x * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ x * (x / 16) :=
      mul_le_mul_of_nonneg_left (by linarith) hx0.le
    nlinarith
  refine ⟨hY₁, hY₂, by linarith, by linarith, ?_, ?_, le_max_left _ _, min_le_left _ _, ?_, ?_,
    hPNR, hV, hk₁, hk₂, ?_, ?_, ?_⟩
  · -- `N ≥ exp(L/T²²)`
    linarith [hf.m22, Real.exp_pos (Real.log x / Real.log (Real.log x) ^ 22)]
  · -- `N ≤ x`
    have : x / e ≤ x := div_le_self hx0.le (by rw [he]; exact Real.one_le_exp (by positivity))
    linarith
  · -- `R ≥ e/8 ≥ exp(L/T²²)`: `x e^{L^{0.38}} ≤ Y ≤ 8 P N R ≤ 8 e^{L^{0.36}} (x/e) R`
    have hPe : (2 : ℝ) ^ i ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) := by linarith
    have hNx : (2 : ℝ) ^ j ≤ x / e := by linarith
    have h3638 : Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Real.exp (Real.log x ^ (0.38 : ℝ)) :=
      Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
    have h₁ : x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤
        8 * (Real.exp (Real.log x ^ (0.36 : ℝ)) * (x / e) * 2 ^ l) := by
      calc x * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ x * Real.exp (Real.log x ^ (0.38 : ℝ)) :=
            mul_le_mul_of_nonneg_left h3638 hx0.le
        _ ≤ 8 * (2 ^ i * 2 ^ j * 2 ^ l) := hY₁.trans hY8
        _ ≤ 8 * (Real.exp (Real.log x ^ (0.36 : ℝ)) * (x / e) * 2 ^ l) := by gcongr
    have h₂ : e ≤ 8 * 2 ^ l := by
      have hpos : 0 < x * Real.exp (Real.log x ^ (0.36 : ℝ)) := by positivity
      have : x * Real.exp (Real.log x ^ (0.36 : ℝ)) * e ≤
          x * Real.exp (Real.log x ^ (0.36 : ℝ)) * (8 * 2 ^ l) := by
        have := mul_le_mul_of_nonneg_right h₁ he0.le
        field_simp at this ⊢
        linarith
      exact le_of_mul_le_mul_left this hpos
    linarith [hf.m22, Real.exp_pos (Real.log x / Real.log (Real.log x) ^ 22)]
  · -- `R ≤ x`: `P N R ≤ 2Y`, `P ≥ 1/2`, `N ≥ e/2`, `Y ≤ x e^{L^{0.47}}`, `8 e^{L^{0.47}} ≤ e`
    have h₁ : (2 : ℝ) ^ l * (e / 4) ≤ 2 * Y := by
      calc (2 : ℝ) ^ l * (e / 4) = (1 / 2) * (e / 2) * 2 ^ l := by ring
        _ ≤ 2 ^ i * 2 ^ j * 2 ^ l := by
            gcongr
            linarith
        _ ≤ 2 * Y := hPNR
    have h₂ : 2 * Y ≤ 2 * x * Real.exp (Real.log x ^ (0.47 : ℝ)) := by linarith
    have h₃ : 8 * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ e := hf.m47
    have h₄ : (2 : ℝ) ^ l * e ≤ 8 * x * Real.exp (Real.log x ^ (0.47 : ℝ)) := by linarith
    have h₅ : 8 * x * Real.exp (Real.log x ^ (0.47 : ℝ)) ≤ x * e := by nlinarith
    exact le_of_mul_le_mul_right (by linarith) he0
  · intro p hp
    obtain ⟨hp₁, hp₂⟩ := mem_filter.1 hp
    have hpP := (hs p hp₁).1
    obtain ⟨h₁, h₂⟩ := (boxIndex_eq_iff hpP.two_le).1 hp₂.1
    refine ⟨hpP, by exact_mod_cast h₁, ?_⟩
    rw [pow_succ] at h₂
    exact_mod_cast (by omega : p ≤ 2 * 2 ^ i)
  · intro v hv
    obtain ⟨hv₁, hv₂⟩ := mem_filter.1 hv
    have hv2 : 2 ≤ v := (mem_Ioc.1 hv₁).1
    obtain ⟨h₁, h₂⟩ := (boxIndex_eq_iff hv2).1 hv₂.1
    rw [(floor_two_pow l).1, (floor_two_pow l).2, mem_Ioc]
    exact ⟨h₁, h₂⟩
  · intro v hv
    obtain ⟨hv₁, -⟩ := mem_filter.1 hv
    obtain ⟨hv₁, hv₂⟩ := mem_Ioc.1 hv₁
    refine hcf v hv₁.le ?_
    have : (v : ℝ) ≤ 2 * Y := (Nat.cast_le.2 hv₂).trans (Nat.floor_le (by linarith))
    have : 0 ≤ x ^ 2 := by positivity
    linarith

/-- The conclusion of `eventually_integral_boxPoly_le_of_twist` at `x`. -/
def BoxTwistBound (x Cm CU vlo As : ℝ) : Prop :=
  ∀ (Y P N R V lo hi : ℝ) (sP uR : Finset ℕ) (k : ℕ) (χ : DirichletCharacter ℂ k)
    (c : ℕ → ℂ), BoxData x Cm CU vlo Y P N R V lo hi sP uR k c →
    ∀ A' E κ' : ℝ, PrimeTwistBound x A' E Cm κ' → IntegerKernelBound x Cm κ' →
    ∀ τ₁ τ₂ : ℝ, τ₁ ≤ τ₂ →
      (∀ τ ∈ Set.Icc τ₁ τ₂, Real.log x ^ E ≤ |τ| ∧
        |τ| + 2 ≤ 2 * (x * Real.log x ^ (Cm + 2))) →
      ∫ τ in τ₁..τ₂, ‖boxPoly Y P V sP ((Ioc ⌊lo⌋₊ ⌊hi⌋₊).filter Nat.Prime) uR χ c τ‖ ^ 2 ≤
        Real.log x ^ (-(2 * As)) * Real.log x ^ (2 * CU + 5) +
          (2 / vlo) ^ 2 * 4 * (4 * κ' * Real.log x ^ (-A')) ^ 2 *
            (9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4))

/-- `BoxTwistBound` holds eventually (`eventually_integral_boxPoly_le_of_twist`). -/
theorem eventually_boxTwistBound (Cm CU vlo As : ℝ) (hvlo : 0 < vlo) (hCm : 0 ≤ Cm)
    (hAs : 0 < As) : ∀ᶠ x : ℝ in atTop, BoxTwistBound x Cm CU vlo As :=
  eventually_integral_boxPoly_le_of_twist Cm CU vlo As hvlo hCm hAs

/-- `|Y^{is}| = 1` for `Y > 0`. -/
theorem norm_ofReal_cpow_mul_I {Y : ℝ} (hY : 0 < Y) (s : ℝ) :
    ‖(Y : ℂ) ^ ((s : ℂ) * Complex.I)‖ = 1 := by
  rw [ofReal_cpow_mul_I hY, Complex.norm_exp_ofReal_mul_I]

/-- **The energy of a separated term.** If `J(t) = ∫ a(ξ) Y^{-2πiξ} G(t + σ + 2πξ) dξ` with
`G` continuous and bounded, the mean squares of `G` over the shifted intervals are `≤ E₁` for
`|ξ| ≤ L^{C_sep}` and `≤ E₂` always, `∫ |a| ≤ L^K` and the tail of `a` is `≤ K_A L^{-A_t}`,
then `∫ |J|² ≤ L^K (E₁ L^K + E₂ K_A L^{-A_t})`. -/
theorem integral_sq_le_of_separated {L K KA At Cf E₁ E₂ Mb Y σ t₁ t₂ : ℝ} {a : ℝ → ℂ}
    (hai : Integrable a) (ha₁ : (∫ ξ, ‖a ξ‖) ≤ L ^ K)
    (hat : (∫ ξ in {ξ : ℝ | L ^ Cf < |ξ|}, ‖a ξ‖) ≤ KA * L ^ (-At)) {G : ℝ → ℂ}
    (hGc : Continuous G) (hMb : ∀ τ, ‖G τ‖ ≤ Mb) (hY : 0 < Y) {J : ℝ → ℂ}
    (hJ : ∀ t, J t = ∫ ξ, a ξ * (Y : ℂ) ^ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I) *
      G (t + σ + 2 * Real.pi * ξ)) (h₁₂ : t₁ ≤ t₂) (hE₁0 : 0 ≤ E₁) (hE₂0 : 0 ≤ E₂)
    (hE₁ : ∀ ξ : ℝ, |ξ| ≤ L ^ Cf →
      ∫ τ in t₁ + (σ + 2 * Real.pi * ξ)..t₂ + (σ + 2 * Real.pi * ξ), ‖G τ‖ ^ 2 ≤ E₁)
    (hE₂ : ∀ ξ : ℝ,
      ∫ τ in t₁ + (σ + 2 * Real.pi * ξ)..t₂ + (σ + 2 * Real.pi * ξ), ‖G τ‖ ^ 2 ≤ E₂) :
    ∫ t in t₁..t₂, ‖J t‖ ^ 2 ≤ L ^ K * (E₁ * L ^ K + E₂ * (KA * L ^ (-At))) := by
  have hh : Continuous (Function.uncurry fun ξ τ => ‖G (τ + (σ + 2 * Real.pi * ξ))‖) := by
    have : Continuous fun p : ℝ × ℝ => p.2 + (σ + 2 * Real.pi * p.1) := by fun_prop
    exact (hGc.comp this).norm
  have hen := integral_sq_le_of_le_integral_split (c := 1) (M := Mb) (R := L ^ Cf)
    (h := fun ξ τ => ‖G (τ + (σ + 2 * Real.pi * ξ))‖) h₁₂ hai.norm (fun ξ => norm_nonneg _)
    hh (fun _ _ => norm_nonneg _) (fun ξ τ => hMb _) hE₁0 (E₂ := E₂)
    (fun ξ hξ => by
      rw [intervalIntegral.integral_comp_add_right (fun τ => ‖G τ‖ ^ 2)]
      exact hE₁ ξ hξ)
    (fun ξ => by
      rw [intervalIntegral.integral_comp_add_right (fun τ => ‖G τ‖ ^ 2)]
      exact hE₂ ξ)
    (F := fun t => ‖J t‖) (fun _ => norm_nonneg _) (fun t => by
      rw [hJ, one_mul]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Filter.Eventually.of_forall fun ξ => ?_)))
      dsimp only
      rw [norm_mul, norm_mul, norm_ofReal_cpow_mul_I hY, mul_one, add_assoc])
  refine hen.trans ?_
  have hW0 : 0 ≤ ∫ ξ, ‖a ξ‖ := integral_nonneg fun ξ => norm_nonneg _
  have htail0 : 0 ≤ ∫ ξ in {ξ : ℝ | L ^ Cf < |ξ|}, ‖a ξ‖ :=
    setIntegral_nonneg (measurableSet_lt measurable_const continuous_abs.measurable)
      fun ξ _ => norm_nonneg _
  rw [one_pow, one_mul]
  gcongr
  exact hW0.trans ha₁

/-- Separation of one term: `J_m(t) = ∫ a(ξ) Y^{-2πiξ} G(t + σ + 2πξ) dξ`. -/
theorem boxTerm_eq_integral {a : ℝ → ℂ} (hai : Integrable a) {ψ₁ : ℝ → ℂ}
    (harep : ∀ y : ℝ, 0 < y →
      ψ₁ y = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))
    {Y V : ℝ} (hY : 0 < Y) (s sp spN : Finset ℕ) {k : ℕ} (cf : ℕ → ℂ) (σ : ℝ)
    (i j l α β : ℕ) (χ : DirichletCharacter ℂ k)
    (hsp : sp.filter (fun p => boxIndex p = j) = spN)
    (hsm : ∀ n ∈ s.filter (fun p => boxIndex p = i ∧ p % k = α), 0 < n)
    (hspN : ∀ n ∈ spN, 0 < n)
    (hUm : ∀ n ∈ (Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = l ∧ u % k = β), 0 < n)
    (t : ℝ) :
    boxTerm Y V s sp cf ψ₁ σ (((i, j), l), ((α, β), χ)) t =
      ∫ ξ, a ξ * (Y : ℂ) ^ (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * Complex.I) *
        boxPoly Y (2 ^ i) V (s.filter (fun p => boxIndex p = i ∧ p % k = α)) spN
          ((Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = l ∧ u % k = β)) χ cf
          (t + σ + 2 * Real.pi * ξ) := by
  unfold boxTerm
  rw [hsp]
  exact boxSum_eq_integral hai harep hY (by positivity) hsm hspN hUm χ cf σ t

/-- **The mean square of one term.** For a relevant box, separation and the energy of the
average, with the bound `E₁` (S15–S18) on `|ξ| ≤ L^{C_sep}` and the trivial bound `E₂`
beyond; for an irrelevant one `J_m = 0`. -/
theorem integral_boxTerm_le {x c Cm Cf CU vlo As K KA At : ℝ} (hc : 0 < c) (hvlo : 0 < vlo)
    (hCm : 0 ≤ Cm) (hf : TupleFacts c Cm x) (hB2 : BoxTwistBound x Cm CU vlo As)
    {A' E κ' : ℝ} (hAP1 : PrimeTwistBound x A' E Cm κ') (hAP2 : IntegerKernelBound x Cm κ')
    {ψ₁ : ℝ → ℂ} {a : ℝ → ℂ} (hai : Integrable a) (ha₁ : (∫ ξ, ‖a ξ‖) ≤ Real.log x ^ K)
    (harep : ∀ y : ℝ, 0 < y →
      ψ₁ y = ∫ ξ, a ξ * (y : ℂ) ^ (((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I))
    (hat : (∫ ξ in {ξ : ℝ | Real.log x ^ Cf < |ξ|}, ‖a ξ‖) ≤ KA * Real.log x ^ (-At))
    {s : Finset ℕ} {V A B : ℝ} {cf : ℕ → ℂ} {Y σ : ℝ} {k : ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ p ∧
      (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)))
    (hV : vlo ≤ V) (hA : Real.exp (c * Real.log x / Real.log (Real.log x) ^ 20) ≤ A)
    (hB : B ≤ x * Real.exp (-(c * Real.log x / Real.log (Real.log x) ^ 20)))
    (hcf : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ 2 → ‖cf u‖ ≤ Real.log x ^ CU)
    (hψs : ∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2)
    (hY₁ : x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y)
    (hY₂ : Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)))
    (hk₁ : 1 ≤ k) (hk₂ : (k : ℝ) ≤ Real.log x ^ Cm) {t₁ t₂ : ℝ} (h₁₂ : t₁ ≤ t₂)
    (hlen : t₂ - t₁ ≤ 4 * (x * Real.log x ^ (Cm + 2)))
    (hrange : ∀ t ∈ Set.Icc t₁ t₂, ∀ ξ : ℝ, |ξ| ≤ Real.log x ^ Cf →
      Real.log x ^ E ≤ |t + (σ + 2 * Real.pi * ξ)| ∧
        |t + (σ + 2 * Real.pi * ξ)| + 2 ≤ 2 * (x * Real.log x ^ (Cm + 2)))
    (m : ((ℕ × ℕ) × ℕ) × ((ℕ × ℕ) × DirichletCharacter ℂ k)) :
    ∫ t in t₁..t₂, ‖boxTerm Y V s ((Iic ⌊B⌋₊).filter fun p : ℕ => p.Prime ∧ A < p) cf ψ₁ σ m t‖
        ^ 2 ≤
      Real.log x ^ K * ((Real.log x ^ (-(2 * As)) * Real.log x ^ (2 * CU + 5) +
          (2 / vlo) ^ 2 * 4 * (4 * κ' * Real.log x ^ (-A')) ^ 2 *
            (9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4))) * Real.log x ^ K +
        (2 / vlo) ^ 2 * Real.log x ^ (2 * CU + 5) * (KA * Real.log x ^ (-At))) := by
  obtain ⟨⟨⟨i, j⟩, l⟩, ⟨⟨α, β⟩, χ⟩⟩ := m
  have hx0 : 0 < x := by linarith [hf.box.2.1]
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY₁
  have hL0 : 0 < Real.log x := by linarith [hf.big]
  by_cases hrel : ∃ ps ∈ s.filter (fun p => boxIndex p = i ∧ p % k = α),
      ∃ pl ∈ ((Iic ⌊B⌋₊).filter fun p : ℕ => p.Prime ∧ A < p).filter (fun p => boxIndex p = j),
      ∃ u ∈ (Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = l ∧ u % k = β),
        ψ₁ ((ps * pl * u : ℕ) / Y) ≠ 0
  · obtain ⟨ps, hps, pl, hpl, u, hu, hψ0⟩ := hrel
    obtain ⟨hn₁, hn₂⟩ := hψs _ hψ0
    rw [le_div_iff₀ hY0, one_mul] at hn₁
    rw [div_le_iff₀ hY0] at hn₂
    have hd := boxData_of_mem (CU := CU) hc hf hs hV hA hB hcf hY₁ hY₂ hk₁ hk₂ hps hpl hu hn₁
      hn₂
    have hB0 : 0 ≤ B := by
      have hpl' := mem_filter.1 (mem_filter.1 hpl).1
      have h := mem_Iic.1 hpl'.1
      by_contra hneg
      push Not at hneg
      rw [Nat.floor_of_nonpos hneg.le] at h
      have := hpl'.2.1.two_le
      omega
    have hsmpos : ∀ n ∈ s.filter (fun p => boxIndex p = i ∧ p % k = α), 0 < n :=
      fun n hn => (hd.hsP n hn).1.pos
    have hspNpos : ∀ n ∈ (Ioc ⌊max ((2 : ℝ) ^ j) A⌋₊ ⌊min (2 * (2 : ℝ) ^ j) B⌋₊).filter
        Nat.Prime, 0 < n := fun n hn => (mem_filter.1 hn).2.pos
    have hUmpos : ∀ n ∈ (Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = l ∧ u % k = β),
        0 < n := fun n hn => by
      have := (mem_Ioc.1 (mem_filter.1 hn).1).1
      omega
    have hP0 : (0 : ℝ) < 2 ^ i := by positivity
    refine integral_sq_le_of_separated (L := Real.log x) (K := K) (KA := KA) (At := At)
      (Cf := Cf) (Y := Y) (σ := σ) (t₁ := t₁) (t₂ := t₂)
      (G := boxPoly Y (2 ^ i) V (s.filter (fun p => boxIndex p = i ∧ p % k = α))
        ((Ioc ⌊max ((2 : ℝ) ^ j) A⌋₊ ⌊min (2 * (2 : ℝ) ^ j) B⌋₊).filter Nat.Prime)
        ((Ioc 1 ⌊2 * Y⌋₊).filter (fun u => boxIndex u = l ∧ u % k = β)) χ cf)
      (E₁ := Real.log x ^ (-(2 * As)) * Real.log x ^ (2 * CU + 5) +
          (2 / vlo) ^ 2 * 4 * (4 * κ' * Real.log x ^ (-A')) ^ 2 *
            (9 * (1 + |κ'|) * Real.log x ^ (2 * CU + 4)))
      (E₂ := (2 / vlo) ^ 2 * Real.log x ^ (2 * CU + 5))
      hai ha₁ hat (continuous_boxPoly hsmpos hspNpos hUmpos χ cf)
      (fun τ => norm_boxPoly_le hY0 hP0 (lt_of_lt_of_le hvlo hV) hsmpos
        hspNpos hUmpos χ cf τ) hY0 (fun t => ?_) h₁₂ ?_ ?_
      (fun ξ hξ => hB2 _ _ _ _ _ _ _ _ _ k χ cf hd A' E κ' hAP1 hAP2 _ _ (by linarith)
        fun τ hτ => ?_)
      (fun ξ => integral_boxPoly_le hvlo hCm hd hf.box χ (by linarith) (by linarith))
    · exact boxTerm_eq_integral hai harep hY0 s _ _ cf σ i j l α β χ (spareBox_eq hB0 j) hsmpos
        hspNpos hUmpos t
    · positivity
    · positivity
    · have ht : τ - (σ + 2 * Real.pi * ξ) ∈ Set.Icc t₁ t₂ :=
        ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
      have := hrange _ ht ξ hξ
      rwa [sub_add_cancel] at this
  · -- an irrelevant box: `J_m = 0`
    push Not at hrel
    have h0 : ∀ t, boxTerm Y V s ((Iic ⌊B⌋₊).filter fun p : ℕ => p.Prime ∧ A < p) cf ψ₁ σ
        (((i, j), l), ((α, β), χ)) t = 0 := by
      intro t
      rw [boxTerm]
      simp only
      refine mul_eq_zero_of_right _ (sum_eq_zero fun ps hps => sum_eq_zero fun pl hpl =>
        sum_eq_zero fun u hu => ?_)
      rw [hrel ps hps pl hpl u hu, zero_mul, mul_zero]
    simp only [h0, norm_zero]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t _ => by simp,
      intervalIntegral.integral_zero]
    have : 0 ≤ KA * Real.log x ^ (-At) := le_trans (setIntegral_nonneg
      (measurableSet_lt measurable_const continuous_abs.measurable) fun ξ _ => norm_nonneg _) hat
    positivity

/-! ### The bookkeeping -/

/-- The shifted times `τ = t + σ + 2πξ`, for `L^{B'} ≤ |t| ≤ T₀`, `|σ| ≤ L^{C_m}` and
`|ξ| ≤ L^{C_sep}`, satisfy `L^E ≤ |τ|` and `|τ| + 2 ≤ 2T₀`, once `B' ≥ max(C_m, C_sep) + 2`,
`B' ≥ E + max(C_m, C_sep) + 2` and `L ≥ 28`. -/
theorem shifted_range {L Cm Cf E B' T₀ t σ ξ : ℝ} (hL : 28 ≤ L) (hCf : 0 < Cf)
    (hB₁ : max Cm Cf + 2 ≤ B') (hB₂ : E + (max Cm Cf + 2) ≤ B')
    (ht₁ : L ^ B' ≤ |t|) (ht₂ : |t| ≤ T₀)
    (hσ : |σ| ≤ L ^ Cm) (hξ : |ξ| ≤ L ^ Cf) :
    L ^ E ≤ |t + (σ + 2 * Real.pi * ξ)| ∧ |t + (σ + 2 * Real.pi * ξ)| + 2 ≤ 2 * T₀ := by
  set Mx := max Cm Cf
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hCmM : L ^ Cm ≤ L ^ Mx := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
  have hCfM : L ^ Cf ≤ L ^ Mx := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
  have hM1 : 1 ≤ L ^ Mx := Real.one_le_rpow hL1 (le_trans hCf.le (le_max_right _ _))
  have hpi : |2 * Real.pi * ξ| ≤ 7 * L ^ Mx := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have := Real.pi_lt_d2
    have : 0 ≤ |ξ| := abs_nonneg ξ
    nlinarith
  have hs : |σ + 2 * Real.pi * ξ| ≤ 8 * L ^ Mx :=
    (abs_add_le _ _).trans (by linarith)
  have hL2 : (784 : ℝ) ≤ L ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hB'M : 784 * L ^ Mx ≤ L ^ B' := by
    calc 784 * L ^ Mx ≤ L ^ (2 : ℝ) * L ^ Mx := mul_le_mul_of_nonneg_right hL2 (by positivity)
      _ = L ^ (Mx + 2) := by rw [Real.rpow_add hL0]; ring
      _ ≤ L ^ B' := Real.rpow_le_rpow_of_exponent_le hL1 hB₁
  have hB'E : 784 * L ^ E ≤ L ^ B' := by
    calc 784 * L ^ E ≤ L ^ (2 : ℝ) * L ^ E := mul_le_mul_of_nonneg_right hL2 (by positivity)
      _ ≤ L ^ Mx * (L ^ (2 : ℝ) * L ^ E) := le_mul_of_one_le_left (by positivity) hM1
      _ = L ^ (E + (Mx + 2)) := by rw [Real.rpow_add hL0, Real.rpow_add hL0]; ring
      _ ≤ L ^ B' := Real.rpow_le_rpow_of_exponent_le hL1 hB₂
  constructor
  · have h : |t| ≤ |t + (σ + 2 * Real.pi * ξ)| + |σ + 2 * Real.pi * ξ| := by
      have := abs_add_le (t + (σ + 2 * Real.pi * ξ)) (-(σ + 2 * Real.pi * ξ))
      rwa [add_neg_cancel_right, abs_neg] at this
    linarith
  · have h := abs_add_le t (σ + 2 * Real.pi * ξ)
    linarith

/-- `L^a L^b L^c L^d L^e = L^{a+b+c+d+e}` for `L > 0`. -/
theorem rpow_mul_five {L : ℝ} (hL : 0 < L) (a b c d e : ℝ) :
    L ^ a * L ^ b * L ^ c * L ^ d * L ^ e = L ^ (a + b + c + d + e) := by
  rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_add hL]

/-- **The bookkeeping.** With `n ≤ 64 L^{3C_m + 3}` indices, `2A_s ≥ A₀ + D`,
`2A' = A₀ + D - 1` and `A_t ≥ A₀ + D - K`, `D = 6C_m + 6 + 2K + 2C_U + 5`:
`n² L^K (E₁ L^K + E₂ K_A L^{-A_t}) ≤ C_T L^{-A₀}`. -/
theorem tupleBound_le {L Cm K CU As A' At A₀ KA κ' vlo n : ℝ} (hL : 1 ≤ L) (hvlo : 0 < vlo)
    (hKA : 0 ≤ KA) (hn0 : 0 ≤ n) (hn : n ≤ 64 * L ^ (3 * Cm + 3))
    (hAs : A₀ + (6 * Cm + 6 + 2 * K + 2 * CU + 5) ≤ 2 * As)
    (hA' : 2 * A' = A₀ + (6 * Cm + 6 + 2 * K + 2 * CU + 4))
    (hAt : A₀ + (6 * Cm + 6 + K + 2 * CU + 5) ≤ At) :
    n * (n * (L ^ K * ((L ^ (-(2 * As)) * L ^ (2 * CU + 5) +
        (2 / vlo) ^ 2 * 4 * (4 * κ' * L ^ (-A')) ^ 2 * (9 * (1 + |κ'|) * L ^ (2 * CU + 4))) *
          L ^ K + (2 / vlo) ^ 2 * L ^ (2 * CU + 5) * (KA * L ^ (-At))))) ≤
      4096 * (1 + (2 / vlo) ^ 2 * 4 * 16 * κ' ^ 2 * (9 * (1 + |κ'|)) + (2 / vlo) ^ 2 * KA) *
        L ^ (-A₀) := by
  have hL0 : 0 < L := by linarith
  set Q := L ^ (6 * Cm + 6) with hQ
  have hQ0 : 0 < Q := by positivity
  -- `n² ≤ 4096 Q`
  have hn2 : n * n ≤ 4096 * Q := by
    have h := mul_le_mul hn hn hn0 (by positivity)
    have : L ^ (3 * Cm + 3) * L ^ (3 * Cm + 3) = Q := by
      rw [← Real.rpow_add hL0, hQ]
      ring_nf
    nlinarith
  set Cκ := (2 / vlo) ^ 2 * 4 * 16 * κ' ^ 2 * (9 * (1 + |κ'|)) with hCκ
  set C₃ := (2 / vlo) ^ 2 * KA with hC₃
  have hCκ0 : 0 ≤ Cκ := by positivity
  have hC₃0 : 0 ≤ C₃ := by positivity
  -- the three terms, times `Q`
  have h₁ : Q * (L ^ K * L ^ (-(2 * As)) * L ^ (2 * CU + 5) * L ^ K) ≤ L ^ (-A₀) := by
    rw [hQ, ← mul_assoc, ← mul_assoc, ← mul_assoc, rpow_mul_five hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h₂ : Q * (L ^ K * L ^ (-(2 * A')) * L ^ (2 * CU + 4) * L ^ K) ≤ L ^ (-A₀) := by
    rw [hQ, ← mul_assoc, ← mul_assoc, ← mul_assoc, rpow_mul_five hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have h₃ : Q * (L ^ K * L ^ (2 * CU + 5) * L ^ (-At) * 1) ≤ L ^ (-A₀) := by
    rw [mul_one, hQ, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hsq : (4 * κ' * L ^ (-A')) ^ 2 = 16 * κ' ^ 2 * L ^ (-(2 * A')) := by
    rw [mul_pow, mul_pow, rpow_neg_sq hL0.le]
    norm_num
  have hB : L ^ K * ((L ^ (-(2 * As)) * L ^ (2 * CU + 5) +
      (2 / vlo) ^ 2 * 4 * (4 * κ' * L ^ (-A')) ^ 2 * (9 * (1 + |κ'|) * L ^ (2 * CU + 4))) *
        L ^ K + (2 / vlo) ^ 2 * L ^ (2 * CU + 5) * (KA * L ^ (-At))) =
      L ^ K * L ^ (-(2 * As)) * L ^ (2 * CU + 5) * L ^ K +
        Cκ * (L ^ K * L ^ (-(2 * A')) * L ^ (2 * CU + 4) * L ^ K) +
        C₃ * (L ^ K * L ^ (2 * CU + 5) * L ^ (-At) * 1) := by
    rw [hsq, hCκ, hC₃]
    ring
  have hBQ : Q * (L ^ K * ((L ^ (-(2 * As)) * L ^ (2 * CU + 5) +
      (2 / vlo) ^ 2 * 4 * (4 * κ' * L ^ (-A')) ^ 2 * (9 * (1 + |κ'|) * L ^ (2 * CU + 4))) *
        L ^ K + (2 / vlo) ^ 2 * L ^ (2 * CU + 5) * (KA * L ^ (-At)))) ≤
      (1 + Cκ + C₃) * L ^ (-A₀) := by
    rw [hB, mul_add, mul_add, mul_left_comm Q Cκ, mul_left_comm Q C₃]
    nlinarith [mul_le_mul_of_nonneg_left h₂ hCκ0, mul_le_mul_of_nonneg_left h₃ hC₃0]
  have hB0 : 0 ≤ L ^ K * ((L ^ (-(2 * As)) * L ^ (2 * CU + 5) +
      (2 / vlo) ^ 2 * 4 * (4 * κ' * L ^ (-A')) ^ 2 * (9 * (1 + |κ'|) * L ^ (2 * CU + 4))) *
        L ^ K + (2 / vlo) ^ 2 * L ^ (2 * CU + 5) * (KA * L ^ (-At))) := by positivity
  generalize L ^ K * ((L ^ (-(2 * As)) * L ^ (2 * CU + 5) +
      (2 / vlo) ^ 2 * 4 * (4 * κ' * L ^ (-A')) ^ 2 * (9 * (1 + |κ'|) * L ^ (2 * CU + 4))) *
        L ^ K + (2 / vlo) ^ 2 * L ^ (2 * CU + 5) * (KA * L ^ (-At))) = Bnd at hBQ hB0 ⊢
  calc n * (n * Bnd) = (n * n) * Bnd := by ring
    _ ≤ (4096 * Q) * Bnd := mul_le_mul_of_nonneg_right hn2 hB0
    _ = 4096 * (Q * Bnd) := by ring
    _ ≤ 4096 * ((1 + Cκ + C₃) * L ^ (-A₀)) := by linarith
    _ = 4096 * (1 + Cκ + C₃) * L ^ (-A₀) := by ring

/-- The boxes below `N₀ = ⌈3L⌉` cover `[1, x²]`, and `1 ≤ N₀ ≤ 4L`. -/
theorem boxCount_facts {x : ℝ} (hx0 : 0 < x) (hL : 1 ≤ Real.log x) :
    1 ≤ ⌈3 * Real.log x⌉₊ ∧ (⌈3 * Real.log x⌉₊ : ℝ) ≤ 4 * Real.log x ∧
      x ^ 2 ≤ (2 : ℝ) ^ ⌈3 * Real.log x⌉₊ := by
  set L := Real.log x
  refine ⟨Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne', ?_, ?_⟩
  · linarith [Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * L by linarith)]
  · rw [← Real.rpow_natCast (2 : ℝ) ⌈3 * L⌉₊]
    calc x ^ 2 = Real.exp (2 * L) := by
          rw [show 2 * L = L + L by ring, Real.exp_add, Real.exp_log hx0]
          ring
      _ ≤ Real.exp (Real.log 2 * (3 * L)) := by
          have := Real.log_two_gt_d9
          exact Real.exp_le_exp.2 (by nlinarith)
      _ = (2 : ℝ) ^ (3 * L) := (Real.rpow_def_of_pos two_pos _).symm
      _ ≤ (2 : ℝ) ^ ((⌈3 * L⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)

end Erdos408.TwoSided.TupleHigh
