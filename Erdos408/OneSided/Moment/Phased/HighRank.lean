import Erdos408.OneSided.Bands
import Erdos408.OneSided.Moment.Phased.EdgeAtoms
import Erdos408.OneSided.Moment.Phased.GhostAtoms

/-!
# The high-rank absolute bound

M10 at high rank (`exists_realized_history_le` in `Moment/Phased.lean`, PD `mem:atom`,
`mem:rank-absolute`). For a block system `𝒞` of rank `r`,
`∑_s μ(s) |𝐛(s)| ∑_h |w(s, h)| |𝐛(end)| ∏_C [C realized] ≤ L^{C₁(N+1)} (C₁ exp(-L^{α₋}))^r`.

Instead of conditioning chronologically on the pivot values, sum over them. A realized block
`C` has one common band prime `p_C`, so
`∏_C [C realized] ≤ ∑_{(p_C)} ∏_C ∏_{a ∈ C} [β_a = p_C]`, and for fixed values every address
of every block carries a prescription (`blockPres`).

* `sum_chainInit_pres_le`: the initial slots carry the measure `∏ ν(act)`, so a prescribed
  slot costs an atom and a free slot at most `∑_{p ∈ 𝒫_i} ν(p) ≤ 4`. The initial vector needs
  `z = e₁` and the empty memory.
* `sum_history_pres_le`: for a fixed prescription `π`, the row iteration of
  `Moment/Phased/Rows.lean` with the prescribed ghost and edge rows bounds the absolute history
  sum by `4^{KM} R_G^{N+1} R_E^N ∏_a atomCost(π_a)`. The final return is dropped:
  `|𝐛(end)| ≤ 1 ≤ v₀^{size}`.
* `sum_history_realized_le`: summing over the pivot values, a block of size `n` costs
  `∑_p (c ν(p))^n ≤ (c² (4K + 1) Δ)^{n - 1}` with `Δ = sup ν`.
* `exists_realized_history_le_aux`: the constants. Band primes exceed `exp(L^{α₋})`, so
  `Δ ≤ 4 exp(-L^{α₋})`; with `B ≤ L³` the edge rows are `L^{O(1)}`, the ghost rows `O(1)`, and
  the initial slots `4^{K(M+1)}` with `M ≤ N`.
-/

noncomputable section

namespace Erdos408.OneSided

open Filter Finset

variable {K : ℕ}

/-! ### Band facts -/

section Facts

variable {q x : ℝ} {d : Data K}

/-- The damping defects are in `[0, 1]`. -/
private theorem dampDefect_mem_Icc (hq : 0 < q) (hq₁ : q < 1) (N j : ℕ) :
    0 ≤ dampDefect q N j ∧ dampDefect q N j ≤ 1 := by
  have hs : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
  unfold dampDefect
  split_ifs <;> constructor <;> linarith [Real.sqrt_nonneg q]

/-- For primes `p ≥ 2N + 1`, the baseline is `b'_p ≥ 1/2`. -/
private theorem half_le_baseline (hq : 0 < q) (hq₁ : q < 1) {N p : ℕ}
    (hp : 2 * N + 1 ≤ p) : 1 / 2 ≤ baseline q N p := by
  have hp1 : (0 : ℝ) < p + 1 := by positivity
  have hNp : 2 * ((N : ℝ) + 1) ≤ p + 1 := by exact_mod_cast (show 2 * (N + 1) ≤ p + 1 by omega)
  have hsum : ∑ j ∈ range (N + 1), dampDefect q N j ≤ (N : ℝ) + 1 :=
    calc ∑ j ∈ range (N + 1), dampDefect q N j ≤ ∑ _j ∈ range (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (dampDefect_mem_Icc hq hq₁ N j).2
      _ = (N : ℝ) + 1 := by simp
  have h₁ : ((p : ℝ) + 1)⁻¹ * ∑ j ∈ range (N + 1), dampDefect q N j ≤ 1 / 2 := by
    rw [inv_mul_le_iff₀ hp1]
    linarith
  unfold baseline
  linarith

/-- Eventually every band prime is at least `2N + 1` for `N = 2R`. -/
private theorem eventually_two_mul_add_one_le {C CX alo ahi g : ℝ} (halo : 1 / 10 < alo) :
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

/-- The harmonic mass is nonnegative. -/
private theorem harmonicMass_nonneg (S : Finset ℕ) : 0 ≤ harmonicMass S :=
  sum_nonneg fun p _ => by positivity

/-- A particle's prime is a band prime. -/
private theorem fst_mem_bandPrimes (xp : Particle x d) : xp.1.1 ∈ bandPrimes x d := by
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.1 xp.2
  obtain ⟨ℓ, -, hℓ⟩ := mem_image.1 hxp
  rw [← hℓ]
  exact hp

/-- The harmonic mass `V(p)` of the bands containing `p` is nonnegative. -/
private theorem primeMass_nonneg (p : ℕ) : 0 ≤ primeMass x d p :=
  sum_nonneg fun i _ => by
    split_ifs
    · exact harmonicMass_nonneg _
    · exact le_rfl

/-- With band masses at least `1/2`, a prime of a band has `V(p) ≥ 1/2`. -/
private theorem half_le_primeMass (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i))) {i : Fin K}
    {p : ℕ} (hpi : p ∈ band x (d.a i)) : 1 / 2 ≤ primeMass x d p :=
  calc 1 / 2 ≤ harmonicMass (band x (d.a i)) := hV i
    _ = if p ∈ band x (d.a i) then harmonicMass (band x (d.a i)) else 0 := (ite_eq_left hpi).symm
    _ ≤ primeMass x d p :=
        single_le_sum (f := fun i => if p ∈ band x (d.a i) then harmonicMass (band x (d.a i))
          else 0) (fun j _ => by split_ifs; exact harmonicMass_nonneg _; exact le_rfl)
          (mem_univ i)

/-- With band masses at most `1`, `V(p) ≤ K`. -/
private theorem primeMass_le (hV : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) (p : ℕ) :
    primeMass x d p ≤ K :=
  calc primeMass x d p ≤ ∑ _i : Fin K, (1 : ℝ) :=
        sum_le_sum fun i _ => by
          split_ifs
          · exact hV i
          · norm_num
    _ = K := by simp

/-- With baselines at least `1/2` at the band primes, the birth weights are nonnegative. -/
private theorem primeWeight_nonneg {N : ℕ} (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p)
    (p : ℕ) : 0 ≤ primeWeight q x d N p := by
  unfold primeWeight
  by_cases hp : p ∈ bandPrimes x d
  · have := hb p hp
    exact one_div_nonneg.2 (mul_nonneg (mul_nonneg (primeMass_nonneg p) (by positivity))
      (by linarith))
  · have h0 : primeMass x d p = 0 :=
      sum_eq_zero fun i _ => ite_eq_right fun hpi => hp (mem_biUnion.2 ⟨i, mem_univ i, hpi⟩)
    rw [h0]
    simp

/-- At a band prime, `ν(p) ≤ 4/p` and `V(p) ν(p) ≤ 2/p`. -/
private theorem primeWeight_le {N : ℕ} (hV : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)))
    (hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p) {p : ℕ} (hp : p ∈ bandPrimes x d) :
    primeWeight q x d N p ≤ 4 * (1 / p) ∧
      primeMass x d p * primeWeight q x d N p ≤ 2 * (1 / p) := by
  obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
  have hV₁ := half_le_primeMass hV hpi
  have hb₁ := hb p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (TypeII.band_prime hpi).pos
  unfold primeWeight
  constructor
  · calc 1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p)
        ≤ 1 / (1 / 2 * p * (1 / 2)) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul (mul_le_mul hV₁ (by linarith) hp0.le (by linarith)) hb₁ (by norm_num)
              (mul_nonneg (by linarith) (by linarith)))
      _ = 4 * (1 / p) := by field_simp; norm_num
  · have hV0 : primeMass x d p ≠ 0 := by linarith
    have hb0 : baseline q N p ≠ 0 := by linarith
    calc primeMass x d p * (1 / (primeMass x d p * ((p : ℝ) + 1) * baseline q N p))
        = 1 / (((p : ℝ) + 1) * baseline q N p) := by field_simp
      _ ≤ 1 / (p * (1 / 2)) :=
          one_div_le_one_div_of_le (by positivity)
            (mul_le_mul (by linarith) hb₁ (by norm_num) (by linarith))
      _ = 2 * (1 / p) := by field_simp

/-- The hitting particles have one line per band prime, so a sum over them of a nonnegative
function of the prime is at most the sum over the band primes. -/
private theorem sum_hits_le_sum_bandPrimes (z : ℤ × ℤ) {f : ℕ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    ∑ xp with HitsAt x d z xp, f xp.1.1 ≤ ∑ p ∈ bandPrimes x d, f p := by
  rw [← sum_image (f := f) (g := fun xp : Particle x d => xp.1.1)]
  · exact sum_le_sum_of_subset_of_nonneg
      (image_subset_iff.2 fun xp _ => fst_mem_bandPrimes xp) fun p _ _ => hf p
  · intro xp hxp yp hyp h
    exact hitsAt_eq_of_prime (mem_filter.1 (mem_coe.1 hxp)).2 (mem_filter.1 (mem_coe.1 hyp)).2 h

/-- With band masses at most `1`, `∑_{p band prime} 1/p ≤ K`. -/
private theorem sum_one_div_bandPrimes_le (hV : ∀ i, harmonicMass (band x (d.a i)) ≤ 1) :
    ∑ p ∈ bandPrimes x d, (1 : ℝ) / p ≤ K :=
  calc ∑ p ∈ bandPrimes x d, (1 : ℝ) / p
      ≤ ∑ p ∈ bandPrimes x d, ∑ i, if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 := by
        refine sum_le_sum fun p hp => ?_
        obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
        calc (1 : ℝ) / p = if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 :=
              (ite_eq_left hpi).symm
          _ ≤ ∑ i, if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 :=
              single_le_sum (f := fun i => if p ∈ band x (d.a i) then (1 : ℝ) / p else 0)
                (fun j _ => by split_ifs <;> positivity) (mem_univ i)
    _ = ∑ i, ∑ p ∈ bandPrimes x d, if p ∈ band x (d.a i) then (1 : ℝ) / p else 0 := sum_comm
    _ = ∑ i, harmonicMass (band x (d.a i)) := by
        refine sum_congr rfl fun i _ => ?_
        rw [sum_ite_mem, inter_eq_right.2
          (show band x (d.a i) ⊆ bandPrimes x d from fun p hp => mem_biUnion.2 ⟨i, mem_univ i, hp⟩)]
        rfl
    _ ≤ ∑ _i : Fin K, (1 : ℝ) := sum_le_sum fun i _ => hV i
    _ = K := by simp

/-- `ρ⁴ = √q`. -/
private theorem pendingWeight_pow_four (hq : 0 < q) : pendingWeight q ^ 4 = Real.sqrt q := by
  unfold pendingWeight
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Real.sqrt_eq_rpow]
  norm_num

/-- The births of a history are band primes. -/
private theorem births_mem_bandPrimes {Y d₀ u v r : ℝ} {B N : ℕ} (s : ChainState x d Y d₀ u v r B)
    {hh : History x d Y d₀ u v r N} (hhh : hh ∈ histories x d Y d₀ u v r B N)
    (a : BirthAddr (K := K) x B N) {p : ℕ} (hp : births s hh a = some p) : p ∈ bandPrimes x d := by
  simp only [histories, mem_product, Fintype.mem_piFinset] at hhh
  rcases a with ⟨i, k⟩ | ⟨j, i⟩ | ⟨j, k⟩
  · simp only [births, Option.some.injEq] at hp
    subst hp
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_band_of_mem_lists s.2.1.2 i k⟩
  · simp only [births] at hp
    split_ifs at hp
    simp only [Option.some.injEq] at hp
    subst hp
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_band_of_mem_edgeChoices (hhh.2 j) i⟩
  · simp only [births] at hp
    have hmem := List.mem_of_getElem? hp
    rw [batchPrimes, Multiset.mem_sort, Multiset.mem_sum] at hmem
    obtain ⟨xp, -, hxp⟩ := hmem
    rw [Multiset.eq_of_mem_replicate hxp]
    exact fst_mem_bandPrimes xp

end Facts

/-! ### A fixed prescription -/

section Prescribed

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

/-- **The initial slots** (PD `mem:rank-absolute`): the chain measure carries `∏ ν(act)`, so
against prescriptions of the initial slots the initial vector has mass at most
`4^{K(M+1)} ∏_a atomCost(π_a)`. A free slot costs `∑_{p ∈ 𝒫_i} ν(p) ≤ 4`. -/
theorem sum_chainInit_pres_le (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4) {c₀ : ℝ} (hc₀ : 1 ≤ c₀)
    (π : Fin K × Fin (padCount x + 1) → Option ℕ) :
    ∑ s : ChainState x d Y d₀ u v r B, chainMeasure q x d Y d₀ u v r B N s *
        ‖chainInit x d Y d₀ u v r B s‖ * ∏ a, presInd (π a) (some (s.2.1.1 a.1 a.2)) ≤
      4 ^ (K * (padCount x + 1)) * ∏ a, atomCost c₀ (primeWeight q x d N) (π a) := by
  classical
  set ν := primeWeight q x d N with hνdef
  set g : Lists K (padCount x) → ℝ := fun l =>
    ∏ i, ∏ h, ν (l i h) * presInd (π (i, h)) (some (l i h))
    with hg
  set k : MemState (Particle x d) B → ℝ := fun S => if memSize S.1 = 0 then 1 else 0 with hk
  set f : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) → ℝ :=
    fun z => if z.1 = (1, 0) then 1 else 0 with hf
  have hg0 : ∀ l, 0 ≤ g l := fun l =>
    prod_nonneg fun i _ => prod_nonneg fun h _ => mul_nonneg (hν _) (presInd_nonneg _ _)
  -- the summand factors over the position, the lists and the memory
  have hterm : ∀ s : ChainState x d Y d₀ u v r B, chainMeasure q x d Y d₀ u v r B N s *
      ‖chainInit x d Y d₀ u v r B s‖ * ∏ a, presInd (π a) (some (s.2.1.1 a.1 a.2)) =
      f s.1 * (g s.2.1.1 * k s.2.2) := by
    intro s
    have hw : memSize s.2.2.1 = 0 →
        memWeight (fun xp : Particle x d => ν xp.1.1) s.2.2.1 = 1 := by
      intro h0
      have : ∀ xp, s.2.2.1 xp = 0 := fun xp => by have := le_memSize s.2.2.1 xp; omega
      simp [memWeight, this]
    have hsplit : chainMeasure q x d Y d₀ u v r B N s *
        ∏ a, presInd (π a) (some (s.2.1.1 a.1 a.2)) =
        g s.2.1.1 * memWeight (fun xp : Particle x d => ν xp.1.1) s.2.2.1 := by
      simp only [chainMeasure, hg, Fintype.prod_prod_type, prod_mul_distrib]
      ring
    unfold chainInit
    by_cases h₁ : s.1.1 = (1, 0) <;> by_cases h₂ : memSize s.2.2.1 = 0
    · rw [ite_eq_left ⟨h₁, h₂⟩, norm_one, mul_one, hsplit, hw h₂]
      simp only [hf, hk, h₁, h₂, ↓reduceIte]
      ring
    all_goals
      rw [ite_eq_right (by tauto), norm_zero, mul_zero, zero_mul]
      simp only [hf, hk, h₁, h₂, ↓reduceIte]
      ring
  -- the three factors
  have hfz : ∑ z, f z ≤ 1 := by
    rw [hf, sum_boole]
    have h : (univ.filter fun z : ↥(rootPositions (d₀ * Y * d.Hm) d.Hn u v r) =>
        z.1 = (1, 0)).card ≤ 1 :=
      card_le_one.2 fun a ha b hb =>
        Subtype.ext (((mem_filter.1 ha).2).trans ((mem_filter.1 hb).2).symm)
    exact_mod_cast h
  have hkS : ∑ S, k S ≤ 1 := by
    rw [hk, sum_boole]
    exact_mod_cast card_le_one.2 fun a ha b hb => Subtype.ext (funext fun xp => by
      have h₁ := (mem_filter.1 ha).2
      have h₂ := (mem_filter.1 hb).2
      have := le_memSize a.1 xp
      have := le_memSize b.1 xp
      omega)
  have hslot : ∀ πa : Option ℕ, ∀ i, ∑ p ∈ band x (d.a i), ν p * presInd πa (some p) ≤
      4 * atomCost c₀ ν πa := by
    intro πa i
    cases πa with
    | none =>
      simp only [presInd_none, mul_one, atomCost, Option.elim]
      linarith [hνi i]
    | some p₀ =>
      simp only [presInd_some, Option.some.injEq, mul_ite, mul_one, mul_zero, sum_ite_eq',
        atomCost, Option.elim]
      have h4 : (1 : ℝ) ≤ 4 * c₀ := by linarith
      calc (if p₀ ∈ band x (d.a i) then ν p₀ else 0) ≤ ν p₀ := by
            split_ifs
            exacts [le_rfl, hν p₀]
        _ ≤ 4 * c₀ * ν p₀ := le_mul_of_one_le_left (hν p₀) h4
        _ = 4 * (c₀ * ν p₀) := mul_assoc _ _ _
  have hgl : ∑ l : ↥(lists x d (padCount x)), g l.1 ≤
      4 ^ (K * (padCount x + 1)) * ∏ a, atomCost c₀ ν (π a) := by
    rw [sum_coe_sort (lists x d (padCount x)) g]
    calc ∑ l ∈ lists x d (padCount x), g l
        ≤ ∑ l ∈ Fintype.piFinset (fun i => Fintype.piFinset fun _ : Fin (padCount x + 1) =>
            band x (d.a i)), g l :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun l _ _ => hg0 l
      _ = ∏ i, ∏ h : Fin (padCount x + 1),
            ∑ p ∈ band x (d.a i), ν p * presInd (π (i, h)) (some p) := by
          simp only [hg, prod_univ_sum]
      _ ≤ ∏ i, ∏ h : Fin (padCount x + 1), 4 * atomCost c₀ ν (π (i, h)) :=
          prod_le_prod₀ (fun i _ => prod_nonneg fun h _ => sum_nonneg fun p _ =>
            mul_nonneg (hν _) (presInd_nonneg _ _))
            fun i _ => prod_le_prod₀ (fun h _ => sum_nonneg fun p _ =>
              mul_nonneg (hν _) (presInd_nonneg _ _)) fun h _ => hslot _ i
      _ = 4 ^ (K * (padCount x + 1)) * ∏ a, atomCost c₀ ν (π a) := by
          rw [Fintype.prod_prod_type]
          simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
          ring
  calc _ = ∑ s : ChainState x d Y d₀ u v r B, f s.1 * (g s.2.1.1 * k s.2.2) :=
        sum_congr rfl fun s _ => hterm s
    _ = (∑ z, f z) * ((∑ l : ↥(lists x d (padCount x)), g l.1) * ∑ S, k S) := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_prod_type, ← mul_sum, ← sum_mul]
    _ ≤ 1 * ((4 ^ (K * (padCount x + 1)) * ∏ a, atomCost c₀ ν (π a)) * 1) := by
        have hf0 : 0 ≤ ∑ z, f z := sum_nonneg fun z _ => by simp only [hf]; split_ifs <;> norm_num
        have hk0 : 0 ≤ ∑ S, k S := sum_nonneg fun S _ => by simp only [hk]; split_ifs <;> norm_num
        have hg' : 0 ≤ ∑ l : ↥(lists x d (padCount x)), g l.1 := sum_nonneg fun l _ => hg0 _
        have hX : 0 ≤ 4 ^ (K * (padCount x + 1)) * ∏ a, atomCost c₀ ν (π a) :=
          mul_nonneg (by positivity) (prod_nonneg fun a _ => atomCost_nonneg (by linarith) hν _)
        exact mul_le_mul hfz (mul_le_mul hgl hkS hk0 hX) (mul_nonneg hg' hk0) zero_le_one
    _ = 4 ^ (K * (padCount x + 1)) * ∏ a, atomCost c₀ ν (π a) := by ring

/-- **A fixed prescription** (PD `mem:rank-absolute`): if the prescribed ghost rows are at most
`R_G ∏ atomCost` and the prescribed edge rows at most `R_E ∏ atomCost`, against the weight
`v₀^{size}`, then the absolute history sum against `∏_a [β_a = π_a]` is at most
`4^{K(M+1)} R_G^{N+1} R_E^N ∏_a atomCost(π_a)`. The final return is dropped. -/
theorem sum_history_pres_le (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4) {v₀ c₀ RG RE : ℝ}
    (hv₀ : 1 ≤ v₀) (hc₀ : 1 ≤ c₀) (hRG : 0 ≤ RG) (hRE : 0 ≤ RE)
    (hG : ∀ (j : Fin (N + 1)) (πg : Fin B → Option ℕ) (t : ChainState x d Y d₀ u v r B),
      ∑ c ∈ multBox B ×ˢ multBox B, ‖chainGhostCoef q x d Y d₀ u v r B N j t c‖ *
          (∏ k : Fin B, presInd (πg k) (batchPrimes x d c.2)[k.1]?) *
          v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤
        RG * (∏ k, atomCost c₀ (primeWeight q x d N) (πg k)) * v₀ ^ memSize t.2.2.1)
    (hE : ∀ (πe : Fin K → Option ℕ) (t : ChainState x d Y d₀ u v r B),
      ∑ e ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t e‖ *
          (∏ i, presInd (πe i) (if (e.2.2.2.1 i).2 then none else some (e.2.2.2.1 i).1)) *
          v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B t e).2.2.1 ≤
        RE * (∏ i, atomCost c₀ (primeWeight q x d N) (πe i)) * v₀ ^ memSize t.2.2.1)
    (π : BirthAddr (K := K) x B N → Option ℕ) :
    ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ hh ∈ histories x d Y d₀ u v r B N, ‖chainWeight q A₀ s hh‖ *
          ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ * ∏ a, presInd (π a) (births s hh a) ≤
      4 ^ (K * (padCount x + 1)) * RG ^ (N + 1) * RE ^ N *
        ∏ a, atomCost c₀ (primeWeight q x d N) (π a) := by
  classical
  set ν := primeWeight q x d N with hνdef
  set G : Fin (N + 1) → ChainState x d Y d₀ u v r B → GhostChoice x d → ℝ := fun j t c =>
    ‖chainGhostCoef q x d Y d₀ u v r B N j t c‖ *
      ∏ k : Fin B, presInd (π (.inr (.inr (j, k)))) (batchPrimes x d c.2)[k.1]? with hGdef
  set E : Fin N → ChainState x d Y d₀ u v r B → EdgeChoice x d Y d₀ u v r → ℝ := fun j t e =>
    ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t e‖ *
      ∏ i, presInd (π (.inr (.inl (j, i))))
        (if (e.2.2.2.1 i).2 then none else some (e.2.2.2.1 i).1) with hEdef
  set ag : Fin (N + 1) → ℝ := fun j => RG * ∏ k, atomCost c₀ ν (π (.inr (.inr (j, k))))
    with hag
  set be : Fin N → ℝ := fun j => RE * ∏ i, atomCost c₀ ν (π (.inr (.inl (j, i)))) with hbe
  set ini : ChainState x d Y d₀ u v r B → ℝ := fun s =>
    ∏ a : Fin K × Fin (padCount x + 1), presInd (π (.inl a)) (some (s.2.1.1 a.1 a.2)) with hini
  have hμ : ∀ s, 0 ≤ chainMeasure q x d Y d₀ u v r B N s := fun s =>
    mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  have hini0 : ∀ s, 0 ≤ ini s := fun s => prod_nonneg fun a _ => presInd_nonneg _ _
  have hagb : 0 ≤ (∏ j, ag j) * ∏ j, be j :=
    mul_nonneg (prod_nonneg fun j _ => mul_nonneg hRG (prod_nonneg fun k _ =>
      atomCost_nonneg (by linarith) hν _))
      (prod_nonneg fun j _ => mul_nonneg hRE (prod_nonneg fun k _ =>
        atomCost_nonneg (by linarith) hν _))
  -- the row iteration
  have hrow : ∀ s, ∑ hh ∈ histories x d Y d₀ u v r B N,
      (∏ j : Fin (N + 1), G j (chainVisit s hh j) (hh.1 j)) *
        (∏ j : Fin N, E j (chainGhostOut x d Y d₀ u v r B (chainVisit s hh j.castSucc)
          (hh.1 j.castSucc)) (hh.2 j)) *
        ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ ≤
      (∏ j, ag j) * (∏ j, be j) * v₀ ^ memSize s.2.2.1 :=
    sum_history_le_of_rows (h := fun t => v₀ ^ memSize t.2.2.1)
      (f := fun t => ‖chainInit x d Y d₀ u v r B t‖)
      (fun t => by
        refine le_trans ?_ (one_le_pow₀ hv₀)
        unfold chainInit
        split_ifs <;> simp) N G E ag be
      (fun j t c => mul_nonneg (norm_nonneg _) (prod_nonneg fun k _ => presInd_nonneg _ _))
      (fun j t e => mul_nonneg (norm_nonneg _) (prod_nonneg fun k _ => presInd_nonneg _ _))
      (fun j => mul_nonneg hRG (prod_nonneg fun k _ => atomCost_nonneg (by linarith) hν _))
      (fun j => mul_nonneg hRE (prod_nonneg fun k _ => atomCost_nonneg (by linarith) hν _))
      (fun j t => hG j _ t) (fun j t => hE _ t)
  -- the prescriptions split by operation
  have hfac : ∀ s hh, ‖chainWeight q A₀ s hh‖ * ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ *
      ∏ a, presInd (π a) (births s hh a) =
      ini s * ((∏ j : Fin (N + 1), G j (chainVisit s hh j) (hh.1 j)) *
        (∏ j : Fin N, E j (chainGhostOut x d Y d₀ u v r B (chainVisit s hh j.castSucc)
          (hh.1 j.castSucc)) (hh.2 j)) *
        ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖) := by
    intro s hh
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [births, Fintype.prod_prod_type, chainWeight, norm_mul, norm_prod, hGdef, hEdef,
      hini, prod_mul_distrib]
    ring
  -- the initial vector needs the empty memory
  have hstart : ∀ s, ‖chainInit x d Y d₀ u v r B s‖ * v₀ ^ memSize s.2.2.1 =
      ‖chainInit x d Y d₀ u v r B s‖ := by
    intro s
    unfold chainInit
    split_ifs with h
    · rw [h.2, pow_zero, mul_one]
    · rw [norm_zero, zero_mul]
  calc ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ hh ∈ histories x d Y d₀ u v r B N, ‖chainWeight q A₀ s hh‖ *
          ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ * ∏ a, presInd (π a) (births s hh a)
      = ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
          (ini s * ∑ hh ∈ histories x d Y d₀ u v r B N,
            (∏ j : Fin (N + 1), G j (chainVisit s hh j) (hh.1 j)) *
              (∏ j : Fin N, E j (chainGhostOut x d Y d₀ u v r B (chainVisit s hh j.castSucc)
                (hh.1 j.castSucc)) (hh.2 j)) *
              ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖) := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_congr rfl fun hh _ => hfac s hh, ← mul_sum]
    _ ≤ ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
          (ini s * ((∏ j, ag j) * (∏ j, be j) * v₀ ^ memSize s.2.2.1)) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hrow s) (hini0 s))
          (mul_nonneg (hμ s) (norm_nonneg _))
    _ = (∏ j, ag j) * (∏ j, be j) * ∑ s, chainMeasure q x d Y d₀ u v r B N s *
          ‖chainInit x d Y d₀ u v r B s‖ * ini s := by
        rw [mul_sum]
        refine sum_congr rfl fun s _ => ?_
        calc chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
              (ini s * ((∏ j, ag j) * (∏ j, be j) * v₀ ^ memSize s.2.2.1))
            = (∏ j, ag j) * (∏ j, be j) * (chainMeasure q x d Y d₀ u v r B N s *
              (‖chainInit x d Y d₀ u v r B s‖ * v₀ ^ memSize s.2.2.1) * ini s) := by ring
          _ = _ := by rw [hstart s]
    _ ≤ (∏ j, ag j) * (∏ j, be j) *
          (4 ^ (K * (padCount x + 1)) * ∏ a, atomCost c₀ ν (π (.inl a))) :=
        mul_le_mul_of_nonneg_left (sum_chainInit_pres_le hν hνi hc₀ _) hagb
    _ = 4 ^ (K * (padCount x + 1)) * RG ^ (N + 1) * RE ^ N * ∏ a, atomCost c₀ ν (π a) := by
        rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
        simp only [hag, hbe, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
          Fintype.prod_prod_type]
        ring

end Prescribed

/-! ### Block systems -/

section Blocks

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
open scoped Classical in
/-- A realized block has one common prime among the possible births `P`:
`[C realized] ≤ ∑_{p ∈ P} ∏_{a ∈ C} [β_a = p]`. -/
theorem realized_le_sum (β : α → Option ℕ) {P : Finset ℕ} (hβ : ∀ a p, β a = some p → p ∈ P)
    {C : Finset α} (hC : C.Nonempty) :
    (if BlockRealized β C then (1 : ℝ) else 0) ≤ ∑ p ∈ P, ∏ a ∈ C, presInd (some p) (β a) := by
  have h0 : ∀ p, 0 ≤ ∏ a ∈ C, presInd (some p) (β a) := fun p =>
    prod_nonneg fun a _ => presInd_nonneg _ _
  split_ifs with h
  · obtain ⟨p, hp⟩ := h
    obtain ⟨a₀, ha₀⟩ := hC
    calc (1 : ℝ) = ∏ a ∈ C, presInd (some p) (β a) :=
          (prod_eq_one fun a ha => by rw [presInd_some, hp a ha, ite_eq_left rfl]).symm
      _ ≤ _ := single_le_sum (fun p _ => h0 p) (hβ a₀ p (hp a₀ ha₀))
  · exact sum_nonneg fun p _ => h0 p

open scoped Classical in
/-- The prescription of a block system with values `p`: every address of a block `C` is
prescribed to `p_C`, and the other addresses are free. -/
def blockPres (𝒞 : Finset (Finset α)) (p : ↥𝒞 → ℕ) (a : α) : Option ℕ :=
  if h : ∃ C : ↥𝒞, a ∈ C.1 then some (p h.choose) else none

/-- For disjoint blocks, a product over the addresses of a function that is one on free
addresses is the product over the blocks of its values at the block primes. -/
theorem prod_blockPres {𝒞 : Finset (Finset α)}
    (h𝒞 : (𝒞 : Set (Finset α)).PairwiseDisjoint id) (p : ↥𝒞 → ℕ) (Φ : α → Option ℕ → ℝ)
    (hΦ : ∀ a, Φ a none = 1) :
    ∏ a, Φ a (blockPres 𝒞 p a) = ∏ C : ↥𝒞, ∏ a ∈ C.1, Φ a (some (p C)) := by
  classical
  have hdisj : ((univ : Finset ↥𝒞) : Set ↥𝒞).PairwiseDisjoint fun C : ↥𝒞 => C.1 :=
    fun C _ C' _ hne => h𝒞 C.2 C'.2 fun h => hne (Subtype.ext h)
  have hval : ∀ C : ↥𝒞, ∀ a ∈ C.1, blockPres 𝒞 p a = some (p C) := by
    intro C a ha
    have h : ∃ C : ↥𝒞, a ∈ C.1 := ⟨C, ha⟩
    rw [blockPres, dite_eq_left h]
    by_contra hne
    have hCC : h.choose ≠ C := fun e => hne (by rw [e])
    exact disjoint_left.1 (h𝒞 h.choose.2 C.2 fun e => hCC (Subtype.ext e)) h.choose_spec ha
  have hnone : ∀ a ∈ univ, a ∉ univ.biUnion (fun C : ↥𝒞 => C.1) →
      Φ a (blockPres 𝒞 p a) = 1 := by
    intro a _ ha
    have h : ¬∃ C : ↥𝒞, a ∈ C.1 := fun ⟨C, hC⟩ => ha (mem_biUnion.2 ⟨C, mem_univ _, hC⟩)
    rw [blockPres, dite_eq_right h, hΦ]
  rw [← prod_subset (subset_univ _) hnone, prod_biUnion hdisj]
  exact prod_congr rfl fun C _ => prod_congr rfl fun a ha => by rw [hval C a ha]

/-- A block of size `n ≥ 2` with a summed common prime costs
`∑_p (c ν(p))^n ≤ (c² (S + 1) Δ)^{n - 1}`, for `ν ≤ Δ` and `∑ ν ≤ S`. -/
theorem sum_pow_atom_le {ν : ℕ → ℝ} {P : Finset ℕ} {c Δ S : ℝ} (hc : 1 ≤ c)
    (hν : ∀ p, 0 ≤ ν p) (hΔ : ∀ p ∈ P, ν p ≤ Δ) (hΔ0 : 0 ≤ Δ) (hS : ∑ p ∈ P, ν p ≤ S)
    (hS0 : 0 ≤ S) {n : ℕ} (hn : 2 ≤ n) :
    ∑ p ∈ P, (c * ν p) ^ n ≤ (c ^ 2 * (S + 1) * Δ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hc0 : 0 ≤ c := by linarith
  rw [show m + 2 - 1 = m + 1 by omega]
  calc ∑ p ∈ P, (c * ν p) ^ (m + 2)
      ≤ ∑ p ∈ P, c ^ (m + 2) * Δ ^ (m + 1) * ν p := by
        refine sum_le_sum fun p hp => ?_
        rw [show (c * ν p) ^ (m + 2) = c ^ (m + 2) * ν p ^ (m + 1) * ν p by ring]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hν p) (hΔ p hp) _) (pow_nonneg hc0 _)) (hν p)
    _ = c ^ (m + 2) * Δ ^ (m + 1) * ∑ p ∈ P, ν p := (mul_sum _ _ _).symm
    _ ≤ c ^ (m + 2) * Δ ^ (m + 1) * S :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (c ^ 2) ^ (m + 1) * Δ ^ (m + 1) * (S + 1) ^ (m + 1) := by
        have h₁ : c ^ (m + 2) ≤ (c ^ 2) ^ (m + 1) := by
          rw [← pow_mul]
          exact pow_le_pow_right₀ hc (by omega)
        have h₂ : S ≤ (S + 1) ^ (m + 1) :=
          (le_add_of_nonneg_right zero_le_one).trans (le_self_pow₀ (by linarith) (by omega))
        exact mul_le_mul (mul_le_mul_of_nonneg_right h₁ (pow_nonneg hΔ0 _)) h₂ hS0
          (mul_nonneg (pow_nonneg (pow_nonneg hc0 _) _) (pow_nonneg hΔ0 _))
    _ = (c ^ 2 * (S + 1) * Δ) ^ (m + 1) := by rw [mul_pow, mul_pow]; ring

end Blocks

/-! ### The realized blocks -/

section Realized

variable {q A₀ x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B N : ℕ}

open scoped Classical in
/-- **The high-rank absolute bound at fixed rows** (PD `mem:rank-absolute`): under the
prescribed row bounds of `sum_history_pres_le`, the absolute history sum constrained by a
block system of rank `r` is at most `4^{K(M+1)} R_G^{N+1} R_E^N (c² (4K + 1) Δ)^r`, where
`Δ ≥ ν` on the band primes and `∑ ν ≤ 4K`. The common prime of each block is summed over. -/
theorem sum_history_realized_le (hν : ∀ p, 0 ≤ primeWeight q x d N p)
    (hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4)
    (hνS : ∑ p ∈ bandPrimes x d, primeWeight q x d N p ≤ 4 * K) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ p ∈ bandPrimes x d, primeWeight q x d N p ≤ Δ) {v₀ c₀ RG RE : ℝ}
    (hv₀ : 1 ≤ v₀) (hc₀ : 1 ≤ c₀) (hRG : 0 ≤ RG) (hRE : 0 ≤ RE)
    (hG : ∀ (j : Fin (N + 1)) (πg : Fin B → Option ℕ) (t : ChainState x d Y d₀ u v r B),
      ∑ c ∈ multBox B ×ˢ multBox B, ‖chainGhostCoef q x d Y d₀ u v r B N j t c‖ *
          (∏ k : Fin B, presInd (πg k) (batchPrimes x d c.2)[k.1]?) *
          v₀ ^ memSize (chainGhostOut x d Y d₀ u v r B t c).2.2.1 ≤
        RG * (∏ k, atomCost c₀ (primeWeight q x d N) (πg k)) * v₀ ^ memSize t.2.2.1)
    (hE : ∀ (πe : Fin K → Option ℕ) (t : ChainState x d Y d₀ u v r B),
      ∑ e ∈ edgeChoices x d Y d₀ u v r, ‖chainEdgeCoef q A₀ x d Y d₀ u v r B N t e‖ *
          (∏ i, presInd (πe i) (if (e.2.2.2.1 i).2 then none else some (e.2.2.2.1 i).1)) *
          v₀ ^ memSize (chainEdgeOut x d Y d₀ u v r B t e).2.2.1 ≤
        RE * (∏ i, atomCost c₀ (primeWeight q x d N) (πe i)) * v₀ ^ memSize t.2.2.1)
    {𝒞 : Finset (Finset (BirthAddr (K := K) x B N))}
    (h𝒞 : 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N)) :
    ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ hh ∈ histories x d Y d₀ u v r B N, ‖chainWeight q A₀ s hh‖ *
          ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ *
            ∏ C ∈ 𝒞, (if BlockRealized (births s hh) C then 1 else 0) ≤
      4 ^ (K * (padCount x + 1)) * RG ^ (N + 1) * RE ^ N *
        (c₀ ^ 2 * (4 * K + 1) * Δ) ^ blockRank 𝒞 := by
  set ν := primeWeight q x d N with hνdef
  have h𝒞' := h𝒞
  simp only [blockSystems, mem_filter, mem_univ, true_and] at h𝒞'
  obtain ⟨hdisj, h2⟩ := h𝒞'
  set Ps := Fintype.piFinset fun _ : ↥𝒞 => bandPrimes x d with hPs
  set T := 4 ^ (K * (padCount x + 1)) * RG ^ (N + 1) * RE ^ N with hT
  have hμ : ∀ s, 0 ≤ chainMeasure q x d Y d₀ u v r B N s := fun s =>
    mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun h _ => hν _)
      (memWeight_nonneg (fun xp => hν _) _)
  -- the realized blocks against the summed block primes
  have hreal : ∀ s, ∀ hh ∈ histories x d Y d₀ u v r B N,
      ∏ C ∈ 𝒞, (if BlockRealized (births s hh) C then (1 : ℝ) else 0) ≤
        ∑ p ∈ Ps, ∏ a, presInd (blockPres 𝒞 p a) (births s hh a) := by
    intro s hh hhh
    rw [← prod_coe_sort 𝒞 fun C => if BlockRealized (births s hh) C then (1 : ℝ) else 0]
    calc ∏ C : ↥𝒞, (if BlockRealized (births s hh) C.1 then (1 : ℝ) else 0)
        ≤ ∏ C : ↥𝒞, ∑ p ∈ bandPrimes x d, ∏ a ∈ C.1, presInd (some p) (births s hh a) :=
          prod_le_prod₀ (fun C _ => by split_ifs <;> norm_num) fun C _ =>
            realized_le_sum _ (fun a p hp => births_mem_bandPrimes s hhh a hp)
              (card_pos.1 (lt_of_lt_of_le two_pos (h2 C.1 C.2)))
      _ = ∑ p ∈ Ps, ∏ C : ↥𝒞, ∏ a ∈ C.1, presInd (some (p C)) (births s hh a) :=
          prod_univ_sum _ _
      _ = ∑ p ∈ Ps, ∏ a, presInd (blockPres 𝒞 p a) (births s hh a) :=
          sum_congr rfl fun p _ =>
            (prod_blockPres hdisj p (fun a o => presInd o (births s hh a))
              fun a => presInd_none _).symm
  -- the fixed prescriptions
  have hfix : ∀ p : ↥𝒞 → ℕ,
      ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ hh ∈ histories x d Y d₀ u v r B N, ‖chainWeight q A₀ s hh‖ *
          ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ *
            ∏ a, presInd (blockPres 𝒞 p a) (births s hh a) ≤
        T * ∏ C : ↥𝒞, (c₀ * ν (p C)) ^ (C.1.card) := by
    intro p
    refine (sum_history_pres_le hν hνi hv₀ hc₀ hRG hRE hG hE (blockPres 𝒞 p)).trans
      (le_of_eq ?_)
    rw [prod_blockPres hdisj p (fun _ o => atomCost c₀ ν o) fun _ => rfl]
    simp only [atomCost, Option.elim, prod_const, hT]
  calc ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ hh ∈ histories x d Y d₀ u v r B N, ‖chainWeight q A₀ s hh‖ *
          ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ *
            ∏ C ∈ 𝒞, (if BlockRealized (births s hh) C then 1 else 0)
      ≤ ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ hh ∈ histories x d Y d₀ u v r B N, ‖chainWeight q A₀ s hh‖ *
          ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ *
            ∑ p ∈ Ps, ∏ a, presInd (blockPres 𝒞 p a) (births s hh a) :=
        sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (sum_le_sum fun hh hhh =>
          mul_le_mul_of_nonneg_left (hreal s hh hhh)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (mul_nonneg (hμ s) (norm_nonneg _))
    _ = ∑ p ∈ Ps, ∑ s, chainMeasure q x d Y d₀ u v r B N s * ‖chainInit x d Y d₀ u v r B s‖ *
        ∑ hh ∈ histories x d Y d₀ u v r B N, ‖chainWeight q A₀ s hh‖ *
          ‖chainInit x d Y d₀ u v r B (chainEnd s hh)‖ *
            ∏ a, presInd (blockPres 𝒞 p a) (births s hh a) := by
        simp only [mul_sum]
        exact (sum_congr rfl fun s _ => sum_comm).trans sum_comm
    _ ≤ ∑ p ∈ Ps, T * ∏ C : ↥𝒞, (c₀ * ν (p C)) ^ (C.1.card) := sum_le_sum fun p _ => hfix p
    _ = T * ∏ C : ↥𝒞, ∑ p ∈ bandPrimes x d, (c₀ * ν p) ^ (C.1.card) := by
        rw [← mul_sum, prod_univ_sum]
    _ ≤ T * ∏ C : ↥𝒞, (c₀ ^ 2 * (4 * K + 1) * Δ) ^ (C.1.card - 1) := by
        refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun C _ => sum_nonneg fun p _ =>
          pow_nonneg (mul_nonneg (by linarith) (hν _)) _) fun C _ => ?_)
          (by positivity)
        exact sum_pow_atom_le hc₀ hν hΔ hΔ0 hνS (by positivity) (h2 C.1 C.2)
    _ = T * (c₀ ^ 2 * (4 * K + 1) * Δ) ^ blockRank 𝒞 := by
        rw [prod_pow_eq_pow_sum, blockRank, sum_coe_sort 𝒞 fun C => C.card - 1]

end Realized

/-! ### The constants -/

open scoped Classical in
/-- **M10, high rank** (PD `mem:rank-absolute`): for `B ≤ L³` and `N = 2R`, the absolute history
sum constrained by a block system of rank `r` is at most `L^{C₁(N+1)} (C₁ exp(-L^{α₋}))^r`.
Here `v₀ = (K + 1)/(ρ (1 - ρ²))` is the Schur weight of the ghost bound, the ghost atoms cost
`v₀ K ν/ρ`, and the edge rows are at most `(2 v₀)^K (2B + 4)^K 16 (1 + 52 L^{3A₀})`. -/
theorem exists_realized_history_le_aux {q C CX alo ahi g A₀ : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (halo : 1 / 10 < alo) :
    ∃ C₁ : ℝ, ∀ᶠ x : ℝ in atTop, ∀ d : Data K, Admissible C CX alo ahi g x d → ∀ j k : ℕ,
      ∀ u v r : ℝ, (2 : ℝ) ^ k * 2 ^ j * d.Hm ≤ u → u ≤ 16 * ((2 : ℝ) ^ k * 2 ^ j * d.Hm) →
        d.Hn ≤ v → v ≤ 2 * d.Hn → 0 ≤ r → r ≤ 1 →
      ∀ B N : ℕ, (B : ℝ) ≤ Real.log x ^ 3 → N = 2 * momentPower x →
      ∀ 𝒞 ∈ blockSystems (BirthAddr (K := K) x B N),
        ∑ s, chainMeasure q x d (2 ^ j) (2 ^ k) u v r B N s *
            ‖chainInit x d (2 ^ j) (2 ^ k) u v r B s‖ *
          ∑ h ∈ histories x d (2 ^ j) (2 ^ k) u v r B N,
            ‖chainWeight q A₀ s h‖ * ‖chainInit x d (2 ^ j) (2 ^ k) u v r B (chainEnd s h)‖ *
              ∏ C ∈ 𝒞, (if BlockRealized (births s h) C then 1 else 0) ≤
          Real.log x ^ (C₁ * (N + 1)) *
            (C₁ * Real.exp (-Real.log x ^ alo)) ^ blockRank 𝒞 := by
  set ρ := pendingWeight q with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hq _
  have hρ1 : ρ < 1 := Real.rpow_lt_one hq.le hq₁ (by norm_num)
  have hρ2 : ρ ^ 2 < 1 := pow_lt_one₀ hρ0.le hρ1 (by norm_num)
  set w := 1 - ρ ^ 2 with hw
  have hw0 : 0 < w := by linarith
  have hw1 : w ≤ 1 := by have := pow_nonneg hρ0.le 2; linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set v₀ := ((K : ℝ) + 1) / (ρ * w) with hv
  have hv₀ : 0 < v₀ := by positivity
  have hv₁ : 1 ≤ v₀ := by
    rw [hv, le_div_iff₀ (by positivity)]
    have : ρ * w ≤ 1 * 1 := mul_le_mul hρ1.le hw1 hw0.le zero_le_one
    linarith
  -- `M/ρ/v₀ ≤ w` for `M ≤ K + 1`
  have hdiv : ∀ M : ℝ, 0 ≤ M → M ≤ K + 1 → M / ρ / v₀ ≤ w := by
    intro M hM0 hM
    rw [div_div, show ρ * v₀ = ((K : ℝ) + 1) / w by rw [hv]; field_simp, div_div_eq_mul_div,
      div_le_iff₀ (by positivity)]
    calc M * w ≤ ((K : ℝ) + 1) * w := mul_le_mul_of_nonneg_right hM hw0.le
      _ = w * ((K : ℝ) + 1) := mul_comm _ _
  set cG := v₀ * K / ρ with hcG
  have hcG0 : 0 ≤ cG := by positivity
  set c₀ := 1 + cG with hc₀def
  have hc₀ : 1 ≤ c₀ := by linarith
  set RG := Real.exp (v₀ * (2 * K / ρ)) with hRG
  set A₁ := (2 * v₀) ^ K * 6 ^ K * 848 with hA₁
  set e := 3 * (K : ℝ) + 3 * |A₀| + 1 with he
  have he0 : 0 ≤ e := by positivity
  refine ⟨max (e + 2) (4 * c₀ ^ 2 * (4 * K + 1)), ?_⟩
  filter_upwards [eventually_harmonicMass_band halo.le, eventually_two_mul_add_one_le halo,
    Real.tendsto_log_atTop.eventually_ge_atTop (max (max 1 ((4 : ℝ) ^ K)) (max RG A₁)),
    eventually_gt_atTop (0 : ℝ)]
    with x hV hbig hL hx0 d hd j k u v r _ _ _ _ _ _ B N hB hN 𝒞 h𝒞
  set C₁ := max (e + 2) (4 * c₀ ^ 2 * (4 * K + 1)) with hC₁
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := le_of_max_le_left (le_of_max_le_left hL)
  have hL4 : (4 : ℝ) ^ K ≤ L := le_of_max_le_right (le_of_max_le_left hL)
  have hLG : RG ≤ L := le_of_max_le_left (le_of_max_le_right hL)
  have hLA : A₁ ≤ L := le_of_max_le_right (le_of_max_le_right hL)
  have hL0 : 0 < L := by linarith
  -- the band facts
  have hV₀ : ∀ i, 1 / 2 ≤ harmonicMass (band x (d.a i)) := fun i => (hV _ (hd.window i).1).1
  have hV₁ : ∀ i, harmonicMass (band x (d.a i)) ≤ 1 := fun i => (hV _ (hd.window i).1).2
  have hb : ∀ p ∈ bandPrimes x d, 1 / 2 ≤ baseline q N p := fun p hp =>
    half_le_baseline hq hq₁ (hN ▸ hbig d hd p hp)
  have hν : ∀ p, 0 ≤ primeWeight q x d N p := primeWeight_nonneg hb
  have hνi : ∀ i, ∑ p ∈ band x (d.a i), primeWeight q x d N p ≤ 4 := fun i =>
    calc ∑ p ∈ band x (d.a i), primeWeight q x d N p
        ≤ ∑ p ∈ band x (d.a i), 4 * (1 / (p : ℝ)) :=
          sum_le_sum fun p hp => (primeWeight_le hV₀ hb (mem_biUnion.2 ⟨i, mem_univ i, hp⟩)).1
      _ = 4 * harmonicMass (band x (d.a i)) := (mul_sum _ _ _).symm
      _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left (hV₁ i) (by norm_num)
      _ = 4 := mul_one 4
  have hVp : ∀ i, ∀ p ∈ band x (d.a i), 1 / 2 ≤ primeMass x d p := fun i p hp =>
    half_le_primeMass hV₀ hp
  have hνS : ∑ p ∈ bandPrimes x d, primeWeight q x d N p ≤ 4 * K :=
    calc ∑ p ∈ bandPrimes x d, primeWeight q x d N p
        ≤ ∑ p ∈ bandPrimes x d, 4 * (1 / (p : ℝ)) :=
          sum_le_sum fun p hp => (primeWeight_le hV₀ hb hp).1
      _ = 4 * ∑ p ∈ bandPrimes x d, (1 : ℝ) / p := (mul_sum _ _ _).symm
      _ ≤ 4 * K := mul_le_mul_of_nonneg_left (sum_one_div_bandPrimes_le hV₁) (by norm_num)
  -- the atom: band primes exceed `exp(L^{α₋})`
  set Δ := 4 * Real.exp (-L ^ alo) with hΔdef
  have hΔ : ∀ p ∈ bandPrimes x d, primeWeight q x d N p ≤ Δ := by
    intro p hp
    obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
    have hp1 : Real.exp (L ^ alo) ≤ p :=
      (Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (hd.window i).1)).trans
        (exp_le_of_mem_band hpi)
    calc primeWeight q x d N p ≤ 4 * (1 / p) := (primeWeight_le hV₀ hb hp).1
      _ ≤ 4 * (1 / Real.exp (L ^ alo)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (Real.exp_pos _) hp1)
            (by norm_num)
      _ = Δ := by rw [hΔdef, Real.exp_neg, one_div]
  -- the ghost rows
  have hG : ∀ (jj : Fin (N + 1)) (πg : Fin B → Option ℕ)
      (t : ChainState x d (2 ^ j) (2 ^ k) u v r B),
      ∑ c ∈ multBox B ×ˢ multBox B,
          ‖chainGhostCoef q x d (2 ^ j) (2 ^ k) u v r B N jj t c‖ *
          (∏ kk : Fin B, presInd (πg kk) (batchPrimes x d c.2)[kk.1]?) *
          v₀ ^ memSize (chainGhostOut x d (2 ^ j) (2 ^ k) u v r B t c).2.2.1 ≤
        RG * (∏ kk, atomCost c₀ (primeWeight q x d N) (πg kk)) * v₀ ^ memSize t.2.2.1 := by
    intro jj πg t
    obtain ⟨hη0, hη1⟩ := dampDefect_mem_Icc hq hq₁ N jj
    have hsurv0 : 0 ≤ (1 - dampDefect q N jj) / ρ ^ 2 := div_nonneg (by linarith) (by positivity)
    have hsurv1 : (1 - dampDefect q N jj) / ρ ^ 2 ≤ ρ ^ 2 := by
      have hqs : q ≤ Real.sqrt q := by
        have h₁ := Real.mul_self_sqrt hq.le
        have h₂ : Real.sqrt q ≤ 1 := Real.sqrt_le_one.2 hq₁.le
        calc q = Real.sqrt q * Real.sqrt q := h₁.symm
          _ ≤ Real.sqrt q * 1 := mul_le_mul_of_nonneg_left h₂ (Real.sqrt_nonneg q)
          _ = Real.sqrt q := mul_one _
      have hqj : 1 - dampDefect q N jj ≤ ρ ^ 4 := by
        rw [hρ, pendingWeight_pow_four hq]
        unfold dampDefect
        split_ifs <;> linarith
      rw [div_le_iff₀ (by positivity)]
      calc 1 - dampDefect q N jj ≤ ρ ^ 4 := hqj
        _ = ρ ^ 2 * ρ ^ 2 := by ring
    have hdel : |-dampDefect q N jj / ρ| ≤ 1 / ρ := by
      rw [abs_div, abs_neg, abs_of_nonneg hη0, abs_of_pos hρ0]
      exact div_le_div_of_nonneg_right hη1 hρ0.le
    have hdelj : (1 - dampDefect q N jj) / ρ ^ 2 + |-dampDefect q N jj / ρ| / v₀ ≤ 1 :=
      calc (1 - dampDefect q N jj) / ρ ^ 2 + |-dampDefect q N jj / ρ| / v₀
          ≤ ρ ^ 2 + 1 / ρ / v₀ := add_le_add hsurv1 (div_le_div_of_nonneg_right hdel hv₀.le)
        _ ≤ ρ ^ 2 + w := add_le_add le_rfl (hdiv 1 zero_le_one (by linarith))
        _ = 1 := by rw [hw]; ring
    have hcre : ∀ p, |-dampDefect q N jj * primeMass x d p / ρ| =
        dampDefect q N jj / ρ * primeMass x d p := by
      intro p
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hη0, abs_of_nonneg (primeMass_nonneg p),
        abs_of_pos hρ0]
      ring
    have hη : dampDefect q N jj / ρ ≤ 1 / ρ := div_le_div_of_nonneg_right hη1 hρ0.le
    have hcGj : ∀ xp : Particle x d, |-dampDefect q N jj * primeMass x d xp.1.1 / ρ| *
        primeWeight q x d N xp.1.1 * v₀ ≤ cG * primeWeight q x d N xp.1.1 := by
      intro xp
      have hcreK : |-dampDefect q N jj * primeMass x d xp.1.1 / ρ| ≤ K / ρ := by
        rw [hcre]
        calc dampDefect q N jj / ρ * primeMass x d xp.1.1 ≤ 1 / ρ * K :=
              mul_le_mul hη (primeMass_le hV₁ _) (primeMass_nonneg _) (by positivity)
          _ = K / ρ := by ring
      calc |-dampDefect q N jj * primeMass x d xp.1.1 / ρ| * primeWeight q x d N xp.1.1 * v₀
          ≤ K / ρ * primeWeight q x d N xp.1.1 * v₀ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcreK (hν _)) hv₀.le
        _ = cG * primeWeight q x d N xp.1.1 := by rw [hcG]; ring
    have hsum : Real.exp (v₀ * ∑ xp with HitsAt x d t.1.1 xp,
        |-dampDefect q N jj * primeMass x d xp.1.1 / ρ| * primeWeight q x d N xp.1.1) ≤ RG := by
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hv₀.le)
      calc ∑ xp with HitsAt x d t.1.1 xp,
            |-dampDefect q N jj * primeMass x d xp.1.1 / ρ| * primeWeight q x d N xp.1.1
          ≤ ∑ xp with HitsAt x d t.1.1 xp, 2 / ρ * (1 / (xp.1.1 : ℝ)) := by
            refine sum_le_sum fun xp _ => ?_
            have h := (primeWeight_le hV₀ hb (fst_mem_bandPrimes xp)).2
            rw [hcre]
            calc dampDefect q N jj / ρ * primeMass x d xp.1.1 * primeWeight q x d N xp.1.1
                = dampDefect q N jj / ρ * (primeMass x d xp.1.1 * primeWeight q x d N xp.1.1) :=
                  mul_assoc _ _ _
              _ ≤ 1 / ρ * (2 * (1 / (xp.1.1 : ℝ))) :=
                  mul_le_mul hη h (mul_nonneg (primeMass_nonneg _) (hν _)) (by positivity)
              _ = 2 / ρ * (1 / (xp.1.1 : ℝ)) := by ring
        _ ≤ ∑ p ∈ bandPrimes x d, 2 / ρ * (1 / (p : ℝ)) :=
            sum_hits_le_sum_bandPrimes t.1.1 (f := fun p => 2 / ρ * (1 / (p : ℝ)))
              fun p => by positivity
        _ = 2 / ρ * ∑ p ∈ bandPrimes x d, (1 : ℝ) / p := (mul_sum _ _ _).symm
        _ ≤ 2 / ρ * K := mul_le_mul_of_nonneg_left (sum_one_div_bandPrimes_le hV₁) (by positivity)
        _ = 2 * K / ρ := by ring
    refine (sum_chainGhost_pres_le hν hsurv0 hv₀ hcG0 hdelj hcGj πg t).trans ?_
    have hprod : ∏ kk, atomCost cG (primeWeight q x d N) (πg kk) ≤
        ∏ kk, atomCost c₀ (primeWeight q x d N) (πg kk) :=
      prod_le_prod₀ (fun kk _ => atomCost_nonneg hcG0 hν _)
        fun kk _ => atomCost_mono (by linarith) hν _
    calc (∏ kk, atomCost cG (primeWeight q x d N) (πg kk)) *
          (Real.exp (v₀ * ∑ xp with HitsAt x d t.1.1 xp,
            |-dampDefect q N jj * primeMass x d xp.1.1 / ρ| * primeWeight q x d N xp.1.1) *
            v₀ ^ memSize t.2.2.1)
        ≤ (∏ kk, atomCost c₀ (primeWeight q x d N) (πg kk)) * (RG * v₀ ^ memSize t.2.2.1) :=
          mul_le_mul hprod (mul_le_mul_of_nonneg_right hsum (pow_nonneg hv₀.le _))
            (mul_nonneg (Real.exp_pos _).le (pow_nonneg hv₀.le _))
            (prod_nonneg fun kk _ => atomCost_nonneg (by linarith) hν _)
      _ = RG * (∏ kk, atomCost c₀ (primeWeight q x d N) (πg kk)) * v₀ ^ memSize t.2.2.1 := by
          ring
  -- the edge rows
  set RE := v₀ ^ K * 2 ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀))) with hRE
  have hRE0 : 0 ≤ RE := by positivity
  have hU : 0 < (2 : ℝ) ^ k * 2 ^ j * d.Hm := by
    have h₁ := hd.Hm_ge
    have h₂ : 0 < x ^ d.γ := Real.rpow_pos_of_pos hx0 _
    have : 0 < d.Hm := by linarith
    positivity
  have hE : ∀ (πe : Fin K → Option ℕ) (t : ChainState x d (2 ^ j) (2 ^ k) u v r B),
      ∑ e ∈ edgeChoices x d (2 ^ j) (2 ^ k) u v r,
          ‖chainEdgeCoef q A₀ x d (2 ^ j) (2 ^ k) u v r B N t e‖ *
          (∏ i, presInd (πe i) (if (e.2.2.2.1 i).2 then none else some (e.2.2.2.1 i).1)) *
          v₀ ^ memSize (chainEdgeOut x d (2 ^ j) (2 ^ k) u v r B t e).2.2.1 ≤
        RE * (∏ i, atomCost c₀ (primeWeight q x d N) (πe i)) * v₀ ^ memSize t.2.2.1 :=
    fun πe t => sum_chainEdge_pres_le hq hq₁ (by positivity) (one_le_pow₀ (by norm_num)) hU hL0
      hν hνi hVp hv₁ hc₀ πe t
  refine (sum_history_realized_le hν hνi hνS (by positivity) hΔ hv₁ hc₀ (Real.exp_pos _).le
    hRE0 hG hE h𝒞).trans ?_
  -- the numerics: `M ≤ N`, `B ≤ L³`, and the constants below `L`
  have hMN : padCount x ≤ N := by
    have h₁ : (padCount x : ℝ) ≤ L ^ (1 / 100 : ℝ) := Nat.floor_le (by positivity)
    have h₂ : L ^ (1 / 100 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h₃ : L ^ (1 / 2 : ℝ) / 2 ≤ momentPower x := Nat.le_ceil _
    have : (padCount x : ℝ) ≤ N := by
      rw [hN]
      push_cast
      linarith
    exact_mod_cast this
  have h4 : (4 : ℝ) ^ (K * (padCount x + 1)) ≤ L ^ (N + 1) :=
    calc (4 : ℝ) ^ (K * (padCount x + 1)) = ((4 : ℝ) ^ K) ^ (padCount x + 1) := pow_mul _ _ _
      _ ≤ L ^ (padCount x + 1) := pow_le_pow_left₀ (by positivity) hL4 _
      _ ≤ L ^ (N + 1) := pow_le_pow_right₀ hL1 (by omega)
  have hGN : RG ^ (N + 1) ≤ L ^ (N + 1) := pow_le_pow_left₀ (Real.exp_pos _).le hLG _
  have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
  have hA0 : 1 ≤ L ^ (3 * |A₀|) := Real.one_le_rpow hL1 (by positivity)
  have hA1 : L ^ (3 * A₀) ≤ L ^ (3 * |A₀|) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_abs_self A₀])
  have hREe : RE ≤ L ^ e :=
    calc RE = (2 * v₀) ^ K * (2 * B + 4) ^ K * (16 * (1 + 52 * L ^ (3 * A₀))) := by
          rw [hRE, mul_pow]
          ring
      _ ≤ (2 * v₀) ^ K * (6 * L ^ 3) ^ K * (16 * (53 * L ^ (3 * |A₀|))) := by
          have h₁ : (2 * (B : ℝ) + 4) ^ K ≤ (6 * L ^ 3) ^ K :=
            pow_le_pow_left₀ (by positivity) (by linarith) _
          have h₂ : 16 * (1 + 52 * L ^ (3 * A₀)) ≤ 16 * (53 * L ^ (3 * |A₀|)) := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₂ (by positivity)
            (by positivity)
      _ = A₁ * ((L ^ 3) ^ K * L ^ (3 * |A₀|)) := by
          rw [hA₁, mul_pow 6]
          ring
      _ ≤ L * ((L ^ 3) ^ K * L ^ (3 * |A₀|)) := mul_le_mul_of_nonneg_right hLA (by positivity)
      _ = L ^ e := by
          rw [he, Real.rpow_add hL0, Real.rpow_add hL0, ← pow_mul,
            show 3 * (K : ℝ) = ((3 * K : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            Real.rpow_one]
          ring
  have hEN : RE ^ N ≤ L ^ (e * N) := by
    rw [Real.rpow_mul_natCast hL0.le]
    exact pow_le_pow_left₀ hRE0 hREe _
  have hTot : (4 : ℝ) ^ (K * (padCount x + 1)) * RG ^ (N + 1) * RE ^ N ≤ L ^ (C₁ * (N + 1)) := by
    have hN1 : (L ^ (N + 1) : ℝ) = L ^ ((N : ℝ) + 1) := by
      rw [← Real.rpow_natCast]
      push_cast
      ring_nf
    calc (4 : ℝ) ^ (K * (padCount x + 1)) * RG ^ (N + 1) * RE ^ N
        ≤ L ^ (N + 1) * L ^ (N + 1) * L ^ (e * N) :=
          mul_le_mul (mul_le_mul h4 hGN (pow_nonneg (Real.exp_pos _).le _) (by positivity))
            hEN (pow_nonneg hRE0 _) (by positivity)
      _ = L ^ (((N : ℝ) + 1) + ((N : ℝ) + 1) + e * N) := by
          rw [hN1, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      _ ≤ L ^ (C₁ * (N + 1)) := by
          refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
          have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have h₁ : ((N : ℝ) + 1) + ((N : ℝ) + 1) + e * N = (e + 2) * (N + 1) - e := by ring
          have h₂ : (e + 2) * ((N : ℝ) + 1) ≤ C₁ * (N + 1) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          linarith
  have hpow : (c₀ ^ 2 * (4 * K + 1) * Δ) ^ blockRank 𝒞 ≤
      (C₁ * Real.exp (-L ^ alo)) ^ blockRank 𝒞 := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [hΔdef, show c₀ ^ 2 * (4 * K + 1) * (4 * Real.exp (-L ^ alo)) =
      (4 * c₀ ^ 2 * (4 * K + 1)) * Real.exp (-L ^ alo) by ring]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  exact mul_le_mul hTot hpow (by positivity) (by positivity)

end Erdos408.OneSided
