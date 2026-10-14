module

public import Erdos408.TwoSided.Endpoint.Factor.Bounds
public import Erdos408.TwoSided.Endpoint.Low
public import Mathlib.Data.Fin.Tuple.Finset

/-!
# Small-prime removal and the spare-slot factorization

S13–S14 of `blueprint/two_sided_correlation.md` §6.3 (PD (6.30)–(6.32); WD §5.4; O2, O4). Fix
a small group `g_s ∉ big`, so `S g_s = {last}` for `S = unsharedSlots C`.

* E3: if no `p ∈ P_{g_s}` has `p² ∣ w`, then
  `W_S^b(w) = V_{g_s}⁻¹ ∑_{p_s ∈ P_{g_s}, p_s ∣ w} W_{S'}^b(w/p_s)`, with `S' g_s = ∅`, since
  `b` ignores the small labels.
* E4: replace `f_B` by the count `f̃_B` over all tuples (repetitions allowed); they differ
  only on `w` with `q² ∣ w` for a slot prime `q > x^ε`.
* E5: `f̃_B(w) = ∑_{p_l ∣ w} 𝒜_B(w/p_l)` exactly, where `p_l` runs over the spare-slot
  primes and `𝒜_B(u) = ∑_{Q'} B(Q') [∏ Q' ∣ u]`; `B` reads `Fin.init` (O4).

So the first endpoint is `𝒰_tup - 𝒰_con` off a sparse exceptional set, with
`𝒰_tup(w) = ψ₁(w/Y) w^{iσ} V⁻¹ ∑_{p_s p_l u = w} c(u)`, `c = 𝒲 W_{S'}^b 𝒜_B` (PD (6.31) with
the spare slot as `p_l`), and `𝒰_con(w) = ψ₁(w/Y) w^{iσ} C_B V⁻¹ ∑_{p_s n = w} 𝒲 W_{S'}^b (n)`.

The removal identity E3 and the scale separation are in `Factor/Identity.lean`; the pointwise
bounds (U6; U7 and U9 are in `Setup.lean`) and the mean value theorem used for the exceptional
positions are in `Factor/Bounds.lean`.
-/

@[expose] public section

namespace Erdos408.TwoSided

open Filter

/-- The spare-slot primes `x^{u_d} < p ≤ x^{v_d}` of the last slot. -/
noncomputable def sparePrimes (x : ℝ) {d : ℕ} (u v : Fin (d + 1) → ℝ) : Finset ℕ :=
  (Finset.Iic ⌊x ^ v (Fin.last d)⌋₊).filter fun p : ℕ => p.Prime ∧ x ^ u (Fin.last d) < p

/-- `𝒜_B(n) = ∑_{Q'} B(Q') [∏ Q' ∣ n]` over all tuples of primes of the weighted slots,
repetitions allowed (E5). -/
noncomputable def weightedSlotCount (x : ℝ) {d : ℕ} (u v : Fin (d + 1) → ℝ)
    (Bc : (Fin d → ℕ) → ℝ) (n : ℕ) : ℝ :=
  ∑ Q ∈ (Fintype.piFinset fun i : Fin d =>
      (Finset.Iic ⌊x ^ v i.castSucc⌋₊).filter fun p : ℕ => p.Prime ∧ x ^ u i.castSucc < p) with
      ∏ i, Q i ∣ n,
    Bc Q

/-- The tuple part (PD (6.31)) of the first endpoint:
`𝒰_tup(w) = ψ₁(w/Y) w^{iσ} V_{g_s}⁻¹ ∑_{p_s p_l u = w} 𝒲(u) 𝒜_B(u) W_{S'}^b(u)`, with
`p_s ∈ P_{g_s}`, `p_l` a spare-slot prime and `S' = S` except `S' g_s = ∅`. -/
noncomputable def tupleCoeff (x q q₀ : ℝ) {r d : ℕ} (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ)
    (Bc : (Fin d → ℕ) → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    {J : ℕ} (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ) (gs : ι)
    (ψ₁ : ℝ → ℂ) (Y σ : ℝ) (w : ℕ) : ℂ :=
  ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (((harmonicMass (P gs))⁻¹ : ℝ) : ℂ) *
    ∑ ps ∈ (P gs).filter (· ∣ w), ∑ pl ∈ (sparePrimes x u v).filter (· ∣ w / ps),
      ((markedWeight Finset.univ q (fun i => band x (a i)) (w / ps / pl) *
          weightedSlotCount x u v Bc (w / ps / pl) : ℝ) : ℂ) *
        markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b (w / ps / pl)

/-- The constant part of the first endpoint:
`𝒰_con(w) = ψ₁(w/Y) w^{iσ} C_B V_{g_s}⁻¹ ∑_{p_s n = w} 𝒲(n) W_{S'}^b(n)`. -/
noncomputable def constCoeff (x q q₀ : ℝ) {r d : ℕ} (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ)
    (Bc : (Fin d → ℕ) → ℝ) {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ)
    {J : ℕ} (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ) (gs : ι)
    (ψ₁ : ℝ → ℂ) (Y σ : ℝ) (w : ℕ) : ℂ :=
  ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) *
    ((slotMean x u v Bc / harmonicMass (P gs) : ℝ) : ℂ) *
    ∑ ps ∈ (P gs).filter (· ∣ w),
      (markedWeight Finset.univ q (fun i => band x (a i)) (w / ps) : ℂ) *
        markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b (w / ps)

/-- **E4–E5.** If no slot prime `q` has `q² ∣ w`, then
`f_B(w) = ∑_{p_l ∣ w} 𝒜_B(w / p_l)` over the spare-slot primes: a tuple dividing `w` has
distinct entries, and `B` reads `Fin.init`. -/
theorem slotCount_eq_sum_sparePrimes {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (u v : Fin (d + 1) → ℝ)
    (Bc : (Fin d → ℕ) → ℝ) {w : ℕ}
    (hsq : ∀ p : ℕ, p.Prime → (∃ i, x ^ u i < p ∧ (p : ℝ) ≤ x ^ v i) → ¬ p ^ 2 ∣ w) :
    slotCount x u v Bc w =
      ∑ pl ∈ (sparePrimes x u v).filter (· ∣ w), weightedSlotCount x u v Bc (w / pl) := by
  set s : Fin (d + 1) → Finset ℕ := fun i =>
    (Finset.Iic ⌊x ^ v i⌋₊).filter fun p : ℕ => p.Prime ∧ x ^ u i < p with hs
  -- a tuple dividing `w` is injective
  have hinj : ∀ Q ∈ Fintype.piFinset s, ∏ i, Q i ∣ w → Function.Injective Q := by
    intro Q hQ hdvd i i' hii'
    by_contra hne
    have hQi := Finset.mem_filter.1 (Fintype.mem_piFinset.1 hQ i)
    refine hsq (Q i) hQi.2.1 ⟨i, hQi.2.2,
      (Nat.le_floor_iff (Real.rpow_nonneg hx _)).1 (Finset.mem_Iic.1 hQi.1)⟩ ?_
    have hpair : Q i * Q i' ∣ ∏ k, Q k := by
      rw [← Finset.prod_pair hne]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    rw [pow_two]
    nth_rewrite 2 [hii']
    exact hpair.trans hdvd
  have hall : (slotTuples x u v).filter (fun Q => ∏ i, Q i ∣ w) =
      (Fintype.piFinset s).filter (fun Q => ∏ i, Q i ∣ w) := by
    ext Q
    simp only [slotTuples, Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hinj Q h.1 h.2⟩, h.2⟩⟩
  -- split off the spare slot
  have hR : ∑ pl ∈ (sparePrimes x u v).filter (· ∣ w), weightedSlotCount x u v Bc (w / pl) =
      ∑ y ∈ s (Fin.last d) ×ˢ Fintype.piFinset (Fin.init s),
        if y.1 ∣ w ∧ ∏ i, y.2 i ∣ w / y.1 then Bc y.2 else 0 := by
    rw [Finset.sum_product, sparePrimes, Finset.sum_filter]
    refine Finset.sum_congr rfl fun pl _ => ?_
    unfold weightedSlotCount
    rw [Finset.sum_filter]
    split_ifs with h
    · exact Finset.sum_congr rfl fun Q _ => by simp only [h, true_and]
    · exact (Finset.sum_eq_zero fun Q _ => by simp only [h, false_and, ite_false]).symm
  unfold slotCount
  rw [hR, hall, Finset.sum_filter]
  refine Finset.sum_nbij' (fun Q => (Q (Fin.last d), Fin.init Q))
    (fun y => Fin.snoc y.2 y.1) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ
    exact Finset.mem_product.2 (Fin.mem_piFinset_iff_last_init.1 hQ)
  · intro y hy
    rw [Finset.mem_product] at hy
    rw [Fin.mem_piFinset_iff_last_init, Fin.snoc_last, Fin.init_snoc]
    exact hy
  · intro Q _
    exact Fin.snoc_init_self Q
  · intro y _
    simp only [Fin.snoc_last, Fin.init_snoc]
  · intro Q _
    rw [Fin.prod_univ_castSucc]
    refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
    · have hl : Q (Fin.last d) ∣ w := (dvd_mul_left _ _).trans h
      refine ⟨hl, (Nat.dvd_div_iff_mul_dvd hl).2 ?_⟩
      rw [mul_comm]
      exact h
    · rw [mul_comm]
      exact (Nat.dvd_div_iff_mul_dvd h.1).1 h.2

/-- `|𝒜_B(n)| ≤ (2/ε)^d` for `0 < n ≤ x²`, when the slots start above `x^ε` and `|B| ≤ 1`. -/
theorem abs_weightedSlotCount_le {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε) {d : ℕ}
    {u v : Fin (d + 1) → ℝ} (hu : ∀ i, ε ≤ u i) {Bc : (Fin d → ℕ) → ℝ}
    (hB : ∀ Q, |Bc Q| ≤ 1) {n : ℕ} (hn : 0 < n) (hnx : (n : ℝ) ≤ x ^ 2) :
    |weightedSlotCount x u v Bc n| ≤ (2 / ε) ^ d := by
  set F := n.primeFactors.filter fun p : ℕ => x ^ ε < (p : ℝ)
  set T := Fintype.piFinset fun i : Fin d =>
    (Finset.Iic ⌊x ^ v i.castSucc⌋₊).filter fun p : ℕ => p.Prime ∧ x ^ u i.castSucc < p
  have hsub : T.filter (fun Q => ∏ i, Q i ∣ n) ⊆ Fintype.piFinset fun _ => F := by
    intro Q hQ
    obtain ⟨hQ, hdvd⟩ := Finset.mem_filter.1 hQ
    rw [Fintype.mem_piFinset] at hQ ⊢
    intro i
    obtain ⟨-, hp, hlt⟩ := Finset.mem_filter.1 (hQ i)
    exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hp,
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans hdvd, hn.ne'⟩,
      lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx.le (hu i.castSucc)) hlt⟩
  calc |weightedSlotCount x u v Bc n| ≤ ∑ Q ∈ T.filter (fun Q => ∏ i, Q i ∣ n), |Bc Q| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ Q ∈ T.filter (fun Q => ∏ i, Q i ∣ n), (1 : ℝ) := Finset.sum_le_sum fun _ _ => hB _
    _ ≤ (Fintype.piFinset fun _ : Fin d => F).card := by
        rw [Finset.sum_const, nsmul_one]
        exact_mod_cast Finset.card_le_card hsub
    _ = (F.card : ℝ) ^ d := by rw [Fintype.card_piFinset]; simp
    _ ≤ (2 / ε) ^ d :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Sieve.card_primeFactors_gt_le hx hε hn hnx) _

/-- **E3–E5 (exact factorization off the exceptional set).** Eventually, for groups as in
(6.1), a small group `g_s`, all bands, slots and coefficients, every pattern `C` vanishing off
the big groups and every test `b` that ignores the small groups: if `w ≥ 1` has no square
factor `p²` with `p ∈ P_{g_s}` and none `q²` with `q` a slot prime, then
`𝒰(w) = 𝒰_tup(w) - 𝒰_con(w)`. It uses E3, `f_B(w) = f̃_B(w)` (a repeated tuple prime `q`
forces `q² ∣ w`), E5, and the invariance of `𝒲`, `𝒜_B` and `W_{S'}^b` under the active and
spare primes (U3, U8). This is PD (6.30)–(6.31), with the spare slot as `p_l`. -/
theorem eventually_endpointCoeff_eq_tuple_sub_const (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ)
    (K₀ : ℕ) (CN c : ℝ) (d : ℕ) (hahi : ahi < 1 / 5) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big → ∀ gs ∉ big,
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v →
        ∀ (J : ℕ) (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ),
          (∀ g ∉ big, C g = ∅) → (∀ p p', (∀ g ∈ big, p g = p' g) → b p = b p') →
        ∀ (ψ₁ : ℝ → ℂ) (Y σ : ℝ) (w : ℕ), 1 ≤ w →
          (∀ p ∈ P gs, ¬ p ^ 2 ∣ w) →
          (∀ p : ℕ, p.Prime → (∃ i, x ^ u i < p ∧ (p : ℝ) ≤ x ^ v i) → ¬ p ^ 2 ∣ w) →
          endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w =
            tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ w -
              constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ w := by
  filter_upwards [FactorAux.eventually_scales hahi hc, eventually_gt_atTop 0] with x hsc hx
  obtain ⟨hL, -, hband, hslot⟩ := hsc
  intro ι _ _ P big hadm gs hgs r a u v Bc hin hsl J C b hC hb ψ₁ Y σ w hw hsqP hsqQ
  obtain ⟨hPr, hbs, hbandr, hslotr⟩ :=
    FactorAux.scales_of_admissible hx hL hband hslot hadm hin hsl
  set S := unsharedSlots C with hSdef
  set S' := Function.update S gs ∅ with hS'def
  set Fs := (P gs).filter (· ∣ w) with hFs
  set Fl := (sparePrimes x u v).filter (· ∣ w) with hFl
  have hSgs : S gs = {Fin.last J} := by
    rw [hSdef, unsharedSlots, hC gs hgs, Finset.map_empty]
    rfl
  -- the primes of the three kinds are distinct
  have hpl : ∀ pl ∈ Fl, pl.Prime ∧ Real.exp (Real.log x ^ (0.46 : ℝ)) < pl ∧ pl ∣ w := by
    intro pl hpl
    obtain ⟨hpl, hdvd⟩ := Finset.mem_filter.1 hpl
    obtain ⟨-, hp, hlt⟩ := Finset.mem_filter.1 hpl
    exact ⟨hp, (hslotr (Fin.last d)).trans hlt, hdvd⟩
  have hps : ∀ ps ∈ Fs, ps.Prime ∧ Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ ps ∧
      (ps : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) ∧ ps ∣ w := by
    intro ps hps
    obtain ⟨hpsP, hdvd⟩ := Finset.mem_filter.1 hps
    exact ⟨(hPr gs ps hpsP).1, hbs gs hgs ps hpsP, (hPr gs ps hpsP).2, hdvd⟩
  have hne : ∀ {p p' : ℕ}, (p : ℝ) < p' → p ≠ p' := fun h h' => by
    rw [h'] at h
    exact lt_irrefl _ h
  -- band primes see neither `p_s` nor `p_l`
  have hbandp : ∀ i, ∀ p ∈ band x (a i), p.Prime := fun i p hp =>
    (Finset.mem_filter.1 hp).2
  have hW₁ : ∀ ps ∈ Fs, markedWeight Finset.univ q (fun i => band x (a i)) (w / ps) =
      markedWeight Finset.univ q (fun i => band x (a i)) w := by
    intro ps hps'
    obtain ⟨hpsp, hps27, -, hdvd⟩ := hps ps hps'
    refine markedWeight_congr _ _ _ fun i _ p hp => ?_
    exact FactorAux.dvd_div_iff_of_coprime hdvd (FactorAux.coprime_of_prime_ne (hbandp i p hp)
      hpsp (hne ((hbandr i p hp).trans_le hps27)))
  have hplps : ∀ ps ∈ Fs, ∀ pl ∈ Fl, pl ∣ w / ps := by
    intro ps hps' pl hpl'
    obtain ⟨hpsp, -, hps46, hdvd⟩ := hps ps hps'
    obtain ⟨hplp, hpl46, hpldvd⟩ := hpl pl hpl'
    exact (FactorAux.dvd_div_iff_of_coprime hdvd (FactorAux.coprime_of_prime_ne hplp hpsp
      (hne (hps46.trans_lt hpl46)).symm)).2 hpldvd
  have hW₂ : ∀ ps ∈ Fs, ∀ pl ∈ Fl,
      markedWeight Finset.univ q (fun i => band x (a i)) (w / ps / pl) =
        markedWeight Finset.univ q (fun i => band x (a i)) w := by
    intro ps hps' pl hpl'
    obtain ⟨hplp, hpl46, -⟩ := hpl pl hpl'
    rw [← hW₁ ps hps']
    refine markedWeight_congr _ _ _ fun i _ p hp => ?_
    refine FactorAux.dvd_div_iff_of_coprime (hplps ps hps' pl hpl')
      (FactorAux.coprime_of_prime_ne (hbandp i p hp) hplp (hne ?_))
    calc (p : ℝ) < Real.exp (Real.log x ^ (0.27 : ℝ)) := hbandr i p hp
      _ ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) :=
        Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL.le (by norm_num))
      _ < pl := hpl46
  -- the marks of `S'` do not see `p_l`
  have hM : ∀ ps ∈ Fs, ∀ pl ∈ Fl,
      markedListWeight P q₀ S' b (w / ps / pl) = markedListWeight P q₀ S' b (w / ps) := by
    intro ps hps' pl hpl'
    obtain ⟨hplp, hpl46, -⟩ := hpl pl hpl'
    refine markedListWeight_congr _ _ _ fun g p hp => ?_
    exact FactorAux.dvd_div_iff_of_coprime (hplps ps hps' pl hpl')
      (FactorAux.coprime_of_prime_ne (hPr g p hp).1 hplp (hne ((hPr g p hp).2.trans_lt hpl46)))
  -- `𝒜_B` does not see `p_s`
  have hA : ∀ ps ∈ Fs, ∀ pl ∈ Fl,
      weightedSlotCount x u v Bc (w / ps / pl) = weightedSlotCount x u v Bc (w / pl) := by
    intro ps hps' pl hpl'
    obtain ⟨hpsp, -, hps46, hdvd⟩ := hps ps hps'
    obtain ⟨hplp, hpl46, hpldvd⟩ := hpl pl hpl'
    have hpsl : ps ∣ w / pl := (FactorAux.dvd_div_iff_of_coprime hpldvd
      (FactorAux.coprime_of_prime_ne hpsp hplp (hne (hps46.trans_lt hpl46)))).2 hdvd
    rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul]
    unfold weightedSlotCount
    refine Finset.sum_congr (Finset.filter_congr fun Q hQ => ?_) fun _ _ => rfl
    refine FactorAux.dvd_div_iff_of_coprime hpsl (Nat.Coprime.prod_left fun i _ => ?_)
    obtain ⟨-, hQp, hQlt⟩ := Finset.mem_filter.1 (Fintype.mem_piFinset.1 hQ i)
    exact FactorAux.coprime_of_prime_ne hQp hpsp
      (hne (hps46.trans_lt ((hslotr i.castSucc).trans hQlt))).symm
  have hFl' : ∀ ps ∈ Fs, (sparePrimes x u v).filter (· ∣ w / ps) = Fl := by
    intro ps hps'
    obtain ⟨hpsp, -, hps46, hdvd⟩ := hps ps hps'
    refine Finset.filter_congr fun pl hpl' => ?_
    obtain ⟨-, hplp, hlt⟩ := Finset.mem_filter.1 hpl'
    exact FactorAux.dvd_div_iff_of_coprime hdvd (FactorAux.coprime_of_prime_ne hplp hpsp
      (hne (hps46.trans_lt ((hslotr (Fin.last d)).trans hlt))).symm)
  -- E3 and E5
  have hE3 := FactorAux.markedListWeight_eq_removal (fun g p hp => (hPr g p hp).1) hadm.1 q₀
    S b gs (Fin.last J) hSgs (fun p p' h => hb p p' fun g hg => h g fun h' => hgs (h' ▸ hg))
    hsqP
  have hE5 := slotCount_eq_sum_sparePrimes hx.le u v Bc hsqQ
  -- assemble
  have htup : tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ w =
      ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) * (((harmonicMass (P gs))⁻¹ : ℝ) : ℂ) *
        ((∑ ps ∈ Fs, markedListWeight P q₀ S' b (w / ps)) *
          ∑ pl ∈ Fl, ((markedWeight Finset.univ q (fun i => band x (a i)) w *
            weightedSlotCount x u v Bc (w / pl) : ℝ) : ℂ)) := by
    rw [Finset.sum_mul_sum]
    unfold tupleCoeff
    refine congrArg _ (Finset.sum_congr rfl fun ps hps' => ?_)
    rw [hFl' ps hps']
    refine Finset.sum_congr rfl fun pl hpl' => ?_
    rw [hW₂ ps hps' pl hpl', hA ps hps' pl hpl', hM ps hps' pl hpl', mul_comm]
  have hcon : constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ w =
      ψ₁ (w / Y) * (w : ℂ) ^ ((σ : ℂ) * Complex.I) *
        ((slotMean x u v Bc / harmonicMass (P gs) : ℝ) : ℂ) *
        ((markedWeight Finset.univ q (fun i => band x (a i)) w : ℝ) *
          ∑ ps ∈ Fs, markedListWeight P q₀ S' b (w / ps)) := by
    rw [Finset.mul_sum]
    unfold constCoeff
    exact congrArg _ (Finset.sum_congr rfl fun ps hps' => by rw [hW₁ ps hps'])
  rw [htup, hcon]
  unfold endpointCoeff centeredCore
  rw [hE3, hE5, mul_sub, Finset.mul_sum]
  push_cast
  ring

/-- **E3–E4 (the exceptional positions).** There is `C_R` such that, eventually, for all data
as in package E and a small group `g_s`, the mean square over `|t| ≤ T₀ = x L^{C_m + 2}` of
`𝒰 - 𝒰_tup + 𝒰_con` is at most `L^{C_R} (e^{-L^{0.27}} + x^{-ε})`, `x^{-ε} = e^{-cL/T²⁰}`. By
E3–E5 the coefficient vanishes except on `w ∈ [Y, 2Y]` with `p_s² ∣ w` (count
`≤ 4Y e^{-L^{0.27}} v₊`, U1) or `q² ∣ w` for a slot prime (count `≤ 4Y x^{-ε}`), where it is
`≤ L^{C}` (U7, U9, U11); then the mean value theorem over `[-T₀, T₀]` with `T₀/Y ≤ L^{C_m + 2}`
(`FactorAux.integral_norm_twistedPoly_sq_le`). This is the square-exception paragraph after
PD (6.30), and WD (5.12). -/
theorem exists_integral_removal_le (q q₀ c₀ C₀ vlo vhi alo ahi : ℝ) (K₀ : ℕ) (CN c : ℝ)
    (d : ℕ) (hq : 0 < q) (hq₁ : q < 1) (hq₀ : 0 < q₀) (hq₀₁ : q₀ < 1) (hvlo : 0 < vlo)
    (halo : 1 / 10 < alo) (hal : alo ≤ ahi) (hahi : ahi < 1 / 5) (hc : 0 < c) (m₀ : ℕ)
    (Cm : ℝ) (M₁ : ℕ → ℝ) :
    ∃ CR : ℝ, ∀ᶠ x : ℝ in atTop,
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Finset ℕ) (big : Finset ι),
        GroupAdmissible c₀ C₀ vlo vhi x P big → ∀ gs ∉ big,
        ∀ (r : ℕ) (a : Fin r → ℝ) (u v : Fin (d + 1) → ℝ) (Bc : (Fin d → ℕ) → ℝ),
          InertAdmissible K₀ CN alo ahi x a → AdmissibleSlots c x u v → (∀ Q, |Bc Q| ≤ 1) →
        ∀ (J : ℕ) (C : ι → Finset (Fin J)) (b : (ι → Fin (J + 1) → ℕ) → ℂ),
          (∀ g, (C g).card ≤ m₀) → (∀ g ∉ big, C g = ∅) → (∀ p, ‖b p‖ ≤ 1) →
          (∀ p p', (∀ g ∈ big, p g = p' g) → b p = b p') →
        ∀ ψ₁ : ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₁ →
          (∀ y, ψ₁ y ≠ 0 → 1 ≤ y ∧ y ≤ 2) →
          (∀ (j : ℕ) (y : ℝ), ‖iteratedDeriv j ψ₁ y‖ ≤ M₁ j) →
        ∀ (Y σ : ℝ) (k : ℕ) (h : ℤ),
          x * Real.exp (Real.log x ^ (0.38 : ℝ)) ≤ Y →
          Y ≤ x * Real.exp (Real.log x ^ (0.47 : ℝ)) →
          |σ| ≤ Real.log x ^ Cm → 1 ≤ k → (k : ℝ) ≤ Real.log x ^ Cm →
          ∫ t in -(x * Real.log x ^ (Cm + 2))..(x * Real.log x ^ (Cm + 2)),
              ‖twistedPoly Y (fun w => endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ w -
                  tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ w +
                  constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ w) h k t‖ ^ 2 ≤
            Real.log x ^ CR * (Real.exp (-Real.log x ^ (0.27 : ℝ)) +
              Real.exp (-(c * Real.log x / Real.log (Real.log x) ^ 20))) := by
  obtain ⟨K, hK1, hKW⟩ := exists_norm_markedListWeight_le_pow hq₀ hq₀₁ hvlo m₀
  set a₁ := |Real.log (2 / (1 - q))| with ha₁
  set a₂ := |2 * C₀ * Real.log K| with ha₂
  set D : ℝ := (M₁ 0 * (2 + 2 / vlo)) ^ 2 * 4 ^ (6 * (d + 2)) with hD
  set E : ℝ := ((6 * (d + 2) : ℕ) : ℝ) + 2 * a₁ + 2 * a₂ + 1 with hE
  refine ⟨|Cm| + 3 + E, ?_⟩
  filter_upwards [eventually_endpointCoeff_eq_tuple_sub_const q q₀ c₀ C₀ vlo vhi alo ahi K₀ CN c
      d hahi hc, FactorAux.eventually_scales hahi hc,
    OneSided.eventually_harmonicMass_band halo.le, FactorAux.eventually_inert_le K₀ CN,
    FactorAux.eventually_slot_ratio_le hc, FactorAux.eventually_two_exp_le,
    Real.tendsto_log_atTop.eventually_ge_atTop D,
    Real.tendsto_log_atTop.eventually_ge_atTop (100 * max vhi 2), eventually_gt_atTop 1]
    with x hid hsc hVb hr hslr hexp hDL hvL hx
  intro ι _ _ P big hadm gs hgs r a u v Bc hin hsl hBc J C b hC hCb hb hbb ψ₁ hψ hψs hψd Y σ k
    h hY₁ hY₂ hσ hk₁ hk₂
  obtain ⟨hL, hT, -, -⟩ := hsc
  set L := Real.log x with hLdef
  set T := Real.log L with hTdef
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  set ε := c / T ^ 20 with hεdef
  have hε : 0 < ε := by positivity
  have hu : ∀ i, ε ≤ u i := fun i => by
    have := hsl.1 i
    unfold logLog at this
    exact this
  have hv1 : ∑ i, v i ≤ 1 := by
    have := hsl.2
    unfold logLog at this
    linarith
  -- the scale `Y`
  have hxY : x ≤ Y :=
    le_trans (le_mul_of_one_le_right hx0.le (Real.one_le_exp (by positivity))) hY₁
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have h2Y : 2 * Y ≤ x ^ 2 := by
    calc 2 * Y ≤ 2 * (x * Real.exp (L ^ (0.47 : ℝ))) := by linarith
      _ = x * (2 * Real.exp (L ^ (0.47 : ℝ))) := by ring
      _ ≤ x * x := mul_le_mul_of_nonneg_left hexp hx0.le
      _ = x ^ 2 := (sq x).symm
  set N := ⌊2 * Y⌋₊ with hNdef
  have hN : (N : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := Nat.le_floor (by norm_num; linarith)
  -- the pieces of the coefficient bound
  set Λ : ℝ := (4 * L) ^ (d + 2) with hΛ
  have h4L : 1 ≤ 4 * L := by linarith
  have hΛ1 : 1 ≤ Λ := one_le_pow₀ h4L
  have hpowΛ : ∀ y : ℝ, 0 ≤ y → y ≤ 4 * L → ∀ n ≤ d + 2, y ^ n ≤ Λ := fun y hy hyL n hn =>
    (pow_le_pow_left₀ hy hyL n).trans (pow_le_pow_right₀ h4L hn)
  have hratio : 2 / ε ≤ 4 * L := by linarith
  have hM0 : 0 ≤ M₁ 0 := (norm_nonneg _).trans (hψd 0 0)
  have hψb : ∀ y, ‖ψ₁ y‖ ≤ M₁ 0 := fun y => by simpa using hψd 0 y
  have hcpow : ∀ w : ℕ, 0 < w → ‖(w : ℂ) ^ ((σ : ℂ) * Complex.I)‖ = 1 := by
    intro w hw
    rw [Complex.norm_natCast_cpow_of_pos hw]
    simp
  -- U7: the inert weight
  have hW : ∀ n, 0 ≤ markedWeight Finset.univ q (fun i => band x (a i)) n ∧
      markedWeight Finset.univ q (fun i => band x (a i)) n ≤ L ^ a₁ := by
    intro n
    obtain ⟨h₀, h₁⟩ := markedWeight_bands_le hq hq₁ a
      (fun i => (hVb (a i) (hin.2.1 i).1).1) n
    refine ⟨h₀, h₁.trans ?_⟩
    have hK : 1 ≤ 2 / (1 - q) := by rw [le_div_iff₀ (by linarith)]; linarith
    calc (2 / (1 - q)) ^ r ≤ L ^ (1 * Real.log (2 / (1 - q))) :=
          pow_le_rpow_mul_log hK hL0 (by rw [one_mul]; linarith [hin.1])
      _ ≤ L ^ a₁ :=
          Real.rpow_le_rpow_of_exponent_le hL.le (by rw [one_mul]; exact le_abs_self _)
  -- U9: the marked list weights
  have hcardι : (Fintype.card ι : ℝ) ≤ 2 * C₀ * T := by
    have h₁ := hadm.2.2.1
    have h₂ := hadm.2.2.2.2.1
    have : Fintype.card ι = (Finset.univ \ big).card + big.card := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    rw [this]
    push_cast
    linarith
  have hMW : ∀ S : ι → Finset (Fin (J + 1)), (∀ g, (S g).card ≤ m₀ + 1) →
      ∀ n, ‖markedListWeight P q₀ S b n‖ ≤ L ^ a₂ := by
    intro S hS n
    refine (hKW P (fun g => (hadm.2.2.2.2.2.1 g).1) (J + 1) S b hS hb n).trans ?_
    calc K ^ Fintype.card ι ≤ L ^ (2 * C₀ * Real.log K) :=
          pow_le_rpow_mul_log hK1 hL0 hcardι
      _ ≤ L ^ a₂ := Real.rpow_le_rpow_of_exponent_le hL.le (le_abs_self _)
  have hS : ∀ g, (unsharedSlots C g).card ≤ m₀ + 1 := fun g => by
    rw [card_unsharedSlots]; exact Nat.add_le_add_right (hC g) 1
  have hS' : ∀ g, (Function.update (unsharedSlots C) gs ∅ g).card ≤ m₀ + 1 := by
    intro g
    rcases eq_or_ne g gs with rfl | hg
    · rw [Function.update_self, Finset.card_empty]
      exact Nat.zero_le _
    · rw [Function.update_of_ne hg]
      exact hS g
  -- the slot statistics and the prime factor counts
  have hf : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x ^ 2 → |slotCount x u v Bc n| ≤ Λ := fun n hn hnx =>
    (Sieve.abs_slotCount_le hx hε hu hBc hn hnx).trans
      (hpowΛ _ (by positivity) hratio _ (by omega))
  have hA : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x ^ 2 → |weightedSlotCount x u v Bc n| ≤ Λ :=
    fun n hn hnx => (abs_weightedSlotCount_le hx hε hu hBc hn hnx).trans
      (hpowΛ _ (by positivity) hratio _ (by omega))
  have hCB : |slotMean x u v Bc| ≤ Λ :=
    (FactorAux.abs_slotMean_le hx hv1 hBc).trans
      (hpowΛ _ (by linarith) (by linarith) _ (by omega))
  have hω : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x ^ 2 → (n.primeFactors.card : ℝ) ≤ Λ :=
    fun n hn hnx => (FactorAux.card_primeFactors_le_four_mul_log hx hn hnx).trans
      (by simpa using hpowΛ (4 * L) (by linarith) le_rfl 1 (by omega))
  have hPpr : ∀ p ∈ P gs, p.Prime := fun p hp =>
    (mem_primesIcc.1 (hadm.2.2.2.2.2.2.1 gs hgs hp)).1
  have hFs : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x ^ 2 → (((P gs).filter (· ∣ n)).card : ℝ) ≤ Λ := by
    intro n hn hnx
    refine le_trans ?_ (hω n hn hnx)
    exact_mod_cast Finset.card_le_card fun p hp => Nat.mem_primeFactors.2
      ⟨hPpr p (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2, hn.ne'⟩
  have hspare : ∀ p ∈ sparePrimes x u v, p.Prime := fun p hp => by
    unfold sparePrimes at hp
    exact (Finset.mem_filter.1 hp).2.1
  have hFl : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ x ^ 2 →
      (((sparePrimes x u v).filter (· ∣ n)).card : ℝ) ≤ Λ := by
    intro n hn hnx
    refine le_trans ?_ (hω n hn hnx)
    exact_mod_cast Finset.card_le_card fun p hp => Nat.mem_primeFactors.2
      ⟨hspare p (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2, hn.ne'⟩
  have hV : vlo ≤ harmonicMass (P gs) := (hadm.2.2.2.2.2.1 gs).1
  have hV0 : 0 < harmonicMass (P gs) := hvlo.trans_le hV
  have hVinv : (harmonicMass (P gs))⁻¹ ≤ vlo⁻¹ := inv_anti₀ hvlo hV
  -- the coefficient bound `|𝒰 - 𝒰_tup + 𝒰_con| ≤ B₀`
  set U := endpointCoeff x q q₀ a u v Bc P C b ψ₁ Y σ with hUdef
  set Ut := tupleCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ with hUtdef
  set Uc := constCoeff x q q₀ a u v Bc P C b gs ψ₁ Y σ with hUcdef
  set Z : ℝ := M₁ 0 * L ^ a₁ * L ^ a₂ with hZ
  have hZ0 : 0 ≤ Z := by positivity
  set B₀ : ℝ := Z * ((2 + 2 / vlo) * Λ ^ 3) with hB₀
  have hcoef : ∀ w : ℕ, 1 ≤ w → (w : ℝ) ≤ x ^ 2 → ‖U w - Ut w + Uc w‖ ≤ B₀ := by
    intro w hw hwx
    have hw0 : 0 < w := hw
    have hLa₁ : 0 ≤ L ^ a₁ := by positivity
    have hLa₂ : 0 ≤ L ^ a₂ := by positivity
    -- the endpoint
    have hU : ‖U w‖ ≤ Z * (2 * Λ) := by
      rw [hUdef]
      unfold endpointCoeff
      rw [norm_mul, norm_mul, norm_mul, hcpow w hw0, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      have hcc : |centeredCore x q a u v Bc w| ≤ L ^ a₁ * (2 * Λ) := by
        unfold centeredCore
        rw [abs_mul, abs_of_nonneg (hW w).1]
        refine mul_le_mul (hW w).2 ?_ (abs_nonneg _) hLa₁
        calc |slotCount x u v Bc w - slotMean x u v Bc|
            ≤ |slotCount x u v Bc w| + |slotMean x u v Bc| := abs_sub _ _
          _ ≤ Λ + Λ := add_le_add (hf w hw0 hwx) hCB
          _ = 2 * Λ := by ring
      calc ‖ψ₁ (w / Y)‖ * |centeredCore x q a u v Bc w| *
            ‖markedListWeight P q₀ (unsharedSlots C) b w‖
          ≤ M₁ 0 * (L ^ a₁ * (2 * Λ)) * L ^ a₂ :=
            mul_le_mul (mul_le_mul (hψb _) hcc (abs_nonneg _) hM0) (hMW _ hS w)
              (norm_nonneg _) (by positivity)
        _ = Z * (2 * Λ) := by rw [hZ]; ring
    -- the tuple part
    have hUt : ‖Ut w‖ ≤ Z * (vlo⁻¹ * Λ ^ 3) := by
      rw [hUtdef]
      unfold tupleCoeff
      rw [norm_mul, norm_mul, norm_mul, hcpow w hw0, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.2 hV0.le)]
      have hsum : ‖∑ ps ∈ (P gs).filter (· ∣ w), ∑ pl ∈ (sparePrimes x u v).filter (· ∣ w / ps),
          ((markedWeight Finset.univ q (fun i => band x (a i)) (w / ps / pl) *
              weightedSlotCount x u v Bc (w / ps / pl) : ℝ) : ℂ) *
            markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b (w / ps / pl)‖ ≤
          Λ * (Λ * (L ^ a₁ * Λ * L ^ a₂)) := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ (Λ * (L ^ a₁ * Λ * L ^ a₂)) fun ps hps => ?_).trans
          ?_
        · obtain ⟨hpsP, hpsd⟩ := Finset.mem_filter.1 hps
          have hps0 : 0 < w / ps := Nat.div_pos (Nat.le_of_dvd hw0 hpsd) (hPpr ps hpsP).pos
          have hpsx : ((w / ps : ℕ) : ℝ) ≤ x ^ 2 :=
            (Nat.cast_le.2 (Nat.div_le_self _ _)).trans hwx
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_card_nsmul _ _ (L ^ a₁ * Λ * L ^ a₂) fun pl hpl => ?_).trans ?_
          · obtain ⟨hplS, hpld⟩ := Finset.mem_filter.1 hpl
            have hplp : pl.Prime := hspare pl hplS
            have hpl0 : 0 < w / ps / pl := Nat.div_pos (Nat.le_of_dvd hps0 hpld) hplp.pos
            have hplx : ((w / ps / pl : ℕ) : ℝ) ≤ x ^ 2 :=
              (Nat.cast_le.2 (Nat.div_le_self _ _)).trans hpsx
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW _).1]
            exact mul_le_mul (mul_le_mul (hW _).2 (hA _ hpl0 hplx) (abs_nonneg _) hLa₁)
              (hMW _ hS' _) (norm_nonneg _) (by positivity)
          · rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (hFl _ hps0 hpsx) (by positivity)
        · rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hFs w hw0 hwx) (by positivity)
      calc ‖ψ₁ (w / Y)‖ * (harmonicMass (P gs))⁻¹ * ‖_‖
          ≤ M₁ 0 * vlo⁻¹ * (Λ * (Λ * (L ^ a₁ * Λ * L ^ a₂))) :=
            mul_le_mul (mul_le_mul (hψb _) hVinv (inv_nonneg.2 hV0.le) hM0) hsum
              (norm_nonneg _) (by positivity)
        _ = Z * (vlo⁻¹ * Λ ^ 3) := by rw [hZ]; ring
    -- the constant part
    have hUc : ‖Uc w‖ ≤ Z * (vlo⁻¹ * Λ ^ 2) := by
      rw [hUcdef]
      unfold constCoeff
      rw [norm_mul, norm_mul, norm_mul, hcpow w hw0, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_div, abs_of_pos hV0]
      have hsum : ‖∑ ps ∈ (P gs).filter (· ∣ w),
          (markedWeight Finset.univ q (fun i => band x (a i)) (w / ps) : ℂ) *
            markedListWeight P q₀ (Function.update (unsharedSlots C) gs ∅) b (w / ps)‖ ≤
          Λ * (L ^ a₁ * L ^ a₂) := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ (L ^ a₁ * L ^ a₂) fun ps hps => ?_).trans ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW _).1]
          exact mul_le_mul (hW _).2 (hMW _ hS' _) (norm_nonneg _) hLa₁
        · rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hFs w hw0 hwx) (by positivity)
      have hCV : |slotMean x u v Bc| / harmonicMass (P gs) ≤ Λ * vlo⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hCB hVinv (inv_nonneg.2 hV0.le) (by linarith)
      calc ‖ψ₁ (w / Y)‖ * (|slotMean x u v Bc| / harmonicMass (P gs)) * ‖_‖
          ≤ M₁ 0 * (Λ * vlo⁻¹) * (Λ * (L ^ a₁ * L ^ a₂)) :=
            mul_le_mul (mul_le_mul (hψb _) hCV (by positivity) hM0) hsum
              (norm_nonneg _) (by positivity)
        _ = Z * (vlo⁻¹ * Λ ^ 2) := by rw [hZ]; ring
    -- combine
    have hΛ3 : Λ ≤ Λ ^ 3 := by
      calc Λ = Λ ^ 1 := (pow_one Λ).symm
        _ ≤ Λ ^ 3 := pow_le_pow_right₀ hΛ1 (by norm_num)
    have hΛ2 : Λ ^ 2 ≤ Λ ^ 3 := pow_le_pow_right₀ hΛ1 (by norm_num)
    have hvi : 0 ≤ vlo⁻¹ := inv_nonneg.2 hvlo.le
    calc ‖U w - Ut w + Uc w‖ ≤ ‖U w‖ + ‖Ut w‖ + ‖Uc w‖ :=
          (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ Z * (2 * Λ) + Z * (vlo⁻¹ * Λ ^ 3) + Z * (vlo⁻¹ * Λ ^ 2) := by
          linarith
      _ = Z * (2 * Λ + vlo⁻¹ * Λ ^ 3 + vlo⁻¹ * Λ ^ 2) := by ring
      _ ≤ Z * ((2 + 2 / vlo) * Λ ^ 3) := by
          refine mul_le_mul_of_nonneg_left ?_ hZ0
          calc 2 * Λ + vlo⁻¹ * Λ ^ 3 + vlo⁻¹ * Λ ^ 2
              ≤ 2 * Λ ^ 3 + vlo⁻¹ * Λ ^ 3 + vlo⁻¹ * Λ ^ 3 :=
                add_le_add (add_le_add (by linarith) le_rfl)
                  (mul_le_mul_of_nonneg_left hΛ2 hvi)
            _ = (2 + 2 / vlo) * Λ ^ 3 := by ring
  -- the exceptional positions
  set m := ⌊x ^ ε⌋₊ with hmdef
  have hxε : x ^ ε = Real.exp (c * L / T ^ 20) := by
    rw [Real.rpow_def_of_pos hx0]
    show Real.exp (L * ε) = _
    rw [hεdef]
    ring_nf
  set e₁ := Real.exp (-L ^ (0.27 : ℝ)) with he₁
  set e₂ := Real.exp (-(c * L / T ^ 20)) with he₂
  set ind : ℕ → ℝ := fun w => ∑ p ∈ P gs, (if p ^ 2 ∣ w then (1 : ℝ) else 0) +
    ∑ q' ∈ Finset.Ioo m (N + 1), (if q' ^ 2 ∣ w then (1 : ℝ) else 0) with hind
  have hpt : ∀ w ∈ Finset.Icc ⌈Y⌉₊ N, ‖U w - Ut w + Uc w‖ ^ 2 ≤ B₀ ^ 2 * ind w := by
    intro w hw
    obtain ⟨hw₁, hw₂⟩ := Finset.mem_Icc.1 hw
    have hw1 : 1 ≤ w := le_trans (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hY0).ne') hw₁
    have hwx : (w : ℝ) ≤ x ^ 2 := le_trans (by exact_mod_cast hw₂) (hN.trans h2Y)
    have hind0 : 0 ≤ ind w := by
      rw [hind]
      positivity
    by_cases hex : (∃ p ∈ P gs, p ^ 2 ∣ w) ∨
        ∃ p : ℕ, p.Prime ∧ (∃ i, x ^ u i < p ∧ (p : ℝ) ≤ x ^ v i) ∧ p ^ 2 ∣ w
    · have h1 : 1 ≤ ind w := by
        rw [hind]
        have h₁ : 0 ≤ ∑ p ∈ P gs, (if p ^ 2 ∣ w then (1 : ℝ) else 0) := by positivity
        have h₂ : 0 ≤ ∑ q' ∈ Finset.Ioo m (N + 1), (if q' ^ 2 ∣ w then (1 : ℝ) else 0) := by
          positivity
        rcases hex with ⟨p, hp, hpw⟩ | ⟨p, -, ⟨i, hpi, -⟩, hpw⟩
        · have := Finset.single_le_sum (f := fun p => if p ^ 2 ∣ w then (1 : ℝ) else 0)
            (fun _ _ => by positivity) hp
          rw [ite_eq_left hpw] at this
          linarith
        · have hpm : p ∈ Finset.Ioo m (N + 1) := by
            rw [Finset.mem_Ioo]
            constructor
            · have : (m : ℝ) < p := lt_of_le_of_lt (Nat.floor_le (by positivity))
                (lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hx.le (hu i)) hpi)
              exact_mod_cast this
            · have hpw' : p ≤ w := (Nat.le_self_pow two_ne_zero p).trans
                (Nat.le_of_dvd hw1 hpw)
              omega
          have := Finset.single_le_sum (f := fun p => if p ^ 2 ∣ w then (1 : ℝ) else 0)
            (fun _ _ => by positivity) hpm
          rw [ite_eq_left hpw] at this
          linarith
      have hc := hcoef w hw1 hwx
      calc ‖U w - Ut w + Uc w‖ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc 2
        _ = B₀ ^ 2 * 1 := (mul_one _).symm
        _ ≤ B₀ ^ 2 * ind w := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    · obtain ⟨hex₁, hex₂⟩ := not_or.1 hex
      have heq := hid P big hadm gs hgs r a u v Bc hin hsl J C b hCb hbb ψ₁ Y σ w hw1
        (fun p hp hpw => hex₁ ⟨p, hp, hpw⟩) (fun p hp hpi hpw => hex₂ ⟨p, hp, hpi, hpw⟩)
      have h0 : U w - Ut w + Uc w = 0 := by
        rw [hUdef, hUtdef, hUcdef, heq]
        ring
      rw [h0, norm_zero, zero_pow two_ne_zero]
      positivity
  -- the count of the exceptional positions
  have hsub : Finset.Icc ⌈Y⌉₊ N ⊆ Finset.Icc 1 N := by
    intro w hw
    rw [Finset.mem_Icc] at hw ⊢
    exact ⟨le_trans (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hY0).ne') hw.1, hw.2⟩
  have hvhi : 0 < vhi := hV0.trans_le (hadm.2.2.2.2.2.1 gs).2
  have hcnt₁ : ∑ p ∈ P gs, ∑ w ∈ Finset.Icc 1 N, (if p ^ 2 ∣ w then (1 : ℝ) else 0) ≤
      N * (vhi * e₁) := by
    calc ∑ p ∈ P gs, ∑ w ∈ Finset.Icc 1 N, (if p ^ 2 ∣ w then (1 : ℝ) else 0)
        ≤ ∑ p ∈ P gs, (N : ℝ) * e₁ * (1 / p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp0 : 0 < p := (hPpr p hp).pos
          rw [Finset.sum_boole]
          refine (FactorAux.card_filter_dvd_le N (pow_pos hp0 2)).trans ?_
          have hp1 : 1 / (p : ℝ) ≤ e₁ := by
            rw [he₁, Real.exp_neg, one_div]
            exact inv_anti₀ (Real.exp_pos _)
              (mem_primesIcc.1 (hadm.2.2.2.2.2.2.1 gs hgs hp)).2.1
          have hpp : (0 : ℝ) < p := by exact_mod_cast hp0
          rw [Nat.cast_pow, div_eq_mul_inv, ← inv_pow, pow_two]
          calc (N : ℝ) * ((p : ℝ)⁻¹ * (p : ℝ)⁻¹) = N * (1 / p) * (1 / p) := by ring
            _ ≤ N * e₁ * (1 / p) := by
                gcongr
      _ = N * e₁ * harmonicMass (P gs) := by rw [← Finset.mul_sum]; rfl
      _ ≤ N * (vhi * e₁) := by
          rw [show (N : ℝ) * (vhi * e₁) = N * e₁ * vhi by ring]
          exact mul_le_mul_of_nonneg_left (hadm.2.2.2.2.2.1 gs).2 (by positivity)
  have hcnt₂ : ∑ q' ∈ Finset.Ioo m (N + 1), ∑ w ∈ Finset.Icc 1 N,
      (if q' ^ 2 ∣ w then (1 : ℝ) else 0) ≤ N * (2 * e₂) := by
    calc ∑ q' ∈ Finset.Ioo m (N + 1), ∑ w ∈ Finset.Icc 1 N, (if q' ^ 2 ∣ w then (1 : ℝ) else 0)
        ≤ ∑ q' ∈ Finset.Ioo m (N + 1), (N : ℝ) * ((q' : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun q' hq' => ?_
          have hq0 : 0 < q' := lt_of_le_of_lt (Nat.zero_le m) (Finset.mem_Ioo.1 hq').1
          rw [Finset.sum_boole]
          refine (FactorAux.card_filter_dvd_le N (pow_pos hq0 2)).trans ?_
          rw [Nat.cast_pow, div_eq_mul_inv]
      _ = N * ∑ q' ∈ Finset.Ioo m (N + 1), ((q' : ℝ) ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
      _ ≤ N * (2 / (m + 1)) := mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le m (N + 1))
          (Nat.cast_nonneg _)
      _ ≤ N * (2 * e₂) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hm : x ^ ε < (m : ℝ) + 1 := Nat.lt_floor_add_one _
          rw [hxε] at hm
          rw [he₂, Real.exp_neg, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos _) hm.le) (by norm_num)
  have hsum : ∑ w ∈ Finset.Icc ⌈Y⌉₊ N, ‖U w - Ut w + Uc w‖ ^ 2 ≤
      B₀ ^ 2 * (N * (vhi * e₁ + 2 * e₂)) := by
    calc ∑ w ∈ Finset.Icc ⌈Y⌉₊ N, ‖U w - Ut w + Uc w‖ ^ 2
        ≤ ∑ w ∈ Finset.Icc ⌈Y⌉₊ N, B₀ ^ 2 * ind w := Finset.sum_le_sum hpt
      _ ≤ ∑ w ∈ Finset.Icc 1 N, B₀ ^ 2 * ind w :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => by
            rw [hind]
            positivity
      _ = B₀ ^ 2 * (∑ p ∈ P gs, ∑ w ∈ Finset.Icc 1 N, (if p ^ 2 ∣ w then (1 : ℝ) else 0) +
          ∑ q' ∈ Finset.Ioo m (N + 1), ∑ w ∈ Finset.Icc 1 N,
            (if q' ^ 2 ∣ w then (1 : ℝ) else 0)) := by
          rw [← Finset.mul_sum, hind]
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (s := Finset.Icc 1 N) (t := P gs),
            Finset.sum_comm (s := Finset.Icc 1 N) (t := Finset.Ioo m (N + 1))]
      _ ≤ B₀ ^ 2 * (N * (vhi * e₁ + 2 * e₂)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          linarith
  -- `B₀² ≤ L^E`
  have hB₀sq : B₀ ^ 2 ≤ L ^ E := by
    have hsq : ∀ a' : ℝ, (L ^ a') ^ 2 = L ^ (2 * a') := fun a' => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      ring_nf
    have hexpand : B₀ ^ 2 = D * (L ^ (6 * (d + 2)) * (L ^ a₁) ^ 2 * (L ^ a₂) ^ 2) := by
      rw [hB₀, hZ, hΛ, hD]
      ring
    rw [hexpand, hsq, hsq]
    calc D * (L ^ (6 * (d + 2)) * L ^ (2 * a₁) * L ^ (2 * a₂))
        ≤ L * (L ^ (6 * (d + 2)) * L ^ (2 * a₁) * L ^ (2 * a₂)) :=
          mul_le_mul_of_nonneg_right hDL (by positivity)
      _ = L ^ E := by
          rw [hE, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one,
            Real.rpow_natCast]
          ring
  -- the mean value theorem over `[-T₀, T₀]`
  have hT₀0 : 0 ≤ x * L ^ (Cm + 2) := by positivity
  refine (FactorAux.integral_norm_twistedPoly_sq_le hY1 (fun w => U w - Ut w + Uc w) h k
    hT₀0).trans ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : Real.log N ≤ 2 * L := by
    calc Real.log N ≤ Real.log (x ^ 2) := Real.log_le_log hNpos (hN.trans h2Y)
      _ = 2 * L := by rw [Real.log_pow]; push_cast; ring
  have hLC : L ^ (Cm + 2) ≤ L ^ (|Cm| + 2) :=
    Real.rpow_le_rpow_of_exponent_le hL.le (by linarith [le_abs_self Cm])
  have hL1C : L ≤ L ^ (|Cm| + 2) := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
      _ ≤ L ^ (|Cm| + 2) :=
          Real.rpow_le_rpow_of_exponent_le hL.le (by linarith [abs_nonneg Cm])
  have hfirst : x * L ^ (Cm + 2) - -(x * L ^ (Cm + 2)) + 8 * N * (1 + Real.log N) ≤
      50 * Y * L ^ (|Cm| + 2) := by
    have h₀ : x * L ^ (Cm + 2) ≤ Y * L ^ (|Cm| + 2) :=
      mul_le_mul hxY hLC (by positivity) hY0.le
    have h₁ : 0 ≤ 1 + Real.log N := by linarith [Real.log_natCast_nonneg N]
    have h₂ : 8 * (N : ℝ) * (1 + Real.log N) ≤ 8 * (2 * Y) * (3 * L) := by
      have := mul_le_mul hN (show 1 + Real.log N ≤ 3 * L by linarith) h₁ (by linarith)
      linarith
    have h₃ : 48 * Y * L ≤ 48 * Y * L ^ (|Cm| + 2) :=
      mul_le_mul_of_nonneg_left hL1C (by linarith)
    linarith
  have hG : vhi * e₁ + 2 * e₂ ≤ max vhi 2 * (e₁ + e₂) := by
    have he₁0 : 0 ≤ e₁ := (Real.exp_pos _).le
    have he₂0 : 0 ≤ e₂ := (Real.exp_pos _).le
    calc vhi * e₁ + 2 * e₂ ≤ max vhi 2 * e₁ + max vhi 2 * e₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) he₁0)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) he₂0)
      _ = max vhi 2 * (e₁ + e₂) := by ring
  have hsum0 : 0 ≤ ∑ w ∈ Finset.Icc ⌈Y⌉₊ N, ‖U w - Ut w + Uc w‖ ^ 2 := by positivity
  have hY2 : (0 : ℝ) < Y ^ 2 := by positivity
  calc (Y ^ 2)⁻¹ * ((x * L ^ (Cm + 2) - -(x * L ^ (Cm + 2)) + 8 * N * (1 + Real.log N)) *
        ∑ w ∈ Finset.Icc ⌈Y⌉₊ N, ‖U w - Ut w + Uc w‖ ^ 2)
      ≤ (Y ^ 2)⁻¹ * ((50 * Y * L ^ (|Cm| + 2)) * (B₀ ^ 2 * (N * (vhi * e₁ + 2 * e₂)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hfirst hsum hsum0 (by positivity))
          (inv_nonneg.2 hY2.le)
    _ ≤ (Y ^ 2)⁻¹ * ((50 * Y * L ^ (|Cm| + 2)) *
          (L ^ E * ((2 * Y) * (max vhi 2 * (e₁ + e₂))))) := by
        have hG0 : 0 ≤ vhi * e₁ + 2 * e₂ := by positivity
        gcongr
    _ = 100 * max vhi 2 * (L ^ (|Cm| + 2) * L ^ E) * (e₁ + e₂) := by
        field_simp
        ring
    _ ≤ L * (L ^ (|Cm| + 2) * L ^ E) * (e₁ + e₂) := by
        gcongr
    _ = L ^ (|Cm| + 3 + E) * (e₁ + e₂) := by
        have hfin : L * (L ^ (|Cm| + 2) * L ^ E) = L ^ (|Cm| + 3 + E) := by
          calc L * (L ^ (|Cm| + 2) * L ^ E) = L ^ (1 : ℝ) * (L ^ (|Cm| + 2) * L ^ E) := by
                rw [Real.rpow_one]
            _ = L ^ (1 + ((|Cm| + 2) + E)) := by
                rw [Real.rpow_add hL0 1, Real.rpow_add hL0 (|Cm| + 2) E]
            _ = L ^ (|Cm| + 3 + E) := by ring_nf
        rw [hfin]

end Erdos408.TwoSided
