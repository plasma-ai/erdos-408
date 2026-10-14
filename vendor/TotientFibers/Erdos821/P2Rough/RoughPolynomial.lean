import Erdos821.Prelim

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.P2Rough

open Finset

theorem mem_primesUpTo_iff {z : ℝ} (hz : 0 ≤ z) {p : ℕ} (hp : p.Prime) :
    p ∈ Erdos821.Blueprint.primesUpTo z ↔ (p : ℝ) ≤ z := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hI, _⟩
    rcases Finset.mem_Icc.mp hI with ⟨_, hfloor⟩
    exact le_trans (Nat.cast_le.mpr hfloor) (Nat.floor_le hz)
  · intro hpz
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.one_le, Nat.le_floor hpz⟩, hp⟩

def intervalSieveData (lo hi z : ℝ) : Erdos821.Blueprint.SieveData ℕ where
  objects := Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊
  weight := fun _ => 1
  primes := Erdos821.Blueprint.primesUpTo z
  bad := fun p n => p ∣ n
  X := ((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).card : ℝ)
  density := fun p => 1 / (p : ℝ)
  nonneg := by intros; norm_num
  prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  X_nonneg := by positivity

def primeRecipSum (y : ℝ) : ℝ :=
  ∑ p ∈ Erdos821.Blueprint.primesUpTo y, (p : ℝ)⁻¹

theorem intervalSieveData_densityBounds (hc : Erdos821.Blueprint.ClassicalInputs) :
    ∃ C : ℝ, 0 < C ∧ ∀ lo hi z : ℝ, 2 ≤ z →
      (intervalSieveData lo hi z).densityBounds z (1 / 2) C := by
  obtain ⟨M, hM⟩ := hc.mertens.1
  have hMnn : 0 ≤ M := by
    have h := hM 2 (by norm_num)
    have hnonneg : 0 ≤ |(∑ p ∈ Erdos821.Blueprint.primesUpTo (2 : ℝ),
        (p : ℝ)⁻¹) - Real.log (Real.log 2)| := abs_nonneg _
    linarith
  let C : ℝ := 2 * M + Real.log 2 + 2
  have hCpos : 0 < C := by
    dsimp [C]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro lo hi z hz
  refine ⟨by linarith, by norm_num, ?_, ?_⟩
  · intro p hp
    have hp' := (intervalSieveData lo hi z).prime p hp
    have hpz := (mem_primesUpTo_iff (by linarith : (0 : ℝ) ≤ z) hp').mp hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
    refine ⟨hpz, ?_, ?_⟩
    · exact one_div_nonneg.mpr (by positivity)
    · have hrecip : 1 / (p : ℝ) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) hp2
      dsimp [intervalSieveData]
      linarith
  · intro w hw
    let A := (intervalSieveData lo hi z).primes.filter
      (fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ (2 : ℕ))
    by_cases hw2 : 2 ≤ w
    · have hwpos : 0 < w := lt_of_lt_of_le (by norm_num) hw2
      have hw2sq : 2 ≤ w ^ (2 : ℕ) := by nlinarith
      let Qlo := Erdos821.Blueprint.primesUpTo w
      let Qhi := Erdos821.Blueprint.primesUpTo (w ^ (2 : ℕ))
      have hQsubset : Qlo ⊆ Qhi := by
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        apply (mem_primesUpTo_iff (by linarith) hp').2
        have hpw := (mem_primesUpTo_iff (by linarith) hp').mp hp
        nlinarith [hw2, hpw]
      have hAsub : A ⊆ Qhi \ Qlo := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpS, hband⟩
        rcases Finset.mem_filter.mp hpS with ⟨hpI, hprime⟩
        have hpQhi : p ∈ Qhi := by
          apply (mem_primesUpTo_iff (by positivity) hprime).2
          exact hband.2
        have hpQlo : p ∉ Qlo := by
          intro hpL
          have hpw := (mem_primesUpTo_iff (by linarith) hprime).mp hpL
          linarith [hband.1]
        exact Finset.mem_sdiff.mpr ⟨hpQhi, hpQlo⟩
      have hdisj : Disjoint Qlo (Qhi \ Qlo) := by
        rw [Finset.disjoint_left]
        intro p hpL hpD
        exact (Finset.mem_sdiff.mp hpD).2 hpL
      have hunion : Qlo ∪ (Qhi \ Qlo) = Qhi := by
        ext p
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (hpL | ⟨hpH, _⟩)
          · exact hQsubset hpL
          · exact hpH
        · intro hpH
          by_cases hpL : p ∈ Qlo
          · exact Or.inl hpL
          · exact Or.inr ⟨hpH, hpL⟩
      have hsumDiff :
          (∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹) = primeRecipSum (w ^ (2 : ℕ)) - primeRecipSum w := by
        have hsplit : primeRecipSum (w ^ (2 : ℕ)) =
            primeRecipSum w + ∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹ := by
          calc primeRecipSum (w ^ (2 : ℕ))
              = ∑ p ∈ Qlo ∪ (Qhi \ Qlo), (p : ℝ)⁻¹ := by
                  unfold primeRecipSum
                  rw [hunion]
            _ = primeRecipSum w + ∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹ := by
                  unfold primeRecipSum
                  rw [Finset.sum_union hdisj]
        linarith [hsplit]
      have hsumSub : (∑ p ∈ A, (p : ℝ)⁻¹) ≤
          ∑ p ∈ Qhi \ Qlo, (p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hAsub
        intro p hpQ hnotA
        positivity
      have hMhi := hM (w ^ (2 : ℕ)) hw2sq
      have hMlo := hM w hw2
      have hlogid :
          Real.log (Real.log (w ^ (2 : ℕ))) - Real.log (Real.log w) = Real.log 2 := by
        have hlogw : 0 < Real.log w := Real.log_pos hw
        rw [Real.log_pow w 2]
        rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num]
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hlogw)]
        ring
      have hupper : primeRecipSum (w ^ (2 : ℕ)) - Real.log (Real.log (w ^ (2 : ℕ))) ≤ M := by
        simpa [primeRecipSum] using (abs_le.mp hMhi).2
      have hlowerRaw : -M ≤ primeRecipSum w - Real.log (Real.log w) := by
        simpa [primeRecipSum] using (abs_le.mp hMlo).1
      have hlower : Real.log (Real.log w) - primeRecipSum w ≤ M := by
        linarith [hlowerRaw]
      have hbound : primeRecipSum (w ^ (2 : ℕ)) - primeRecipSum w ≤
          Real.log 2 + 2 * M := by
        linarith [hlogid]
      have hCval : C = 2 * M + Real.log 2 + 2 := rfl
      simpa [A, intervalSieveData, one_div] using
        le_trans hsumSub (by linarith [hbound, hCval])
    · have hwsmall : w ^ (2 : ℕ) < 4 := by nlinarith [hw, hw2]
      have hAsub : A ⊆ Finset.Icc 2 3 := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpS, hband⟩
        have hprime : p.Prime := (Finset.mem_filter.mp hpS).2
        have hp2 : 2 ≤ p := hprime.two_le
        have hp4 : p < 4 := by
          exact_mod_cast lt_of_le_of_lt hband.2 hwsmall
        exact Finset.mem_Icc.mpr ⟨hp2, by omega⟩
      have hsumSub : (∑ p ∈ A, 1 / (p : ℝ)) ≤
          ∑ p ∈ (Finset.Icc 2 3 : Finset ℕ), 1 / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hAsub
        intro p hpQ hnotA
        positivity
      have hsumCap : (∑ p ∈ (Finset.Icc 2 3 : Finset ℕ), 1 / (p : ℝ)) ≤ 2 := by
        calc ∑ p ∈ (Finset.Icc 2 3 : Finset ℕ), 1 / (p : ℝ)
            ≤ ∑ _p ∈ (Finset.Icc 2 3 : Finset ℕ), (1 / 2 : ℝ) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
                exact_mod_cast (Finset.mem_Icc.mp hp).1
              exact one_div_le_one_div_of_le (by norm_num) hp2
          _ = 1 := by norm_num
          _ ≤ 2 := by norm_num
      have hCval : C = 2 * M + Real.log 2 + 2 := rfl
      have hsumCap' :
          (∑ p ∈ (Finset.Icc 2 3 : Finset ℕ), (p : ℝ)⁻¹) ≤ 2 := by
        simpa [one_div] using hsumCap
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hCtwo : 2 ≤ C := by rw [hCval]; linarith
      have hsmallBound : (∑ p ∈ A, 1 / (p : ℝ)) ≤ C := by
        calc ∑ p ∈ A, 1 / (p : ℝ)
            ≤ ∑ p ∈ (Finset.Icc 2 3 : Finset ℕ), (p : ℝ)⁻¹ := by
              simpa [one_div] using hsumSub
          _ ≤ 2 := hsumCap'
          _ ≤ C := hCtwo
      simpa [A, intervalSieveData, one_div] using hsmallBound

theorem primeProductHarmonicBound (hc : Erdos821.Blueprint.ClassicalInputs) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℝ, 2 ≤ z →
      (∏ p ∈ Erdos821.Blueprint.primesUpTo z, (1 + 1 / (p : ℝ))) ≤
        K * Real.log (2 * z) := by
  obtain ⟨M, hM⟩ := hc.mertens.1
  refine ⟨Real.exp M, Real.exp_pos M, ?_⟩
  intro z hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsum : primeRecipSum z ≤ Real.log (Real.log z) + M := by
    have h := (abs_le.mp (hM z hz)).2
    unfold primeRecipSum
    linarith
  have hprod := Erdos821.Prelim.Mertens.one_add_product_le_exp
    (Erdos821.Blueprint.primesUpTo z)
  have hprod' :
      (∏ p ∈ Erdos821.Blueprint.primesUpTo z, (1 + 1 / (p : ℝ))) ≤
        Real.exp (primeRecipSum z) := by
    simpa [primeRecipSum, one_div] using hprod
  have hexp : Real.exp (primeRecipSum z) ≤
      Real.exp (Real.log (Real.log z) + M) := Real.exp_le_exp.mpr hsum
  have hexpEq : Real.exp (Real.log (Real.log z) + M) = Real.exp M * Real.log z := by
    rw [Real.exp_add, Real.exp_log hlogz]
    ring
  have hlogle : Real.log z ≤ Real.log (2 * z) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  calc ∏ p ∈ Erdos821.Blueprint.primesUpTo z, (1 + 1 / (p : ℝ))
      ≤ Real.exp (primeRecipSum z) := hprod'
    _ ≤ Real.exp (Real.log (Real.log z) + M) := hexp
    _ = Real.exp M * Real.log z := hexpEq
    _ ≤ Real.exp M * Real.log (2 * z) :=
      mul_le_mul_of_nonneg_left hlogle (Real.exp_pos M).le

noncomputable def roughBlockCount (z : ℝ) (hz : 1 < z) : ℕ :=
  Nat.find (Erdos821.PrelimLemmas.exists_Zscale_lt_two hz)

theorem roughBlockCount_spec {z : ℝ} (hz : 1 < z) :
    Erdos821.PrelimLemmas.Zscale z (roughBlockCount z hz) < 2 :=
  Nat.find_spec (Erdos821.PrelimLemmas.exists_Zscale_lt_two hz)

noncomputable def roughBlock (z : ℝ) (j : ℕ) : Finset ℕ :=
  Erdos821.PrelimLemmas.Block ℕ (intervalSieveData 1 1 z) z j

noncomputable def roughBlockIndex (z : ℝ) (hz : 1 < z) : Finset ℕ :=
  Finset.range (roughBlockCount z hz)

noncomputable def roughSupport (z : ℝ) (hz : 1 < z) (h : ℕ) : Finset (Finset ℕ) :=
  Prelim.BlockSieve.SieveSupport
    ((roughBlockIndex z hz).biUnion (fun j => roughBlock z j))
    (roughBlockIndex z hz) (fun j => roughBlock z j) (fun j => (j + 1) * h)

noncomputable def roughUDivisorSet (z : ℝ) (hz : 1 < z) (h : ℕ) : Finset ℕ :=
  (roughSupport z hz h).image (fun s => ∏ p ∈ s, p)

noncomputable def roughLambda (z : ℝ) (hz : 1 < z) (h : ℕ) (d : ℕ) : ℝ :=
  if d ∈ roughUDivisorSet z hz h then (-1 : ℝ) ^ d.primeFactors.card else 0

theorem roughBlock_prime (z : ℝ) (j p : ℕ) (hp : p ∈ roughBlock z j) : p.Prime := by
  rcases Finset.mem_filter.mp hp with ⟨hpz, _⟩
  exact (Finset.mem_filter.mp hpz).2

theorem roughSupport_prime {z : ℝ} {hz : 1 < z} {h : ℕ} {s : Finset ℕ}
    (hs : s ∈ roughSupport z hz h) {p : ℕ} (hp : p ∈ s) : p.Prime := by
  have hs' := (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hs |>.1 hp
  rw [Finset.mem_biUnion] at hs'
  obtain ⟨j, -, hpj⟩ := hs'
  exact roughBlock_prime z j p hpj

theorem roughSupport_product_injective {z : ℝ} {hz : 1 < z} {h : ℕ}
    {s t : Finset ℕ} (hs : s ∈ roughSupport z hz h)
    (ht : t ∈ roughSupport z hz h)
    (heq : (∏ p ∈ s, p) = (∏ p ∈ t, p)) : s = t := by
  have hpfS := Erdos821.PrelimLemmas.primeFactors_prod_eq s
    (fun p hp => roughSupport_prime hs hp)
  have hpfT := Erdos821.PrelimLemmas.primeFactors_prod_eq t
    (fun p hp => roughSupport_prime ht hp)
  calc s = (∏ p ∈ s, p).primeFactors := hpfS.symm
    _ = (∏ p ∈ t, p).primeFactors := congrArg Nat.primeFactors heq
    _ = t := hpfT

theorem roughLambda_abs_le (z : ℝ) (hz : 1 < z) (h d : ℕ) :
    |roughLambda z hz h d| ≤ 1 := by
  by_cases hd : d ∈ roughUDivisorSet z hz h
  · simp [roughLambda, hd]
  · simp [roughLambda, hd]

theorem roughSupport_subset_primes {z : ℝ} {hz : 1 < z} {h : ℕ}
    {s : Finset ℕ} (hs : s ∈ roughSupport z hz h) :
    s ⊆ Erdos821.Blueprint.primesUpTo z := by
  have hsP := (Prelim.BlockSieve.mem_sieveSupport _ _ _ _ _).mp hs |>.1
  intro p hp
  have hpin := hsP hp
  rw [Finset.mem_biUnion] at hpin
  obtain ⟨j, -, hpj⟩ := hpin
  exact Erdos821.PrelimLemmas.Block_subset ℕ (intervalSieveData 1 1 z) z j hpj

theorem roughUDivisorSet_support {z : ℝ} {hz : 1 < z} {h d : ℕ}
    (hd : d ∈ roughUDivisorSet z hz h) :
    Squarefree d ∧ (d : ℝ) ≤ z ^ (4 * h + 2) ∧
      d.primeFactors ⊆ Erdos821.Blueprint.primesUpTo z := by
  rcases Finset.mem_image.mp hd with ⟨s, hs, rfl⟩
  have hprime : ∀ p ∈ s, p.Prime := fun p hp => roughSupport_prime hs hp
  have hsq : Squarefree (∏ p ∈ s, p) :=
    Erdos821.PrelimLemmas.prod_primes_squarefree s hprime
  have hpf : (∏ p ∈ s, p).primeFactors = s :=
    Erdos821.PrelimLemmas.primeFactors_prod_eq s hprime
  have hslevel : s ∈ Prelim.BlockSieve.SieveSupport
      ((Finset.range (roughBlockCount z hz)).biUnion
        (fun j => Erdos821.PrelimLemmas.Block ℕ
          (intervalSieveData 1 1 z) z j))
      (Finset.range (roughBlockCount z hz))
      (fun j => Erdos821.PrelimLemmas.Block ℕ (intervalSieveData 1 1 z) z j)
      (fun j => (j + 1) * h) := by
    simpa [roughSupport, roughBlockIndex, roughBlock] using hs
  have hlevel := Erdos821.PrelimLemmas.support_level_le ℕ
    (intervalSieveData 1 1 z) z hz h (roughBlockCount z hz) s hslevel
  have hcast : ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := Nat.cast_prod _ _
  have hsubset := roughSupport_subset_primes hs
  refine ⟨hsq, ?_, ?_⟩
  · rw [hcast]
    exact hlevel
  · rw [hpf]
    exact hsubset

theorem roughLambda_support {z : ℝ} {hz : 1 < z} {h d : ℕ}
    (hd : roughLambda z hz h d ≠ 0) :
    Squarefree d ∧ (d : ℝ) ≤ z ^ (4 * h + 2) ∧
      d.primeFactors ⊆ Erdos821.Blueprint.primesUpTo z := by
  have hmem : d ∈ roughUDivisorSet z hz h := by
    by_contra hnot
    have hzero : roughLambda z hz h d = 0 := by simp [roughLambda, hnot]
    exact hd hzero
  exact roughUDivisorSet_support hmem

theorem primeProduct_dvd_iff {s : Finset ℕ} {n : ℕ}
    (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  constructor
  · intro hd p hp
    exact dvd_trans (Finset.dvd_prod_of_mem _ hp) hd
  · intro hall
    induction s using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
      have hp : p.Prime := hs p (Finset.mem_insert_self p s)
      have hs' : ∀ q ∈ s, q.Prime := fun q hq =>
        hs q (Finset.mem_insert_of_mem hq)
      have hsDvd : (∏ q ∈ s, q) ∣ n :=
        ih hs' (fun q hq => hall q (Finset.mem_insert_of_mem hq))
      have hpDvd : p ∣ n := hall p (Finset.mem_insert_self p s)
      have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
        rw [hp.coprime_iff_not_dvd]
        exact Erdos821.PrelimLemmas.prime_not_dvd_prod hp hs' hps
      have hmul : p * (∏ q ∈ s, q) ∣ n :=
        hcop.mul_dvd_of_dvd_of_dvd hpDvd hsDvd
      simpa [Finset.prod_insert hps] using hmul

theorem roughSupport_eq_interval (lo hi z : ℝ) (hz : 1 < z) (h : ℕ) :
    roughSupport z hz h =
      Prelim.BlockSieve.SieveSupport
        ((roughBlockIndex z hz).biUnion
          (fun j => Erdos821.PrelimLemmas.Block ℕ (intervalSieveData lo hi z) z j))
        (roughBlockIndex z hz)
        (fun j => Erdos821.PrelimLemmas.Block ℕ (intervalSieveData lo hi z) z j)
        (fun j => (j + 1) * h) := by
  ext s
  simp [roughSupport, roughBlock, roughBlockIndex,
    Erdos821.PrelimLemmas.Block, intervalSieveData]

theorem roughSupport_bad_iff_dvd (lo hi z : ℝ) (hz : 1 < z) (h n : ℕ)
    {s : Finset ℕ} (hs : s ∈ roughSupport z hz h) :
    s ⊆ Erdos821.PrelimLemmas.badFinset ℕ (intervalSieveData lo hi z) n ↔
      (∏ p ∈ s, p) ∣ n := by
  let S := intervalSieveData lo hi z
  have hsP : s ⊆ S.primes := by
    simpa [S, intervalSieveData] using roughSupport_subset_primes hs
  have hprime : ∀ p ∈ s, p.Prime := fun p hp => roughSupport_prime hs hp
  have hprod := primeProduct_dvd_iff (s := s) (n := n) hprime
  constructor
  · intro hbad
    apply hprod.mpr
    intro p hp
    exact (Erdos821.PrelimLemmas.mem_badFinset ℕ S n p).mp (hbad hp) |>.2
  · intro hdvd p hp
    apply (Erdos821.PrelimLemmas.mem_badFinset ℕ S n p).mpr
    exact ⟨hsP hp, (hprod.mp hdvd) p hp⟩

theorem roughLambda_divisor_sum_eq_Uval (lo hi z : ℝ) (hz : 1 < z)
    (η C : ℝ) (hdb : (intervalSieveData lo hi z).densityBounds z η C)
    (h n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, roughLambda z hz h d) =
      Prelim.BlockSieve.Uval (roughBlockIndex z hz)
        (fun j => Erdos821.PrelimLemmas.Block ℕ (intervalSieveData lo hi z) z j)
        (fun j => (j + 1) * h)
        (Erdos821.PrelimLemmas.badFinset ℕ (intervalSieveData lo hi z) n) := by
  let S := intervalSieveData lo hi z
  let supp := roughSupport z hz h
  let productIndex : Finset ℕ → ℕ := fun s => ∏ p ∈ s, p
  let Uset := roughUDivisorSet z hz h
  let bad := Erdos821.PrelimLemmas.badFinset ℕ S n
  have hInj : Set.InjOn productIndex (↑supp : Set (Finset ℕ)) := by
    intro s hs t ht heq
    exact roughSupport_product_injective (Finset.mem_coe.mp hs)
      (Finset.mem_coe.mp ht) heq
  have hInjFilter : Set.InjOn productIndex
      (↑(supp.filter (fun s => productIndex s ∈ n.divisors)) : Set (Finset ℕ)) := by
    intro s hs t ht heq
    exact roughSupport_product_injective
      (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).1
      (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1 heq
  have hfilterImage : (supp.filter (fun s => productIndex s ∈ n.divisors)).image
        productIndex = Uset.filter (fun d => d ∈ n.divisors) := by
    change (supp.filter (fun s => productIndex s ∈ n.divisors)).image productIndex =
      (supp.image productIndex).filter (fun d => d ∈ n.divisors)
    ext d
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨s, ⟨hs, hdiv⟩, rfl⟩
      exact ⟨⟨s, hs, rfl⟩, hdiv⟩
    · rintro ⟨⟨s, hs, rfl⟩, hdiv⟩
      exact ⟨s, ⟨hs, hdiv⟩, rfl⟩
  have hsumFilter : (∑ d ∈ n.divisors, roughLambda z hz h d) =
      ∑ d ∈ n.divisors.filter (fun d => d ∈ Uset),
        (-1 : ℝ) ^ d.primeFactors.card := by
    calc
      (∑ d ∈ n.divisors, roughLambda z hz h d) =
          ∑ d ∈ n.divisors, (if d ∈ Uset then (-1 : ℝ) ^ d.primeFactors.card else 0) := by
            apply Finset.sum_congr rfl
            intro d _
            rfl
      _ = ∑ d ∈ n.divisors.filter (fun d => d ∈ Uset),
          (-1 : ℝ) ^ d.primeFactors.card := by
            symm
            rw [Finset.sum_filter]
  have hinter : n.divisors.filter (fun d => d ∈ Uset) =
      Uset.filter (fun d => d ∈ n.divisors) := by
    ext d
    simp only [Finset.mem_filter]
    tauto
  have hsumReindex :
      (∑ d ∈ Uset.filter (fun d => d ∈ n.divisors),
        (-1 : ℝ) ^ d.primeFactors.card) =
      ∑ s ∈ supp.filter (fun s => productIndex s ∈ n.divisors),
        (-1 : ℝ) ^ s.card := by
    calc
      (∑ d ∈ Uset.filter (fun d => d ∈ n.divisors),
          (-1 : ℝ) ^ d.primeFactors.card)
        = ∑ d ∈ (supp.filter (fun s => productIndex s ∈ n.divisors)).image
            productIndex, (-1 : ℝ) ^ d.primeFactors.card := by rw [hfilterImage]
      _ = ∑ s ∈ supp.filter (fun s => productIndex s ∈ n.divisors),
          (-1 : ℝ) ^ s.card := by
            rw [Finset.sum_image hInjFilter]
            apply Finset.sum_congr rfl
            intro s hs
            have hs' := (Finset.mem_filter.mp hs).1
            have hpf := Erdos821.PrelimLemmas.primeFactors_prod_eq s
              (fun p hp => roughSupport_prime hs' hp)
            simp only [productIndex]
            rw [hpf]
  have hfilterBad : supp.filter (fun s => productIndex s ∈ n.divisors) =
      supp.filter (fun s => s ⊆ bad) := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hs, hdiv⟩
      have hdvd : productIndex s ∣ n := (Nat.mem_divisors.mp hdiv).1
      exact ⟨hs, (roughSupport_bad_iff_dvd lo hi z hz h n hs).2 hdvd⟩
    · rintro ⟨hs, hsub⟩
      have hdvd := (roughSupport_bad_iff_dvd lo hi z hz h n hs).1 hsub
      exact ⟨hs, Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩⟩
  have hU := Erdos821.PrelimLemmas.Uval_eq_support_sum ℕ S z hz
    (roughBlockCount z hz) (roughBlockCount_spec hz) η C hdb h n
  have hSupport := roughSupport_eq_interval lo hi z hz h
  calc
    (∑ d ∈ n.divisors, roughLambda z hz h d)
        = ∑ s ∈ supp.filter (fun s => s ⊆ bad), (-1 : ℝ) ^ s.card := by
          rw [hsumFilter, hinter, hsumReindex, hfilterBad]
    _ = Prelim.BlockSieve.Uval (roughBlockIndex z hz)
        (fun j => Erdos821.PrelimLemmas.Block ℕ S z j)
        (fun j => (j + 1) * h) bad := by
          change (∑ s ∈ (roughSupport z hz h).filter (fun s => s ⊆ bad),
            (-1 : ℝ) ^ s.card) = _
          rw [hSupport]
          exact hU.symm

theorem reciprocal_powerset_expansion (P : Finset ℕ) :
    (∑ s ∈ P.powerset, ∏ p ∈ s, (1 : ℝ) / (p : ℝ)) =
      ∏ p ∈ P, (1 + 1 / (p : ℝ)) := by
  classical
  induction P using Finset.induction with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.sum_powerset_insert hp]
    have hinsert :
        (∑ s ∈ P.powerset, ∏ q ∈ insert p s, (1 : ℝ) / (q : ℝ)) =
          (1 / (p : ℝ)) * ∑ s ∈ P.powerset,
            ∏ q ∈ s, (1 : ℝ) / (q : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hps : p ∉ s := fun hp' => hp ((Finset.mem_powerset.mp hs) hp')
      rw [Finset.prod_insert hps]
    rw [hinsert, ih, Finset.prod_insert hp]
    ring

theorem roughLambda_reciprocal_sum_le (z : ℝ) (hz : 1 < z) (h : ℕ) :
    (∑ d ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊,
      |roughLambda z hz h d| / (d : ℝ)) ≤
      ∏ p ∈ Erdos821.Blueprint.primesUpTo z, (1 + 1 / (p : ℝ)) := by
  let supp := roughSupport z hz h
  let Uset := roughUDivisorSet z hz h
  let productIndex : Finset ℕ → ℕ := fun s => ∏ p ∈ s, p
  have hInj : Set.InjOn productIndex (↑supp : Set (Finset ℕ)) := by
    intro s hs t ht heq
    exact roughSupport_product_injective (Finset.mem_coe.mp hs)
      (Finset.mem_coe.mp ht) heq
  have hUsub : Uset ⊆ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊ := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨s, hs, rfl⟩
    have hprime : ∀ p ∈ s, p.Prime := fun p hp => roughSupport_prime hs hp
    have hlevel : (∏ p ∈ s, (p : ℝ)) ≤ z ^ (4 * h + 2) := by
      have hslevel : s ∈ Prelim.BlockSieve.SieveSupport
          ((Finset.range (roughBlockCount z hz)).biUnion
            (fun j => Erdos821.PrelimLemmas.Block ℕ
              (intervalSieveData 1 1 z) z j))
          (Finset.range (roughBlockCount z hz))
          (fun j => Erdos821.PrelimLemmas.Block ℕ (intervalSieveData 1 1 z) z j)
          (fun j => (j + 1) * h) := by
        simpa [roughSupport, roughBlockIndex, roughBlock] using hs
      exact Erdos821.PrelimLemmas.support_level_le ℕ (intervalSieveData 1 1 z)
        z hz h (roughBlockCount z hz) s hslevel
    have hdcast : ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := Nat.cast_prod _ _
    have hfloor : ∏ p ∈ s, p ≤ ⌊z ^ (4 * h + 2)⌋₊ :=
      Nat.le_floor (hdcast ▸ hlevel)
    have hone : 1 ≤ ∏ p ∈ s, p := by
      apply Finset.one_le_prod
      intro p hp
      exact hprime p hp |>.one_le
    exact Finset.mem_Icc.mpr ⟨hone, hfloor⟩
  have hsumEq :
      (∑ d ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊,
        |roughLambda z hz h d| / (d : ℝ)) =
        ∑ d ∈ Uset, 1 / (d : ℝ) := by
    calc
      _ = ∑ d ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊,
          (if d ∈ Uset then 1 / (d : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            by_cases hmem : d ∈ Uset
            · simp [roughLambda, Uset, hmem, one_div]
            · simp [roughLambda, Uset, hmem, one_div]
      _ = ∑ d ∈ (Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊).filter (· ∈ Uset),
          1 / (d : ℝ) := by
            symm
            rw [Finset.sum_filter]
      _ = ∑ d ∈ Uset.filter (· ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊),
          1 / (d : ℝ) := by
            have hcomm : (Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊).filter (· ∈ Uset) =
                Uset.filter (· ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊) := by
              ext d
              simp [and_comm]
            rw [hcomm]
      _ = ∑ d ∈ Uset, 1 / (d : ℝ) := by
            rw [Finset.filter_eq_self.mpr hUsub]
  have hsumImage :
      (∑ d ∈ Uset, 1 / (d : ℝ)) =
        ∑ s ∈ supp, ∏ p ∈ s, 1 / (p : ℝ) := by
    change (∑ d ∈ supp.image productIndex, 1 / (d : ℝ)) = _
    rw [Finset.sum_image hInj]
    apply Finset.sum_congr rfl
    intro s hs
    have hcast : ((productIndex s : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := Nat.cast_prod _ _
    rw [hcast]
    simp only [one_div]
    exact (Finset.prod_inv_distrib (s := s) (fun p : ℕ => (p : ℝ))).symm
  have hsubset : supp ⊆ (Erdos821.Blueprint.primesUpTo z).powerset := by
    intro s hs
    exact Finset.mem_powerset.mpr (roughSupport_subset_primes hs)
  have hsumLe :
      (∑ s ∈ supp, ∏ p ∈ s, 1 / (p : ℝ)) ≤
        ∑ s ∈ (Erdos821.Blueprint.primesUpTo z).powerset,
          ∏ p ∈ s, 1 / (p : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro s hs _
    positivity
  calc
    (∑ d ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊,
        |roughLambda z hz h d| / (d : ℝ))
        = ∑ d ∈ Uset, 1 / (d : ℝ) := hsumEq
    _ = ∑ s ∈ supp, ∏ p ∈ s, 1 / (p : ℝ) := hsumImage
    _ ≤ ∑ s ∈ (Erdos821.Blueprint.primesUpTo z).powerset,
        ∏ p ∈ s, 1 / (p : ℝ) := hsumLe
    _ = ∏ p ∈ Erdos821.Blueprint.primesUpTo z, (1 + 1 / (p : ℝ)) :=
        reciprocal_powerset_expansion _

theorem rough_iff_badFinset_empty (z : ℝ) (hz : 2 ≤ z) (n : ℕ) (hn : 0 < n) :
    Erdos821.Blueprint.Analytic.rough z n ↔
      Erdos821.PrelimLemmas.badFinset ℕ (intervalSieveData 1 1 z) n = ∅ := by
  let S := intervalSieveData 1 1 z
  have hNoBad : Erdos821.Blueprint.Analytic.rough z n ↔
      ∀ p ∈ S.primes, ¬ p ∣ n := by
    constructor
    · rintro ⟨_, hrough⟩ p hp hdiv
      have hpPrime := S.prime p hp
      have hpz : (p : ℝ) ≤ z := by
        simpa [S, intervalSieveData] using
          (mem_primesUpTo_iff (by linarith [hz]) hpPrime).mp hp
      exact (not_lt_of_ge hpz) (hrough p hpPrime hdiv)
    · intro h
      refine ⟨hn, ?_⟩
      intro p hp hdiv
      by_contra hpnot
      have hpz : (p : ℝ) ≤ z := le_of_not_gt hpnot
      have hpMem : p ∈ S.primes := by
        simpa [S, intervalSieveData] using
          (mem_primesUpTo_iff (by linarith [hz]) hp).2 hpz
      exact h p hpMem hdiv
  have hEmpty :
      (Erdos821.PrelimLemmas.badFinset ℕ S n = ∅) ↔ ∀ p ∈ S.primes, ¬ p ∣ n := by
    unfold Erdos821.PrelimLemmas.badFinset
    constructor
    · intro hempty p hp hdiv
      have hmem : p ∈ S.primes.filter (fun q => S.bad q n) :=
        Finset.mem_filter.mpr ⟨hp, hdiv⟩
      simpa [hempty] using hmem
    · intro h
      rw [Finset.filter_eq_empty_iff]
      exact h
  exact hNoBad.trans hEmpty.symm

theorem roughLambda_pointwise (hc : Erdos821.Blueprint.ClassicalInputs)
    (z : ℝ) (hz : 2 ≤ z) (h : ℕ) (he : Even h) (n : ℕ) (hn : 0 < n) :
    (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0) ≤
      ∑ d ∈ n.divisors, roughLambda z (by linarith [hz]) h d := by
  obtain ⟨C, hC, hdbAll⟩ := intervalSieveData_densityBounds hc
  let S := intervalSieveData 1 1 z
  have hz1 : 1 < z := by linarith
  have hdb : S.densityBounds z (1 / 2) C := by
    exact hdbAll 1 1 z hz
  let J := roughBlockIndex z hz1
  let bad := Erdos821.PrelimLemmas.badFinset ℕ S n
  have hcov := Erdos821.PrelimLemmas.badFinset_covered ℕ S z hz1 (roughBlockCount z hz1)
    (roughBlockCount_spec hz1) (1 / 2) C hdb n
  have heJ : ∀ j ∈ J, Even ((j + 1) * h) := fun j _ => he.mul_left (j + 1)
  have hU := Prelim.BlockSieve.Uval_ge_avoid J
    (fun j => Erdos821.PrelimLemmas.Block ℕ S z j)
    (fun j => (j + 1) * h) bad hcov heJ
  have hInd : (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0) =
      (if bad = ∅ then (1 : ℝ) else 0) := by
    by_cases hr : Erdos821.Blueprint.Analytic.rough z n
    · have hb := (rough_iff_badFinset_empty z hz n hn).mp hr
      simp [hr, bad, S, hb]
    · have hb : bad ≠ ∅ := by
        intro hempty
        exact hr ((rough_iff_badFinset_empty z hz n hn).mpr (by simpa [bad, S] using hempty))
      simp [hr, bad, hb]
  have hDiv := roughLambda_divisor_sum_eq_Uval 1 1 z hz1 (1 / 2) C hdb h n hn
  calc
    (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0)
        = (if bad = ∅ then (1 : ℝ) else 0) := hInd
    _ ≤ Prelim.BlockSieve.Uval J (fun j => Erdos821.PrelimLemmas.Block ℕ S z j)
        (fun j => (j + 1) * h) bad := hU
    _ = ∑ d ∈ n.divisors, roughLambda z hz1 h d := hDiv.symm

theorem interval_multiples_count_bound (a b d : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hd : 0 < d) :
    |(((Finset.Icc a b).filter (fun n => d ∣ n)).card : ℝ) -
      ((Finset.Icc a b).card : ℝ) / (d : ℝ)| ≤ 1 := by
  let F := (Finset.Icc a b).filter (fun n => d ∣ n)
  let G := (Finset.Ioc 0 b).filter (fun n => d ∣ n)
  let H := (Finset.Ioc 0 (a - 1)).filter (fun n => d ∣ n)
  have hset : F = G \ H := by
    ext n
    simp only [F, G, H, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc, Finset.mem_sdiff]
    omega
  have hHG : H ⊆ G := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIoc, hdiv⟩
    rcases Finset.mem_Ioc.mp hnIoc with ⟨hnpos, hna⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ioc.mpr ⟨hnpos, le_trans hna (le_trans (Nat.sub_le _ _) hab)⟩, hdiv⟩
  have hcountNat : F.card = b / d - (a - 1) / d := by
    rw [hset, Finset.card_sdiff_of_subset hHG]
    simp [G, H, Nat.Ioc_filter_dvd_card_eq_div]
  have hcardNat : (Finset.Icc a b).card = b - (a - 1) := by
    rw [Nat.card_Icc]
    omega
  have hquot : (a - 1) / d ≤ b / d := Nat.div_le_div_right (by omega)
  have hcountR : (F.card : ℝ) = ((b / d : ℕ) : ℝ) - (((a - 1) / d : ℕ) : ℝ) := by
    rw [hcountNat, Nat.cast_sub hquot]
  have hcardR : ((Finset.Icc a b).card : ℝ) = (b : ℝ) - ((a - 1 : ℕ) : ℝ) := by
    rw [hcardNat, Nat.cast_sub (by omega)]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hmodB : b % d < d := Nat.mod_lt _ hd
  have hmodA : (a - 1) % d < d := Nat.mod_lt _ hd
  have hdecompB : (b : ℝ) = ((b / d : ℕ) : ℝ) * (d : ℝ) + ((b % d : ℕ) : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.mod_add_div b d)
    push_cast at h
    nlinarith [h]
  have hdecompA : ((a - 1 : ℕ) : ℝ) = (((a - 1) / d : ℕ) : ℝ) * (d : ℝ) +
      (((a - 1) % d : ℕ) : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.mod_add_div (a - 1) d)
    push_cast at h
    nlinarith [h]
  have hdecomp : (b : ℝ) - ((a - 1 : ℕ) : ℝ) =
      (((b / d : ℕ) : ℝ) - (((a - 1) / d : ℕ) : ℝ)) * (d : ℝ) +
        (((b % d : ℕ) : ℝ) - (((a - 1) % d : ℕ) : ℝ)) := by
    rw [hdecompB, hdecompA]
    ring
  have herror : (F.card : ℝ) - ((Finset.Icc a b).card : ℝ) / (d : ℝ) =
      ((((a - 1) % d : ℕ) : ℝ) - ((b % d : ℕ) : ℝ)) / (d : ℝ) := by
    rw [hcountR, hcardR, hdecomp]
    field_simp [ne_of_gt hdR]
    ring
  have hmodBcast : ((b % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmodB
  have hmodAcast : (((a - 1) % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hmodA
  have hmodBnonneg : 0 ≤ ((b % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmodAnonneg : 0 ≤ (((a - 1) % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrem : |(((a - 1) % d : ℕ) : ℝ) - ((b % d : ℕ) : ℝ)| ≤ (d : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [hmodBcast, hmodAcast, hmodBnonneg, hmodAnonneg, hdR]
  calc
    |(F.card : ℝ) - ((Finset.Icc a b).card : ℝ) / (d : ℝ)|
        = |(((a - 1) % d : ℕ) : ℝ) - ((b % d : ℕ) : ℝ)| / (d : ℝ) := by
          rw [herror, abs_div, abs_of_pos hdR]
    _ ≤ (d : ℝ) / (d : ℝ) := div_le_div_of_nonneg_right hrem hdR.le
    _ = 1 := div_self hdR.ne'

theorem sum_Uval_le_main_add_remainder (α : Type)
    (S : Erdos821.Blueprint.SieveData α) (z : ℝ) (hz : 1 < z)
    (Jmax : ℕ) (hJ : Erdos821.PrelimLemmas.Zscale z Jmax < 2)
    (η C : ℝ) (hdb : S.densityBounds z η C) (h : ℕ) :
    (∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Uval
      (Finset.range Jmax) (fun j => Erdos821.PrelimLemmas.Block α S z j)
      (fun j => (j + 1) * h) (Erdos821.PrelimLemmas.badFinset α S a)) ≤
      S.X * (∏ j ∈ Finset.range Jmax,
        Erdos821.PrelimLemmas.blockExpS (Erdos821.PrelimLemmas.Block α S z j)
          S.density ((j + 1) * h)) + S.remainderSum (z ^ (4 * h + 2 : ℕ)) := by
  let J := Finset.range Jmax
  let B := fun j => Erdos821.PrelimLemmas.Block α S z j
  let e := fun j => (j + 1) * h
  let P := J.biUnion B
  let supp := Prelim.BlockSieve.SieveSupport P J B e
  have hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂) := by
    intro j₁ hj₁ j₂ hj₂ hne
    exact Erdos821.PrelimLemmas.Block_disjoint α S z hz hne
  have hdouble := Erdos821.PrelimLemmas.sum_Uval_eq_double α S z hz Jmax hJ η C hdb h
  have hmain : (∑ s ∈ supp, (-1 : ℝ) ^ s.card * S.g (∏ p ∈ s, p)) =
      ∏ j ∈ J, Erdos821.PrelimLemmas.blockExpS (B j) S.density (e j) := by
    have hweight := Erdos821.PrelimLemmas.support_weighted_sum_eq J B e S.density hdisj
    have hg : ∀ s ∈ supp, S.g (∏ p ∈ s, p) = ∏ p ∈ s, S.density p := by
      intro s hs
      exact Erdos821.PrelimLemmas.g_prod_eq α S z Jmax h s hs
    calc
      (∑ s ∈ supp, (-1 : ℝ) ^ s.card * S.g (∏ p ∈ s, p))
          = ∑ s ∈ supp, (-1 : ℝ) ^ s.card * ∏ p ∈ s, S.density p := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [hg s hs]
      _ = ∏ j ∈ J, Erdos821.PrelimLemmas.blockExpS (B j) S.density (e j) := hweight
  have hcombine :
      (∑ a ∈ S.objects, S.weight a * Prelim.BlockSieve.Uval J B e
        (Erdos821.PrelimLemmas.badFinset α S a)) =
        S.X * (∏ j ∈ J, Erdos821.PrelimLemmas.blockExpS (B j) S.density (e j)) +
          ∑ s ∈ supp, (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p) := by
    rw [hdouble]
    calc
      (∑ s ∈ supp, ∑ a ∈ S.objects,
          if s ⊆ Erdos821.PrelimLemmas.badFinset α S a then
            S.weight a * (-1 : ℝ) ^ s.card else 0)
          = ∑ s ∈ supp, (-1 : ℝ) ^ s.card *
              (S.X * S.g (∏ p ∈ s, p) + S.remainder (∏ p ∈ s, p)) := by
                apply Finset.sum_congr rfl
                intro s hs
                exact Erdos821.PrelimLemmas.inner_sum_eq α S z Jmax h s hs
      _ = (∑ s ∈ supp,
            (S.X * ((-1 : ℝ) ^ s.card * S.g (∏ p ∈ s, p)) +
              (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p))) := by
                apply Finset.sum_congr rfl
                intro s hs
                ring
      _ = S.X * (∑ s ∈ supp, (-1 : ℝ) ^ s.card * S.g (∏ p ∈ s, p)) +
            ∑ s ∈ supp, (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = S.X * (∏ j ∈ J, Erdos821.PrelimLemmas.blockExpS (B j) S.density (e j)) +
            ∑ s ∈ supp, (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p) := by rw [hmain]
  have hterm : ∀ s ∈ supp,
      (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p) ≤ |S.remainder (∏ p ∈ s, p)| := by
    intro s hs
    rcases neg_one_pow_eq_or (R := ℝ) s.card with hsign | hsign
    · rw [hsign, one_mul]
      exact le_abs_self _
    · rw [hsign, neg_one_mul]
      exact neg_le_abs _
  have hsumAbs : (∑ s ∈ supp,
      (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p)) ≤
      ∑ s ∈ supp, |S.remainder (∏ p ∈ s, p)| := by
    apply Finset.sum_le_sum
    intro s hs
    exact hterm s hs
  have hInj := Erdos821.PrelimLemmas.support_prod_injOn α S z Jmax h
  have hImageEq : (∑ s ∈ supp, |S.remainder (∏ p ∈ s, p)|) =
      ∑ d ∈ supp.image (fun s : Finset ℕ => ∏ p ∈ s, p), |S.remainder d| := by
    rw [Finset.sum_image]
    intro s hs t ht heq
    exact hInj (Finset.mem_coe.mpr hs) (Finset.mem_coe.mpr ht) heq
  have hsub := Erdos821.PrelimLemmas.support_image_subset α S z hz Jmax h
    (z ^ (4 * h + 2 : ℕ)) rfl
  have hImageLe : (∑ d ∈ supp.image (fun s : Finset ℕ => ∏ p ∈ s, p),
      |S.remainder d|) ≤ S.remainderSum (z ^ (4 * h + 2 : ℕ)) := by
    unfold Erdos821.Blueprint.SieveData.remainderSum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro d hd hnot
    exact abs_nonneg _
  have hrem : (∑ s ∈ supp,
      (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p)) ≤
      S.remainderSum (z ^ (4 * h + 2 : ℕ)) := by
    calc
      (∑ s ∈ supp, (-1 : ℝ) ^ s.card * S.remainder (∏ p ∈ s, p))
          ≤ ∑ s ∈ supp, |S.remainder (∏ p ∈ s, p)| := hsumAbs
      _ = ∑ d ∈ supp.image (fun s : Finset ℕ => ∏ p ∈ s, p), |S.remainder d| := hImageEq
      _ ≤ S.remainderSum (z ^ (4 * h + 2 : ℕ)) := hImageLe
  rw [hcombine]
  linarith [hrem]

theorem intervalSieveData_remainder_abs_le (lo hi z D : ℝ)
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) {d : ℕ}
    (hd : d ∈ (intervalSieveData lo hi z).products D) :
    |(intervalSieveData lo hi z).remainder d| ≤ 1 := by
  let S := intervalSieveData lo hi z
  have hdm : d ∈ S.products D := by simpa [S] using hd
  have hdm' : d ∈ Finset.Icc 1 ⌊D⌋₊ ∧ Squarefree d ∧ d.primeFactors ⊆ S.primes := by
    simpa [S, intervalSieveData, Erdos821.Blueprint.SieveData.products] using hdm
  obtain ⟨hdIcc, hsq, hfactor⟩ := hdm'
  have hdpos : 0 < d := by
    have hd1 := (Finset.mem_Icc.mp hdIcc).1
    omega
  have hprime : ∀ p ∈ d.primeFactors, p.Prime := fun p hp => S.prime p (hfactor hp)
  have hpf : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
  let a := ⌈lo⌉₊
  let b := ⌊hi⌋₊
  have ha : 1 ≤ a := by
    have hcast : lo ≤ (a : ℝ) := Nat.le_ceil lo
    exact_mod_cast (le_trans hlo hcast)
  by_cases hab : a ≤ b
  · have hmon : ∀ n, S.monomial d n = (if d ∣ n then (1 : ℝ) else 0) := by
      intro n
      have hiff : (∀ p ∈ d.primeFactors, p ∣ n) ↔ d ∣ n := by
        have hprod := primeProduct_dvd_iff (s := d.primeFactors) (n := n) hprime
        rw [hpf] at hprod
        exact hprod.symm
      have hAllIff : (∀ p ∈ d.primeFactors, S.bad p n) ↔ d ∣ n := by
        simpa [intervalSieveData, S] using hiff
      unfold Erdos821.Blueprint.SieveData.monomial
      by_cases hdvd : d ∣ n
      · have hall := hAllIff.mpr hdvd
        rw [if_pos hall, if_pos hdvd]
      · have hnot : ¬ (∀ p ∈ d.primeFactors, S.bad p n) := by
          intro hall
          exact hdvd (hAllIff.mp hall)
        rw [if_neg hnot, if_neg hdvd]
    have hcount :
        (∑ n ∈ S.objects, S.weight n * S.monomial d n) =
          ((Finset.Icc a b).filter (fun n => d ∣ n)).card := by
      calc
        (∑ n ∈ S.objects, S.weight n * S.monomial d n)
            = ∑ n ∈ Finset.Icc a b, if d ∣ n then (1 : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro n hn
                change 1 * S.monomial d n = _
                rw [hmon n]
                simp
        _ = ((Finset.Icc a b).filter (fun n => d ∣ n)).card := by
              rw [← Finset.sum_filter]
              simp
    have hcastProd : ((∏ p ∈ d.primeFactors, p : ℕ) : ℝ) =
        ∏ p ∈ d.primeFactors, (p : ℝ) := Nat.cast_prod _ _
    have hgd : S.g d = 1 / (d : ℝ) := by
      change (∏ p ∈ d.primeFactors, 1 / (p : ℝ)) = 1 / (d : ℝ)
      calc
        ∏ p ∈ d.primeFactors, 1 / (p : ℝ)
            = (∏ p ∈ d.primeFactors, (p : ℝ))⁻¹ := by
                simp only [one_div]
                exact Finset.prod_inv_distrib (s := d.primeFactors) (fun p : ℕ => (p : ℝ))
        _ = (d : ℝ)⁻¹ := by rw [← hcastProd, hpf]
        _ = 1 / (d : ℝ) := by rw [one_div]
    have hX : S.X = ((Finset.Icc a b).card : ℝ) := rfl
    have hcountErr := interval_multiples_count_bound a b d ha hab hdpos
    unfold Erdos821.Blueprint.SieveData.remainder
    rw [hcount, hX, hgd]
    have hdiv : ((Finset.Icc a b).card : ℝ) * (1 / (d : ℝ)) =
        ((Finset.Icc a b).card : ℝ) / (d : ℝ) := by ring
    rw [hdiv]
    exact hcountErr
  · have hEmpty : Finset.Icc a b = ∅ := by
      exact Finset.Icc_eq_empty hab
    have hObjects : S.objects = ∅ := by
      change Finset.Icc a b = ∅
      exact hEmpty
    have hX : S.X = 0 := by
      change ((Finset.Icc a b).card : ℝ) = 0
      rw [hEmpty]
      simp
    unfold Erdos821.Blueprint.SieveData.remainder
    rw [hObjects, hX]
    change |(0 : ℝ) - 0 * S.g d| ≤ 1
    norm_num

theorem intervalSieveData_remainderSum_le (lo hi z D : ℝ)
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hD : 1 ≤ D) :
    (intervalSieveData lo hi z).remainderSum D ≤ D := by
  let S := intervalSieveData lo hi z
  have hterm : ∀ d ∈ S.products D, |S.remainder d| ≤ 1 := by
    intro d hd
    exact intervalSieveData_remainder_abs_le lo hi z D hlo hlohi hd
  have hcard : (S.products D).card ≤ ⌊D⌋₊ := by
    calc
      (S.products D).card ≤ (Finset.Icc 1 ⌊D⌋₊).card :=
        Finset.card_mono (Finset.filter_subset _ _)
      _ = ⌊D⌋₊ := by rw [Nat.card_Icc]; omega
  unfold Erdos821.Blueprint.SieveData.remainderSum
  calc
    (∑ d ∈ S.products D, |S.remainder d|)
        ≤ ∑ _d ∈ S.products D, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro d hd
            exact hterm d hd
    _ = (S.products D).card := by simp
    _ ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast hcard
    _ ≤ D := Nat.floor_le (by linarith)

theorem intervalSieveData_X_le_span_add_one (lo hi z : ℝ)
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    (intervalSieveData lo hi z).X ≤ hi - lo + 1 := by
  let a := ⌈lo⌉₊
  let b := ⌊hi⌋₊
  have hceilLe : a ≤ b + 1 := by
    calc
      a ≤ ⌈hi⌉₊ := Nat.ceil_le_ceil hlohi
      _ ≤ b + 1 := Nat.ceil_le_floor_add_one hi
  have hcard : (Finset.Icc a b).card = b + 1 - a := Nat.card_Icc a b
  have hX : (intervalSieveData lo hi z).X = (b : ℝ) + 1 - (a : ℝ) := by
    change ((Finset.Icc a b).card : ℝ) = _
    rw [hcard, Nat.cast_sub hceilLe]
    push_cast
    ring
  have hceil : lo ≤ (a : ℝ) := Nat.le_ceil lo
  have hfloor : (b : ℝ) ≤ hi := Nat.floor_le (by linarith)
  rw [hX]
  nlinarith

theorem roughLambda_interval_overcount_bound
    (hc : Erdos821.Blueprint.ClassicalInputs) :
    ∃ K : ℝ, 0 < K ∧ ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → Even h →
      ∀ z : ℝ, ∀ hz : 2 ≤ z, ∀ hz1 : 1 < z, ∀ lo hi : ℝ, 1 ≤ lo → lo ≤ hi →
        (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
          ((∑ d ∈ n.divisors, roughLambda z hz1 h d) -
            (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0))) ≤
          K * ((hi - lo) * Real.exp (-((h : ℝ))) + z ^ (4 * h + 2 : ℕ)) := by
  obtain ⟨C, hC, hdbAll⟩ := intervalSieveData_densityBounds hc
  obtain ⟨h₀N, h₀, hh₀, hcorrBound⟩ :=
    Erdos821.PrelimLemmas.exists_corr_error_bound (1 / 2) C (by norm_num) hC.le
  refine ⟨h₀ + 2, ?_⟩
  constructor
  · linarith
  · refine ⟨h₀N, ?_⟩
    intro h hh he z hz hz1 lo hi hlo hlohi
    let S := intervalSieveData lo hi z
    let N := roughBlockCount z hz1
    let J := Finset.range N
    let B := fun j => Erdos821.PrelimLemmas.Block ℕ S z j
    let e := fun j => (j + 1) * h
    let D : ℝ := z ^ (4 * h + 2 : ℕ)
    have hJ : Erdos821.PrelimLemmas.Zscale z N < 2 := roughBlockCount_spec hz1
    have hdb : S.densityBounds z (1 / 2) C := hdbAll lo hi z hz
    have hD1 : 1 ≤ D := by
      dsimp [D]
      exact one_le_pow₀ (by linarith [hz])
    have hRsum := intervalSieveData_remainderSum_le lo hi z D hlo hlohi hD1
    have hXle := intervalSieveData_X_le_span_add_one lo hi z hlo hlohi
    have hsumB : ∀ j ∈ J, ∑ p ∈ B j, S.density p ≤ C := by
      intro j hj
      exact Erdos821.PrelimLemmas.Block_mass_le ℕ S z (1 / 2) C hdb j
    have hgB : ∀ j ∈ J, ∀ p ∈ B j,
        0 ≤ S.density p ∧ S.density p ≤ 1 - (1 / 2 : ℝ) := by
      intro j hj p hp
      have hpS := Erdos821.PrelimLemmas.Block_subset ℕ S z j hp
      rcases hdb.2.2.1 p hpS with ⟨_, hnonneg, hupper⟩
      exact ⟨hnonneg, hupper⟩
    have hdisj : ∀ j₁ ∈ J, ∀ j₂ ∈ J, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂) := by
      intro j₁ hj₁ j₂ hj₂ hne
      exact Erdos821.PrelimLemmas.Block_disjoint ℕ S z hz1 hne
    have hcorr := hcorrBound h N hh he B S.density hgB hsumB
    have hAj0 : ∀ j ∈ J,
        0 ≤ Erdos821.PrelimLemmas.blockExpA (B j) S.density := by
      intro j hj
      unfold Erdos821.PrelimLemmas.blockExpA
      apply Finset.prod_nonneg
      intro p hp
      have hpS := Erdos821.PrelimLemmas.Block_subset ℕ S z j hp
      have hden := hdb.2.2.1 p hpS
      linarith [hden.2.1, hden.2.2]
    have hAj1 : ∀ j ∈ J,
        Erdos821.PrelimLemmas.blockExpA (B j) S.density ≤ 1 := by
      intro j hj
      unfold Erdos821.PrelimLemmas.blockExpA
      apply Finset.prod_le_one₀
      · intro p hp
        have hpS := Erdos821.PrelimLemmas.Block_subset ℕ S z j hp
        have hden := hdb.2.2.1 p hpS
        linarith [hden.2.1, hden.2.2]
      · intro p hp
        have hpS := Erdos821.PrelimLemmas.Block_subset ℕ S z j hp
        exact sub_le_self _ (hdb.2.2.1 p hpS).2.1
    have hAprod : (∏ j ∈ J, Erdos821.PrelimLemmas.blockExpA (B j) S.density) ≤ 1 := by
      apply Finset.prod_le_one₀
      · exact hAj0
      · exact hAj1
    have hexpNonneg : 0 ≤ Real.exp (-((h : ℝ))) := (Real.exp_pos _).le
    have hCorrSimple : Erdos821.PrelimLemmas.corrExp N B S.density h ≤
        h₀ * Real.exp (-((h : ℝ))) := by
      calc Erdos821.PrelimLemmas.corrExp N B S.density h
          ≤ h₀ * Real.exp (-((h : ℝ))) *
              ∏ j ∈ J, Erdos821.PrelimLemmas.blockExpA (B j) S.density := hcorr
        _ = (h₀ * Real.exp (-((h : ℝ)))) *
              (∏ j ∈ J, Erdos821.PrelimLemmas.blockExpA (B j) S.density) := by rfl
        _ ≤ (h₀ * Real.exp (-((h : ℝ)))) * 1 :=
            mul_le_mul_of_nonneg_left hAprod (mul_nonneg hh₀.le hexpNonneg)
        _ = h₀ * Real.exp (-((h : ℝ))) := by ring
    have hUupper := sum_Uval_le_main_add_remainder ℕ S z hz1 N hJ
      (1 / 2) C hdb h
    have hLower := Erdos821.PrelimLemmas.sifted_ge_main_sub_remainder ℕ S z hz1 N hJ
      (1 / 2) C hdb h he
    have hVexp := Erdos821.PrelimLemmas.weighted_V_eq_corrExp N h B S.density hdisj he
    rw [hVexp] at hLower
    have hroughSifted :
        (∑ n ∈ S.objects,
          (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0)) = S.sifted := by
      unfold Erdos821.Blueprint.SieveData.sifted
      apply Finset.sum_congr rfl
      intro n hn
      have hnIcc : n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := by
        simpa [S, intervalSieveData] using hn
      have hnpos : 0 < n := by
        have ha : 1 ≤ ⌈lo⌉₊ := by
          have hc : lo ≤ (⌈lo⌉₊ : ℝ) := Nat.le_ceil lo
          exact_mod_cast (le_trans hlo hc)
        have hnlo := (Finset.mem_Icc.mp hnIcc).1
        omega
      have hroughBad : Erdos821.Blueprint.Analytic.rough z n ↔
          ∀ p ∈ S.primes, ¬ S.bad p n := by
        have hroughEmpty := rough_iff_badFinset_empty z hz n hnpos
        have hbadEq : Erdos821.PrelimLemmas.badFinset ℕ S n =
            Erdos821.PrelimLemmas.badFinset ℕ (intervalSieveData 1 1 z) n := by
          ext p
          simp [Erdos821.PrelimLemmas.badFinset, S, intervalSieveData]
        have hroughEmptyS : Erdos821.Blueprint.Analytic.rough z n ↔
            Erdos821.PrelimLemmas.badFinset ℕ S n = ∅ := by
          simpa [hbadEq.symm] using hroughEmpty
        have hfilter : (Erdos821.PrelimLemmas.badFinset ℕ S n = ∅) ↔
            ∀ p ∈ S.primes, ¬ S.bad p n := by
          unfold Erdos821.PrelimLemmas.badFinset
          rw [Finset.filter_eq_empty_iff]
        exact hroughEmptyS.trans hfilter
      by_cases hr : Erdos821.Blueprint.Analytic.rough z n
      · have hno := hroughBad.mp hr
        change (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0) =
          (if ∀ p ∈ S.primes, ¬ S.bad p n then S.weight n else 0)
        rw [if_pos hr, if_pos hno]
        simp [S, intervalSieveData]
      · have hno : ¬ ∀ p ∈ S.primes, ¬ S.bad p n := fun hno => hr (hroughBad.mpr hno)
        change (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0) =
          (if ∀ p ∈ S.primes, ¬ S.bad p n then S.weight n else 0)
        rw [if_neg hr, if_neg hno]
    have hLambdaTotal :
        (∑ n ∈ S.objects, ∑ d ∈ n.divisors, roughLambda z hz1 h d) =
          ∑ n ∈ S.objects, S.weight n * Prelim.BlockSieve.Uval J B e
            (Erdos821.PrelimLemmas.badFinset ℕ S n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnIcc : n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊ := by
        simpa [S, intervalSieveData] using hn
      have ha : 1 ≤ ⌈lo⌉₊ := by
        have hc : lo ≤ (⌈lo⌉₊ : ℝ) := Nat.le_ceil lo
        exact_mod_cast (le_trans hlo hc)
      have hnpos : 0 < n := by
        have hnle := (Finset.mem_Icc.mp hnIcc).1
        omega
      simpa [S, intervalSieveData, J, N, B, e, roughBlockIndex] using
        (roughLambda_divisor_sum_eq_Uval lo hi z hz1 (1 / 2) C hdb h n hnpos)
    have hOverEq :
        (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
          ((∑ d ∈ n.divisors, roughLambda z hz1 h d) -
            (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0))) =
          (∑ n ∈ S.objects, S.weight n * Prelim.BlockSieve.Uval J B e
            (Erdos821.PrelimLemmas.badFinset ℕ S n)) - S.sifted := by
      change (∑ n ∈ S.objects,
        ((∑ d ∈ n.divisors, roughLambda z hz1 h d) -
          (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0))) = _
      rw [Finset.sum_sub_distrib, hLambdaTotal, hroughSifted]
    have hDiff :
        (∑ n ∈ S.objects, S.weight n * Prelim.BlockSieve.Uval J B e
          (Erdos821.PrelimLemmas.badFinset ℕ S n)) - S.sifted ≤
            S.X * Erdos821.PrelimLemmas.corrExp N B S.density h +
              2 * S.remainderSum D := by
      nlinarith [hUupper, hLower]
    have hDrem := intervalSieveData_remainderSum_le lo hi z D hlo hlohi hD1
    have hXle := intervalSieveData_X_le_span_add_one lo hi z hlo hlohi
    have hexpLeOne : Real.exp (-((h : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hh0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
      linarith
    have hXnonneg : 0 ≤ S.X := S.X_nonneg
    have hAfterCorr :
        S.X * Erdos821.PrelimLemmas.corrExp N B S.density h + 2 * S.remainderSum D ≤
          (hi - lo) * Real.exp (-((h : ℝ))) * h₀ + (h₀ + 2) * D := by
      calc
        _ ≤ S.X * (h₀ * Real.exp (-((h : ℝ)))) + 2 * D := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hCorrSimple hXnonneg)
                (mul_le_mul_of_nonneg_left hDrem (by norm_num))
        _ ≤ (hi - lo + 1) * (h₀ * Real.exp (-((h : ℝ)))) + 2 * D := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right hXle (mul_nonneg hh₀.le hexpNonneg))
                le_rfl
        _ = (hi - lo) * Real.exp (-((h : ℝ))) * h₀ +
              h₀ * Real.exp (-((h : ℝ))) + 2 * D := by ring
        _ ≤ (hi - lo) * Real.exp (-((h : ℝ))) * h₀ + h₀ * D + 2 * D := by
              have hexpD : Real.exp (-((h : ℝ))) ≤ D := le_trans hexpLeOne hD1
              have hmul := mul_le_mul_of_nonneg_left hexpD hh₀.le
              nlinarith
        _ = (hi - lo) * Real.exp (-((h : ℝ))) * h₀ + (h₀ + 2) * D := by ring
    have hlength_nonneg : 0 ≤ hi - lo := sub_nonneg.mpr hlohi
    calc
      (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
          ((∑ d ∈ n.divisors, roughLambda z hz1 h d) -
            (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0)))
          = (∑ n ∈ S.objects, S.weight n * Prelim.BlockSieve.Uval J B e
              (Erdos821.PrelimLemmas.badFinset ℕ S n)) - S.sifted := hOverEq
      _ ≤ S.X * Erdos821.PrelimLemmas.corrExp N B S.density h +
            2 * S.remainderSum D := hDiff
      _ ≤ (hi - lo) * Real.exp (-((h : ℝ))) * h₀ + (h₀ + 2) * D := hAfterCorr
      _ ≤ (h₀ + 2) * ((hi - lo) * Real.exp (-((h : ℝ)) ) + D) := by
            nlinarith [hlength_nonneg, hexpNonneg]

end Erdos821.P2Rough

namespace Erdos821.Blueprint

open Erdos821.P2Rough

theorem roughPolynomial_proof (hc : ClassicalInputs) : RoughPolynomial := by
  obtain ⟨Kharm, hKharm, hprimeProduct⟩ := primeProductHarmonicBound hc
  obtain ⟨Kover, hKover, h₀, hover⟩ := roughLambda_interval_overcount_bound hc
  let K : ℝ := Kharm + Kover + 1
  have hK : 0 < K := by
    dsimp [K]
    linarith
  refine ⟨K, hK, h₀, ?_⟩
  intro h hh he z hz
  have hz1 : 1 < z := by linarith
  refine ⟨fun d => roughLambda z hz1 h d, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    exact roughLambda_abs_le z hz1 h d
  · intro d hd
    exact roughLambda_support (z := z) (hz := hz1) (h := h) hd
  · intro n hn
    exact roughLambda_pointwise hc z hz h he n hn
  · have hrecip := roughLambda_reciprocal_sum_le z hz1 h
    have hprod := hprimeProduct z hz
    have hlog : 0 ≤ Real.log (2 * z) := by
      apply le_of_lt
      apply Real.log_pos
      nlinarith
    calc
      (∑ d ∈ Finset.Icc 1 ⌊z ^ (4 * h + 2)⌋₊,
        |roughLambda z hz1 h d| / d)
          ≤ ∏ p ∈ Erdos821.Blueprint.primesUpTo z, (1 + 1 / (p : ℝ)) := hrecip
      _ ≤ Kharm * Real.log (2 * z) := hprod
      _ ≤ K * Real.log (2 * z) := by
          apply mul_le_mul_of_nonneg_right _ hlog
          dsimp [K]
          linarith
  · intro lo hi hlo hlohi
    have hbound := hover h hh he z hz hz1 lo hi hlo hlohi
    have hfactor : 0 ≤ (hi - lo) * Real.exp (-((h : ℝ))) + z ^ (4 * h + 2 : ℕ) := by
      positivity
    calc
      (∑ n ∈ Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊,
        ((∑ d ∈ n.divisors, roughLambda z hz1 h d) -
          (if Erdos821.Blueprint.Analytic.rough z n then (1 : ℝ) else 0)))
          ≤ (Kover) * ((hi - lo) * Real.exp (-((h : ℝ))) + z ^ (4 * h + 2 : ℕ)) := hbound
      _ ≤ K * ((hi - lo) * Real.exp (-((h : ℝ))) + z ^ (4 * h + 2 : ℕ)) := by
          apply mul_le_mul_of_nonneg_right _ hfactor
          dsimp [K]
          linarith

example (hc : ClassicalInputs) : RoughPolynomial := roughPolynomial_proof hc


end Erdos821.Blueprint
